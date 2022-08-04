/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.AbstractMap.SimpleImmutableEntry;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    private PointerAnalysisResult pta;
    private DataflowResult<Stmt, CPFact> DFResult;
    private final Map<Obj, Set<Var>> rPointsToSet;
    private final Map<SimpleImmutableEntry<Obj, FieldRef>, Value> objFieldConstValue;
    private final Map<FieldAccess, Value> fieldAccessConstValue;
    private final Map<FieldRef, Set<LoadField>> staticFieldStore2LoadMap;
    private final Map<SimpleImmutableEntry<Obj, Value>, Value> objElemConstValue;
    private final Map<ArrayAccess, Map<Value, Value>> arrayAccessConstValue;
    private final Map<LoadArray, Set<SimpleImmutableEntry<Obj, Value>>> loadArrayPropagationQueueMap;

    private Queue<Stmt> workList;

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
        this.rPointsToSet = new HashMap<>();
        this.objFieldConstValue = new HashMap<>();
        this.fieldAccessConstValue = new HashMap<>();
        this.staticFieldStore2LoadMap = new HashMap<>();
        this.objElemConstValue = new HashMap<>();
        this.arrayAccessConstValue = new HashMap<>();
        this.loadArrayPropagationQueueMap = new HashMap<>();
    }

    public void setInternalData(Queue<Stmt> workList, DataflowResult<Stmt, CPFact> DFResult) {
        this.workList = workList;
        this.DFResult = DFResult;
    }
    public void initializePTA(PointerAnalysisResult pta, ICFG<JMethod, Stmt> icfg) {
        this.pta = pta;
        // Initialize Reverse Points-To Set
        for (Var var: pta.getVars()) {
            for (Obj obj: pta.getPointsToSet(var)) {
                rPointsToSet.computeIfAbsent(obj, (key) -> new HashSet<Var>());
                rPointsToSet.get(obj).add(var);
            }
        }
        // Initialize Static StoreField to LoadField Mapping
        Set<StoreField> storeFieldSet = new HashSet<StoreField>();
        Set<LoadField> loadFieldSet = new HashSet<LoadField>();
        for (Stmt stmt: icfg) {
            if (stmt instanceof StoreField storeField && storeField.isStatic())
                storeFieldSet.add(storeField);
            else if (stmt instanceof LoadField loadField && loadField.isStatic())
                loadFieldSet.add(loadField);
        }
        for (StoreField storeField: storeFieldSet) {
            FieldAccess storeFieldAccess = storeField.getLValue();
            FieldRef staticFieldRef = storeFieldAccess.getFieldRef();
            staticFieldStore2LoadMap.computeIfAbsent(staticFieldRef, (key) -> new HashSet<>());
            for (LoadField loadField: loadFieldSet) {
                if (storeFieldAccess.getFieldRef() == loadField.getFieldRef()) {
                    staticFieldStore2LoadMap.get(staticFieldRef).add(loadField);
                }
            }
        }
    }

    public static SimpleImmutableEntry<Obj, FieldRef> FA2Pair(Obj obj, FieldRef field) {
        return new SimpleImmutableEntry<>(obj, field);
    }

    public static SimpleImmutableEntry<Obj, Value> AA2Pair(Obj arrayObj, Value arrayIndexVal) {
        return new SimpleImmutableEntry<Obj, Value>(arrayObj, arrayIndexVal);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact boundFact = new CPFact();
        // Initialize the fact of parameters of method to NAC as we don't implement inter-procedural analysis.
        IR methodBody = cfg.getIR();
        List<Var> paramList = methodBody.getParams();
        for (Var param: paramList) {
            // We only focus on the analysis of int constant propagation.
            if (canHoldInt(param))
                boundFact.update(param, Value.getNAC());
        }
        /* Output doesn't contain `this`.
        // Initialize the fact of `this` variable in method to NAC as we don't implement inter-procedural analysis.
        Var methodThis = methodBody.getThis();
        if (methodThis != null) {
            boundFact.update(methodThis, Value.getNAC());
        }
         */
        // As absence are used as UNDEF in CPFact, this is no need to initialize other variables' fact.
        return boundFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // Union the fact exists in `target` first
        target.forEach((Var var, Value valTarget) -> { // Mention that `valTarget` cannot be UNDEF
            Value valFact = fact.get(var);
            target.update(var, meetValue(valTarget, valFact));
        });
        // Add the left element in `fact` to `target`
        fact.forEach((Var var, Value valFact) -> { // Mention that `valFact` cannot be UNDEF
            Value valTarget = target.get(var);
            target.update(var, meetValue(valTarget, valFact));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // NAC meet v = NAC
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
            // UNDEF meet v = v
        else if (v1.isUndef() || v2.isUndef()) {
            // Mention that the `Value` type is immutable, so we can return them directly.
            if (v1.isUndef())
                return v2;
            else
                return v1;
        }
        // v meet v = ?
        else if (v1.isConstant() && v2.isConstant()) {
            // c meet c = c
            if (v1.equals(v2))
                return v1;
                // c1 meet c2 = NAC
            else
                return Value.getNAC();
        }
        // Unreachable code path
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean equalFlag;

        if (stmt instanceof DefinitionStmt defStmt && defStmt.getLValue() instanceof Var lVar) { // LHS: Var
            CPFact newOut = in.copy();

            if (canHoldInt(lVar)) {
                RValue rValue = defStmt.getRValue();
                Value lAbstractValue = Value.getUndef();
                if (defStmt instanceof LoadArray LAStmt) {
                    ArrayAccess RAAccess = LAStmt.getRValue();
                    Value arrayIndexVal = evaluate(RAAccess.getIndex(), in);
                    if (!arrayIndexVal.isUndef()) {
                        loadArrayPropagationQueueMap.computeIfAbsent(LAStmt, (key) -> new HashSet<>());
                        Set<SimpleImmutableEntry<Obj, Value>> propagationQueue = loadArrayPropagationQueueMap.get(LAStmt);
                        for (SimpleImmutableEntry<Obj, Value> ObjValPair: propagationQueue) {
                            Value arrayIndexVal2 = ObjValPair.getValue();
                            if (isArrayAlias(arrayIndexVal, arrayIndexVal2)) {
                                //propagateArrayAlias(ObjValPair.getKey(), RAAccess);
                                lAbstractValue = meetValue(lAbstractValue, getObjRAAccessValue(ObjValPair.getKey(), arrayIndexVal));
                            }
                        }
                    }
                }
                else
                    lAbstractValue = evaluate(rValue, in);
                newOut.update(lVar, lAbstractValue);
            }
            else
                newOut.update(lVar, Value.getUndef());

            equalFlag = newOut.equals(out);
            if (!equalFlag)
                out.copyFrom(newOut);
        }
        // Identity function
        else {
            if (stmt instanceof StoreField SFStmt && canHoldInt(SFStmt.getRValue())) {
                // Process `x.a = y;`
                FieldAccess LFAccess = SFStmt.getLValue();

                if (!SFStmt.isStatic() && LFAccess instanceof InstanceFieldAccess LIFAccess) {
                    for (Obj storeObj: pta.getPointsToSet(LIFAccess.getBase())) {
                        SimpleImmutableEntry<Obj, FieldRef> LFAPair = FA2Pair(storeObj, LIFAccess.getFieldRef());
                        // Compute object field value
                        objFieldConstValue.computeIfAbsent(LFAPair, (key) -> Value.getUndef());
                        Value eRVal = evaluate(SFStmt.getRValue(), in);
                        Value nLVal = meetValue(objFieldConstValue.get(LFAPair), eRVal);
                        // If the object field value changed, update it
                        if (!Objects.equals(objFieldConstValue.put(LFAPair, nLVal), nLVal)) {
                            // Propagate them to corresponding LoadFields
                            for (Var objAssocVar: rPointsToSet.get(storeObj)) {
                                for (LoadField loadField: objAssocVar.getLoadFields()) {
                                    // If field equals
                                    if (Objects.equals(LIFAccess.getFieldRef(), loadField.getFieldRef())) {
                                        FieldAccess RFAccess = loadField.getRValue();
                                        fieldAccessConstValue.computeIfAbsent(RFAccess, (key) -> Value.getUndef());
                                        // Update the RHS Value of `z = x.a;`
                                        fieldAccessConstValue.put(RFAccess,
                                                meetValue(fieldAccessConstValue.get(RFAccess), nLVal));
                                        // Add the statement to workList
                                        workList.add(loadField);
                                    }
                                }
                            }
                        }
                    }
                }
                else if(SFStmt.isStatic() && LFAccess instanceof StaticFieldAccess LSFAccess) {
                    SimpleImmutableEntry<Obj, FieldRef> FAPair = FA2Pair(null, LSFAccess.getFieldRef());
                    // Compute static field Value
                    objFieldConstValue.computeIfAbsent(FAPair, (key) -> Value.getUndef());
                    Value eRVal = evaluate(SFStmt.getRValue(), in);
                    Value nLVal = meetValue(objFieldConstValue.get(FAPair), eRVal);
                    // If the static field value changed, update it
                    if (!Objects.equals(objFieldConstValue.put(FAPair, nLVal), nLVal)) {
                        // Propagate them to corresponding LoadFields
                        for (LoadField loadField: staticFieldStore2LoadMap.get(LSFAccess.getFieldRef())) {
                            // Update the RHS Value of `z = x.a;`
                            objFieldConstValue.computeIfAbsent(FAPair, (key) -> Value.getUndef());
                            Value nRVal = meetValue(objFieldConstValue.get(FAPair), nLVal);
                            objFieldConstValue.put(FAPair, nRVal);
                            // Add the statement to workList
                            workList.add(loadField);
                        }
                    }
                }
                else
                    throw new AssertionError("Path shouldn't be reached");
            }
            else if (stmt instanceof StoreArray SAStmt && canHoldInt(SAStmt.getRValue())) {
                // Process `x[i] = y;`
                ArrayAccess LAAccess = SAStmt.getLValue();
                Var arrayVar = LAAccess.getBase(), arrayIndexVar = LAAccess.getIndex();
                Value arrayIndexVal = evaluate(arrayIndexVar, in);
                for (Obj storeObj: pta.getPointsToSet(LAAccess.getBase())) {
                    SimpleImmutableEntry<Obj, Value> LAAPair = AA2Pair(storeObj, arrayIndexVal);
                    if (!arrayIndexVal.isUndef()){ // When arrayIndexVal is UnDef, simply won't propagate
                        objElemConstValue.computeIfAbsent(LAAPair, (key) -> Value.getUndef());
                        Value eRVal = evaluate(SAStmt.getRValue(), in);
                        Value nLVal = meetValue(objElemConstValue.get(LAAPair), eRVal);
                        if (!Objects.equals(objElemConstValue.put(LAAPair, nLVal), nLVal)) {
                            if (arrayIndexVal.isConstant()) {
                                SimpleImmutableEntry<Obj, Value> LAAPairStar = AA2Pair(storeObj, Value.getUndef());
                                objElemConstValue.computeIfAbsent(LAAPairStar, (key) -> Value.getUndef());
                                objElemConstValue.put(LAAPair, meetValue(objElemConstValue.get(LAAPair), eRVal));
                            }
                            for (Var objAssocVar: rPointsToSet.get(storeObj)) {
                                for (LoadArray loadArray: objAssocVar.getLoadArrays()) {
                                    loadArrayPropagationQueueMap.computeIfAbsent(loadArray, (key) -> new HashSet<>());
                                    loadArrayPropagationQueueMap.get(loadArray).add(LAAPair);
                                    workList.add(loadArray);
                                }
                            }
                        }
                    }
                }
            }
            equalFlag = out.equals(in);
            if (!equalFlag)
                out.copyFrom(in);
        }
        return !equalFlag;
    }

    public Value getObjRAAccessValue(Obj obj, Value arrayIndexVal) {
        if (arrayIndexVal.isUndef())
            return Value.getUndef();
        else if (arrayIndexVal.isNAC()) {
            SimpleImmutableEntry<Obj, Value> LAAPairNAC = AA2Pair(obj, Value.getNAC());
            SimpleImmutableEntry<Obj, Value> LAAPairUnDef = AA2Pair(obj, Value.getUndef());
            objElemConstValue.computeIfAbsent(LAAPairNAC, (key) -> Value.getUndef());
            objElemConstValue.computeIfAbsent(LAAPairUnDef, (key) -> Value.getUndef());
            return meetValue(
                    objElemConstValue.get(LAAPairNAC),
                    objElemConstValue.get(LAAPairUnDef)
            );
        }
        else if (arrayIndexVal.isConstant()) {
            SimpleImmutableEntry<Obj, Value> LAAPairNAC = AA2Pair(obj, Value.getNAC());
            SimpleImmutableEntry<Obj, Value> LAAPairConst = AA2Pair(obj, arrayIndexVal);
            objElemConstValue.computeIfAbsent(LAAPairNAC, (key) -> Value.getUndef());
            objElemConstValue.computeIfAbsent(LAAPairConst, (key) -> Value.getUndef());
            return meetValue(
                    objElemConstValue.get(LAAPairNAC),
                    objElemConstValue.get(LAAPairConst)
            );
        }
        else {
            throw new AssertionError("Path shouldn't be reached");
        }
    }

    public boolean isArrayAlias(Value arrayIndexVal1, Value arrayIndexVal2) {
        if (arrayIndexVal1.isUndef() || arrayIndexVal2.isUndef())
            return false;
        if (arrayIndexVal1.isConstant() && arrayIndexVal2.isConstant())
            return arrayIndexVal1.equals(arrayIndexVal2);
        if (arrayIndexVal1.isNAC() || arrayIndexVal2.isNAC())
            return true;
        throw new AssertionError("Path shouldn't be reached");
    }

    public void propagateArrayAlias(Obj storeObj, ArrayAccess RAAccess) {
        for (Map.Entry<SimpleImmutableEntry<Obj, Value>, Value> entry: objElemConstValue.entrySet()) {
            if (!Objects.equals(entry.getKey().getKey(), storeObj)) continue;
            Value arrayIndexVal = entry.getKey().getValue(), arrayElemVal = entry.getValue();
            arrayAccessConstValue.computeIfAbsent(RAAccess, (key) -> new HashMap<>());
            Map<Value, Value> RAAccessMap = arrayAccessConstValue.get(RAAccess);
            RAAccessMap.computeIfAbsent(arrayIndexVal, (key) -> Value.getUndef());
            RAAccessMap.put(arrayIndexVal, meetValue(RAAccessMap.get(arrayIndexVal), arrayElemVal));
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            return in.get(var);
        }
        else if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        else if (exp instanceof BinaryExp binaryExp) {
            Value op1Val = evaluate(binaryExp.getOperand1(), in),
                    op2Val = evaluate(binaryExp.getOperand2(), in);
            BinaryExp.Op op = binaryExp.getOperator();

            /*
            Special corner case for division-by-0.
            Even if the dividend is NAC, result is UNDEF.
             */
            if (op2Val.isConstant() && op2Val.getConstant() == 0 &&
                    op instanceof ArithmeticExp.Op arithOp &&
                    (arithOp == ArithmeticExp.Op.DIV || arithOp == ArithmeticExp.Op.REM))
                return Value.getUndef();

            if (op1Val.isNAC() || op2Val.isNAC())
                return Value.getNAC();
            else if (op1Val.isConstant() && op2Val.isConstant()) {
                int resultRaw,
                        op1Raw = op1Val.getConstant(),
                        op2Raw = op2Val.getConstant();

                if (op instanceof ArithmeticExp.Op arithOp) {
                    try {
                        resultRaw = switch (arithOp) {
                            case ADD -> op1Raw + op2Raw;
                            case SUB -> op1Raw - op2Raw;
                            case MUL -> op1Raw * op2Raw;
                            case DIV -> op1Raw / op2Raw;
                            case REM -> op1Raw % op2Raw;
                        };
                    }
                    catch (ArithmeticException e) { // Divisor is 0.
                        return Value.getUndef();
                    }
                }
                else if (op instanceof ConditionExp.Op condExp) {
                    boolean resultBoolRaw = switch (condExp) {
                        case EQ -> op1Raw == op2Raw;
                        case NE -> op1Raw != op2Raw;
                        case LT -> op1Raw < op2Raw;
                        case GT -> op1Raw > op2Raw;
                        case LE -> op1Raw <= op2Raw;
                        case GE -> op1Raw >= op2Raw;
                    };
                    resultRaw = resultBoolRaw ? 1 : 0;
                }
                else if (op instanceof ShiftExp.Op shiftExp) {
                    resultRaw = switch (shiftExp) {
                        case SHL -> op1Raw << op2Raw;
                        case SHR -> op1Raw >> op2Raw;
                        case USHR -> op1Raw >>> op2Raw;
                    };
                }
                else if (op instanceof BitwiseExp.Op bitExp) {
                    resultRaw = switch (bitExp) {
                        case OR -> op1Raw | op2Raw;
                        case AND -> op1Raw & op2Raw;
                        case XOR -> op1Raw ^ op2Raw;
                    };
                }
                else
                    return Value.getNAC();

                return Value.makeConstant(resultRaw);
            }
            else
                return Value.getUndef();
        }
        else if (exp instanceof InstanceFieldAccess RIFAccess) {
            // Get RHS FieldAccess Value
            fieldAccessConstValue.computeIfAbsent(RIFAccess, (key) -> Value.getUndef());
            return fieldAccessConstValue.get(RIFAccess);
        }
        else if (exp instanceof StaticFieldAccess RSFAccess) {
            SimpleImmutableEntry<Obj, FieldRef> FAPair = FA2Pair(null, RSFAccess.getFieldRef());
            objFieldConstValue.computeIfAbsent(FAPair, (key) -> Value.getUndef());
            return objFieldConstValue.get(FAPair);
        }
        else if (exp instanceof ArrayAccess RAAccess) {
            throw new AssertionError("Path shouldn't be reached");
            /*
            Var arrayVar = RAAccess.getBase(), arrayIndexVar = RAAccess.getIndex();
            Value arrayIndexVal = evaluate(arrayIndexVar, in);
            if (arrayIndexVal.isUndef())
                return Value.getUndef();
            else if (arrayIndexVal.isNAC()) {
                arrayAccessConstValue.computeIfAbsent(RAAccess, (key) -> new HashMap<>());
                Map<Value, Value> RAAccessMap = arrayAccessConstValue.get(RAAccess);
                RAAccessMap.computeIfAbsent(Value.getUndef(), (key) -> Value.getUndef());
                RAAccessMap.computeIfAbsent(Value.getNAC(), (key) -> Value.getUndef());
                return meetValue(
                        RAAccessMap.get(Value.getUndef()),
                        RAAccessMap.get(Value.getNAC())
                );
            }
            else if (arrayIndexVal.isConstant()) {
                arrayAccessConstValue.computeIfAbsent(RAAccess, (key) -> new HashMap<>());
                Map<Value, Value> RAAccessMap = arrayAccessConstValue.get(RAAccess);
                RAAccessMap.computeIfAbsent(arrayIndexVal, (key) -> Value.getUndef());
                RAAccessMap.computeIfAbsent(Value.getNAC(), (key) -> Value.getUndef());
                return meetValue(
                        RAAccessMap.get(arrayIndexVal),
                        RAAccessMap.get(Value.getNAC())
                );
            }
            else {
                throw new AssertionError("Path shouldn't be reached");
            }
            */

        }
        // Return NAC according to requirements.
        else
            return Value.getNAC();
    }
}
