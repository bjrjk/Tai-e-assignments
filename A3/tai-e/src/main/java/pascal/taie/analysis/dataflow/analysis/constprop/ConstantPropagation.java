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
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
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

        if (stmt instanceof DefinitionStmt defStmt && defStmt.getLValue() instanceof Var lVar) {
            CPFact newOut = in.copy();

            if (canHoldInt(lVar)) {
                RValue rValue = defStmt.getRValue();
                Value lAbstractValue = evaluate(rValue, in);
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
            equalFlag = out.equals(in);
            if (!equalFlag)
                out.copyFrom(in);
        }
        return !equalFlag;
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
    public static Value evaluate(Exp exp, CPFact in) {
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
        // Return NAC according to requirements.
        else
            return Value.getNAC();
    }
}
