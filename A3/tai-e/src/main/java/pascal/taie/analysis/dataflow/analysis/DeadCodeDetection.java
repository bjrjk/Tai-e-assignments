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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Your task is to recognize dead code in ir and add it to deadCode
        deadCode.addAll(unreachableCodeAnalyze(cfg, constants));
        deadCode.addAll(deadVariableAnalyze(cfg, liveVars));
        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    private static Set<Stmt> unreachableCodeAnalyze(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex)),
                allStmt = cfg.getNodes(),
                visitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex)),
                unvisitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        /* Control-flow unreachable code detection */
        controlFlowUnreachableCodeDFS(cfg, visitedStmt, cfg.getEntry());
        calculateUnvisitedStmtAndJoinClear(allStmt, visitedStmt, unvisitedStmt, deadCode);
        /* Unreachable branch detection */
        unreachableBranchDFS(cfg, constants, visitedStmt, cfg.getEntry());
        calculateUnvisitedStmtAndJoinClear(allStmt, visitedStmt, unvisitedStmt, deadCode);
        return deadCode;
    }

    private static void controlFlowUnreachableCodeDFS(CFG<Stmt> cfg, Set<Stmt> visitedStmt, Stmt node) {
        if (visitedStmt.contains(node)) return;
        visitedStmt.add(node);
        for (Stmt succ: cfg.getSuccsOf(node)) {
            controlFlowUnreachableCodeDFS(cfg, visitedStmt, succ);
        }
    }

    private static void unreachableBranchDFS(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants,
                                             Set<Stmt> visitedStmt, Stmt node) {
        if (visitedStmt.contains(node)) return;
        visitedStmt.add(node);

        // For if statement, if the condition is a constant, do dead code elimination.
        if (node instanceof If ifStmt &&
                ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt)).isConstant()) {
            int constantValue =
                    ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt)).getConstant();
            for (Edge<Stmt> ifEdge: cfg.getOutEdgesOf(ifStmt)) {
                if (constantValue != 0) { // constantValue is true
                    if (ifEdge.getKind() == Edge.Kind.IF_TRUE) {
                        unreachableBranchDFS(cfg, constants, visitedStmt, ifEdge.getTarget());
                        break;
                    }
                }
                else { // constantValue is false
                    if (ifEdge.getKind() == Edge.Kind.IF_FALSE) {
                        unreachableBranchDFS(cfg, constants, visitedStmt, ifEdge.getTarget());
                        break;
                    }
                }
            }
        }
        // For switch statement, if the switch var is a constant, do dead code elimination.
        else if (node instanceof SwitchStmt switchStmt &&
                ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt)).isConstant()) {
            int constantValue =
                    ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt)).getConstant();
            boolean caseFlag = false;
            for (Edge<Stmt> switchEdge: cfg.getOutEdgesOf(switchStmt)) {
                if (switchEdge.getKind() == Edge.Kind.SWITCH_CASE && switchEdge.getCaseValue() == constantValue) {
                    caseFlag = true;
                    unreachableBranchDFS(cfg, constants, visitedStmt, switchEdge.getTarget());
                }
            }
            if (!caseFlag) { // If there is no case value equivalent to constant value, traverse SWITCH_DEFAULT branch.
                unreachableBranchDFS(cfg, constants, visitedStmt, switchStmt.getDefaultTarget());
            }
        }
        // For other statements and the if & switch statements who don't satisfy the requirement, do normal traverse.
        else {
            for (Stmt succ: cfg.getSuccsOf(node)) {
                unreachableBranchDFS(cfg, constants, visitedStmt, succ);
            }
        }
    }

    private static Set<Stmt> deadVariableAnalyze(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex)),
                visitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        deadVariableDFS(cfg, liveVars, visitedStmt, deadCode, cfg.getEntry());
        return deadCode;
    }

    private static void deadVariableDFS(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars,
                                        Set<Stmt> visitedStmt, Set<Stmt> deadCode, Stmt node) {
        if (visitedStmt.contains(node)) return;
        visitedStmt.add(node);
        if (node instanceof AssignStmt assignStmt && hasNoSideEffect(assignStmt.getRValue()) && //No side effect
                assignStmt.getLValue() instanceof Var lVar && // LValue is a variable
                !liveVars.getOutFact(assignStmt).contains(lVar)) { // LValue not a live variable
            deadCode.add(node);
        }
        for (Stmt succ: cfg.getSuccsOf(node)) {
            deadVariableDFS(cfg, liveVars, visitedStmt, deadCode, succ);
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    private static void calculateUnvisitedStmtAndJoinClear(
            Set<Stmt> allStmt, Set<Stmt> visitedStmt, Set<Stmt> unvisitedStmt,
            Set<Stmt> deadCode) {
        unvisitedStmt.addAll(allStmt);
        unvisitedStmt.removeAll(visitedStmt);
        deadCode.addAll(unvisitedStmt);
        visitedStmt.clear();
        unvisitedStmt.clear();
    }
}
