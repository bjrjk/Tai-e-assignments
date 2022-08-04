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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.stmt.Stmt;

import java.util.LinkedList;
import java.util.Queue;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    protected Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
        this.workList = new LinkedList<Node>();
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        analysis.isForward();
        initialize();
        doSolve();
        return result;
    }

    public void setInternalData(ConstantPropagation cp) {
        cp.setInternalData((Queue<Stmt>) workList, (DataflowResult<Stmt, CPFact>) result);
    }

    private void initialize() {
        for (Method method: icfg.entryMethods().toList()) { // Initialize facts for entry node of entry methods
            Node entryNode = icfg.getEntryOf(method);
            result.setInFact(entryNode, analysis.newInitialFact());
            result.setOutFact(entryNode, analysis.newBoundaryFact(entryNode));
        }
        for (Node node: icfg) {
            if (result.getInFact(node) != null && result.getOutFact(node) != null)
                continue;
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        for (Node node: icfg) {
            workList.add(node);
        }

        while (!workList.isEmpty()) {
            Node node = workList.poll();

            Fact in = result.getInFact(node); // Warning: in is not empty here.
            for (ICFGEdge<Node> predEdge: icfg.getInEdgesOf(node)) {
                analysis.meetInto(
                        analysis.transferEdge(predEdge, result.getOutFact(predEdge.getSource())),
                        in
                );;
            }
            result.setInFact(node, in);

            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                for (Node succ: icfg.getSuccsOf(node)) {
                    workList.add(succ);
                }
            }
        }
    }
}
