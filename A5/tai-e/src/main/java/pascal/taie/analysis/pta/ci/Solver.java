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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!callGraph.addReachableMethod(method)) // If method not exists in RM, add it.
            return; // The method is already reachable.
        // S = S Union Sm is automatically done by tai-e framework
        // Apply rules in class StmtProcessor
        for (Stmt stmt: method.getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        public Void visit(New stmt) {
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(stmt.getLValue()),
                    new PointsToSet(heapModel.getObj(stmt))
            );
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        public Void visit(Invoke stmt) {
            if (stmt.isStatic())
                processSingleCall(stmt, null);
            return null;
        }
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic())
                return null;
            // Only process static LoadField here
            addPFGEdge(
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic())
                return null;
            // Only process static StoreField here
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
            );
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target)) // If the edge not exists in PFG, add it.
            return; // The edge has already been added.
        if (!source.getPointsToSet().isEmpty()) {
            workList.addEntry(
                    target,
                    source.getPointsToSet()
            );
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry curEntry = workList.pollEntry();
            PointsToSet delta = propagate(curEntry.pointer(), curEntry.pointsToSet());
            if (curEntry.pointer() instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj: delta.getObjects()) {
                    for (StoreField storeField: var.getStoreFields()) {
                        if (storeField.isStatic())
                            continue;
                        // Only process dynamic StoreField here
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve())
                        );
                    }
                    for (LoadField loadField: var.getLoadFields()) {
                        if (loadField.isStatic())
                            continue;
                        // Only process dynamic LoadField here
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(loadField.getLValue())
                        );
                    }
                    for (StoreArray storeArray: var.getStoreArrays()) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    }
                    for (LoadArray loadArray: var.getLoadArrays()) {
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue())
                        );
                    }
                    // The call have to be dynamic here because obj is not null
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet ptp = pointer.getPointsToSet(),
                    delta = new PointsToSet();
        // delta = pts - pt(n)
        for (Obj obj: pointsToSet.getObjects()) {
            if (!ptp.contains(obj))
                delta.addObject(obj);
        }
        if (!delta.isEmpty()) {
            for (Obj obj: delta.getObjects()) {
                ptp.addObject(obj);
            }
            for (Pointer succPtr: pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(
                        succPtr,
                        delta
                );
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        if (recv == null) // Only process dynamic calls
            return;
        for (Invoke invoke: var.getInvokes()) {
            processSingleCall(invoke, recv);
        }
    }

    private void processSingleCall(Invoke invoke, Obj recv) {
        JMethod method = resolveCallee(recv, invoke);
        if (recv != null)
            workList.addEntry(
                pointerFlowGraph.getVarPtr(method.getIR().getThis()),
                new PointsToSet(recv)
            );
        // If the edge exists in CG, add it and do the following:
        if (callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(invoke), invoke, method))) {
            addReachable(method);
            List<Var> params = method.getIR().getParams();
            List<Var> args = invoke.getInvokeExp().getArgs();
            // Add PFG edge for argument-parameter
            for (int i = 0; i < params.size(); i++) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(args.get(i)),
                        pointerFlowGraph.getVarPtr(params.get(i))
                );
            }
            // Add PFG edge for methodReturnValue-receiverPointer
            for (Var retVar: method.getIR().getReturnVars()) {
                if (invoke.getLValue() != null)
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(retVar),
                            pointerFlowGraph.getVarPtr(invoke.getLValue())
                    );
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
