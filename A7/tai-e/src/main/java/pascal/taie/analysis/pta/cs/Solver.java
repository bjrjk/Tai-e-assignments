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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (!callGraph.addReachableMethod(csMethod)) // If method not exists in RM, add it.
            return; // The method is already reachable.
        // S = S Union Sm is automatically done by tai-e framework
        // Apply rules in class StmtProcessor
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        for (Stmt stmt: csMethod.getMethod().getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(
                            csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj)
                    )
            );
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }

        public Void visit(Invoke stmt) {
            if (stmt.isStatic())
                processSingleCall(context, stmt, null);
            return null;
        }
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic())
                return null;
            // Only process static LoadField here
            addPFGEdge(
                    csManager.getStaticField(stmt.getFieldRef().resolve()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic())
                return null;
            // Only process static StoreField here
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getStaticField(stmt.getFieldRef().resolve())
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
            if (curEntry.pointer() instanceof CSVar varPtr) {
                Var var = varPtr.getVar();
                Context varContext = varPtr.getContext();
                for (CSObj obj: delta.getObjects()) {
                    Obj pObj = obj.getObject();
                    Context objContext = obj.getContext();
                    for (StoreField storeField: var.getStoreFields()) {
                        if (storeField.isStatic())
                            continue;
                        // Only process dynamic StoreField here
                        addPFGEdge(
                                csManager.getCSVar(varContext, storeField.getRValue()),
                                csManager.getInstanceField(obj, storeField.getFieldRef().resolve())
                        );
                    }
                    for (LoadField loadField: var.getLoadFields()) {
                        if (loadField.isStatic())
                            continue;
                        // Only process dynamic LoadField here
                        addPFGEdge(
                                csManager.getInstanceField(obj, loadField.getFieldRef().resolve()),
                                csManager.getCSVar(varContext, loadField.getLValue())
                        );
                    }
                    for (StoreArray storeArray: var.getStoreArrays()) {
                        addPFGEdge(
                                csManager.getCSVar(varContext, storeArray.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    }
                    for (LoadArray loadArray: var.getLoadArrays()) {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(varContext, loadArray.getLValue())
                        );
                    }
                    // The call have to be dynamic here because obj is not null
                    processCall(varPtr, obj);
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
                delta = PointsToSetFactory.make();
        // delta = pts - pt(n)
        for (CSObj obj: pointsToSet.getObjects()) {
            if (!ptp.contains(obj))
                delta.addObject(obj);
        }
        if (!delta.isEmpty()) {
            for (CSObj obj: delta.getObjects()) {
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        if (recv == null) // Only process dynamic calls
            return;
        for (Invoke invoke: recv.getVar().getInvokes()) {
            processSingleCall(recv.getContext(), invoke, recvObj);
        }
    }

    private void processSingleCall(Context invokeContext, Invoke invoke, CSObj recv) {
        JMethod method = resolveCallee(recv, invoke);
        CSCallSite csCallSite = csManager.getCSCallSite(invokeContext, invoke);
        Context targetContext = contextSelector.selectContext(csCallSite, recv, method);
        CSMethod csMethod = csManager.getCSMethod(targetContext, method);
        if (recv != null)
            workList.addEntry(
                    csManager.getCSVar(targetContext, method.getIR().getThis()),
                    PointsToSetFactory.make(recv)
            );
        // If the edge exists in CG, add it and do the following:
        if (callGraph.addEdge(new Edge<CSCallSite, CSMethod>(CallGraphs.getCallKind(invoke), csCallSite, csMethod))) {
            addReachable(csMethod);
            List<Var> params = method.getIR().getParams();
            List<Var> args = invoke.getInvokeExp().getArgs();
            // Add PFG edge for argument-parameter
            for (int i = 0; i < params.size(); i++) {
                addPFGEdge(
                        csManager.getCSVar(invokeContext, args.get(i)),
                        csManager.getCSVar(targetContext, params.get(i))
                );
            }
            // Add PFG edge for methodReturnValue-receiverPointer
            for (Var retVar: method.getIR().getReturnVars()) {
                if (invoke.getLValue() != null)
                    addPFGEdge(
                            csManager.getCSVar(targetContext, retVar),
                            csManager.getCSVar(invokeContext, invoke.getLValue())
                    );
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
