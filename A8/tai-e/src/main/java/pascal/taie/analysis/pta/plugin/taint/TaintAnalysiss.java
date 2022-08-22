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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    public Set<CSObj> processSource(Invoke invoke) {
        Set<CSObj> csObjSet = new HashSet<>();
        for (Source source: config.getSources()) {
            if (Objects.equals(source.method(), invoke.getInvokeExp().getMethodRef().resolve()) &&
                Objects.equals(source.type(), invoke.getInvokeExp().getMethodRef().getReturnType())) {
                csObjSet.add(csManager.getCSObj(emptyContext, manager.makeTaint(invoke, source.type())));
            }
        }
        return csObjSet;
    }

    public void processTransfer(Context invokeContext, CSVar csRecvVar, CSVar csResultVar, Invoke invoke) {
        for (TaintTransfer transfer: config.getTransfers()) {
            // Check whether method equals
            if (Objects.equals(transfer.method(), invoke.getMethodRef().resolve())) {
                // Base to result
                if (transfer.from() == -1 && transfer.to() == -2) {
                    if (csRecvVar != null) { // Dynamic Invoke
                        for (CSObj csObj: csRecvVar.getPointsToSet().getObjects()) {
                            Obj obj = csObj.getObject();
                            if (manager.isTaint(obj)) {
                                CSObj newTaintObj = csManager.getCSObj(emptyContext,
                                        manager.makeTaint(manager.getSourceCall(obj), transfer.type()));
                                solver.workListAddEntry(csResultVar, newTaintObj);
                            }
                        }
                    }
                }
                // Arg to base
                else if (transfer.from() >= 0 && transfer.to() == -1) {
                    if (csRecvVar != null) { // Dynamic Invoke
                        CSVar csArgIVar = csManager.getCSVar(invokeContext,
                                invoke.getInvokeExp().getArg(transfer.from()));
                        for (CSObj csObj: csArgIVar.getPointsToSet().getObjects()) {
                            Obj obj = csObj.getObject();
                            if (manager.isTaint(obj)) {
                                CSObj newTaintObj = csManager.getCSObj(emptyContext,
                                        manager.makeTaint(manager.getSourceCall(obj), transfer.type()));
                                solver.workListAddEntry(csRecvVar, newTaintObj);
                            }
                        }
                    }
                }
                // Arg to result
                else if (transfer.from() >= 0 && transfer.to() == -2) {
                    CSVar csArgIVar = csManager.getCSVar(invokeContext,
                            invoke.getInvokeExp().getArg(transfer.from()));
                    for (CSObj csObj: csArgIVar.getPointsToSet().getObjects()) {
                        Obj obj = csObj.getObject();
                        if (manager.isTaint(obj)) {
                            CSObj newTaintObj = csManager.getCSObj(emptyContext,
                                    manager.makeTaint(manager.getSourceCall(obj), transfer.type()));
                            solver.workListAddEntry(csResultVar, newTaintObj);
                        }
                    }
                }
                else {
                    throw new AssertionError("Unreachable code path!");
                }
            }
        }
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // You could query pointer analysis results you need via variable result.
        // Find all callsites for the whole program
        for (Edge<CSCallSite, CSMethod> edge: solver.callGraph.edges().toList()) {
            // Traverse all sinks
            for (Sink sink: config.getSinks()) {
                // Check whether method equals
                if (Objects.equals(sink.method(), edge.getCallee().getMethod())) {
                    Invoke sinkCall = edge.getCallSite().getCallSite();
                    Var maybeTaintedArgument = sinkCall.getInvokeExp().getArg(sink.index());
                    for (CSObj csObj: result.getPointsToSet(
                            csManager.getCSVar(edge.getCallSite().getContext(), maybeTaintedArgument))) {
                        Obj obj = csObj.getObject();
                        if (manager.isTaint(obj)) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(obj), sinkCall, sink.index()));
                        }
                    }
                }
            }
        }
        return taintFlows;
    }
}
