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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        cp.initializePTA(pta, icfg);
    }

    @Override
    public boolean isForward() {
        solver.setInternalData(cp);
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changedFlag = !out.equals(in);
        if (changedFlag) {
            out.copyFrom(in);
        }
        return changedFlag;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        assert edge.getSource() instanceof Invoke; // callSite should be Invoke

        CPFact newOut = out.copy();
        Invoke callSite = (Invoke) edge.getSource();
        Var lVar = callSite.getLValue();

        if (lVar != null) {
            newOut.remove(lVar);
        }

        return newOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        assert edge.getSource() instanceof Invoke; // callSite should be Invoke

        CPFact calleeIn = new CPFact();
        Invoke callSite = (Invoke) edge.getSource();
        List<Var> argsList = callSite.getInvokeExp().getArgs();
        JMethod callee = edge.getCallee();
        List<Var> paramsList = callee.getIR().getParams();

        assert argsList.size() == paramsList.size(); // count of args must be equal to params
        int size = argsList.size();
        for (int i = 0; i < size; i++) {
            calleeIn.update(paramsList.get(i), callSiteOut.get(argsList.get(i)));
        }

        return calleeIn;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        assert edge.getCallSite() instanceof Invoke; // callSite should be Invoke

        CPFact callerIn = new CPFact();
        Invoke callSite = (Invoke) edge.getCallSite();
        Var lVar = callSite.getLValue();
        if (lVar != null) {
            Value resultValue = Value.getUndef();
            for (Var retVar: edge.getReturnVars()) { // meet value for all return vars
                resultValue = cp.meetValue(resultValue, returnOut.get(retVar));
            }
            callerIn.update(lVar, resultValue);
        }

        return callerIn;
    }
}
