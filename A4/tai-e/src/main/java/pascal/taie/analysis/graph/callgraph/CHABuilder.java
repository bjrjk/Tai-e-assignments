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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new LinkedList<JMethod>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod jMethod = workList.poll();
            if (!callGraph.addReachableMethod(jMethod))
                continue;
            for (Invoke invoke: callGraph.callSitesIn(jMethod).toList()) {
                Set<JMethod> invokeJMethods = resolve(invoke);
                for (JMethod invokeJMethod: invokeJMethods) {
                    if (invokeJMethod == null) continue; // Edge case for abstract method of interfaces
                    callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(invoke), invoke, invokeJMethod));
                    workList.add(invokeJMethod);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> jMethods = new HashSet<JMethod>();
        JClass jMethodClass = callSite.getMethodRef().getDeclaringClass();
        Subsignature jMethodSubSig = callSite.getMethodRef().getSubsignature();
        switch(CallGraphs.getCallKind(callSite)) { // Not complete ?
            case STATIC -> {
                jMethods.add(jMethodClass.getDeclaredMethod(jMethodSubSig));
            }
            case SPECIAL -> {
                jMethods.add(dispatch(jMethodClass, jMethodSubSig));
            }
            case VIRTUAL, INTERFACE -> {
                // the class of receiver variable is jMethodClass?
                Set<JClass> allSubJClasses = getAllSubJClasses(jMethodClass);
                for (JClass jClassIter: allSubJClasses) {
                    jMethods.add(dispatch(jClassIter, jMethodSubSig));
                }
            }
        }
        return jMethods;
    }

    private Set<JClass> getAllSubJClasses(JClass jClass) {
        Set<JClass> jClasses = new HashSet<JClass>(),
                jNewClasses = new HashSet<JClass>();
        jClasses.addAll(hierarchy.getDirectSubclassesOf(jClass));
        jClasses.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
        jClasses.addAll(hierarchy.getDirectImplementorsOf(jClass));
        for (JClass jClassIter: jClasses) {
            jNewClasses.addAll(getAllSubJClasses(jClassIter));
        }
        jClasses.addAll(jNewClasses);
        jClasses.add(jClass); // Including the class itself
        return jClasses;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null)
            return null;

        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null && !jMethod.isAbstract())
            return jMethod;

        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
