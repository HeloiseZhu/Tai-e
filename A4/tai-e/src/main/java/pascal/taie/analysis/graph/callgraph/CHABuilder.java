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
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.*;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

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
        // TODO - finish me
        Queue<JMethod> q = new ArrayDeque<>();
        q.add(entry);
        while(!q.isEmpty()) {
            JMethod method = q.poll();
            if(callGraph.contains(method)) {
                continue;
            }
            callGraph.addReachableMethod(method);
            for(Invoke callsite: callGraph.getCallSitesIn(method)) {
                for(JMethod target : resolve(callsite)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callsite), callsite, target));
                    q.add(target);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> targets = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        JMethod declaredMethod = declaringClass.getDeclaredMethod(subsignature);
        if(callSite.isStatic()) {
            if (declaredMethod != null) {
                targets.add(declaredMethod);
            }
        } else if (callSite.isSpecial()) {
            JMethod method = dispatch(declaringClass, subsignature);
            if (method != null) {
                targets.add(method);
            }
        //} else if (callSite.isVirtual() || callSite.isInterface()) {
        } else {
            Queue<JClass> q = new ArrayDeque<>();
            q.add(declaringClass);
            while(!q.isEmpty()) {
                JClass jClass = q.poll();
                JMethod method = dispatch(jClass, subsignature);
                if(method != null) { targets.add(method); }
                q.addAll(hierarchy.getDirectSubclassesOf(jClass));
                q.addAll(hierarchy.getDirectImplementorsOf(jClass));
                q.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                /* fixed bug 1:
                if(callSite.isInterface()) {
                    q.addAll(hierarchy.getDirectImplementorsOf(jClass));
                    q.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                } else {
                    q.addAll(hierarchy.getDirectSubclassesOf(jClass));
                }*/
            }
        }
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(jclass == null) {
            return null;
        }
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if(method != null && !method.isAbstract()) {
            return method;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
