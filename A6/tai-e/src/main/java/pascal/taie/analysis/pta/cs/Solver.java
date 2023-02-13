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
import pascal.taie.analysis.graph.callgraph.CallKind;
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
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
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
        // TODO - finish me
        if(!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach(
                    stmt -> stmt.accept(new StmtProcessor(csMethod))
            );
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

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(csManager.getCSObj(heapContext, obj))
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

        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return null;
        }

        public Void visit(Invoke callsite) {
            if(callsite.isStatic()) {
                CSCallSite csCallSite = csManager.getCSCallSite(context, callsite);
                JMethod callee = resolveCallee(null, callsite);
                Context calleeContext = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);

                _ProcessCall(CallKind.STATIC, csCallSite, csCallee);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            if(!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if(entry.pointer() instanceof CSVar csVar) {
                Var var = csVar.getVar();
                Context context = csVar.getContext();
                for(CSObj obj : delta) {
                    var.getStoreFields().forEach(
                            stmt-> addPFGEdge(
                                    csManager.getCSVar(context, stmt.getRValue()),
                                    csManager.getInstanceField(obj, stmt.getFieldRef().resolve())
                            )
                    );
                    var.getLoadFields().forEach(
                            stmt-> addPFGEdge(
                                    csManager.getInstanceField(obj, stmt.getFieldRef().resolve()),
                                    csManager.getCSVar(context, stmt.getLValue())
                            )
                    );
                    var.getStoreArrays().forEach(
                            stmt-> addPFGEdge(
                                    csManager.getCSVar(context, stmt.getRValue()),
                                    csManager.getArrayIndex(obj)
                            )
                    );
                    var.getLoadArrays().forEach(
                            stmt-> addPFGEdge(
                                    csManager.getArrayIndex(obj),
                                    csManager.getCSVar(context, stmt.getLValue())
                            )
                    );
                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pts to pointer(pt) and its PFG successors,
     * returns the difference set of pts and pt.
     */
    private PointsToSet propagate(Pointer pt, PointsToSet pts) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        pts.forEach(obj->{
            if(!pt.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
            }
        });
        if(!delta.isEmpty()) {
            delta.forEach(obj-> pt.getPointsToSet().addObject(obj));
            pointerFlowGraph.getSuccsOf(pt).forEach(succ-> workList.addEntry(succ, delta));
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
        // TODO - finish me
        recv.getVar().getInvokes().forEach(callsite ->{
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callsite);
            JMethod callee = resolveCallee(recvObj, callsite);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
            workList.addEntry(
                    csManager.getCSVar(calleeContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj)
            );
            _ProcessCall(null, csCallSite, csCallee);
        });
    }

    private void _ProcessCall(CallKind kind, CSCallSite csCallSite, CSMethod csCallee) {
        if(!callGraph.getCalleesOf(csCallSite).contains(csCallee)) {
            Invoke callsite = csCallSite.getCallSite();
            JMethod callee = csCallee.getMethod();
            if(kind == null) {
                if (callsite.isInterface()) {
                    kind = CallKind.INTERFACE;
                } else if (callsite.isVirtual()) {
                    kind = CallKind.VIRTUAL;
                } else if (callsite.isSpecial()) {
                    kind = CallKind.SPECIAL;
                } else if (callsite.isStatic()) {
                    kind = CallKind.STATIC;
                } else if (callsite.isDynamic()) {
                    kind = CallKind.DYNAMIC;
                } else {
                    kind = CallKind.OTHER;
                }
            }
            callGraph.addEdge(new Edge<>(kind, csCallSite, csCallee));
            addReachable(csCallee);
            List<Var> args = callsite.getRValue().getArgs();
            List<Var> params = callee.getIR().getParams();
            for (int i = 0; i < params.size(); i++) {
                addPFGEdge(
                        csManager.getCSVar(csCallSite.getContext(), args.get(i)),
                        csManager.getCSVar(csCallee.getContext(), params.get(i))
                );
            }
            if(callsite.getLValue() != null) {
                callee.getIR().getReturnVars().forEach(
                        ret-> addPFGEdge(
                                csManager.getCSVar(csCallee.getContext(), ret),
                                csManager.getCSVar(csCallSite.getContext(), callsite.getLValue())
                        )
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
