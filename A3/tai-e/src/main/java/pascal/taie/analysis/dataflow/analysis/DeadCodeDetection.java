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
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.*;

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
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Set<Stmt> visited = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Queue<Stmt> queue = new LinkedList<>();

        queue.add(cfg.getEntry());
        while(!queue.isEmpty()) {
            Stmt stmt = queue.poll();
            if(visited.contains(stmt)) {
                continue;
            }
            visited.add(stmt);

            if(stmt instanceof If ifStmt) {
                Value conditionValue = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(stmt));
                if(conditionValue.isConstant()) {
                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        Edge.Kind kind = edge.getKind();
                        if((conditionValue.getConstant() != 0 && kind == Edge.Kind.IF_TRUE) ||
                                (conditionValue.getConstant() == 0 && kind == Edge.Kind.IF_FALSE)) {
                            queue.add(edge.getTarget());
                        }
                    }
                    continue;
                }
            }
            else if(stmt instanceof SwitchStmt switchStmt) {
                Value switchVal = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(stmt));
                if(switchVal.isConstant()) {
                    boolean f = false;
                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        Edge.Kind kind = edge.getKind();
                        Stmt target = edge.getTarget();
                        if (kind == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == switchVal.getConstant()) {
                            queue.add(target);
                            f = true;
                        }
                    }
                    if(!f) {
                        queue.add(switchStmt.getDefaultTarget());
                    }
                    continue;
                }
            }
            else if (stmt instanceof DefinitionStmt<?,?> defStmt) {
                SetFact<Var> outFact = liveVars.getOutFact(stmt);
                LValue lVal = defStmt.getLValue();
                if(lVal instanceof Var var && !outFact.contains(var) &&
                        //stmt instanceof AssignStmt<?,?>) {
                        hasNoSideEffect(defStmt.getRValue())) {
                        //(stmt instanceof AssignStmt<?,?> || hasNoSideEffect(defStmt.getRValue()))) {
                    visited.remove(stmt);
                }
            }

            queue.addAll(cfg.getSuccsOf(stmt));
        }

        for(Stmt stmt : cfg.getNodes()) {
            if(!visited.contains(stmt) && !cfg.isEntry(stmt) && !cfg.isExit(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
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
}
