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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.MapFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Map;
import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        for(Var param : cfg.getIR().getParams()) {
            if(canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var : fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else if (v1.equals(v2)) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact temp = out.copy();
        out.clear();
        out.copyFrom(in);
        if(stmt instanceof DefinitionStmt<?,?>) {
            LValue lVar = ((DefinitionStmt<?, ?>) stmt).getLValue();
            RValue rExp = ((DefinitionStmt<?, ?>) stmt).getRValue();
            if(lVar instanceof Var && canHoldInt((Var) lVar)) {
                Value rExpVal = evaluate(rExp, in);
                out.update((Var) lVar, rExpVal);
            }
        }
        return !out.equals(temp);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if(exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if(exp instanceof Var) {
            return in.get((Var) exp);
        } else if(exp instanceof BinaryExp) {
            Value val1 = in.get(((BinaryExp) exp).getOperand1());
            Value val2 = in.get(((BinaryExp) exp).getOperand2());
            if(val1.isConstant() && val2.isConstant()) {
                int c1 = val1.getConstant();
                int c2 = val2.getConstant();
                if (exp instanceof ArithmeticExp) {
                    switch (((ArithmeticExp) exp).getOperator()) {
                        case ADD: return Value.makeConstant(c1 + c2);
                        case SUB: return Value.makeConstant(c1 - c2);
                        case MUL: return Value.makeConstant(c1 * c2);
                        case DIV: if (c2 == 0) { return Value.getUndef(); }
                                else { return Value.makeConstant(c1 / c2); }
                        case REM: if (c2 == 0) { return Value.getUndef(); }
                                else { return Value.makeConstant(c1 % c2); }
                        default: break;
                    }
                } else if (exp instanceof ConditionExp) {
                    switch (((ConditionExp) exp).getOperator()) {
                        case EQ: return Value.makeConstant(c1 == c2 ? 1 : 0);
                        case NE: return Value.makeConstant(c1 != c2 ? 1 : 0);
                        case LT: return Value.makeConstant(c1 < c2 ? 1 : 0);
                        case GT: return Value.makeConstant(c1 > c2 ? 1 : 0);
                        case LE: return Value.makeConstant(c1 <= c2 ? 1 : 0);
                        case GE: return Value.makeConstant(c1 >= c2 ? 1 : 0);
                        default: break;
                    }
                } else if (exp instanceof ShiftExp) {
                    switch (((ShiftExp) exp).getOperator()) {
                        case SHL: return Value.makeConstant(c1 << c2);
                        case SHR: return Value.makeConstant(c1 >> c2);
                        case USHR: return Value.makeConstant(c1 >>> c2);
                        default: break;
                    }
                } else if (exp instanceof BitwiseExp) {
                    switch (((BitwiseExp) exp).getOperator()) {
                        case OR: return Value.makeConstant(c1 | c2);
                        case AND: return Value.makeConstant(c1 & c2);
                        case XOR: return Value.makeConstant(c1 ^ c2);
                        default: break;
                    }
                }
            }
            if(exp instanceof ArithmeticExp) {
                ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
                if((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) && val2.isConstant() && val2.getConstant() == 0) {
                    return Value.getUndef();
                }
            }
            if (val1.isNAC() || val2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
