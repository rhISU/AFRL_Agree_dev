package com.rockwellcollins.atc.agree.analysis.lustre.visitors;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.rockwellcollins.atc.agree.analysis.AgreeException;

import jkind.lustre.ArrayAccessExpr;
import jkind.lustre.ArrayExpr;
import jkind.lustre.ArrayUpdateExpr;
import jkind.lustre.BinaryExpr;
import jkind.lustre.BoolExpr;
import jkind.lustre.CastExpr;
import jkind.lustre.CondactExpr;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.InductDataExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NodeCallExpr;
import jkind.lustre.QuantExpr;
import jkind.lustre.RealExpr;
import jkind.lustre.RecordAccessExpr;
import jkind.lustre.RecordExpr;
import jkind.lustre.RecordUpdateExpr;
import jkind.lustre.TupleExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.visitors.ExprVisitor;

public class IdRewriteVisitor implements ExprVisitor<Expr> {

    private final IdRewriter rewriter;

    public IdRewriteVisitor(IdRewriter rewriter) {
        this.rewriter = rewriter;
    }

    @Override
    public Expr visit(ArrayAccessExpr e) {
        throw new AgreeException("We do not support array expressions");
    }

    @Override
    public Expr visit(ArrayExpr e) {
        throw new AgreeException("We do not support array expressions");
    }

    @Override
    public Expr visit(ArrayUpdateExpr e) {
        throw new AgreeException("We do not support array expressions");
    }

    @Override
    public Expr visit(BinaryExpr e) {
        return new BinaryExpr(e.left.accept(this), e.op, e.right.accept(this));
    }

    @Override
    public Expr visit(BoolExpr e) {
        return new BoolExpr(e.value);
    }

    @Override
    public Expr visit(CastExpr e) {
        return new CastExpr(e.type, e.expr.accept(this));
    }

    @Override
    public Expr visit(CondactExpr e) {
        return new CondactExpr(e.clock.accept(this), (NodeCallExpr) e.call.accept(this), acceptList(e.args));
    }

    @Override
    public Expr visit(IdExpr e) {
        return rewriter.rewrite(e);
    }

    @Override
    public Expr visit(IfThenElseExpr e) {
        return new IfThenElseExpr(e.cond.accept(this), e.thenExpr.accept(this), e.elseExpr.accept(this));
    }

    @Override
    public Expr visit(IntExpr e) {
        return new IntExpr(e.value);
    }

    @Override
    public Expr visit(NodeCallExpr e) {
        return new NodeCallExpr(e.node, acceptList(e.args));
    }

    @Override
    public Expr visit(RealExpr e) {
        return new RealExpr(e.value);
    }

    @Override
    public Expr visit(RecordAccessExpr e) {
        return new RecordAccessExpr(e.record.accept(this), e.field);
    }

    @Override
    public Expr visit(RecordExpr e) {
        Map<String, Expr> newFields = new HashMap<>();
        for (Entry<String, Expr> entry : e.fields.entrySet()) {
            newFields.put(entry.getKey(), entry.getValue().accept(this));
        }
        return new RecordExpr(e.id, newFields);
    }

    @Override
    public Expr visit(RecordUpdateExpr e) {
        return new RecordUpdateExpr(e.record.accept(this), e.field, e.value.accept(this));
    }

    @Override
    public Expr visit(TupleExpr e) {
        throw new AgreeException("We do not currently support typles");
    }

    @Override
    public Expr visit(UnaryExpr e) {
        return new UnaryExpr(e.op, e.expr.accept(this));
    }

    private List<Expr> acceptList(List<Expr> exprs) {
        List<Expr> result = new ArrayList<>();

        for (Expr expr : exprs) {
            result.add(expr.accept(this));
        }

        return result;
    }

    @Override
    public Expr visit(InductDataExpr e) {
        throw new AgreeException("We do not support Quantified Expressions or Inductive Datatypes");
    }

    @Override
    public Expr visit(QuantExpr e) {
        throw new AgreeException("We do not support Quantified Expressions or Inductive Datatypes");
    }

}
