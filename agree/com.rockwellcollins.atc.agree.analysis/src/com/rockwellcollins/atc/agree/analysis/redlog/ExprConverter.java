package com.rockwellcollins.atc.agree.analysis.redlog;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import com.rockwellcollins.atc.agree.analysis.AgreeException;

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.Node;
import jkind.lustre.NodeCallExpr;
import jkind.lustre.RealExpr;
import jkind.lustre.RecordAccessExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.UnaryOp;

public class ExprConverter {
	
	private List<Node> globalLustreNodes;
	private HashMap<String, Expr> currentNodeCallArgs;
	
	private Expr originalExpr;
	protected Expr getOriginalExpr() {
		return this.originalExpr;
	}
	
 	private Expr prefixedExpr;
	protected Expr getPrefixedExpr() {
		return this.prefixedExpr;
	}
 	
 	private int orderOfOrigExpr;
 	protected int getOrderOfOrigExpr() {
 		return this.orderOfOrigExpr;
 	}
	
	private HashMap<Integer, HashSet<String>> localVarOrderInfo;
	// if each expr is treated as a block-level input/output relationship, then zeroOrderVarList are the possible block-level output variables
	private HashSet<String> zeroOrderVarList;
	protected HashSet<String> getZeroOrderVarList() {
		return this.zeroOrderVarList;
	}
	
	private HashMap<String, Integer> allVarAndHighestOrder;
	protected HashMap<String, Integer> getAllVarAndHighestOrder() {
		return this.allVarAndHighestOrder;
	}
	
	//protected ExprConverter(Expr prefixedExpr, HashMap<Integer, HashSet<String>> localVarOrderInfo) {
	protected ExprConverter(Expr origExpr, String prefix, List<Node> globalLustreNodes) {
		this.originalExpr = origExpr;
		this.globalLustreNodes = globalLustreNodes;
		this.currentNodeCallArgs = null;
		this.orderOfOrigExpr = 0;
		// using HashMap to record order relationship between two variables, then do ACYCLIC tree searches backwards from system output to system input(s) to determine the system order. 		
		this.localVarOrderInfo = new HashMap<>();
		// through reconstruction, we
		// 1. add the prefix
		// 2. determine the localVarOrderInfo
		// 3. determine if expr is time-dependent
		this.prefixedExpr = exprReconstruct(origExpr, prefix, 0);
		
		this.zeroOrderVarList = localVarOrderInfo.get(0);
		this.allVarAndHighestOrder = new HashMap<>();
		for (int order : localVarOrderInfo.keySet()) {
			if (this.orderOfOrigExpr < order) {
				this.orderOfOrigExpr = order;
			}
			for (String varName : localVarOrderInfo.get(order)) {
				String varRootName =  varName.replace(RedlogAstBuilder.preSuffix, "");
				if (!allVarAndHighestOrder.containsKey(varName)) {
					allVarAndHighestOrder.put(varRootName, order);
				} else if (allVarAndHighestOrder.get(varRootName) < order) {
					allVarAndHighestOrder.put(varRootName, order);
				}
			}
		}
	}
	
	// through reconstruction, we
	// 1. add the prefix
	// 2. determine the localVarOrderInfo
	// 3. determine if expr is time-dependent
	@SuppressWarnings("unchecked")
	private Expr exprReconstruct(Expr expr, String prefix, int order)
    {
    	if (expr instanceof BoolExpr) {
    		return new BoolExpr(((BoolExpr) expr).value);
    	}
    	if (expr instanceof IdExpr) {
    		// if conversion happens NOT within a node call,
    		if (this.currentNodeCallArgs == null) {
    			String varName = prefix + ((IdExpr) expr).id;
    			if (!localVarOrderInfo.containsKey(order)) {
    				HashSet<String> varSetAtCurrentOrder = new HashSet<>();
    				varSetAtCurrentOrder.add(varName);   
        			localVarOrderInfo.put(order, varSetAtCurrentOrder); 			
    			}
    			else {
    				localVarOrderInfo.get(order).add(varName);
    			}
    			return new IdExpr(varName);
    		}
    		// if conversion happens WITHIN a node call
    		else {
    			String inputName = ((IdExpr) expr).id;
    			Expr argExpr = this.currentNodeCallArgs.get(inputName);
    			Object temp = this.currentNodeCallArgs.clone();
    			// when convert the current argExpr, we hide the currentNodeCallArgs since the argExpr doesn't contain the current arguments anymore, then recover it when the conversion is done.
    			this.currentNodeCallArgs = null;
    			Expr convertedArgExpr = exprReconstruct(argExpr, prefix, order);
    			this.currentNodeCallArgs = (HashMap<String, Expr>) temp;
    			return convertedArgExpr;
    		}
    	} else if (expr instanceof RecordAccessExpr) {
    		return new RecordAccessExpr(exprReconstruct(((RecordAccessExpr) expr).record, prefix, order), ((RecordAccessExpr) expr).field);
    	} else if (expr instanceof UnaryExpr) {
    		if (((UnaryExpr) expr).op == UnaryOp.PRE) {
    			return exprReconstruct(((UnaryExpr) expr).expr, RedlogAstBuilder.preSuffix + prefix, order + 1);
    		} else {
    			return new UnaryExpr(((UnaryExpr) expr).op, exprReconstruct(((UnaryExpr) expr).expr, prefix, order));
    		}
    	} else if (expr instanceof BinaryExpr) {
    		return new BinaryExpr(exprReconstruct(((BinaryExpr) expr).left, prefix, order), ((BinaryExpr) expr).op, exprReconstruct(((BinaryExpr) expr).right, prefix, order));
    	} else if (expr instanceof IfThenElseExpr) {
    		// translate "if a then b else c" into equivalent "(a and b) or ((not a) and c)"
    		Expr conditionExpr = exprReconstruct(((IfThenElseExpr) expr).cond, prefix, order);
    		BinaryExpr ifTrueCaseExpr = new BinaryExpr(conditionExpr, BinaryOp.AND, exprReconstruct(((IfThenElseExpr) expr).thenExpr, prefix, order));
    		UnaryExpr notConditionExpr =  new UnaryExpr(UnaryOp.NOT, conditionExpr);
    		BinaryExpr ifFalseCaseExpr = new BinaryExpr(notConditionExpr, BinaryOp.AND,  exprReconstruct(((IfThenElseExpr) expr).elseExpr, prefix, order));
    		return new BinaryExpr(ifTrueCaseExpr, BinaryOp.OR, ifFalseCaseExpr);
    	} else if ((expr instanceof RealExpr) || (expr instanceof IntExpr)) {
    		return expr;
    	} else if (expr instanceof NodeCallExpr) {
    		Expr convertedEquationExpr = null;
    		for (Node nodeCall : globalLustreNodes) {
    			if (nodeCall.id.equals(((NodeCallExpr) expr).node)) {
    				this.currentNodeCallArgs = new HashMap<>();
    	    		for (int i = 0; i < nodeCall.inputs.size(); i ++) {
    	    			currentNodeCallArgs.put(nodeCall.inputs.get(i).id, ((NodeCallExpr) expr).args.get(i));
    	    		}
    				//TODO: for now, we assume a nodeCall has only one equation with zero order.
    				Expr equationExpr = nodeCall.equations.get(0).expr;
    				convertedEquationExpr = exprReconstruct(equationExpr, prefix, order);
    				// clear current NodeCall and current NodeCallArgs.
    				this.currentNodeCallArgs = null;
    				break;
    			}
    		}
    		return convertedEquationExpr;
    	} else // TODO: need support for TupleExpr, RecordExpr, CondactExpr, ArrayExpr, ArrayAccessExpr... 
    		throw new AgreeException("Add prefix to expr doesn't yet support this expr: " + expr.toString());
    }
	
}