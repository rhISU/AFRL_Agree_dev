package com.rockwellcollins.atc.agree.analysis.redlog;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import jkind.lustre.NodeCallExpr;
import jkind.lustre.BoolExpr;
import jkind.lustre.UnaryExpr;
import jkind.lustre.BinaryExpr;
import jkind.lustre.IfThenElseExpr;
import jkind.lustre.IntExpr;
import jkind.lustre.NamedType;
import jkind.lustre.RealExpr;
import jkind.lustre.RecordAccessExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.VarDecl;
import jkind.lustre.Contract;

import com.rockwellcollins.atc.agree.analysis.redlog.RedlogProgram;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeASTBuilder;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeConnection;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeNode;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeProgram;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeStatement;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeVar;
import com.rockwellcollins.atc.agree.analysis.handlers.VerifyComposedContract.VerificationDirection;
import com.rockwellcollins.atc.agree.analysis.AgreeException;

public class RedlogAstBuilder {
	protected static final String guarSuffix = "__GUARANTEE";
	
	public static RedlogProgram getContractRedlogProgram(AgreeProgram agreeProgram, VerificationDirection dir) {
		
        List<VarDecl> sysInputs = new ArrayList<>();
        List<VarDecl> sysOutputs = new ArrayList<>();
        List<VarDecl> allVariables = new ArrayList<>();
        HashMap<VarDecl, Contract> systemContracts = new HashMap<>();
        List<Contract> componentContracts = new ArrayList<>();
        //List<AgreeStatement> componentAssertions = new ArrayList<>();
    	List<AgreeStatement> connectionAssertions = new ArrayList<>();
        List<String> properties = new ArrayList<>();
        for (AgreeVar var : agreeProgram.topNode.inputs) {
        	
        	sysInputs.add(new AgreeVar(var.id.toLowerCase(),var.type, var.reference, var.compInst));
        }
        
        for (AgreeVar var : agreeProgram.topNode.outputs) {
        	sysOutputs.add(new AgreeVar(var.id.toLowerCase(),var.type, var.reference, var.compInst));
        }
        
    	List<Expr> systemAssumptions = new ArrayList<>();
    	List<Expr> systemGuarantees = new ArrayList<>();
        for (AgreeStatement assumption : agreeProgram.topNode.assumptions) {
        	systemAssumptions.add(assumption.expr);
        }
        
        int i = 0;
        for (AgreeStatement guarantee : agreeProgram.topNode.guarantees) {
        	systemGuarantees.add(guarantee.expr);
            String guarName = guarSuffix + i++;
            //locals.add(new AgreeVar(guarName, NamedType.BOOL, guarantee.reference, topNode.compInst));
            //equations.add(new Equation(new IdExpr(guarName), guarantee.expr));
            properties.add(guarName);
            systemContracts.put(new AgreeVar(guarName, NamedType.BOOL, guarantee.reference, agreeProgram.topNode.compInst), 
            		new Contract(agreeProgram.topNode.id, systemAssumptions, systemGuarantees));
        }
        
        for (AgreeNode node : agreeProgram.topNode.subNodes) {
            List<Expr> componentAssumptions = new ArrayList<>();
        	List<Expr> componentGuarantees = new ArrayList<>();
        	String prefix = node.id + AgreeASTBuilder.dotChar;
        	for (AgreeVar var : node.inputs) {
                AgreeVar input = new AgreeVar((prefix + var.id).toLowerCase(), var.type, var.reference, var.compInst);
        		allVariables.add(input);
        	}
        	for (AgreeVar var : node.outputs) {
                AgreeVar output = new AgreeVar((prefix + var.id).toLowerCase(), var.type, var.reference, var.compInst);
        		allVariables.add(output);
        	}
        	for (AgreeStatement assumption : node.assumptions) {
        		componentAssumptions.add(addPrefixToExpr(prefix, assumption.expr));
        	}
        	for (AgreeStatement guarantee : node.guarantees) {
        		componentGuarantees.add(addPrefixToExpr(prefix, guarantee.expr));
        	}
        	componentContracts.add(new Contract(node.id, componentAssumptions, componentGuarantees));
        }
        
        
        
        addConnectionConstraints(agreeProgram.topNode, connectionAssertions);
        
        RedlogProgram redlogProgram = new RedlogProgram(sysInputs, sysOutputs, allVariables, systemContracts, componentContracts, connectionAssertions, agreeProgram.globalLustreNodes, properties);
		return redlogProgram;
	}
	
    private static void addConnectionConstraints(AgreeNode agreeNode, List<AgreeStatement> assertions) {
        for (AgreeConnection conn : agreeNode.connections) {
            String destName =
                    conn.destinationNode == null ? "" : conn.destinationNode.id + AgreeASTBuilder.dotChar;
            destName = destName + conn.destinationVarName;

            String sourName = conn.sourceNode == null ? "" : conn.sourceNode.id + AgreeASTBuilder.dotChar;
            sourName = sourName + conn.sourceVarName;

            Expr connExpr = new BinaryExpr(new IdExpr(sourName), BinaryOp.EQUAL, new IdExpr(destName));

            assertions.add(new AgreeStatement("", connExpr, conn.reference));
        }
    }
    
    // during analysis of exprs, this method will detect "pre/prev" operator and set "isProgramTimeDependent" true.
    // if system has time-dependent properties, at least one of the components contains "pre/prev" operator, so only searching "pre/prev" in components' assumption/guarantee is enough.
    private static Expr addPrefixToExpr(String prefix, Expr expr)
    {
    	if (expr instanceof BoolExpr) {
    		return new BoolExpr(((BoolExpr) expr).value);
    	}
    	if (expr instanceof IdExpr) {
    		return new IdExpr(prefix + ((IdExpr) expr).id);
    	} else if (expr instanceof RecordAccessExpr) {
    		return new RecordAccessExpr(addPrefixToExpr(prefix, ((RecordAccessExpr) expr).record), ((RecordAccessExpr) expr).field);
    	} else if (expr instanceof UnaryExpr) {
    		if (((UnaryExpr) expr).op.name().equalsIgnoreCase("pre")) {
    			return addPrefixToExpr("Pre__" + prefix, ((UnaryExpr) expr).expr);
    		}
    		else//TODO: implement other unary operators
    			throw new AgreeException("Add prefix to expr doesn't yet support this expr: " + expr.toString());
    	} else if (expr instanceof BinaryExpr) {
    		return new BinaryExpr(addPrefixToExpr(prefix, ((BinaryExpr) expr).left), ((BinaryExpr) expr).op, addPrefixToExpr(prefix, ((BinaryExpr) expr).right));
    	} else if (expr instanceof IfThenElseExpr) {
    		return new IfThenElseExpr(addPrefixToExpr(prefix, ((IfThenElseExpr) expr).cond), 
    				addPrefixToExpr(prefix, ((IfThenElseExpr) expr).thenExpr), addPrefixToExpr(prefix, ((IfThenElseExpr) expr).elseExpr));
    	} else if ((expr instanceof RealExpr) || (expr instanceof IntExpr)) {
    		return expr;
    	} else if (expr instanceof NodeCallExpr) {
    		List<Expr> prefixedArgs = new ArrayList<>();
    		for (Expr arg : ((NodeCallExpr) expr).args) {
    			prefixedArgs.add(addPrefixToExpr(prefix, arg));
    		}
    		NodeCallExpr newExpr = new NodeCallExpr(((NodeCallExpr) expr).node, prefixedArgs);
    		return newExpr;
    	} else // TODO: need support for TupleExpr, RecordExpr, CondactExpr, ArrayExpr, ArrayAccessExpr... 
    		throw new AgreeException("Add prefix to expr doesn't yet support this expr: " + expr.toString());
    }
    
}
