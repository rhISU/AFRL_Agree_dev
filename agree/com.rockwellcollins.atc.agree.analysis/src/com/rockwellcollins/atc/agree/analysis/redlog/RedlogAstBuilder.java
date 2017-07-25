package com.rockwellcollins.atc.agree.analysis.redlog;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import jkind.lustre.BinaryExpr;
import jkind.lustre.NamedType;
import jkind.lustre.BinaryOp;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.VarDecl;
import jkind.lustre.Contract;

import com.rockwellcollins.atc.agree.analysis.redlog.RedlogProgram;
import com.rockwellcollins.atc.agree.analysis.redlog.ExprConverter;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeASTBuilder;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeConnection;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeNode;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeProgram;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeStatement;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeVar;

public class RedlogAstBuilder {
	protected static final String guarSuffix = "__GUARANTEE";
	protected static final String preSuffix = "Pre__";
	protected static final String nextSuffix = "Next__";
	
	// auxiliary variables for nodeCalls are generated during analysis the exprs, we need to give them unique names by giving each expr a uniqe number id.
	// and "exprCount" is created for this purpose.
	private int exprCount;
	private List<VarDecl> sysInputs;
	private List<VarDecl> sysOutputs;
	private List<VarDecl> targetCompInputs;
	private List<VarDecl> targetCompOutputs;
	private List<VarDecl> contextCompVariables;
	private HashMap<VarDecl, Contract> systemContracts;
	private Contract targetCompContract;
	private List<Contract> contextCompContracts;
	private HashMap<String, String> connectionMap;
	private List<AgreeStatement> connectionAssertions;
	private List<String> properties;
	
	private List<ExprConverter> exprLocalOrderInfoList;
	
	public RedlogProgram getContractRedlogProgram(AgreeProgram agreeProgram, String targetCompName) {
		
		this.exprCount = 0;
        this.sysInputs = new ArrayList<>();
        this.sysOutputs = new ArrayList<>();
        this.targetCompInputs = null;
        this.targetCompOutputs = null;
        this.contextCompVariables = new ArrayList<>();
        this.systemContracts = new HashMap<>();
        this.targetCompContract = null;
        this.connectionMap = new HashMap<>();
        this.contextCompContracts = new ArrayList<>();
        this.connectionAssertions = new ArrayList<>();
        this.properties = new ArrayList<>();
        this.exprLocalOrderInfoList = new ArrayList<>();
        for (AgreeVar var : agreeProgram.topNode.inputs) {
        	
        	sysInputs.add(new AgreeVar(var.id, var.type, var.reference, var.compInst));
        }
        
        for (AgreeVar var : agreeProgram.topNode.outputs) {
        	sysOutputs.add(new AgreeVar(var.id, var.type, var.reference, var.compInst));
        }
        
        // each contract contains all the assumptions 
    	List<Expr> systemAssumptions = new ArrayList<>();
    	// List<Expr> systemGuarantees = new ArrayList<>();
        for (AgreeStatement assumption : agreeProgram.topNode.assumptions) {
        	systemAssumptions.add(assumption.expr);
        }
        
        // system assertion can be treated as system assumption
        for (AgreeStatement assertion : agreeProgram.topNode.assertions) {
        	systemAssumptions.add(assertion.expr);
        }
        
        int i = 0;
        for (AgreeStatement guarantee : agreeProgram.topNode.guarantees) {
        	List<Expr> systemGuarantees = new ArrayList<>();
        	systemGuarantees.add(guarantee.expr);
            String guarName = guarSuffix + i++;
            //locals.add(new AgreeVar(guarName, NamedType.BOOL, guarantee.reference, topNode.compInst));
            //equations.add(new Equation(new IdExpr(guarName), guarantee.expr));
            properties.add(guarName);
            systemContracts.put(new AgreeVar(guarName, NamedType.BOOL, guarantee.reference, agreeProgram.topNode.compInst), 
            		new Contract(agreeProgram.topNode.id, systemAssumptions, systemGuarantees));
        }
        
        // for prototype implementation, we don't need separate methods for property composition and decomp.
        // if targetCompName is null, we do composition analysis
        // if targetCompName is not null, we compare the string to the node.id to determine which sub is the decomp target.
        // targetCompName comes from system internal SystemSubcomponentImpl object in the context.
        for (AgreeNode node : agreeProgram.topNode.subNodes) {
            List<Expr> componentAssumptions = new ArrayList<>();
        	List<Expr> componentGuarantees = new ArrayList<>();
        	String prefix = node.id + AgreeASTBuilder.dotChar;
        	
        	// isolate target comp input/output variables
        	if (targetCompName!=null && node.id.equals(targetCompName))
        	{
        		targetCompInputs = new ArrayList<>(); // initialized if target comp exists
        		targetCompOutputs = new ArrayList<>(); // initialized if target comp exists
        		for (AgreeVar var : node.inputs) {
	                AgreeVar input = new AgreeVar((prefix + var.id).toLowerCase(), var.type, var.reference, var.compInst);
	        		targetCompInputs.add(input);
	        	}
	        	for (AgreeVar var : node.outputs) {
	                AgreeVar output = new AgreeVar((prefix + var.id).toLowerCase(), var.type, var.reference, var.compInst);
	        		targetCompOutputs.add(output);
	        	}
	        	for (AgreeStatement assumption : node.assumptions) {
	        		componentAssumptions.add(new ExprConverter(assumption.expr, prefix, agreeProgram.globalLustreNodes).getPrefixedExpr());
	        	}
	        	
	        	// component assertion is treated as component guarantee 
	        	// sometimes assertions contain duplicated guarantee(s), check before adding.
	        	// TODO: figure out how duplication occurs in AgreeStatement, removing duplication should be easier than current implementation.
	        	List<String> guaranteeDuplicationCheckList = new ArrayList<>();
	        	for (AgreeStatement guarantee : node.guarantees) {
	        		ExprConverter exprInfo = new ExprConverter(guarantee.expr, prefix, agreeProgram.globalLustreNodes);
	        		Expr prefixedGuarantee = exprInfo.getPrefixedExpr();
	        		String prefixedGuaranteeString = prefixedGuarantee.toString();
	        		if (! guaranteeDuplicationCheckList.contains(prefixedGuaranteeString)) {
	        			guaranteeDuplicationCheckList.add(prefixedGuaranteeString);
	        			this.exprLocalOrderInfoList.add(exprInfo);
	        			componentGuarantees.add(exprInfo.getPrefixedExpr());
	        		}
	        	} 
	        	for (AgreeStatement assertion : node.assertions) {
	        		ExprConverter exprInfo = new ExprConverter(assertion.expr, prefix, agreeProgram.globalLustreNodes);
	        		Expr prefixedAssertion = exprInfo.getPrefixedExpr();
	        		String prefixedAssertionString = prefixedAssertion.toString();
	        		if (! guaranteeDuplicationCheckList.contains(prefixedAssertionString)) {
	        			guaranteeDuplicationCheckList.add(prefixedAssertionString);
	        			this.exprLocalOrderInfoList.add(exprInfo);
	        			componentGuarantees.add(exprInfo.getPrefixedExpr());
	        		}
	        	}
	        	targetCompContract = new Contract(node.id, componentAssumptions, componentGuarantees);
        	}
        	else
	        {
	        	for (AgreeVar var : node.inputs) {
	                AgreeVar input = new AgreeVar((prefix + var.id).toLowerCase(), var.type, var.reference, var.compInst);
	        		contextCompVariables.add(input);
	        	}
	        	for (AgreeVar var : node.outputs) {
	                AgreeVar output = new AgreeVar((prefix + var.id).toLowerCase(), var.type, var.reference, var.compInst);
	        		contextCompVariables.add(output);
	        	}
	        	for (AgreeStatement assumption : node.assumptions) {
	        		componentAssumptions.add(new ExprConverter(assumption.expr, prefix, agreeProgram.globalLustreNodes).getPrefixedExpr());
	        	}
	        	// component assertion is treated as component guarantee 
	        	// sometimes assertions contain duplicated guarantee(s), check before adding.
	        	// TODO: figure out how duplication occurs in AgreeStatement, removing duplication should be easier than current implementation.
	        	List<String> guaranteeDuplicationCheckList = new ArrayList<>();
	        	for (AgreeStatement guarantee : node.guarantees) {
	        		ExprConverter exprInfo = new ExprConverter(guarantee.expr, prefix, agreeProgram.globalLustreNodes);
	        		Expr prefixedGuarantee = exprInfo.getPrefixedExpr();
	        		String prefixedGuaranteeString = prefixedGuarantee.toString();
	        		if (! guaranteeDuplicationCheckList.contains(prefixedGuaranteeString)) {
	        			guaranteeDuplicationCheckList.add(prefixedGuaranteeString);
	        			this.exprLocalOrderInfoList.add(exprInfo);
	        			componentGuarantees.add(exprInfo.getPrefixedExpr());
	        		}
	        	} 
	        	for (AgreeStatement assertion : node.assertions) {
	        		ExprConverter exprInfo = new ExprConverter(assertion.expr, prefix, agreeProgram.globalLustreNodes);
	        		Expr prefixedAssertion = exprInfo.getPrefixedExpr();
	        		String prefixedAssertionString = prefixedAssertion.toString();
	        		if (! guaranteeDuplicationCheckList.contains(prefixedAssertionString)) {
	        			guaranteeDuplicationCheckList.add(prefixedAssertionString);
	        			this.exprLocalOrderInfoList.add(exprInfo);
	        			componentGuarantees.add(exprInfo.getPrefixedExpr());
	        		}
	        	}
	        	contextCompContracts.add(new Contract(node.id, componentAssumptions, componentGuarantees));
        	}
        }
        
        collectConnectionConstraints(agreeProgram.topNode);
        
        RedlogProgram redlogProgram = new RedlogProgram(agreeProgram.globalLustreNodes, properties);
        redlogProgram.setSysInputs(sysInputs);
        redlogProgram.setSysOutputs(sysOutputs);
        if (targetCompName != null) {
        	redlogProgram.setTargetCompInputs(targetCompInputs);
        	redlogProgram.setTargetCompOutputs(targetCompOutputs);
            redlogProgram.setTargetCompContract(targetCompContract);
        }
        redlogProgram.setContextCompVariables(contextCompVariables);
        redlogProgram.setSystemContracts(systemContracts);
        redlogProgram.setContextCompContracts(contextCompContracts);
        redlogProgram.setConnectionAssertions(connectionAssertions);
        redlogProgram.setMaxSysOrder(calculateSysOrder());
        // RedlogProgram redlogProgram = new RedlogProgram(sysInputs, sysOutputs, targetCompInputs, targetCompOutputs, contextCompVariables, systemContracts, targetCompContract, contextCompContracts, connectionAssertions, agreeProgram.globalLustreNodes, properties, calculateSysOrder());
		return redlogProgram;
	}
	
    private void collectConnectionConstraints(AgreeNode agreeNode) {
        for (AgreeConnection conn : agreeNode.connections) {
            String destName = conn.destinationNode == null ? "" : conn.destinationNode.id + AgreeASTBuilder.dotChar;
            destName += conn.destinationVarName;

            String sourName = conn.sourceNode == null ? "" : conn.sourceNode.id + AgreeASTBuilder.dotChar;
            sourName += conn.sourceVarName;
            
            // a destination variable can only have ONE source variable
            if (!this.connectionMap.containsKey(destName)) {
            	this.connectionMap.put(destName, sourName);
            }

            Expr connExpr = new BinaryExpr(new IdExpr(sourName), BinaryOp.EQUAL, new IdExpr(destName));

            this.connectionAssertions.add(new AgreeStatement("", connExpr, conn.reference));
        }
    }
    
    // in current implementation stage, assume there's only one system output variable
    private int calculateSysOrder() {
    	//assuming each guarantee/assertion expr contains at least one variable in its zero order form.
    	// e.g., "pre(z) = pre(x) + pre(y)" is not allowed
    	HashSet<String> allVariableSet = new HashSet<>();
    	HashMap<String, List<ExprConverter>> varOrderRelationMap = new HashMap<>();
    	for (ExprConverter exprOrderInfo : this.exprLocalOrderInfoList) {
        	HashSet<String> zeroOrderVarList = exprOrderInfo.getZeroOrderVarList();
    		if (zeroOrderVarList != null) {
    			allVariableSet.addAll(zeroOrderVarList);
    			for (String var : zeroOrderVarList) {
        			if (varOrderRelationMap.containsKey(var)) {
        				varOrderRelationMap.get(var).add(exprOrderInfo);
        			} else {
        				List<ExprConverter> exprOrderInfoList = new ArrayList<>();
        				exprOrderInfoList.add(exprOrderInfo);
        				varOrderRelationMap.put(var, exprOrderInfoList);
        			}
        		}
    		}
    	}

    	// doing depth-first search from the system output backwards till system input(s), the largest accumulative order difference along the end-2-end branch is the system order
    	HashMap<String, List<String>> varVisitedSourceMap = new HashMap<>();
    	Stack<String> varStack = new Stack<>();
    	Stack<Integer> orderStack =  new Stack<>();
    	List<String> sysInputVarNameList = new ArrayList<>();
    	for (VarDecl agreeVar : sysInputs) {
    		sysInputVarNameList.add(agreeVar.id);
    	}
    	
    	// a list of the variables whose upstream subgraph (including feedback path) are completely explored
    	// system-level inputs are not included since they don't have upstream sub-graph
    	List<String> fullyVisitedVarList = new ArrayList<>();
    	// record the current order of explored upstream sub-graph
    	HashMap<String, Integer> varOrderInfoMap = new HashMap<>();
    	
    	
    	// assume only one system output
    	varStack.push(sysOutputs.get(0).id);
    	orderStack.push(0);
    	while (!varStack.isEmpty()) {
    		String currentVar = varStack.peek();
    		if (!varOrderInfoMap.containsKey(currentVar)) {
    			varOrderInfoMap.put(currentVar, 0);
    		}
    		
    		boolean hasUnvisitedInput = false;
    		
    		// if current var has NOT (been fully explored or system input), then execute the exploration
    		if (!(fullyVisitedVarList.contains(currentVar) || sysInputVarNameList.contains(currentVar))) {
    		
				if (!varVisitedSourceMap.containsKey(currentVar)) {	
					varVisitedSourceMap.put(currentVar, new ArrayList<>());
	    		}
	    		// if current var belongs to a connection (as a destination var)
	    		if (connectionMap.keySet().contains(currentVar)) {
	    			String sourceVar = connectionMap.get(currentVar);
	    			// if source variable hasn't been visited yet, then...
	    			if (!varVisitedSourceMap.get(currentVar).contains(sourceVar)) {
	    				// 1. set flag
	    				hasUnvisitedInput = true;
	    				// 2.1. stop push at loop, which is equivalent to "push (visited) and pop".
	    				if (varStack.contains(sourceVar)) {
	    					//pure connection won't have any effect on order, so do nothing here
						}
	    				// 2.2 otherwise push        					
	    				else {
							varStack.push(sourceVar);
							orderStack.push(0);
						}
	    				// 3. set source var as visited
	        			varVisitedSourceMap.get(currentVar).add(sourceVar);
	    			}
	    		}
	    		else {
	    			outerloop:
	    			for (ExprConverter exprOrderInfo : varOrderRelationMap.get(currentVar)) {
	        			for (String sourceVar : exprOrderInfo.getAllVarAndHighestOrder().keySet()) {
	        				// if source variable hasn't been visited yet, then...
	        				if (!varVisitedSourceMap.get(currentVar).contains(sourceVar)) {
	        					// 1. set flag
	            				hasUnvisitedInput = true;
	            				// 2.1. stop push at loop, which is equivalent to "push (visited) and pop".
	            				if (varStack.contains(sourceVar)) {
	            					// only self visit with different order is worth recording. 
	            					int currentVarMaxOrderSoFar = varOrderInfoMap.get(currentVar);
	            					int selfLoopOrder = exprOrderInfo.getAllVarAndHighestOrder().get(sourceVar);
	            					if (currentVarMaxOrderSoFar < selfLoopOrder) {
	            						varOrderInfoMap.put(currentVar, selfLoopOrder);
	            					}
	        					}
	            				// 2.2 otherwise push        					
	            				else {
	        						varStack.push(sourceVar);
	        						// whenever push a source variable, we also push the order difference between it and its destination variable
	        						orderStack.push(exprOrderInfo.getAllVarAndHighestOrder().get(sourceVar));
	        					}
	                			// 3. set source var as visited
	                			varVisitedSourceMap.get(currentVar).add(sourceVar);
	                			break outerloop;
	        				}
	        			}        				
	    			}
	    		}
    		}
    		if (!hasUnvisitedInput) {
    			fullyVisitedVarList.add(currentVar);
    			varStack.pop();
    			// whenever pop a source variable, we also pop the order difference between it and its destination variable
    			int orderDifference = orderStack.pop();
    			if (!varStack.isEmpty()) {
    				int currentVarMaxOrder = varOrderInfoMap.get(currentVar);
    				String parentVar = varStack.peek();
    				int parentVarMaxOrderSoFar = varOrderInfoMap.get(parentVar);
    				if (parentVarMaxOrderSoFar < currentVarMaxOrder + orderDifference) {
    					varOrderInfoMap.put(parentVar, currentVarMaxOrder + orderDifference);
    				}
    			}
    		}
    	}    	
    	return varOrderInfoMap.get(sysOutputs.get(0).id);
    }
    
}
