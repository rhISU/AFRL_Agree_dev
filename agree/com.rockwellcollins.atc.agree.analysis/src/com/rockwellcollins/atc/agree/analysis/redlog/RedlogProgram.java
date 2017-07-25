package com.rockwellcollins.atc.agree.analysis.redlog;

import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.Map.Entry;

import com.google.common.base.Strings;
import com.rockwellcollins.atc.agree.agree.ThisExpr;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeStatement;
import com.rockwellcollins.atc.agree.analysis.AgreeException;

import jkind.lustre.BinaryExpr;
import jkind.lustre.BinaryOp;
import jkind.lustre.BoolExpr;
import jkind.lustre.IdExpr;
import jkind.lustre.Node;
import jkind.lustre.Expr;
import jkind.lustre.Contract;
import jkind.Assert;
import jkind.lustre.VarDecl;
import jkind.lustre.NamedType;
import jkind.util.Util;

public class RedlogProgram {

	private List<VarDecl> sysInputs;
	public List<VarDecl> getSysInputs() {
		return this.sysInputs;
	}
	protected void setSysInputs(List<VarDecl> sysInputs) {
		this.sysInputs = sysInputs;
	}
	private List<VarDecl> sysOutputs;
	public List<VarDecl> getSysOutputs() {
		return this.sysOutputs;
	}
	protected void setSysOutputs(List<VarDecl> sysOutputs) {
		this.sysOutputs = sysOutputs;
	}
	private List<VarDecl> targetCompInputs;
	protected void setTargetCompInputs(List<VarDecl> targetCompInputs) {
		this.targetCompInputs = targetCompInputs;
	}
	private List<VarDecl> targetCompOutputs;
	protected void setTargetCompOutputs(List<VarDecl> targetCompOutputs) {
		this.targetCompOutputs = targetCompOutputs;
	}
	private List<VarDecl> contextCompVariables;
	public List<VarDecl> getContextCompVariables() {
		return this.contextCompVariables;
	}
	protected void setContextCompVariables(List<VarDecl> contextCompVariables) {
		this.contextCompVariables = contextCompVariables;
		// check variables types
		checkVarTypes();
	}
	private List<Contract> contextCompContracts;
	protected void setContextCompContracts(List<Contract> contextCompContracts) {
		this.contextCompContracts = contextCompContracts;
	}
	private HashMap<VarDecl, Contract> systemContracts;
	public HashMap<VarDecl, Contract> getSystemContracts() {
		return this.systemContracts;
	}
	protected void setSystemContracts(HashMap<VarDecl, Contract> systemContracts) {
		this.systemContracts = systemContracts;
	}
	private Contract targetCompContract;
	protected void setTargetCompContract(Contract targetCompContract) {
		this.targetCompContract = targetCompContract;
	}
	private List<AgreeStatement> connectionAssertions;
	protected void setConnectionAssertions(List<AgreeStatement> connectionAssertions) {
		this.connectionAssertions = connectionAssertions;
	}
	private int maxSysOrder;
	protected void setMaxSysOrder(int maxSysOrder) {
		this.maxSysOrder = maxSysOrder;
	}
	
	private List<Node> globalLustreNodes;
	private List<String> properties;
	public List<String> getProperties() {
		return this.properties;
	}
	private boolean hasIntVar;
    public boolean hasIntVar()
    {
    	return this.hasIntVar;
    }
    
	private boolean hasRealVar;
	
	public RedlogProgram(List<Node> globalLustreNodes, List<String> properties) {
		this.sysInputs = null;
		this.sysOutputs = null;
		this.targetCompInputs = null; 
		this.targetCompOutputs = null;
		this.contextCompVariables = null;
		this.contextCompContracts = null;
		this.targetCompContract = null;
		this.systemContracts = null;
		this.connectionAssertions = null;
		this.globalLustreNodes = Util.safeList(globalLustreNodes);
		this.properties = Util.safeList(properties);
		this.maxSysOrder = 0;
	}
	
	// Recommend to use the shorter version of constructor instead of this one
    public RedlogProgram(List<VarDecl> sysInputs, List<VarDecl> sysOutputs, List<VarDecl> targetCompInputs, List<VarDecl> targetCompOutputs, List<VarDecl> allVariables, 
    		HashMap<VarDecl, Contract> systemContracts, Contract targetCompContract, List<Contract> componentContracts, List<AgreeStatement> connectionAssertions, 
    		List<Node> globalLustreNodes, List<String> properties, int maxSysOrder) {
		this.sysInputs = Util.safeList(sysInputs);
		this.sysOutputs = Util.safeList(sysOutputs);
		this.targetCompInputs = Util.safeList(targetCompInputs); // is null if system level implementation is chosen in compositional verification
		this.targetCompOutputs = Util.safeList(targetCompOutputs); // is null if system level implementation is chosen in compositional verification
		this.contextCompVariables = Util.safeList(allVariables);
		this.contextCompContracts = Util.safeList(componentContracts);
		this.targetCompContract = targetCompContract; // is null if system level implementation is chosen in compositional verification
		Assert.isNotNull(systemContracts);
		this.systemContracts = systemContracts;
		this.connectionAssertions = Util.safeList(connectionAssertions);
		this.globalLustreNodes = Util.safeList(globalLustreNodes);
		this.properties = Util.safeList(properties);
		this.maxSysOrder = maxSysOrder;
		checkVarTypes();
	}
    
    private void checkVarTypes() {
    	// make sure all component variables are type checked.
    	List<VarDecl> allCompVars = new ArrayList<VarDecl>();
    	allCompVars.addAll(contextCompVariables);
    	if (targetCompContract!=null)
    	{
    		allCompVars.addAll(targetCompInputs);
    		allCompVars.addAll(targetCompOutputs);
    	}
    	//TODO: need to go deep into customized data types to find out the base tyep of the data.
    	for (VarDecl var : allCompVars) {
    		if (!(var.type instanceof NamedType)) {
    			throw new AgreeException("Redlog has not yet supportted type: " + var.type.toString());
    		} else if (!hasIntVar && ((NamedType) var.type).name.equals("int")) {
    			hasIntVar = true;
    			if (hasRealVar) return;
    		} else if (!hasRealVar && ((NamedType) var.type).name.equals("real")) {
    			hasRealVar = true;
    			if (hasIntVar) return;
    		}
    	}
    }
    
    public String toString() {
    	StringBuilder content = new StringBuilder();
    	content.append("off echo$\r\n\r\noff nat$\r\n\r\n");
    	
    	String setDomain;
    	if (hasRealVar && hasIntVar) {
    		// TODO: pop out a window warning :"Warning, Redlog is trying to solve an Int-Real-mixed type problem. Check counterexample (if any) for type consistency."
    		setDomain = "rlset r$\r\n\r\n";
    	} else if (hasRealVar) {
    		setDomain = "rlset r$\r\n\r\n";
    	} else if (hasIntVar) {
    		setDomain = "rlset z$\r\n\r\n";
    	} else {
    		throw new AgreeException("SAT problem solving using Redlog is not implemented yet.");
    	}
    	content.append(setDomain);
    	
    	// if targetCompContract == null, it means this compositional verification is initiated from the system-level implementation, 
    	// we then need to derive the strongest system property
    	if (targetCompContract == null)
    	{
    		// initial system constraints derivation
        	if (this.maxSysOrder > 0 ) {
        		content.append("__initialSystemConstraint:=");
        		String initialSysCondition = this.getInitialSysConstraint();
        		content.append(initialSysCondition + ";\r\n\r\n");
            	content.append("\"//begin printing the initial system constraint:\";\r\n");
            	content.append("rlqe __initialSystemConstraint;\r\n");
            	content.append("\"//end printing\";\r\n\r\n");
    		}
        	
        	// get the strongest system property for general steps
    		content.append("__strongestSystemProperty:=");
        	String strongestSysProperty = this.getStrongestSysProperty();
        	content.append(strongestSysProperty + ";\r\n\r\n");
        	content.append("\"//begin printing the strongest system property:\";\r\n");
        	content.append("rlqe __strongestSystemProperty;\r\n");
        	content.append("\"//end printing\";\r\n\r\n");
    	}
    	// if targetCompContract != null, it means this compositional verification is initiated from a target component, 
    	// we then need to derive the weakest component contract for the target component
    	// assume only one guarantee for now
    	// TODO: extend to time-dependent cases.
    	else 
		{
        	content.append("__weakestComponentProperty:=");
        	String theWeakestCompProperty = this.getWeakestCompProperty();
        	content.append(theWeakestCompProperty + ";\r\n\r\n");
        	int unpairedLeftParenthesisCount = 0;
        	content.append("__result:=");
        	for (VarDecl var : targetCompInputs) {
        		content.append("all(" + var.id + ", ");
        		unpairedLeftParenthesisCount++;
        	}
        	for (VarDecl var : targetCompOutputs) {
        		content.append("all(" + var.id + ", ");
        		unpairedLeftParenthesisCount++;
        	}
        	/*
        	for (String varId : sysInputsOutputsAtComponentLevel) {
        		content.append("all(" + varId + ", ");
        		unpairedLeftParenthesisCount++;
        	}
        	*/
        	content.append("(");
        	unpairedLeftParenthesisCount++;
        	
        	content.append(zeroOrderContractToRedlogString(targetCompContract) + " impl (" + theWeakestCompProperty + ")");
        	content.append(Strings.repeat(")", unpairedLeftParenthesisCount) + ";\r\n\r\n");
        	// get the weakest component property
        	content.append("\"//begin printing the weakest component property:\";\r\n");
        	content.append("rlqe __weakestComponentProperty;\r\n");
        	content.append("\"//end printing\";\r\n\r\n");
    	}
    	
    	// verification steps for non-time-dependent system and property
    	// TODO: is it possible to have time-dependent property for non-time-dependent system?
    	if (this.maxSysOrder == 0) {
    		for (String property : this.properties) {
            	int unpairedLeftParenthesisCount = 0;
            	content.append("__result__of" + property + ":=");
        		for (VarDecl var : sysInputs) {
            		content.append("all(" + var.id + ", ");
            		unpairedLeftParenthesisCount++;
            	}
            	for (VarDecl var : sysOutputs) {
            		content.append("all(" + var.id + ", ");
            		unpairedLeftParenthesisCount++;
            	}
	        	content.append("(");
	        	unpairedLeftParenthesisCount++;
	        	content.append("__strongestSystemProperty impl ");
	        	for (VarDecl contractVar : this.systemContracts.keySet()) {
	        		if (contractVar.equals(property)) {
	        			content.append(zeroOrderContractToRedlogString(systemContracts.get(contractVar)));
	        			break;
	        		}
	        	}
	        	content.append(Strings.repeat(")", unpairedLeftParenthesisCount) + ";\r\n\r\n");
	    		// prove the postulated system property
	        	content.append("\"//begin printing system property verification result:\";\r\n");
	        	content.append("rlqea __result__of" + property + ";\r\n");
	            content.append("SHOWTIME;\r\n\r\n");
	        	content.append("\"//end printing\";\r\n\r\n");
    		}
    	} 
    	
    	// for time-dependent system and non-time dependent property
    	// TODO: what's the inductive formula for proving time-dependent property? 
    	else {
    		for (String property : this.properties) {
            	// base steps: for n-th order system, there're n initial steps
            	int unpairedLeftParenthesisCount = 0;
            	content.append("__base__of" + property + ":=");
        		String prefix = "";
        		for (int i = 0; i < this.maxSysOrder; i++) {
    	        	for (VarDecl var : sysInputs) {
    	        		content.append("all(" + prefix + var.id + ", ");
    	        		unpairedLeftParenthesisCount++;
    	        	}
    	        	for (VarDecl var : sysOutputs) {
    	        		content.append("all(" + prefix + var.id + ", ");
    	        		unpairedLeftParenthesisCount++;
    	        	}
        			prefix += RedlogAstBuilder.nextSuffix;
        		}
        		content.append("(");
	        	unpairedLeftParenthesisCount++;
	        	content.append("__initialSystemConstraint impl ");
	        	for (VarDecl contractVar : this.systemContracts.keySet()) {
	        		if (contractVar.equals(property)) {
	        			content.append(getContractStrForBaseSteps(systemContracts.get(contractVar)));
	        			break;
	        		}
	        	}
        		content.append(Strings.repeat(")", unpairedLeftParenthesisCount) + ";\r\n\r\n");
            	// prove the postulated system property
            	content.append("\"//begin printing system property base verification result:\";\r\n");
            	content.append("rlqea __base__of" + property + ";\r\n");
                content.append("SHOWTIME;\r\n");
            	content.append("\"//end printing\";\r\n\r\n");

            	// inductive step: A => G AGREE contract should be interpreted as Global(A) => Globally(G)
        		// for n-th order system, there're n pre steps
        		// reset prefix and unpairedLeftParenthesisCount
            	content.append("__inductive__of" + property + ":=");
        		prefix = "";
        		unpairedLeftParenthesisCount = 0;
        		for (int i = 0; i <= this.maxSysOrder; i++) {
    	        	for (VarDecl var : sysInputs) {
    	        		content.append("all(" + prefix + var.id + ", ");
    	        		unpairedLeftParenthesisCount++;
    	        	}
    	        	for (VarDecl var : sysOutputs) {
    	        		content.append("all(" + prefix + var.id + ", ");
    	        		unpairedLeftParenthesisCount++;
    	        	}
        			prefix += RedlogAstBuilder.preSuffix;
        		}
        		content.append("(");
	        	unpairedLeftParenthesisCount++;
	        	content.append("(__strongestSystemProperty and ");
	        	for (VarDecl contractVar : this.systemContracts.keySet()) {
	        		if (contractVar.equals(property)) {
	        			Contract contract = systemContracts.get(contractVar);
	        			Expr nameMarkedContractAssumeExpr = getNameMarkedContractAssumeExpr(contract);
	        			Expr nameMarkedContractGuaranteeExpr = getNameMarkedContractGuaranteeExpr(contract);
	        			// remove name mark before adding to the content.
	        			if (nameMarkedContractAssumeExpr == null) {
	        				String originalGuaranteeStr = nameMarkedContractGuaranteeExpr.toString();
	        				content.append(getOneStepShiftedExprStr(originalGuaranteeStr, systemContracts.get(contractVar).name, false).replace(contract.name + "__", "") + ")");
		    	        	content.append(" impl " +  originalGuaranteeStr.replace(contract.name + "__", ""));
	        			} else {
	        				String originalAssumeStr = nameMarkedContractAssumeExpr.toString();
	        				String originalGuaranteeStr = nameMarkedContractGuaranteeExpr.toString();	        				
	        				content.append(getOneStepShiftedExprStr(originalAssumeStr, systemContracts.get(contractVar).name, false).replace(contract.name + "__", "") + " and ");
	        				content.append(getOneStepShiftedExprStr(originalGuaranteeStr, systemContracts.get(contractVar).name, false).replace(contract.name + "__", "") + " and ");
	        				content.append(originalAssumeStr.replace(contract.name + "__", "") + ")");
	        				content.append(" impl " +  originalGuaranteeStr.replace(contract.name + "__", ""));
	        			}
        				break;
	        		}
	        	}
        		content.append(Strings.repeat(")", unpairedLeftParenthesisCount) + ";\r\n\r\n");
        		content.append("\"//begin printing system property inductive verification result:\";\r\n");
            	content.append("rlqea __inductive__of" + property + ";\r\n");
                content.append("SHOWTIME;\r\n");
            	content.append("\"//end printing\";\r\n\r\n");
    		}
    	}
    	
    	//TODO: need also to replace other special chars in the future
    	return content.toString().replace(".val", "").replace("=>", "impl").replace("_", "!_");
    }
    
    private String getInitialSysConstraint() {
    	StringBuilder explicitComposedInitConstraintB4QE = new StringBuilder();
    	int unpairedLeftParenthesisCount = 0;
    	for (VarDecl var : contextCompVariables) {
    		String orderShiftString = "";
    		for (int i = 0; i < this.maxSysOrder; i++) {
    			explicitComposedInitConstraintB4QE.append("ex(" + orderShiftString.toLowerCase() + var.id + ", ");
    			unpairedLeftParenthesisCount++;
    			orderShiftString += RedlogAstBuilder.nextSuffix;
    		}
    	}
    	explicitComposedInitConstraintB4QE.append("(");
    	unpairedLeftParenthesisCount++;
    	for (AgreeStatement conn : connectionAssertions) {
    		List<String> forwardShiftedExprStrList = getOrderShiftedConnStrList(conn.expr, this.maxSysOrder, true);
    		for (int i = 0; i < forwardShiftedExprStrList.size(); i++) {
    			explicitComposedInitConstraintB4QE.append(forwardShiftedExprStrList.get(i) + " and ");
    		}
    	}
    	for (Contract contract : contextCompContracts) {
   			// assume no assumption, 
   			// TODO: extend to general cases that include assumption
   			for (Expr expr : contract.ensures) {
   				List<String> forwardShiftedExprStrList = getForwardShiftedExprStrList(expr, contract.name, this.maxSysOrder);
   				for (int i = 0; i < forwardShiftedExprStrList.size(); i++) {
       				explicitComposedInitConstraintB4QE.append(forwardShiftedExprStrList.get(i) + " and ");
       			}
   			}
    	}
    	explicitComposedInitConstraintB4QE.setLength(explicitComposedInitConstraintB4QE.length() - 5);
    	
    	explicitComposedInitConstraintB4QE.append(Strings.repeat(")", unpairedLeftParenthesisCount));
    	// first replaceAll() eliminates the Pre__ terms in the initial constraint (and leaves only numbers), second replaceAll() eliminate the numerical initial values and leaves non-Pre__ vars.
    	return explicitComposedInitConstraintB4QE.toString().replaceAll("(\\s->\\s)(Pre__([^)]+))", "").replaceAll("(\\w+)(.(\\w+))?(\\s->\\s)", "");
    }
    
    private String getStrongestSysProperty()
    {
    	StringBuilder explicitComposedContractB4QE = new StringBuilder();
    	int unpairedLeftParenthesisCount = 0;
    	for (VarDecl var : contextCompVariables) {
    		String orderShiftString = "";
    		for (int i = 0; i <= this.maxSysOrder; i++) {
    			explicitComposedContractB4QE.append("ex(" + orderShiftString.toLowerCase() + var.id + ", ");
    			unpairedLeftParenthesisCount++;
    			orderShiftString += RedlogAstBuilder.preSuffix;
    		}
    	}
    	
    	explicitComposedContractB4QE.append("(");
    	unpairedLeftParenthesisCount++;
    	for (AgreeStatement conn : connectionAssertions) {
    		List<String> backwardShiftedExprStrList = getOrderShiftedConnStrList(conn.expr, this.maxSysOrder, false);
    		for (int i = 0; i < backwardShiftedExprStrList.size(); i++) {
    			explicitComposedContractB4QE.append(backwardShiftedExprStrList.get(i) + " and ");
    		}
    	}
    	for (Contract contract : contextCompContracts) {
    		if (this.maxSysOrder == 0) {
    			explicitComposedContractB4QE.append(zeroOrderContractToRedlogString(contract) + " and ");
    		}
    		else {
    			// assume no assumption, 
    			// TODO: extend to general cases that include assumption
    			for (Expr expr : contract.ensures) {
    				List<String> orderShiftedExprStrList = getBackwardShiftedExprStrList(expr, contract.name, this.maxSysOrder);
    				for (int i = 0; i < orderShiftedExprStrList.size(); i++) {
        				explicitComposedContractB4QE.append(orderShiftedExprStrList.get(i) + " and ");
        			}
    			}
    		}
    	}
    	explicitComposedContractB4QE.setLength(explicitComposedContractB4QE.length() - 5);
    	
    	explicitComposedContractB4QE.append(Strings.repeat(")", unpairedLeftParenthesisCount));
    	return explicitComposedContractB4QE.toString().replaceAll("(\\w)+(.(\\w)+)(\\s->\\s)", "");
    }
    
    
    // TODO: to be updated for time-dependent scenarios.
    private  String getWeakestCompProperty()
    {
    	StringBuilder explicitComposedContractB4QE = new StringBuilder();
    	int unpairedLeftParenthesisCount = 0;
    	for (VarDecl var : contextCompVariables) {
    		explicitComposedContractB4QE.append("all(" + var.id + ", ");
    		unpairedLeftParenthesisCount++;
    	}
    	for (VarDecl var : sysInputs) {
    		explicitComposedContractB4QE.append("all(" + var.id + ", ");
    		unpairedLeftParenthesisCount++;
    	}
    	for (VarDecl var : sysOutputs) {
    		explicitComposedContractB4QE.append("all(" + var.id + ", ");
    		unpairedLeftParenthesisCount++;
    	}
    	explicitComposedContractB4QE.append("(");
    	unpairedLeftParenthesisCount ++;
    	explicitComposedContractB4QE.append("("); // left parenthesis for the implication 
    	for (AgreeStatement conn : connectionAssertions) {
    		explicitComposedContractB4QE.append(conn.expr.toString() + " and ");
    	}
    	for (Contract contract : contextCompContracts) {
    		explicitComposedContractB4QE.append(zeroOrderContractToRedlogString(contract) + " and ");
    	}
    	explicitComposedContractB4QE.setLength(explicitComposedContractB4QE.length() - 5);
    	explicitComposedContractB4QE.append(")"); // right parenthesis for the implication
    	explicitComposedContractB4QE.append(" impl " + zeroOrderContractToRedlogString(systemContracts.entrySet().iterator().next().getValue()));
    	
    	explicitComposedContractB4QE.append(Strings.repeat(")", unpairedLeftParenthesisCount));
    	return explicitComposedContractB4QE.toString();
    }
    
    
    // TODO: move relative code here
    private String getBaseStepProof() {
    	for(int i = 0; i < this.maxSysOrder; i++) {
    		
    	}
		return null;
    }
    
    private String getContractStrForBaseSteps(Contract contract) {
    	//determine contract order
    	//neglect assume for now.
    	int contractOrder = 0;
		for (Expr ensure : contract.ensures) {
			ExprConverter exprInfo = new ExprConverter(ensure, "", globalLustreNodes);
		   	//Expr prefixedGuarantee = exprInfo.getPrefixedExpr();
		   	if (contractOrder < exprInfo.getOrderOfOrigExpr()) {
		   		contractOrder = exprInfo.getOrderOfOrigExpr();
		   	}
		}
    	if (contractOrder == 0) {
    		return zeroOrderContractToRedlogString(contract);
    	} else if (contractOrder > this.maxSysOrder) {
    		throw new AgreeException("Error: Order of the system contract is greater than the sytem order.");
    	} else {
    		Expr nameMarkedContractExpr = getNameMarkedContractExpr(contract);
    		List<String> forwardShiftedExprStrList = getForwardShiftedExprStrList(nameMarkedContractExpr, contract.name, this.maxSysOrder);
			String contractStr = "";
    		for (String exprStr : forwardShiftedExprStrList) {
    			// first replaceAll() eliminates the Pre__ terms in the initial constraint (and leaves only numbers), second replaceAll() eliminate the numerical initial values and leaves non-Pre__ vars.
    			// third replace() remove the contract name prefix, system-level contract doesn't need that in verification steps
				contractStr += exprStr.replaceAll("(\\s->\\s)(Pre__([^)]+))", "").replaceAll("(\\w+)(.(\\w+))?(\\s->\\s)", "").replace(contract.name + "__", "");
			}
    		return contractStr;
    	}
    }
    
    private Expr getNameMarkedContractAssumeExpr(Contract contract) {
		if (contract.requires.size() > 0) {
    		//initialize allRqesExpr
    		Expr allRequiresExpr = new ExprConverter(contract.requires.get(0), contract.name + "__", globalLustreNodes).getPrefixedExpr();
    		if (contract.requires.size() > 1)
    		{
    			for (int i = 1; i < contract.requires.size(); i++) {
    				allRequiresExpr = new BinaryExpr(allRequiresExpr, BinaryOp.AND, new ExprConverter(contract.requires.get(i), contract.name + "__", globalLustreNodes).getPrefixedExpr());
    			}
    		}
    		return allRequiresExpr;
		}
		return null;
    }
    
    private Expr getNameMarkedContractGuaranteeExpr(Contract contract) {
    	// there exists at least one ensure
    	Expr allEnsuresExpr = new ExprConverter(contract.ensures.get(0), contract.name + "__", globalLustreNodes).getPrefixedExpr();
		if (contract.ensures.size() > 1)
		{
			for (int i = 1; i < contract.ensures.size(); i++) {
				allEnsuresExpr = new BinaryExpr(allEnsuresExpr, BinaryOp.AND, new ExprConverter(contract.ensures.get(i), contract.name + "__", globalLustreNodes).getPrefixedExpr());
			}
		}
		return allEnsuresExpr;
    }
    
    private Expr getNameMarkedContractExpr(Contract contract) {
    	Expr allAssumeExpr =  getNameMarkedContractAssumeExpr(contract);
    	Expr allGuaranteeExpr = getNameMarkedContractGuaranteeExpr(contract);
    	if (allAssumeExpr == null) {
    		return allGuaranteeExpr;
    	} else {
			return new BinaryExpr(allAssumeExpr, BinaryOp.IMPLIES, allGuaranteeExpr);
		}
    }
    
    //TODO: rewrite this method to avoid using expr.toString() method, every expr should create an ExprConverter obj first (to be able to deal with Lustre nodes functions.). 
    private static String zeroOrderContractToRedlogString(Contract contract) {
		String assumption = "";
		String guarantee = "";
		if (!contract.requires.isEmpty()) {
			for (Expr require : contract.requires) {
				assumption += require.toString() + " and ";
			}
			assumption = assumption.substring(0, assumption.length() - 5);
		}
		// ensures cannot be empty
		if (!contract.ensures.isEmpty()) { 
			for (Expr ensure : contract.ensures) {
				guarantee += ensure.toString() + " and ";
			}
			guarantee = guarantee.substring(0, guarantee.length() - 5);
		}
		if (assumption.equals("")) {
			return guarantee;
		} else {
			return "(" + assumption + " impl " + guarantee + ")";
		}
    }
    
	// this returned list contains the order-shifted expr strings as well as the original expr string. 
    // TODO: avoid using expr.toString() directly, every expr should create an ExprConverter obj first.
	private static List<String> getForwardShiftedExprStrList(Expr originalExpr, String prefix, int order) {
		List<String> orderShiftedExprList = new ArrayList<String>();
		String originalExprStr = originalExpr.toString();
		orderShiftedExprList.add(originalExprStr);
		// only shift expr that contains variable, (e.g. no need to shift "true/false" statement)
		if (originalExprStr.contains(prefix)) {
			String temp = originalExprStr;
			for (int i = 1; i < order; i++) {
				temp = getOneStepShiftedExprStr(temp, prefix, true);;
				// "Pre__Next__" is canceled to ""
				orderShiftedExprList.add(temp.replace("Pre__Next__", ""));
			}
		}
		return orderShiftedExprList;
	}
    
	// this returned list contains the order-shifted expr strings as well as the original expr string. 
	private static List<String> getBackwardShiftedExprStrList(Expr originalExpr, String prefix, int order) {
		List<String> orderShiftedExprList = new ArrayList<String>();
		String originalExprStr = originalExpr.toString();
		orderShiftedExprList.add(originalExprStr);
		// only shift if necessary and only shift expr that contains variable, (e.g. no need to shift "true/false" statement)
		if (order > 0 && originalExprStr.contains(prefix)) {
			String maxOrderPrefixStr = "";
			for (int i = 1; i <= order; i++) {
				maxOrderPrefixStr += RedlogAstBuilder.preSuffix;
			}
			String temp = originalExprStr;
			// shift order by 1 then check until max order is reached.
			while (!temp.contains(maxOrderPrefixStr)) {
				temp = getOneStepShiftedExprStr(temp, prefix, false);
				orderShiftedExprList.add(temp);
			}
		}
		return orderShiftedExprList;
	}
	
	// the expr passed into this method is prefixed, so it will have "Pre__"-prefixed for every ordered variable, check before
	// this returned list contains the order-shifted expr strings as well as the original expr string. 
	private static List<String> getOrderShiftedConnStrList(Expr connExpr, int sysOrder, boolean forwardShift) {
		List<String> orderShiftedConnList = new ArrayList<String>();
		String originalConnExprStr =  connExpr.toString();
		orderShiftedConnList.add(originalConnExprStr);
		// connections are all 0 order expr
		if (sysOrder > 0) {
			String destVarName = ((jkind.lustre.BinaryExpr)connExpr).right.toString();
			String sourceVarName = ((jkind.lustre.BinaryExpr)connExpr).left.toString();
			String maxOrderPrefixStr = "";
			int totalShiftedOrder = forwardShift? sysOrder - 1 : sysOrder;
			for (int i = 1; i <= totalShiftedOrder; i++) {
				maxOrderPrefixStr += forwardShift? RedlogAstBuilder.nextSuffix : RedlogAstBuilder.preSuffix;
				orderShiftedConnList.add("(" + maxOrderPrefixStr + sourceVarName + " = " + maxOrderPrefixStr + destVarName + ")");
			}
		}
		return orderShiftedConnList;
	}
	
	
	private static String getOneStepShiftedExprStr(String exprStr, String prefix, boolean forwardShift) {
		String temporalPrefix = forwardShift? RedlogAstBuilder.nextSuffix : RedlogAstBuilder.preSuffix;
		return exprStr.replace(prefix, temporalPrefix + prefix).replace(RedlogAstBuilder.preSuffix + RedlogAstBuilder.nextSuffix, "");
	}
}


/*
// obsolete codes
private boolean isVarConnectedToTopSystem(VarDecl var) {
	return sysInputsOutputsAtComponentLevel.contains(var.id);
}

private void findSysInputsOutputsAtComponentLevel() {
	sysInputsOutputsAtComponentLevel = new ArrayList<>();
	for (AgreeStatement conn : connectionAssertions) {
		String source = ((IdExpr) ((BinaryExpr) conn.expr).left).id;
		String destination = ((IdExpr) ((BinaryExpr) conn.expr).right).id;
		
		for (VarDecl sysInput : sysInputs) {
			if (sysInput.id.equals(source) && (!sysInputsOutputsAtComponentLevel.contains(destination))) {
				sysInputsOutputsAtComponentLevel.add(destination);
			}
		}
		for (VarDecl sysOutput : sysOutputs) {
			if (sysOutput.id.equals(destination) && (!sysInputsOutputsAtComponentLevel.contains(source))) {
				sysInputsOutputsAtComponentLevel.add(source);
			}
		}
	}
}
*/
