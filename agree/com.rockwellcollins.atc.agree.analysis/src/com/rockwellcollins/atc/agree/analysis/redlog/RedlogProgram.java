package com.rockwellcollins.atc.agree.analysis.redlog;

import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;

import com.google.common.base.Strings;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeStatement;
import com.rockwellcollins.atc.agree.analysis.AgreeException;

import jkind.lustre.Node;
import jkind.lustre.BinaryExpr;
import jkind.lustre.Expr;
import jkind.lustre.IdExpr;
import jkind.lustre.Contract;
import jkind.Assert;
import jkind.lustre.VarDecl;
import jkind.lustre.NamedType;
import jkind.util.Util;

public class RedlogProgram {

	public final List<VarDecl> sysInputs;
	public final List<VarDecl> sysOutputs;
	public final List<VarDecl> allVariables;
    public final List<Contract> componentContracts;
    public final HashMap<VarDecl, Contract> systemContracts;
	public final List<AgreeStatement> connectionAssertions;
	public final List<Node> globalLustreNodes;
	public final List<String> properties;
	private boolean hasIntVar;
	private boolean hasRealVar;
	private List<String> sysInputsOutputsAtComponentLevel;
	
    public RedlogProgram(List<VarDecl> sysInputs, List<VarDecl> sysOutputs,List<VarDecl> allVariables, 
    		HashMap<VarDecl, Contract> systemContracts, List<Contract> componentContracts, List<AgreeStatement> connectionAssertions, List<Node> globalLustreNodes, List<String> properties) {
		this.sysInputs = Util.safeList(sysInputs);
		this.sysOutputs = Util.safeList(sysOutputs);
		this.allVariables = Util.safeList(allVariables);
		this.componentContracts = Util.safeList(componentContracts);
		Assert.isNotNull(systemContracts);
		this.systemContracts = systemContracts;
		this.connectionAssertions = Util.safeList(connectionAssertions);
		this.globalLustreNodes = Util.safeList(globalLustreNodes);
		this.properties = Util.safeList(properties);
		checkVarTypes();
		findSysInputsOutputsAtComponentLevel();
	}
    
    private void checkVarTypes() {
    	for (VarDecl var : allVariables) {
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
    		// TODO: pop out a window warning :"Warning, Redlog is trying to solve an Int-Real-mixed type problem. Check counterexample (if any) for type consistence."
    		setDomain = "rlset r$\r\n\r\n";
    	} else if (hasRealVar) {
    		setDomain = "rlset r$\r\n\r\n";
    	} else if (hasIntVar) {
    		setDomain = "rlset z$\r\n\r\n";
    	} else {
    		throw new AgreeException("SAT problem solving using Redlog is not implemented yet.");
    	}
    	content.append(setDomain);
    	
    	// appending formula, for now, we only assume there's one contract here
    	// String explicitComposedContractName = systemContracts.keySet().iterator().next().id;
    	// content.append(explicitComposedContractName + ":=");
    	content.append("__systemStrongestProperty:=");
    	
    	StringBuilder explicitComposedContractB4QE = new StringBuilder();
    	int unpairedLeftParenthesisCount = 0;
    	for (VarDecl var : allVariables) {
    		if (!isVarConnectedToTopSystem(var)) {
    			explicitComposedContractB4QE.append("ex(" + var.id + ", ");
    			unpairedLeftParenthesisCount++;
    		}
    	}
    	
    	explicitComposedContractB4QE.append("(");
    	unpairedLeftParenthesisCount++;
    	for (AgreeStatement conn : connectionAssertions) {
    		explicitComposedContractB4QE.append(conn.expr.toString() + " and ");
    	}
    	for (Contract contract : componentContracts) {
    		explicitComposedContractB4QE.append(contractToRedlogString(contract) + " and ");
    	}
    	explicitComposedContractB4QE.setLength(explicitComposedContractB4QE.length() - 5);
    	
    	explicitComposedContractB4QE.append(Strings.repeat(")", unpairedLeftParenthesisCount));
    	unpairedLeftParenthesisCount = 0;
    	
    	content.append(explicitComposedContractB4QE.toString() + ";\r\n\r\n");
    	
    	content.append("__result:=");
    	for (VarDecl var : sysInputs) {
    		content.append("all(" + var.id + ", ");
    		unpairedLeftParenthesisCount++;
    	}
    	for (VarDecl var : sysOutputs) {
    		content.append("all(" + var.id + ", ");
    		unpairedLeftParenthesisCount++;
    	}
    	for (String varId : sysInputsOutputsAtComponentLevel) {
    		content.append("all(" + varId + ", ");
    		unpairedLeftParenthesisCount++;
    	}
    	
    	content.append("(");
    	unpairedLeftParenthesisCount++;
    	content.append("(" + explicitComposedContractB4QE.toString() + ") impl ");
    	// for now, we only assume there's one contract here
    	Contract sysContract = systemContracts.entrySet().iterator().next().getValue();
    	content.append(contractToRedlogString(sysContract));
    	content.append(Strings.repeat(")", unpairedLeftParenthesisCount) + ";\r\n\r\n");
    	// get the system strongest property
    	content.append("\"//begin printing system strongest property:\";\r\n");
    	content.append("rlqe __systemStrongestProperty;\r\n");
    	content.append("\"//end printing\";\r\n\r\n");
    	// prove the postulated system property
    	content.append("\"//begin printing system property verification result:\";\r\n");
    	content.append("rlqea __result;\r\n");
    	content.append("\"//end printing\";\r\n\r\n");
    	content.append("SHOWTIME;");
    	
    	//TODO: need also to replace other special chars in the future
    	return content.toString().replace("_", "!_");
    }
    
    private static String contractToRedlogString(Contract contract) {
		String assumption = "";
		String guarantee = "";
		if (!contract.requires.isEmpty()) {
			for (Expr require : contract.requires) {
				assumption += require.toString() + " and ";
			}
			assumption = assumption.substring(0, assumption.length() - 5);
		}
		// normally in a good desing, ensures cannot be empty
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
    
    public boolean hasIntVar()
    {
    	return this.hasIntVar;
    }
}
