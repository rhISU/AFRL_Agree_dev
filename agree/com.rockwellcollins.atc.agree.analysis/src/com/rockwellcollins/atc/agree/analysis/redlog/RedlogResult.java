package com.rockwellcollins.atc.agree.analysis.redlog;

import java.util.List;

import jkind.api.results.JKindResult;
import jkind.api.results.Renaming;

public class RedlogResult extends JKindResult {

	private String initialSystemConstraint;
	public void setInitialSystemConstraint(String isc) {
		this.initialSystemConstraint = isc;
	}
	public String getInitialSystemConstraint() {
		return this.initialSystemConstraint;
	}
	
	private String strongestSystemProperty;
	public void setStrongestSystemProperty(String ssp) {
		this.strongestSystemProperty = ssp;
	}
	public String getStrongestSystemProperty() {
		return this.strongestSystemProperty;
	}
	
	private String weakestComponentProperty;
	public void setWeakestComponentProperty(String wcp) {
		this.weakestComponentProperty = wcp;
	}
	public String getWeakestComponentProperty() {
		return this.weakestComponentProperty;
	}
	
	private List<String> proerptyResultStringList;
	public void setPropertyResultStringList(List<String> prl) {
		this.proerptyResultStringList = prl;
	}
	public List<String> getPropertyResultStringList() {
		return this.proerptyResultStringList;
	}
	
	public RedlogResult(String name, List<String> properties, Renaming renaming) {
		super(name, properties, renaming);
	}
}
