package com.rockwellcollins.atc.agree.analysis.redlog;

import java.util.List;

import jkind.api.results.JKindResult;
import jkind.api.results.Renaming;

public class RedlogResult extends JKindResult {

	private String systemStrongestProperty;
	
	public RedlogResult(String name, List<String> properties, Renaming renaming) {
		super(name, properties, renaming);
	}
	
	public void setSystemStrongestProperty(String ssp) {
		this.systemStrongestProperty = ssp;
	}

	public String getSystemStrongestProperty() {
		return systemStrongestProperty;
	}
}
