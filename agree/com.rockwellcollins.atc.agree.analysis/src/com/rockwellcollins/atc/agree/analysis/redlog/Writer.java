package com.rockwellcollins.atc.agree.analysis.redlog;

import jkind.results.Counterexample;

public abstract class Writer {
	public abstract void begin();
	
	public abstract void end();
	
	public abstract void writeValid(String prop, double runtime);
	
	public abstract void writeInvalid(String prop, Counterexample ce, double runtime);
	
	public abstract void writeUnknown(String prop, double runtime);
}
