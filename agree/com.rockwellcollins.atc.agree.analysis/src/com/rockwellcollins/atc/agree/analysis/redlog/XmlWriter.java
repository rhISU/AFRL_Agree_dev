package com.rockwellcollins.atc.agree.analysis.redlog;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;

import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.Signal;
import jkind.util.Util;

public class XmlWriter extends Writer {
	private final PrintWriter out;
	
	public XmlWriter(String filename, boolean useStdout) throws FileNotFoundException {
		if (useStdout) {
			this.out = new PrintWriter(System.out, true);
		} else {
			this.out = new PrintWriter(new FileOutputStream(filename));
		}
	}
	
	@Override
	public void begin() {
		out.println("<?xml version=\"1.0\"?>");
		out.println("<RedlogResults xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">");
	}

	@Override
	public void end() {
		out.println("</Results>");
		out.close();
	}

	@Override
	public void writeValid(String prop, double runtime) {
		out.println("  <Property name=\"" + prop + "\">");
		out.println("    <Runtime unit=\"sec\">" + runtime + "</Runtime>");
		out.println("    <Answer>valid</Answer>");
		out.println("  </Property>");
		out.flush();
	}

	
	@Override
	public void writeInvalid(String prop, Counterexample cex, double runtime) {
		out.println("  <Property name=\"" + prop + "\">");
		out.println("    <Runtime unit=\"sec\">" + runtime + "</Runtime>");
		out.println("    <Answer>falsifiable</Answer>");
		writeCounterexample(cex);
		out.println("  </Property>");
		out.flush();
	}
	
	@Override
	public void writeUnknown(String prop, double runtime) {
		out.println("  <Property name=\"" + prop + "\">");
		out.println("    <Runtime unit=\"sec\">" + runtime + "</Runtime>");
		out.println("    <Answer>unknown</Answer>");
		out.println("  </Property>");
		out.flush();
	}
	
	private void writeCounterexample(Counterexample cex) {
		out.println("    <Counterexample>");
		for (Signal<Value> signal : cex.getSignals()) {
			writeSignal(cex.getLength(), signal);
		}
		out.println("    </Counterexample>");
	}

	private void writeSignal(int k, Signal<Value> signal) {
		String name = signal.getName();
		// ignore type for now. types has to be created during building RedlogProgram 
		// Type type = types.get(name);
		out.println("      <Signal name=\"" + name + "\">");
		for (int i = 0; i < k; i++) {
			Value value = signal.getValue(i);
			if (!Util.isArbitrary(value)) {
				out.println("        <Value time=\"" + i + "\">" + value.toString() + "</Value>");
			}
		}
		out.println("      </Signal>");
	}
}
