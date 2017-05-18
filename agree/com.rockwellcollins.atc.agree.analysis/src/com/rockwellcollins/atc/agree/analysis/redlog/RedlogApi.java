package com.rockwellcollins.atc.agree.analysis.redlog;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

import jkind.JKindException;
import jkind.api.ApiUtil;
import jkind.lustre.values.EnumValue;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.Signal;
import jkind.util.Util;

import org.eclipse.core.runtime.IProgressMonitor;

public class RedlogApi {
	protected Integer timeout = null;

	/**
	 * Set a maximum run time for entire execution
	 * 
	 * @param timeout
	 *            A positive timeout in seconds
	 */
	public void setTimeout(int timeout) {
		if (timeout <= 0) {
			throw new RedlogException("Timeout must be positive");
		}
		this.timeout = timeout;
	}

	/**
	 * Run Redlog on a Redlog program
	 * 
	 * @param redlogProgram
	 *            Redlog Program
	 * @param result
	 *            Place to store results as they come in
	 * @param monitor
	 *            Used to check for cancellation
	 * @throws redlog.RedlogException
	 */
	public void execute(RedlogProgram redlogProgram, RedlogResult result, IProgressMonitor monitor) {
		execute(redlogProgram.toString(), result, monitor);
	}

	/**
	 * Run Redlog on a Redlog program
	 * 
	 * @param redlogProgram
	 *            Redlog Program as text
	 * @param result
	 *            Place to store results as they come in
	 * @param monitor
	 *            Used to check for cancellation
	 * @throws redlog.RedlogException
	 */
	public void execute(String redlogProgram, RedlogResult result, IProgressMonitor monitor) {
		File redlogFile = null;
		try {
			redlogFile = writeRedlogFile(redlogProgram);
			execute(redlogFile, result, monitor);
		} finally {
			ApiUtil.safeDelete(redlogFile);
		}
	}

	/**
	 * Run Redlog on a Redlog program
	 * 
	 * @param redlogFile
	 *            File containing Redlog program
	 * @param result
	 *            Place to store results as they come in
	 * @param monitor
	 *            Used to check for cancellation
	 * @throws redlog.RedlogException
	 */
	public void execute(File redlogFile, RedlogResult result, IProgressMonitor monitor) {
		execute(this::getRedlogProcessBuilder, redlogFile, result, monitor);
	}
	
	
	public static void execute(Function<File, ProcessBuilder> runCommand, File redlogFile,
			RedlogResult result, IProgressMonitor monitor) {
		File xmlFile = null;
		try {
			xmlFile = getXmlFile(redlogFile);
			ApiUtil.safeDelete(xmlFile);
			if (xmlFile.exists()) {
				throw new RedlogException("Existing XML file cannot be removed: " + xmlFile);
			}
			callRedlog(runCommand, redlogFile, xmlFile, result, monitor);
		} catch (RedlogException e) {
			throw e;
		} catch (Throwable t) {
			throw new RedlogException(result.getText(), t);
		} finally {
			ApiUtil.safeDelete(xmlFile);
		}
	}
	
	private static void callRedlog(Function<File, ProcessBuilder> runCommand, File redlogFile,
			File xmlFile, RedlogResult result, IProgressMonitor monitor) throws IOException,
			InterruptedException {
		ProcessBuilder builder = runCommand.apply(redlogFile);
		Process process = null;
		try (RedlogXmlFileInputStream xmlStream = new RedlogXmlFileInputStream(xmlFile)) {
			XmlParseThread parseThread = new XmlParseThread(xmlStream, result);

			try {
				result.start();
				process = builder.start();
				String[] pair = readRedlogOutput(process, monitor);
				result.setSystemStrongestProperty(pair[0].replace(" or ", "\r\n or \r\n"));				
				result.setText(pair[1]);
				writeXmlFile(xmlFile, result);
				parseThread.start();
			} finally {
				int code = 0;
				if (process != null) {
					if (monitor.isCanceled() && process.isAlive()) {
						// Only destroy the process if we have to since it can
						// change the exit code on Windows
						process.destroy();
					}
					code = process.waitFor();
				}

				xmlStream.done();
				parseThread.join();

				if (monitor.isCanceled()) {
					result.cancel();
				} else {
					result.done();
				}
				monitor.done();

				if (code != 0 && !monitor.isCanceled()) {
					throw new JKindException("Abnormal termination, exit code " + code
							+ System.lineSeparator() + result.getText());
				}
			}

			if (parseThread.getThrowable() != null) {
				throw new JKindException("Error parsing XML", parseThread.getThrowable());
			}
		}
	}
	
	private static String[] readRedlogOutput(Process process, IProgressMonitor monitor) throws IOException {
		BufferedReader r = new BufferedReader(new InputStreamReader(process.getInputStream()));
		StringBuilder ssp = new StringBuilder();
		StringBuilder verificationResult = new StringBuilder();
		String[] pair = new String[2];
		
		while (true) {
			if (monitor.isCanceled()) {
				return null;
			} else if (r.ready()) {
				String line;
				while (true) {
					line = r.readLine();
					if (line == null) {
						try {
							Thread.sleep(100);
						} catch (InterruptedException e) {
						}
					} else if (line.contains("End-of-file") || line.contains("Quitting")) {
						break;
					} else if (line.startsWith("//begin printing system strongest property:")) {
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								ssp.append(line);
							}
							line = r.readLine();
						}
					} else if (line.startsWith("//begin printing system property verification result:")) {
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								verificationResult.append(line);
							}
							line = r.readLine();
						}
					} else if (line.startsWith("Time: ")) {
						// runtime
						verificationResult.append(line);
					} else {
						continue;
					}
				}
				pair[0] = ssp.toString().replaceAll("[!\r\n]", "").replace("$", "\r\n");
				pair[1] = verificationResult.toString().replaceAll("[!\r\n]", "").replace(",", ",\r\n").replace("$", "\r\n");
				return pair;
			} else if (!process.isAlive()) {
				return null;
			}
		}
	}

	private static void writeXmlFile(File xmlFile, RedlogResult redlogResult) throws FileNotFoundException {
		XmlWriter writer = new XmlWriter(xmlFile.getPath(), false);
		writer.begin();
		String property = redlogResult.getPropertyResults().get(0).getName();
		String redlogOutput = redlogResult.getText();
		String runtimeLine = redlogOutput.substring(redlogResult.getText().indexOf("Time: "));
		double runtime = Double.parseDouble(runtimeLine.replace("Time:", "").replace("ms", "").trim()) / 1000;
		if (redlogResult.getText().replace("{", "").startsWith("true")) {
			writer.writeValid(property, runtime);
		} else if (redlogResult.getText().replace("{", "").startsWith("unknown")) {
			writer.writeUnknown(property, runtime);
		} else {
			Counterexample cex = extractCounterexample(redlogResult);
			writer.writeInvalid(property, cex, runtime);
		}
		writer.end();
	}
	
	private static Counterexample extractCounterexample(RedlogResult redlogResult) {
		// for now, counterexample found by QE has only 1 step
		Counterexample cex = new Counterexample(1);
		for (String line : redlogResult.getText().split("\r\n")) {
			if (line.contains("=")) {
				String[] segments = line.replaceAll("[,{}]", "").split("=");
				String var = segments[0].trim();
				Signal<Value> signal = cex.getOrCreateSignal(var);
				Value value = new EnumValue(segments[1].trim());
				signal.putValue(0, value);
			}
		}
		return cex;
	}
	
	private static File getXmlFile(File redlogFile) {
		return new File(redlogFile.toString() + ".xml");
	}
	
	public static File writeRedlogFile(String redlogProgram) {
		File file = null;
		try {
			file = File.createTempFile("redlog-api", ".txt");
			Util.writeToFile(redlogProgram, file);
			return file;
		} catch (IOException e) {
			ApiUtil.safeDelete(file);
			throw new RedlogException("Cannot write to file: " + file, e);
		}
	}
	
	private ProcessBuilder getRedlogProcessBuilder(File redlogFile) {
		List<String> args = new ArrayList<>();
		args.addAll(Arrays.asList(new String[] {"redpsl.bat", "<"}));
		/*
		if (timeout != null) {
			args.add("-timeout");
			args.add(timeout.toString());
		}*/
		args.add(redlogFile.toString());

		ProcessBuilder builder = new ProcessBuilder(args);
		builder.redirectErrorStream(true);
		return builder;
	}
}
