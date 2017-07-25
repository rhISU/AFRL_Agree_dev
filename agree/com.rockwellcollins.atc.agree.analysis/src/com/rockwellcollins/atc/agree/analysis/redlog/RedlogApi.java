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
				readRedlogOutputIntoResult(process, monitor, result);
				// For now, the proofs of individual system properties are done in one single .redlog file, then to be shown on console.
				// TODO: individual property may initiate an individual verification thread in separate file.
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
	
	private static void readRedlogOutputIntoResult(Process process, IProgressMonitor monitor, RedlogResult result) throws IOException {
		BufferedReader r = new BufferedReader(new InputStreamReader(process.getInputStream()));
		StringBuilder isc = new StringBuilder();
		StringBuilder ssp = new StringBuilder();
		StringBuilder wcp = new StringBuilder();
		
		// each property takes two elements,
		// for inductive proof, first is base step result, second is inductive step result
		// for direct proof, first is set to be null, second is the verification result.
		List<String> resultList = new ArrayList<>();
		boolean baseResultJustAdded = false;
		
		while (true) {
			if (monitor.isCanceled()) {
				return;
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
					} else if (line.startsWith("//begin printing the initial system constraint:")) {
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								isc.append(line);
							}
							line = r.readLine();
						}
					} else if (line.startsWith("//begin printing the strongest system property:")) {
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								ssp.append(line);
							}
							line = r.readLine();
						}
					} else if (line.startsWith("//begin printing the weakest component property:")) {
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								wcp.append(line);
							}
							line = r.readLine();
						}
					} else if (line.startsWith("//begin printing system property verification result:")) {
						StringBuilder verificationResult = new StringBuilder();
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								verificationResult.append(line);
							} else if (line.startsWith("Time: ")) {
								// runtime
								verificationResult.append(line);
							} 
							line = r.readLine();
						}
						resultList.add(null);
						resultList.add(verificationResult.toString().replaceAll("[!\r\n]", "").replace(",", ",\r\n").replace("$", "\r\n"));
					} else if (line.startsWith("//begin printing system property base verification result:")) {
						StringBuilder bsr = new StringBuilder();
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								bsr.append(line);
							} else if (line.startsWith("Time: ")) {
								// runtime
								bsr.append(line);
							} 
							line = r.readLine();
						}
						resultList.add(bsr.toString().replaceAll("[!\r\n]", "").replace(",", ",\r\n").replace("$", "\r\n"));
						baseResultJustAdded = true;
					} else if (line.startsWith("//begin printing system property inductive verification result:")) {
						StringBuilder isr = new StringBuilder();	
						// skip the comment line
						line = r.readLine();
						while (!line.startsWith("//end printing")) {
							if (!line.contains(":")) {
								isr.append(line);
							} else if (line.startsWith("Time: ")) {
								// runtime
								isr.append(line);
							} 
							line = r.readLine();
						}
						if (baseResultJustAdded) {
							resultList.add(isr.toString().replaceAll("[!\r\n]", "").replace(",", ",\r\n").replace("$", "\r\n"));
						} else {
							throw new RedlogException("Missing base step result."); 
						}
					} else { continue; }
				}
				result.setInitialSystemConstraint(isc.toString().replaceAll("[!\r\n]", "").replace("$", "\r\n").replace(" or ", "\r\n or \r\n"));
				result.setStrongestSystemProperty(ssp.toString().replaceAll("[!\r\n]", "").replace("$", "\r\n").replace(" or ", "\r\n or \r\n"));		
				result.setWeakestComponentProperty(wcp.toString().replaceAll("[!\r\n]", "").replace("$", "\r\n").replace(" or ", "\r\n or \r\n"));
				result.setPropertyResultStringList(resultList);
				return;
			} else if (!process.isAlive()) {
				return;
			}
		}
	}

	private static void writeXmlFile(File xmlFile, RedlogResult redlogResult) throws FileNotFoundException {
		XmlWriter writer = new XmlWriter(xmlFile.getPath(), false);
		writer.begin();
		List<String> propertyResultStringList = redlogResult.getPropertyResultStringList();
		if (propertyResultStringList.size() != 2* redlogResult.getPropertyResults().size()) {
			throw new RedlogException("Properties size and results size don't match.");
		}
		for (int i = 0; i < redlogResult.getPropertyResults().size(); i++) {
			String property = redlogResult.getPropertyResults().get(i).getName();
			if (propertyResultStringList.get(2*i) == null) {
				String runtimeLine = propertyResultStringList.get(2*i + 1).substring(propertyResultStringList.get(2*i + 1).indexOf("Time: "));
				//TODO: Sometimes runtime line also include GC time
				double runtime = Double.parseDouble(runtimeLine.replace("Time:", "").replace("ms", "").trim()) / 1000;
				// sometimes, true result returned by redlog is simply "{}".
				if (propertyResultStringList.get(2*i + 1).replace("{", "").startsWith("true") || propertyResultStringList.get(2*i + 1).replace("{", "").startsWith("}")) {
					writer.writeValid(property, runtime);
				} else if (propertyResultStringList.get(2*i + 1).replace("{", "").startsWith("unknown")) {
					writer.writeUnknown(property, runtime);
				} else {
					Counterexample cex = extractCounterexample(propertyResultStringList.get(2*i + 1));
					writer.writeInvalid(property, cex, runtime);
				}
			} else {
				String runtimeLine1 = propertyResultStringList.get(2*i).substring(propertyResultStringList.get(2*i).indexOf("Time: "));
				String runtimeLine2 = propertyResultStringList.get(2*i + 1).substring(propertyResultStringList.get(2*i + 1).indexOf("Time: "));
				//TODO: Sometimes runtime line also include GC time
				double runtime = (Double.parseDouble(runtimeLine1.replace("Time:", "").replace("ms", "").trim())+ Double.parseDouble(runtimeLine2.replace("Time:", "").replace("ms", "").trim())) / 1000;
				// sometimes, true result returned by redlog is simply "{}".
				// first check base step
				if (propertyResultStringList.get(2*i).replace("{", "").startsWith("true") || propertyResultStringList.get(2*i).replace("{", "").startsWith("}")) {
					// then check inductive step
					if (propertyResultStringList.get(2*i + 1).replace("{", "").startsWith("true") || propertyResultStringList.get(2*i + 1).replace("{", "").startsWith("}")) {
						writer.writeValid(property, runtime);	
					} else if (propertyResultStringList.get(2*i + 1).replace("{", "").startsWith("unknown")) {
						writer.writeUnknown(property, runtime);
					} else {
						// TODO: need to distinguish concrete and inductive counterexample
						Counterexample cex = extractCounterexample(propertyResultStringList.get(2*i + 1));
						writer.writeInvalid(property, cex, runtime);
					}
				} else if (propertyResultStringList.get(2*i + 1).replace("{", "").startsWith("unknown")) {
					writer.writeUnknown(property, runtime);
				} else {
					Counterexample cex = extractCounterexample(propertyResultStringList.get(2*i + 1));
					writer.writeInvalid(property, cex, runtime);
				}
			}
		}
		writer.end();
	}
	
	private static Counterexample extractCounterexample(String rawCEX) {
		// for now, counterexample found by QE has only 1 step
		Counterexample cex = new Counterexample(1);
		for (String line : rawCEX.split("\r\n")) {
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
