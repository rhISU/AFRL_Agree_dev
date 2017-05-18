package com.rockwellcollins.atc.agree.analysis.redlog;

import java.io.InputStream;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;

import jkind.api.results.PropertyResult;
import jkind.api.xml.LineInputStream;
import jkind.lustre.values.EnumValue;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.Property;
import jkind.results.Signal;
import jkind.results.ValidProperty;
import jkind.results.InvalidProperty;

public class XmlParseThread extends Thread {
	private final InputStream xmlStream;
	private final RedlogResult result;
	private final DocumentBuilderFactory factory;
	private volatile Throwable throwable;

	public XmlParseThread(InputStream xmlStream, RedlogResult result) {
		super("Xml Parse");
		this.xmlStream = xmlStream;
		this.result = result;
		this.factory = DocumentBuilderFactory.newInstance();
	}
	
	@Override
	public void run() {
		try (LineInputStream lines = new LineInputStream(xmlStream)) {
			StringBuilder buffer = null;
			String line;
			while ((line = lines.readLine()) != null) {
				System.out.println(line);
				boolean beginProperty = line.contains("<Property ");
				boolean endProperty = line.contains("</Property>");
				
				if (beginProperty) {
					buffer = new StringBuilder();
					buffer.append(line);
				} else if (endProperty) {
					buffer.append(line);
					parsePropetyXml(buffer.toString());
					buffer = null;
				} else if (buffer != null) {
					buffer.append(line);
				}
			}
		} catch (Throwable t) {
			throwable = t;
		}
	}

    private Element parseXml(String xml) {
		try {
			DocumentBuilder builder = factory.newDocumentBuilder();
			StringReader stringReader = new StringReader(xml);
            InputSource inputSource = new InputSource(stringReader);
            Document doc = builder.parse(inputSource);
			return doc.getDocumentElement();
		} catch (Exception e) {
			throw new RedlogException("Error parsing: " + xml, e);
		}
	}

	public void parsePropetyXml(String propertyXml) {
		Property prop = getProperty(parseXml(propertyXml));
		String propName = prop.getName();
		PropertyResult pr = result.getPropertyResult(propName);
		if (pr == null) {
			pr = result.addProperty(propName);
			if (pr == null) {
				return;
			}
		}
		pr.setProperty(prop);
	}

	private Property getProperty(Element propertyElement) {
		String name = propertyElement.getAttribute("name");
		double runtime = getRuntime(getElement(propertyElement, "Runtime"));
		String answer = getAnswer(getElement(propertyElement, "Answer"));
		Counterexample cex = getCounterexample(getElement(propertyElement, "Counterexample"), 1);

		switch (answer.toLowerCase()) {
		case "valid":
			return new ValidProperty(name, answer, 0, runtime, null);

		case "falsifiable":
			return new InvalidProperty(name, null, cex, Collections.emptyList(), runtime);
			/*
		case "unknown":
			return new UnknownProperty(name, runtime);
			*/
		default:
			throw new RedlogException("Unknown property answer in XML file: " + answer);
		}
	}

	private double getRuntime(Node runtimeNode) {
		if (runtimeNode == null) {
			return 0;
		}
		return Double.parseDouble(runtimeNode.getTextContent());
	}

	private String getAnswer(Node answerNode) {
		return answerNode.getTextContent();
	}

	
	private Counterexample getCounterexample(Element cexElement, int k) {
		if (cexElement == null) {
			return null;
		}

		Counterexample cex = new Counterexample(k);
		for (Element signalElement : getElements(cexElement, "Signal")) {
			cex.addSignal(getSignal(signalElement));
		}
		return cex;
	}

	private Signal<Value> getSignal(Element signalElement) {
		String name = signalElement.getAttribute("name");
		/*
		String type = signalElement.getAttribute("type");
		if (type.contains("subrange ")) {
			type = "int";
		}*/

		Signal<Value> signal = new Signal<>(name);
		for (Element valueElement : getElements(signalElement, "Value")) {
			int time = Integer.parseInt(valueElement.getAttribute("time"));
			signal.putValue(time, new EnumValue(valueElement.getTextContent()));
		}
		return signal;
	}

	private Element getElement(Element element, String name) {
		return (Element) element.getElementsByTagName(name).item(0);
	}

	private List<Element> getElements(Element element, String name) {
		List<Element> elements = new ArrayList<>();
		NodeList nodeList = element.getElementsByTagName(name);
		for (int i = 0; i < nodeList.getLength(); i++) {
			elements.add((Element) nodeList.item(i));
		}
		return elements;
	}
	
	public Throwable getThrowable() {
		return throwable;
	}
}
