package com.rockwellcollins.atc.agree.analysis.redlog;

import jkind.api.xml.JKindXmlFileInputStream;
import java.io.File;

// this class is identical to JKindXmlFileInputStream, new class just provide a new name 
public class RedlogXmlFileInputStream extends JKindXmlFileInputStream {

	public RedlogXmlFileInputStream(File xmlFile) {
		super(xmlFile);
	}
}
