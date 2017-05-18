package com.rockwellcollins.atc.agree.analysis.extentions;

import java.util.Map;

import jkind.results.Counterexample;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.emf.ecore.EObject;
import org.osate.aadl2.ComponentImplementation;
import org.osate.annexsupport.AnnexHighlighter;
import org.osate.annexsupport.AnnexPlugin;

public class CexExtractorProxy extends ExtensionProxy implements CexExtractor {

    private CexExtractor extractor;

    protected CexExtractorProxy(IConfigurationElement configElem) {
        super(configElem);
        // TODO Auto-generated constructor stub
    }

    @Override
    public void receiveCex(ComponentImplementation compImpl, EObject property, Counterexample cex,
            Map<String, EObject> refMap) {
        CexExtractor extractor = getCexExtractor();

        if (extractor != null) {
            extractor.receiveCex(compImpl, property, cex, refMap);
        }
    }

    @Override
    public String getDisplayText() {
        CexExtractor extractor = getCexExtractor();
        if (extractor != null) {
            return extractor.getDisplayText();
        }
        return null;
    }

    private CexExtractor getCexExtractor() {
        if (extractor != null) {
            return extractor;
        }
        try {
            extractor = (CexExtractor) configElem.createExecutableExtension(ATT_CLASS);
        } catch (Exception e) {
            System.err.println("error instantiating cex extractor in plugin "
                    + configElem.getDeclaringExtension().getContributor().getName());
        }
        return extractor;
    }

}
