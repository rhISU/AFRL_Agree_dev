package com.rockwellcollins.atc.agree.analysis.views;

import java.util.HashMap;
import java.util.Map;

import jkind.api.results.AnalysisResult;
import jkind.results.layout.Layout;
import jkind.lustre.Program;

import org.eclipse.emf.ecore.EObject;
import org.osate.aadl2.ComponentImplementation;

import com.rockwellcollins.atc.agree.agree.AgreeSubclause;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogProgram;

public class AgreeResultsLinker {
    private Map<AnalysisResult, Program> programs = new HashMap<>();
    private Map<AnalysisResult, RedlogProgram> redlogPrograms = new HashMap<>();
    private Map<AnalysisResult, ComponentImplementation> components = new HashMap<>();
    private Map<AnalysisResult, AgreeSubclause> contracts = new HashMap<>();
    private Map<AnalysisResult, Layout> layouts = new HashMap<>();
    private Map<AnalysisResult, Map<String, EObject>> referenceMaps = new HashMap<>();
    private Map<AnalysisResult, String> logs = new HashMap<>();
    
    public void setProgram(AnalysisResult result, Program program) {
        programs.put(result, program);
    }

    public Program getProgram(AnalysisResult result) {
        return programs.get(result);
    }
    
    public void setRedlogProgram(AnalysisResult result, RedlogProgram redlogProgram) {
    	redlogPrograms.put(result, redlogProgram);
    }
    
    public RedlogProgram getRedlogProgram(AnalysisResult result) {
        return redlogPrograms.get(result);
    }
    
    public void setComponent(AnalysisResult result, ComponentImplementation ci) {
        components.put(result, ci);
    }

    public ComponentImplementation getComponent(AnalysisResult result) {
        return components.get(result);
    }

    public void setContract(AnalysisResult result, AgreeSubclause contract) {
        contracts.put(result, contract);
    }

    public AgreeSubclause getContract(AnalysisResult result) {
        return contracts.get(result);
    }

    public void setLayout(AnalysisResult result, Layout layout) {
        layouts.put(result, layout);
    }

    public Layout getLayout(AnalysisResult result) {
        return layouts.get(result);
    }

    public void setReferenceMap(AnalysisResult result, Map<String, EObject> refMap) {
        referenceMaps.put(result, refMap);
    }

    public Map<String, EObject> getReferenceMap(AnalysisResult result) {
        return referenceMaps.get(result);
    }

    public void setLog(AnalysisResult result, String log) {
        logs.put(result, log);
    }

    public String getLog(AnalysisResult result) {
        return logs.get(result);
    }
}
