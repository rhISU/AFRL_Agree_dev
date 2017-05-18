package com.rockwellcollins.atc.agree.analysis.handlers;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import jkind.api.results.AnalysisResult;
import jkind.api.results.CompositeAnalysisResult;
import jkind.lustre.VarDecl;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.provider.ItemProviderAdapter.ResultAndAffectedObjectsWrappingCommand;
import org.eclipse.ui.handlers.IHandlerService;
import org.osate.aadl2.AnnexSubclause;
import org.osate.aadl2.ComponentImplementation;
import org.osate.aadl2.ComponentType;
import org.osate.aadl2.Element;
import org.osate.aadl2.impl.DefaultAnnexSubclauseImpl;
import org.osate.aadl2.impl.SystemSubcomponentImpl;
import org.osate.aadl2.instance.ComponentInstance;
import org.osate.aadl2.instance.SystemInstance;
import org.osate.aadl2.instantiation.InstantiateModel;
import org.osate.annexsupport.AnnexUtil;
import org.osate.ui.dialogs.Dialog;

import com.rockwellcollins.atc.agree.agree.AgreePackage;
import com.rockwellcollins.atc.agree.agree.AgreeSubclause;
import com.rockwellcollins.atc.agree.analysis.Activator;
import com.rockwellcollins.atc.agree.analysis.AgreeException;
import com.rockwellcollins.atc.agree.analysis.AgreeLayout;
import com.rockwellcollins.atc.agree.analysis.AgreeLogger;
import com.rockwellcollins.atc.agree.analysis.AgreeRenaming;
import com.rockwellcollins.atc.agree.analysis.AgreeUtils;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeASTBuilder;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeProgram;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeVar;
import com.rockwellcollins.atc.agree.analysis.preferences.PreferencesUtil;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogAstBuilder;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogProgram;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogResult;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogApi;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogException;


public class VerifyComposedContract extends VerifyHandler{
	
	public enum VerificationDirection {COMPOSITION, DIAGNOSIS}
	
    @Override
    protected boolean isRecursive() {
        return true;
    }

    @Override
    protected String getJobName() {
        return "AGREE - Verify Composed Contract";
    }

    @Override
    protected boolean isMonolithic() {
        return false;
    }

    @Override
    protected boolean isRealizability() {
        return false;
    }
    
    @Override
    protected IStatus runJob(Element root, IProgressMonitor monitor) {
        disableRerunHandler();
        handlerService = (IHandlerService) getWindow().getService(IHandlerService.class);

        // for top-level implementation, we perform component-to-system compositional verification,
        // by first deriving the strongest system property then inferring the system property contract
        if (root instanceof ComponentImplementation) {
	        try {
	            ComponentImplementation compImpl = (ComponentImplementation) root;
	            SystemInstance sysInst = null;
	            try {
	            	sysInst = InstantiateModel.buildInstanceModelFile(compImpl);
	            } catch (Exception e) {
	                Dialog.showError("Model Instantiate", "Error while re-instantiating the model: " + e.getMessage());
	                return Status.CANCEL_STATUS;
	            }
	
	            AnalysisResult result;
	            CompositeAnalysisResult wrapper = new CompositeAnalysisResult("");
	
	            // SystemType sysType = si.getSystemImplementation().getType();
	            ComponentType sysType = AgreeUtils.getInstanceType(sysInst);
	            EList<AnnexSubclause> annexSubClauses = AnnexUtil.getAllAnnexSubclauses(sysType,
	                    AgreePackage.eINSTANCE.getAgreeContractSubclause());
	
	            if (annexSubClauses.size() == 0) {
	                throw new AgreeException(
	                        "There is not an AGREE annex in the '" + sysType.getName() + "' system type.");
	            }
	            
	            wrapVerificationResult(sysInst, wrapper);
	            result = wrapper;
	            
	            showView(result, linker);
	            return doAnalysis(root, monitor);
	        } catch (Throwable e) {
	            String messages = getNestedMessages(e);
	            return new Status(IStatus.ERROR, Activator.PLUGIN_ID, 0, messages, e);
	        }
        }
        // for component-level implementation, we perform system-to-component decompositional diagnosis,
        // by first deriving the weakest component property then comparing the component property contract
        else if (root instanceof SystemSubcomponentImpl) {
        	try {
        		SystemSubcomponentImpl ssi = (SystemSubcomponentImpl) root;
        		ComponentImplementation compImpl = ssi.getContainingComponentImpl();
	            SystemInstance sysInst = null;
	            try {
	            	sysInst = InstantiateModel.buildInstanceModelFile(compImpl);
	            } catch (Exception e) {
	                Dialog.showError("Model Instantiate", "Error while re-instantiating the model: " + e.getMessage());
	                return Status.CANCEL_STATUS;
	            }
	
	            AnalysisResult result;
	            CompositeAnalysisResult wrapper = new CompositeAnalysisResult("");
	
	            // SystemType sysType = si.getSystemImplementation().getType();
	            ComponentType sysType = AgreeUtils.getInstanceType(sysInst);
	            EList<AnnexSubclause> annexSubClauses = AnnexUtil.getAllAnnexSubclauses(sysType,
	                    AgreePackage.eINSTANCE.getAgreeContractSubclause());
	
	            if (annexSubClauses.size() == 0) {
	                throw new AgreeException(
	                        "There is not an AGREE annex in the '" + sysType.getName() + "' system type.");
	            }
	            
	            wrapDiagnosisResult(ssi, sysInst, wrapper);
	            result = wrapper;
	            
	            showView(result, linker);
	            return doAnalysis(root, monitor);
	        } catch (Throwable e) {
	            String messages = getNestedMessages(e);
	            return new Status(IStatus.ERROR, Activator.PLUGIN_ID, 0, messages, e);
	        }	
        }
        else {
        	return new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Must select an AADL Component Implementation.");
        }
    }
    
    private void wrapVerificationResult(ComponentInstance compInst, CompositeAnalysisResult wrapper) {
		AgreeProgram agreeProgram = new AgreeASTBuilder().getAgreeProgram(compInst);
		RedlogProgram redlogProgram = RedlogAstBuilder.getContractRedlogProgram(agreeProgram, VerificationDirection.COMPOSITION);
		ComponentImplementation compImpl = AgreeUtils.getInstanceImplementation(compInst);
		// TODO: need to examine the getContract() method.
		wrapper.addChild(createVerification("System Contract", compImpl, redlogProgram, agreeProgram, getContract(compImpl)));
    }
    
    private void wrapDiagnosisResult(SystemSubcomponentImpl ssi, ComponentInstance compInst, CompositeAnalysisResult wrapper) {
		AgreeProgram agreeProgram = new AgreeASTBuilder().getAgreeProgram(compInst);
		RedlogProgram redlogProgram = RedlogAstBuilder.getContractRedlogProgram(agreeProgram, VerificationDirection.DIAGNOSIS);
		AgreeSubclause contract = null;
        ComponentType ct = ssi.getComponentType();
        for (AnnexSubclause annex : ct.getOwnedAnnexSubclauses()) {
            if (annex instanceof DefaultAnnexSubclauseImpl) {
            	contract = (AgreeSubclause)(((DefaultAnnexSubclauseImpl) annex).getParsedAnnexSubclause());
                break;
            }
        }
		wrapper.addChild(createVerification("Component Diagnosis", null, redlogProgram, agreeProgram, contract));
    }
    
    private AnalysisResult createVerification(String resultName, ComponentImplementation compImpl, RedlogProgram redlogProgram, AgreeProgram agreeProgram,  AgreeSubclause contract) {
        Map<String, EObject> refMap = new HashMap<>();
        AgreeRenaming renaming = new AgreeRenaming(refMap);
        AgreeLayout layout = new AgreeLayout();
        List<String> properties = new ArrayList<>();
        addRenamings(refMap, renaming, properties, layout, redlogProgram, agreeProgram);

        RedlogResult result = new RedlogResult(resultName, properties, renaming);
        queue.add(result);

        linker.setRedlogProgram(result, redlogProgram);
        linker.setComponent(result, compImpl);
        linker.setContract(result, contract);
        linker.setLayout(result, layout);
        linker.setReferenceMap(result, refMap);
        linker.setLog(result, AgreeLogger.getLog());

        return result;
    }
    
    
    
    private void addRenamings(Map<String, EObject> refMap, AgreeRenaming renaming, List<String> properties, AgreeLayout layout,
            RedlogProgram redlogProgram, AgreeProgram agreeProgram) {
        for (VarDecl var : redlogProgram.allVariables) {
            if (var instanceof AgreeVar) {
                addReference(refMap, renaming, layout, var);
            }
        }
        
        for (VarDecl var : redlogProgram.sysInputs) {
            if (var instanceof AgreeVar) {
                addReference(refMap, renaming, layout, var);
            }
        }
        
        for (VarDecl var : redlogProgram.sysOutputs) {
            if (var instanceof AgreeVar) {
                addReference(refMap, renaming, layout, var);
            }
        }
        
        // addRenaming for contract var(s)
        for (VarDecl var : redlogProgram.systemContracts.keySet()) {
        	if (var instanceof AgreeVar) {
        		addReference(refMap, renaming, layout, var);
        	}
        }
        
        properties.addAll(redlogProgram.properties);
    }

    private IStatus doAnalysis(final Element root, final IProgressMonitor globalMonitor) {

        Thread analysisThread = new Thread() {
            public void run() {
                activateTerminateHandlers(globalMonitor);
                RedlogApi api = PreferencesUtil.getRedlogApi();
                //KindApi consistApi = PreferencesUtil.getConsistencyApi();
                //JRealizabilityApi realApi = PreferencesUtil.getJRealizabilityApi();

                while (!queue.isEmpty() && !globalMonitor.isCanceled()) {
                    RedlogResult result = (RedlogResult) queue.peek();
                    NullProgressMonitor subMonitor = new NullProgressMonitor();
                    monitorRef.set(subMonitor);

                    RedlogProgram redlogProgram = linker.getRedlogProgram(result);
                    try {
                    	/*
                        if (result instanceof ConsistencyResult) {
                            consistApi.execute(program, result, subMonitor);
                        } else if (result instanceof JRealizabilityResult) {
                            realApi.execute(program, (JRealizabilityResult) result, subMonitor);
                        } else {
                            api.execute(redlogProgram, result, subMonitor);
                        }*/
                    	api.execute(redlogProgram, result, subMonitor);
                    } catch (RedlogException e) {
                        System.out.println("******** RedlogException Text ********");
                        e.printStackTrace(System.out);
                        System.out.println("******** Redlog Output ********");
                        System.out.println(result.getText());
                        System.out.println("******** Agree redlog program ********");
                        System.out.println(redlogProgram);
                        break;
                    }
                    queue.remove();
                }

                while (!queue.isEmpty()) {
                    ((RedlogResult) queue.remove()).cancel();
                }

                deactivateTerminateHandlers();
                enableRerunHandler(root);
            }
        };
        analysisThread.start();
        return Status.OK_STATUS;
    }

    
    protected String getNestedMessages(Throwable e) {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        while (e != null) {
            if (e.getMessage() != null && !e.getMessage().isEmpty()) {
                pw.println(e.getMessage());
            }
            e = e.getCause();
        }
        pw.close();
        return sw.toString();
    }

}
