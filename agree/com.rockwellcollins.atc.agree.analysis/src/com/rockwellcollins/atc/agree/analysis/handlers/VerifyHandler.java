package com.rockwellcollins.atc.agree.analysis.handlers;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.concurrent.atomic.AtomicReference;

import jkind.JKindException;
import jkind.api.JRealizabilityApi;
import jkind.api.KindApi;
import jkind.api.results.AnalysisResult;
import jkind.api.results.CompositeAnalysisResult;
import jkind.api.results.JKindResult;
import jkind.api.results.JRealizabilityResult;
import jkind.lustre.Node;
import jkind.lustre.Program;
import jkind.lustre.VarDecl;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.handlers.IHandlerActivation;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.xtext.util.Pair;
import org.osate.aadl2.AnnexSubclause;
import org.osate.aadl2.ComponentClassifier;
import org.osate.aadl2.ComponentImplementation;
import org.osate.aadl2.ComponentType;
import org.osate.aadl2.DataPort;
import org.osate.aadl2.Element;
import org.osate.aadl2.EventDataPort;
import org.osate.aadl2.FeatureGroup;
import org.osate.aadl2.instance.ComponentInstance;
import org.osate.aadl2.instance.SystemInstance;
import org.osate.aadl2.instantiation.InstantiateModel;
import org.osate.annexsupport.AnnexUtil;
import org.osate.ui.dialogs.Dialog;

import com.rockwellcollins.atc.agree.agree.AgreeContractSubclause;
import com.rockwellcollins.atc.agree.agree.AgreePackage;
import com.rockwellcollins.atc.agree.agree.AgreeSubclause;
import com.rockwellcollins.atc.agree.agree.Arg;
import com.rockwellcollins.atc.agree.agree.AssertStatement;
import com.rockwellcollins.atc.agree.agree.AssumeStatement;
import com.rockwellcollins.atc.agree.agree.GuaranteeStatement;
import com.rockwellcollins.atc.agree.agree.LemmaStatement;
import com.rockwellcollins.atc.agree.agree.PropertyStatement;
import com.rockwellcollins.atc.agree.analysis.Activator;
import com.rockwellcollins.atc.agree.analysis.AgreeUtils;
import com.rockwellcollins.atc.agree.analysis.AgreeException;
import com.rockwellcollins.atc.agree.analysis.AgreeLayout;
import com.rockwellcollins.atc.agree.analysis.LustreAstBuilder;
import com.rockwellcollins.atc.agree.analysis.LustreContractAstBuilder;
import com.rockwellcollins.atc.agree.analysis.AgreeLayout.SigType;
import com.rockwellcollins.atc.agree.analysis.AgreeLogger;
import com.rockwellcollins.atc.agree.analysis.AgreeRenaming;
import com.rockwellcollins.atc.agree.analysis.ConsistencyResult;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeASTBuilder;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeNode;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeProgram;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeStatement;
import com.rockwellcollins.atc.agree.analysis.ast.AgreeVar;
import com.rockwellcollins.atc.agree.analysis.preferences.PreferenceConstants;
import com.rockwellcollins.atc.agree.analysis.preferences.PreferencesUtil;
import com.rockwellcollins.atc.agree.analysis.views.AgreeResultsLinker;
import com.rockwellcollins.atc.agree.analysis.views.AgreeResultsView;

public abstract class VerifyHandler extends AadlHandler {
    protected AgreeResultsLinker linker = new AgreeResultsLinker();
    protected Queue<AnalysisResult> queue = new ArrayDeque<>();
    protected AtomicReference<IProgressMonitor> monitorRef = new AtomicReference<>();

    private static final String RERUN_ID = "com.rockwellcollins.atc.agree.analysis.commands.rerunAgree";
    private IHandlerActivation rerunActivation;
    private IHandlerActivation terminateActivation;
    private IHandlerActivation terminateAllActivation;
    protected IHandlerService handlerService;

    private enum AnalysisType {
        AssumeGuarantee, Consistency, Realizability
    };

    protected abstract boolean isRecursive();

    protected abstract boolean isMonolithic();

    protected abstract boolean isRealizability();

    @Override
    protected IStatus runJob(Element root, IProgressMonitor monitor) {
        disableRerunHandler();
        handlerService = (IHandlerService) getWindow().getService(IHandlerService.class);

        if (!(root instanceof ComponentImplementation)) {
            return new Status(IStatus.ERROR, Activator.PLUGIN_ID,
                    "Must select an AADL Component Implementation");
        }

        try {
            ComponentImplementation ci = (ComponentImplementation) root;

            SystemInstance si = null;
            try {
                si = InstantiateModel.buildInstanceModelFile(ci);
            } catch (Exception e) {
                Dialog.showError("Model Instantiate",
                        "Error while re-instantiating the model: " + e.getMessage());
                return Status.CANCEL_STATUS;
            }

            AnalysisResult result;
            CompositeAnalysisResult wrapper = new CompositeAnalysisResult("");

            // SystemType sysType = si.getSystemImplementation().getType();
            ComponentType sysType = AgreeUtils.getInstanceType(si);
            EList<AnnexSubclause> annexSubClauses = AnnexUtil.getAllAnnexSubclauses(sysType,
                    AgreePackage.eINSTANCE.getAgreeContractSubclause());

            if (annexSubClauses.size() == 0) {
                throw new AgreeException(
                        "There is not an AGREE annex in the '" + sysType.getName() + "' system type.");
            }

            if (isRecursive()) {
                if(AgreeUtils.usingKind2()){
                    throw new AgreeException("Kind2 only supports monolithic verification");
                }
                result = buildAnalysisResult(ci.getName(), si);
                wrapper.addChild(result);
                result = wrapper;
            } else if (isRealizability()) {
                AgreeProgram agreeProgram = new AgreeASTBuilder().getAgreeProgram(si);
                Program program = LustreAstBuilder.getRealizabilityLustreProgram(agreeProgram);
                wrapper.addChild(
                        createVerification("Realizability Check", si, program, agreeProgram, AnalysisType.Realizability));
                result = wrapper;
            } else {
                wrapVerificationResult(si, wrapper);
                result = wrapper;
            }
            showView(result, linker);
            return doAnalysis(root, monitor);
        } catch (Throwable e) {
            String messages = getNestedMessages(e);
            return new Status(IStatus.ERROR, Activator.PLUGIN_ID, 0, messages, e);
        }
    }

    private void wrapVerificationResult(ComponentInstance si, CompositeAnalysisResult wrapper) {
        AgreeProgram agreeProgram = new AgreeASTBuilder().getAgreeProgram(si);

        // generate different lustre depending on which model checker we are
        // using
      
        Program program;
        if (AgreeUtils.usingKind2()) {
            if(!isMonolithic()){
                throw new AgreeException("Kind2 now only supports monolithic verification");
            }
            program = LustreContractAstBuilder.getContractLustreProgram(agreeProgram);
        } else {
            program = LustreAstBuilder.getAssumeGuaranteeLustreProgram(agreeProgram, isMonolithic());
        }
        List<Pair<String, Program>> consistencies =
                LustreAstBuilder.getConsistencyChecks(agreeProgram, isMonolithic());

        wrapper.addChild(
                createVerification("Contract Guarantees", si, program, agreeProgram, AnalysisType.AssumeGuarantee));
        for (Pair<String, Program> consistencyAnalysis : consistencies) {
            wrapper.addChild(createVerification(consistencyAnalysis.getFirst(), si,
                    consistencyAnalysis.getSecond(), agreeProgram, AnalysisType.Consistency));
        }
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

    private AnalysisResult buildAnalysisResult(String name, ComponentInstance ci) {
        CompositeAnalysisResult result = new CompositeAnalysisResult("Verification for " + name);

        if (containsAGREEAnnex(ci)) {
            wrapVerificationResult(ci, result);
            ComponentImplementation compImpl = AgreeUtils.getInstanceImplementation(ci);
            for (ComponentInstance subInst : ci.getComponentInstances()) {
                if (AgreeUtils.getInstanceImplementation(subInst) != null) {
                    AnalysisResult buildAnalysisResult = buildAnalysisResult(subInst.getName(), subInst);
                    if (buildAnalysisResult != null) {
                        result.addChild(buildAnalysisResult);
                    }
                }
            }

            if (result.getChildren().size() != 0) {
                linker.setComponent(result, compImpl);
                return result;
            }
        }
        return null;
    }

    private boolean containsAGREEAnnex(ComponentInstance ci) {
        ComponentClassifier compClass = ci.getComponentClassifier();
        if (compClass instanceof ComponentImplementation) {
            compClass = ((ComponentImplementation) compClass).getType();
        }
        for (AnnexSubclause annex : AnnexUtil.getAllAnnexSubclauses(compClass,
                AgreePackage.eINSTANCE.getAgreeContractSubclause())) {
            if (annex instanceof AgreeContractSubclause) {
                return true;
            }
        }
        return false;
    }

    private AnalysisResult createVerification(String resultName, ComponentInstance compInst, Program lustreProgram, AgreeProgram agreeProgram,
            AnalysisType analysisType) {

        Map<String, EObject> refMap = new HashMap<>();
        AgreeRenaming renaming = new AgreeRenaming(refMap);
        AgreeLayout layout = new AgreeLayout();
        Node mainNode = null;
        for (Node node : lustreProgram.nodes) {
            if (node.id.equals(lustreProgram.main)) {
                mainNode = node;
                break;
            }
        }
        if (mainNode == null) {
            throw new AgreeException("Could not find main lustre node after translation");
        }

        List<String> properties = new ArrayList<>();
        addRenamings(refMap, renaming, properties, layout, mainNode, agreeProgram);

        JKindResult result;
        switch (analysisType) {
        case Consistency:
            result = new ConsistencyResult(resultName, mainNode.properties, Collections.singletonList(true),
                    renaming);
            break;
        case Realizability:
            result = new JRealizabilityResult(resultName, renaming);
            break;
        case AssumeGuarantee:
            result = new JKindResult(resultName, properties, renaming);
            break;
        default:
            throw new AgreeException("Unhandled Analysis Type");
        }
        queue.add(result);

        ComponentImplementation compImpl = AgreeUtils.getInstanceImplementation(compInst);
        linker.setProgram(result, lustreProgram);
        linker.setComponent(result, compImpl);
        linker.setContract(result, getContract(compImpl));
        linker.setLayout(result, layout);
        linker.setReferenceMap(result, refMap);
        linker.setLog(result, AgreeLogger.getLog());

        // System.out.println(program);
        return result;

    }

    private void addRenamings(Map<String, EObject> refMap, AgreeRenaming renaming, List<String> properties, AgreeLayout layout,
            Node mainNode, AgreeProgram agreeProgram) {
        for (VarDecl var : mainNode.inputs) {
            if (var instanceof AgreeVar) {
                addReference(refMap, renaming, layout, var);
            }
        }
        
        for (VarDecl var : mainNode.locals) {
            if (var instanceof AgreeVar) {
                addReference(refMap, renaming, layout, var);
            }
        }
        
        for (VarDecl var : mainNode.outputs) {
            if (var instanceof AgreeVar) {
                addReference(refMap, renaming, layout, var);
            }
        }
        
        //there is a special case in the AgreeRenaming which handles this translation
        if(AgreeUtils.usingKind2()){
            addKind2Properties(agreeProgram.topNode, properties, renaming, "_TOP", "");
        }else{
            properties.addAll(mainNode.properties);
        }
        
    }
    
    void addKind2Properties(AgreeNode agreeNode, List<String> properties, AgreeRenaming renaming, String prefix, String userPropPrefix){
        int i = 0;
        
        String propPrefix = (userPropPrefix.equals("")) ? "" : userPropPrefix + ": ";
        for(AgreeStatement statement : agreeNode.lemmas){
            renaming.addExplicitRename(prefix+"["+(++i)+"]", propPrefix + statement.string);
            properties.add(prefix.replaceAll("\\.", AgreeASTBuilder.dotChar)+"["+i+"]");
        }
        for(AgreeStatement statement : agreeNode.guarantees){
            renaming.addExplicitRename(prefix+"["+(++i)+"]", propPrefix + statement.string);
            properties.add(prefix.replaceAll("\\.", AgreeASTBuilder.dotChar)+"["+i+"]");
        }
        
        userPropPrefix = userPropPrefix.equals("") ? "" : userPropPrefix + ".";
        for(AgreeNode subNode : agreeNode.subNodes){
            addKind2Properties(subNode, properties, renaming, prefix+"."+subNode.id, userPropPrefix + subNode.id);
        }
    }

    protected void addReference(Map<String, EObject> refMap, AgreeRenaming renaming, AgreeLayout layout,
            VarDecl var) {
        String refStr = getReferenceStr((AgreeVar) var);
        // TODO verify which reference should be put here
        refMap.put(refStr, ((AgreeVar) var).reference);
        refMap.put(var.id, ((AgreeVar) var).reference);
        // TODO we could clean up the agree renaming as well
        renaming.addExplicitRename(var.id, refStr);
        String category = getCategory((AgreeVar) var);
        if (category != null && !layout.getCategories().contains(category)) {
            layout.addCategory(category);
        }
        layout.addElement(category, refStr, SigType.INPUT);
    }

    private String getCategory(AgreeVar var) {
        if (var.compInst == null || var.reference == null) {
            return null;
        }
        return LustreAstBuilder.getRelativeLocation(var.compInst.getInstanceObjectPath());
    }

    private String getReferenceStr(AgreeVar var) {

        String prefix = getCategory(var);
        if (prefix == null) {
            return null;
        }
        if (var.id.endsWith(AgreeASTBuilder.clockIDSuffix)) {
            return null;
        }

        String seperator = (prefix == "" ? "" : ".");
        EObject reference = var.reference;
        if (reference instanceof GuaranteeStatement) {
            return ((GuaranteeStatement) reference).getStr();
        } else if (reference instanceof AssumeStatement) {
            return prefix + " assume: " + ((AssumeStatement) reference).getStr();
        } else if (reference instanceof LemmaStatement) {
            return prefix + " lemma: " + ((LemmaStatement) reference).getStr();
        } else if (reference instanceof AssertStatement) {
            throw new AgreeException("We really didn't expect to see an assert statement here");
        } else if (reference instanceof Arg) {
            return prefix + seperator + ((Arg) reference).getName();
        } else if (reference instanceof DataPort) {
            return prefix + seperator + ((DataPort) reference).getName();
        } else if (reference instanceof EventDataPort) {
            return prefix + seperator + ((EventDataPort) reference).getName();
        } else if (reference instanceof FeatureGroup) {
            return prefix + seperator + ((FeatureGroup) reference).getName();
        } else if (reference instanceof PropertyStatement) {
            return prefix + seperator + ((PropertyStatement) reference).getName();
        } else if (reference instanceof ComponentType || reference instanceof ComponentImplementation) {
            return "Result";
        }
        throw new AgreeException("Unhandled reference type: '" + reference.getClass().getName() + "'");
    }

    protected AgreeSubclause getContract(ComponentImplementation ci) {
        ComponentType ct = ci.getOwnedRealization().getImplemented();
        for (AnnexSubclause annex : ct.getOwnedAnnexSubclauses()) {
            if (annex instanceof AgreeSubclause) {
                return (AgreeSubclause) annex;
            }
        }
        return null;
    }

    protected void showView(final AnalysisResult result, final AgreeResultsLinker linker) {
        getWindow().getShell().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
                try {
                    AgreeResultsView page =
                            (AgreeResultsView) getWindow().getActivePage().showView(AgreeResultsView.ID);
                    page.setInput(result, linker);
                } catch (PartInitException e) {
                    e.printStackTrace();
                }
            }
        });
    }

    protected void clearView() {
        getWindow().getShell().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
                try {
                    AgreeResultsView page =
                            (AgreeResultsView) getWindow().getActivePage().showView(AgreeResultsView.ID);
                    page.setInput(new CompositeAnalysisResult("empty"), null);
                } catch (PartInitException e) {
                    e.printStackTrace();
                }
            }
        });
    }

    private IStatus doAnalysis(final Element root, final IProgressMonitor globalMonitor) {

        Thread analysisThread = new Thread() {
            public void run() {
                activateTerminateHandlers(globalMonitor);
                KindApi api = PreferencesUtil.getKindApi();
                KindApi consistApi = PreferencesUtil.getConsistencyApi();
                JRealizabilityApi realApi = PreferencesUtil.getJRealizabilityApi();

                while (!queue.isEmpty() && !globalMonitor.isCanceled()) {
                    JKindResult result = (JKindResult) queue.peek();
                    NullProgressMonitor subMonitor = new NullProgressMonitor();
                    monitorRef.set(subMonitor);

                    Program program = linker.getProgram(result);
                    try {
                        if (result instanceof ConsistencyResult) {
                            consistApi.execute(program, result, subMonitor);
                        } else if (result instanceof JRealizabilityResult) {
                            realApi.execute(program, (JRealizabilityResult) result, subMonitor);
                        } else {
                            api.execute(program, result, subMonitor);
                        }
                    } catch (JKindException e) {
                        System.out.println("******** JKindException Text ********");
                        e.printStackTrace(System.out);
                        System.out.println("******** JKind Output ********");
                        System.out.println(result.getText());
                        System.out.println("******** Agree Lustre ********");
                        System.out.println(program);
                        break;
                    }
                    queue.remove();
                }

                while (!queue.isEmpty()) {
                    ((JKindResult) queue.remove()).cancel();
                }

                deactivateTerminateHandlers();
                enableRerunHandler(root);

            }
        };
        analysisThread.start();
        return Status.OK_STATUS;
    }

    protected void activateTerminateHandlers(final IProgressMonitor globalMonitor) {
        getWindow().getShell().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
                terminateActivation =
                        handlerService.activateHandler(TERMINATE_ID, new TerminateHandler(monitorRef));
                terminateAllActivation = handlerService.activateHandler(TERMINATE_ALL_ID,
                        new TerminateHandler(monitorRef, globalMonitor));
            }
        });
    }

    protected void deactivateTerminateHandlers() {
        getWindow().getShell().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
                handlerService.deactivateHandler(terminateActivation);
                handlerService.deactivateHandler(terminateAllActivation);
            }
        });
    }

    protected void enableRerunHandler(final Element root) {
        getWindow().getShell().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
                IHandlerService handlerService = getHandlerService();
                rerunActivation =
                        handlerService.activateHandler(RERUN_ID, new RerunHandler(root, VerifyHandler.this));
            }
        });
    }

    protected void disableRerunHandler() {
        if (rerunActivation != null) {
            getWindow().getShell().getDisplay().syncExec(new Runnable() {
                @Override
                public void run() {
                    IHandlerService handlerService = getHandlerService();
                    handlerService.deactivateHandler(rerunActivation);
                    rerunActivation = null;
                }
            });
        }
    }

    private IHandlerService getHandlerService() {
        return (IHandlerService) getWindow().getService(IHandlerService.class);
    }
}