package com.rockwellcollins.atc.agree.analysis.views;

import java.io.File;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.List;
import java.util.Map;

import jkind.api.results.AnalysisResult;
import jkind.api.results.JRealizabilityResult;
import jkind.api.results.PropertyResult;
import jkind.api.ui.results.AnalysisResultTree;
import jkind.interval.NumericInterval;
import jkind.lustre.Program;
import jkind.lustre.values.Value;
import jkind.results.Counterexample;
import jkind.results.InvalidProperty;
import jkind.results.Property;
import jkind.results.Signal;
import jkind.results.UnknownProperty;
import jkind.results.layout.Layout;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.util.EcoreUtil;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.IConsoleView;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.xtext.ui.editor.GlobalURIEditorOpener;
import org.osate.aadl2.ComponentImplementation;
import org.osate.ui.dialogs.Dialog;

import com.rockwellcollins.atc.agree.agree.AgreeSubclause;
import com.rockwellcollins.atc.agree.agree.AssumeStatement;
import com.rockwellcollins.atc.agree.agree.FnCallExpr;
import com.rockwellcollins.atc.agree.agree.GuaranteeStatement;
import com.rockwellcollins.atc.agree.agree.LemmaStatement;
import com.rockwellcollins.atc.agree.analysis.Util;
import com.rockwellcollins.atc.agree.analysis.extentions.CexExtractor;
import com.rockwellcollins.atc.agree.analysis.extentions.CexExtractorRegistry;
import com.rockwellcollins.atc.agree.analysis.extentions.ExtensionRegistry;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogProgram;
import com.rockwellcollins.atc.agree.analysis.redlog.RedlogResult;

public class AgreeMenuListener implements IMenuListener {
    private static final GlobalURIEditorOpener globalURIEditorOpener = Util.getGlobalURIEditorOpener();
    private final IWorkbenchWindow window;
    private final AnalysisResultTree tree;
    private AgreeResultsLinker linker;

    public AgreeMenuListener(IWorkbenchWindow window, AnalysisResultTree tree) {
        this.window = window;
        this.tree = tree;
    }

    public void setLinker(AgreeResultsLinker linker) {
        this.linker = linker;
    }

    @Override
    public void menuAboutToShow(IMenuManager manager) {
        IStructuredSelection selection = (IStructuredSelection) tree.getViewer().getSelection();
        if (!selection.isEmpty()) {
            AnalysisResult result = (AnalysisResult) selection.getFirstElement();
            addLinkedMenus(manager, result);
        }
    }

    private void addLinkedMenus(IMenuManager manager, AnalysisResult result) {
        addOpenComponentMenu(manager, result);
        addOpenContractMenu(manager, result);
        addViewLogMenu(manager, result);
        addViewCounterexampleMenu(manager, result);
        if ((result instanceof RedlogResult) || (result.getParent() instanceof RedlogResult)) {
        	addViewRedlogStrongestPropertyMenu(manager, result);
        	addViewRedlogInputFileMenu(manager, result);
        } else {
        	addViewLustreMenu(manager, result);
        }
        addResultsLinkingMenu(manager, result);
    }

    private void addOpenComponentMenu(IMenuManager manager, AnalysisResult result) {
        ComponentImplementation ci = linker.getComponent(result);
        if (ci != null) {
            manager.add(createHyperlinkAction("Open " + ci.getName(), ci));
        }
    }

    private void addOpenContractMenu(IMenuManager manager, AnalysisResult result) {
        AgreeSubclause contract = linker.getContract(result);
        if (contract != null) {
            manager.add(createHyperlinkAction("Open Contract", contract));
        }
    }

    private void addViewLogMenu(IMenuManager manager, AnalysisResult result) {
        String log = linker.getLog(result);
        if (log == null && result instanceof PropertyResult) {
            log = linker.getLog(result.getParent());
        }
        if (log != null && !log.isEmpty()) {
            manager.add(createWriteConsoleAction("View Log", "Log", log));
        }
    }

    private void addViewCounterexampleMenu(IMenuManager manager, AnalysisResult result) {
        final Counterexample cex = getCounterexample(result);
        CexExtractorRegistry cexReg =
                (CexExtractorRegistry) ExtensionRegistry.getRegistry(ExtensionRegistry.CEX_EXTRACTOR_EXT_ID);
        List<CexExtractor> extractors = cexReg.getCexExtractors();

        if (cex != null) {
            final String cexType = getCounterexampleType(result);

            Map<String, EObject> tempRefMap = linker.getReferenceMap(result.getParent());
            if (tempRefMap == null) {
                tempRefMap = linker.getReferenceMap(result);
            }
            Layout tempLayout = linker.getLayout(result.getParent());
            if (tempLayout == null) {
                tempLayout = linker.getLayout(result);
            }

            final Layout layout = tempLayout;
            final Map<String, EObject> refMap = tempRefMap;

            MenuManager sub = new MenuManager("View " + cexType + "Counterexample in");
            manager.add(sub);

            sub.add(new Action("Console") {
                @Override
                public void run() {
                    viewCexConsole(cex, layout, refMap);
                }
            });

            sub.add(new Action("Eclipse") {
                @Override
                public void run() {
                    viewCexEclipse(cex, layout, refMap);
                }
            });

            sub.add(new Action("Spreadsheet") {
                @Override
                public void run() {
                    viewCexSpreadsheet(cex, layout);
                }
            });

            // send counterexamples to external plugins
            EObject property = refMap.get(result.getName());
            ComponentImplementation compImpl = linker.getComponent(result.getParent());

            for (CexExtractor ex : extractors) {
                sub.add(new Action(ex.getDisplayText()) {
                    @Override
                    public void run() {
                        ex.receiveCex(compImpl, property, cex, refMap);
                    }
                });
            }
        }
    }

    private void addViewLustreMenu(IMenuManager manager, AnalysisResult result) {
        Program program = linker.getProgram(result);
        if (program == null && result instanceof PropertyResult) {
            program = linker.getProgram(result.getParent());
        }
        if (program != null) {
            manager.add(createWriteConsoleAction("View Lustre", "Lustre", program));
        }
    }
    
    private void addViewRedlogStrongestPropertyMenu(IMenuManager manager, AnalysisResult result) {
    	RedlogProgram program = null;
    	String systemStrongestProperty = "";
    	if (result instanceof RedlogResult) {
    		program = linker.getRedlogProgram(result);
    		systemStrongestProperty = ((RedlogResult) result).getSystemStrongestProperty();
    	} else if (result.getParent() instanceof RedlogResult) {
    		program = linker.getRedlogProgram(result.getParent());
    		systemStrongestProperty = ((RedlogResult) result.getParent()).getSystemStrongestProperty();
    	}
    	
        if (program!= null && systemStrongestProperty != null) {
    		String commentsHeader = "";
        	if (program.hasIntVar()) {
        		String[] comments = {"///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////", 
        				"// The infix operator precedence is from strongest to weakest: and, or, impl, repl, equiv.                                           //",
        				"// In integer domain, the operators \"cong\" and \"ncong\" represent congruences with nonparametric modulus given by the third argument. //",
        				"// The example below defines the set of even integers.                                                                               //",
        				"//        f := cong(x,0,2);                                                                                                          //",
        				"//          => x ~2~ 0                                                                                                               //",               
        				"///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////",
        				""};
        		for (int i=0; i<comments.length; i++) {
        			commentsHeader += comments[i] +"\r\n";
        		}
        	} else {
        		String[] comments = {"/////////////////////////////////////////////////////////////////////////////////////////////", 
        				"// The infix operator precedence is from strongest to weakest: and, or, impl, repl, equiv. //",             
        				"/////////////////////////////////////////////////////////////////////////////////////////////",
        				""};
        		for (int i=0; i<comments.length; i++) {
        			commentsHeader += comments[i] +"\r\n";
        		}
        	}
        	
            manager.add(createWriteConsoleAction("View System Strongest Property", "System Strongest Property", commentsHeader + systemStrongestProperty));
            return;
        }
    }
    
    private void addViewRedlogInputFileMenu(IMenuManager manager, AnalysisResult result) {
    	if (result instanceof RedlogResult) {
    		RedlogProgram program = linker.getRedlogProgram(result);
            if (program != null) {
                manager.add(createWriteConsoleAction("View Redlog file", "Redlog", program));
                return;
            }
    	} else if (result.getParent() instanceof RedlogResult) {
    		RedlogProgram program = linker.getRedlogProgram(result.getParent());
            if (program != null) {
                manager.add(createWriteConsoleAction("View Redlog file", "Redlog", program));
                return;
            }
    	}
    }

    private void addResultsLinkingMenu(IMenuManager manager, AnalysisResult result) {
        if (result instanceof PropertyResult) {
            PropertyResult pr = (PropertyResult) result;
            Map<String, EObject> refMap = linker.getReferenceMap(pr.getParent());
            EObject property = refMap.get(pr.getName());
            if (property instanceof GuaranteeStatement) {
                manager.add(createHyperlinkAction("Go To Guarantee", property));
            }
            if (property instanceof LemmaStatement) {
                manager.add(createHyperlinkAction("Go To Lemma", property));
            }
            if (property instanceof AssumeStatement) {
                manager.add(createHyperlinkAction("Go To Assumption", property));
            }
            if (property instanceof FnCallExpr) {
                manager.add(createHyperlinkAction("Go To Node Call", property));
            }
        }
    }

    private static Counterexample getCounterexample(AnalysisResult result) {
        if (result instanceof PropertyResult) {
            Property prop = ((PropertyResult) result).getProperty();
            if (prop instanceof InvalidProperty) {
                return ((InvalidProperty) prop).getCounterexample();
            } else if (prop instanceof UnknownProperty) {
                return ((UnknownProperty) prop).getInductiveCounterexample();
            }
        } else if (result instanceof JRealizabilityResult) {
            PropertyResult propResult = ((JRealizabilityResult) result).getPropertyResult();
            Property prop = propResult.getProperty();
            if (prop instanceof InvalidProperty) {
                return ((InvalidProperty) prop).getCounterexample();
            }

        }

        return null;
    }

    private static String getCounterexampleType(AnalysisResult result) {
        if (result instanceof PropertyResult) {
            Property prop = ((PropertyResult) result).getProperty();
            if (prop instanceof UnknownProperty) {
                return "Inductive ";
            }
        }

        return " ";
    }

    private IAction createHyperlinkAction(String text, final EObject eObject) {
        return new Action(text) {
            @Override
            public void run() {
                globalURIEditorOpener.open(EcoreUtil.getURI(eObject), true);
            }
        };
    }

    private Action createWriteConsoleAction(String actionName, final String consoleName,
            final Object content) {
        return new Action(actionName) {
            @Override
            public void run() {
                final MessageConsole console = findConsole(consoleName);
                showConsole(console);
                console.clearConsole();

                /*
                 * From the Eclipse API: "Clients should avoid writing large
                 * amounts of output to this stream in the UI thread. The
                 * console needs to process the output in the UI thread and if
                 * the client hogs the UI thread writing output to the console,
                 * the console will not be able to process the output."
                 */
                new Thread(new Runnable() {
                    @Override
                    public void run() {
                        console.newMessageStream().println(content.toString());
                    }
                }).start();
            }
        };
    }

    private void viewCexConsole(final Counterexample cex, final Layout layout, Map<String, EObject> refMap) {
        final MessageConsole console = findConsole("Counterexample");
        showConsole(console);
        console.clearConsole();
        console.addPatternMatchListener(new AgreePatternListener(refMap));

        /*
         * From the Eclipse API: "Clients should avoid writing large amounts of
         * output to this stream in the UI thread. The console needs to process
         * the output in the UI thread and if the client hogs the UI thread
         * writing output to the console, the console will not be able to
         * process the output."
         */
        new Thread(new Runnable() {
            @Override
            public void run() {
                try (MessageConsoleStream out = console.newMessageStream()) {
                    for (String category : layout.getCategories()) {
                        if (isEmpty(category, cex, layout)) {
                            continue;
                        }

                        printHLine(out, cex.getLength());
                        out.println("Variables for " + category);
                        printHLine(out, cex.getLength());

                        out.print(String.format("%-60s", "Variable Name"));
                        for (int k = 0; k < cex.getLength(); k++) {
                            out.print(String.format("%-15s", k));
                        }
                        out.println();
                        printHLine(out, cex.getLength());

                        for (Signal<Value> signal : cex.getCategorySignals(layout, category)) {
                            // dont' print out values for properties
                            if (signal.getName().contains(":")) {
                                continue;
                            }
                            out.print(String.format("%-60s", "{" + signal.getName() + "}"));
                            for (int k = 0; k < cex.getLength(); k++) {
                                Value val = signal.getValue(k);
                                if (jkind.util.Util.isArbitrary(val)) {
                                    out.print(String.format("%-15s", "-"));
                                } else if (val instanceof NumericInterval) {
                                    out.print(String.format("%-15s", formatInterval((NumericInterval) val)));
                                } else {
                                    out.print(String.format("%-15s", val.toString()));
                                }
                            }
                            out.println();
                        }
                        out.println();
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }).start();
    }

    private String formatInterval(NumericInterval ni) {
        if (ni.isExact()) {
            return formatDouble(ni.getLow().toDouble());
        }

        String low;
        if (ni.getLow().isFinite()) {
            low = formatDouble(ni.getLow().toDouble());
        } else {
            low = "-inf";
        }

        String high;
        if (ni.getHigh().isFinite()) {
            high = formatDouble(ni.getHigh().toDouble());
        } else {
            high = "inf";
        }

        return "[" + low + ", " + high + "]";
    }

    private static final DecimalFormat format = new DecimalFormat("#.##");

    private String formatDouble(double x) {
        return format.format(x);
    }

    private boolean isEmpty(String category, Counterexample cex, Layout layout) {
        return cex.getCategorySignals(layout, category).isEmpty();
    }

    private void printHLine(MessageConsoleStream out, int nVars) {
        out.print("--------------------------------------------------");
        for (int k = 0; k < nVars; k++) {
            out.print("---------------------");
        }
        out.println();
    }

    private static MessageConsole findConsole(String name) {
        ConsolePlugin plugin = ConsolePlugin.getDefault();
        IConsoleManager conMan = plugin.getConsoleManager();
        IConsole[] existing = conMan.getConsoles();
        for (int i = 0; i < existing.length; i++) {
            if (name.equals(existing[i].getName())) {
                return (MessageConsole) existing[i];
            }
        }
        // no console found, so create a new one
        MessageConsole myConsole = new MessageConsole(name, null);
        conMan.addConsoles(new IConsole[] { myConsole });
        return myConsole;
    }

    private void showConsole(IConsole console) {
        IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
        try {
            IConsoleView view = (IConsoleView) page.showView(IConsoleConstants.ID_CONSOLE_VIEW);
            view.display(console);
            view.setScrollLock(true);
        } catch (PartInitException e) {
        }
    }

    private void viewCexEclipse(Counterexample cex, Layout layout, Map<String, EObject> refMap) {
        try {
            AgreeCounterexampleView cexView =
                    (AgreeCounterexampleView) window.getActivePage().showView(AgreeCounterexampleView.ID);
            cexView.setInput(cex, layout, refMap);
            cexView.setFocus();
        } catch (PartInitException e) {
            e.printStackTrace();
        }
    }

    private void viewCexSpreadsheet(Counterexample cex, Layout layout) {
        try {
            File file = File.createTempFile("cex", ".xls");
            cex.toExcel(file, layout);
            org.eclipse.swt.program.Program.launch(file.toString());
        } catch (IOException e) {
            Dialog.showError("Unable to open spreadsheet", e.getMessage());
            e.printStackTrace();
        }
    }
}
