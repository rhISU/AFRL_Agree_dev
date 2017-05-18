/*
 * generated by Xtext
 */
package com.rockwellcollins.atc.agree.ui.labeling;

import com.google.inject.Inject;

/**
 * Provides labels for a EObjects.
 * 
 * see http://www.eclipse.org/Xtext/documentation.html#labelProvider
 */
public class AgreeLabelProvider extends org.eclipse.xtext.ui.label.DefaultEObjectLabelProvider {

    @Inject
    public AgreeLabelProvider(org.eclipse.emf.edit.ui.provider.AdapterFactoryLabelProvider delegate) {
        super(delegate);
    }

    // Labels and icons can be computed like this:

    // String text(Greeting ele) {
    // return "A greeting to " + ele.getName();
    // }
    //
    // String image(Greeting ele) {
    // return "Greeting.gif";
    // }
}