/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderDzn;
import problems.g4_world.TemplateDesign;

public class TemplateDesignReaderZ extends TemplateDesign implements ReaderDzn {

	void data() {
		int nSlots = nextInt();
		nextInt(); // nTemplates
		int nVariations = nextInt();
		int[] variations = nextInt1D();
		Utilities.control(nVariations == variations.length, "");
		setDataValues(nSlots, variations);
	}
}
