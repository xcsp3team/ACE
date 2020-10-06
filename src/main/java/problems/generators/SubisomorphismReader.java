/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.io.File;

import problems.g3_pattern.Subisomorphism;
import utility.operations.GraphSimpleUndirected;

public class SubisomorphismReader extends Subisomorphism {

	void data() {
		String ptnFileName = imp().askString("Pattern File Name");
		String tgtFileName = imp().askString("Target File Name");
		if (ptnFileName.endsWith("pattern")) {
			imp().parameters.get(0).setValue(ptnFileName.substring(0, ptnFileName.lastIndexOf(File.separator)));
			imp().parameters.get(1).setValue("");
		}
		GraphSimpleUndirected pGraph = GraphSimpleUndirected.loadGraph(ptnFileName);
		GraphSimpleUndirected tGraph = GraphSimpleUndirected.loadGraph(tgtFileName);
		imp().setDataValues(pGraph.nNodes, tGraph.nNodes, pGraph.edges(false), tGraph.edges(false));
	}

}