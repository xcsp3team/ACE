/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g5_special;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// See Christopher Jefferson, Peter Nightingale: Extending Simple Tabular Reduction with Short Supports. IJCAI 2013
public class DistinctVectors implements ProblemAPI {
	int p, a, d;

	@Override
	public void model() {
		Var[][] x = array("x", size(p, a), dom(range(d)));

		allDifferentList(x);
	}
}
