/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.MultiKnapsack;

/*
 * The format of these data files is: #Variables (n), #Constraints (m), Optimal value (0 if unavailable). Profit P(j) for each n, n x m matrix of constraints,
 * Capacity b(i) for each m. See http://www.cs.nott.ac.uk/~jqd/mkp/index.html
 */
public class MultiKnapsack_Parser extends MultiKnapsack implements ReaderTxt {

	void data() {
		int nVars = nextInt();
		int nCtrs = nextInt();
		nextInt(); // optimum
		int[] objCoeffs = range(nVars).map(i -> nextInt());
		int[][] ctrCoeffs = range(nCtrs).range(nVars).map((i, j) -> nextInt());
		int[] ctrLimits = range(nCtrs).map(i -> nextInt());
		Object ctrs = range(nCtrs).mapToObj(i -> buildInternClassObject("KCtr", ctrCoeffs[i], ctrLimits[i]));
		setDataValues(objCoeffs, ctrs);
	}
}
