/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.ReaderFile.ReaderEssence;
import problems.g3_pattern.Sonet;

public class SonetE extends Sonet implements ReaderEssence {

	void data() {
		int m = nextInt(), n = nextInt(), r = nextInt();
		int[][] connections = nextInt2D();
		range(n).range(n).select(((j, k) -> j < k && connections[j][k] == 1));

		setDataValues(m, n, r, range(n).range(n).select(((j, k) -> j < k && connections[j][k] == 1)));
	}
}
