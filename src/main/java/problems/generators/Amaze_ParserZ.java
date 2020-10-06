/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import problems.ReaderFile.ReaderDzn;
import problems.todo.Amaze;

public class Amaze_ParserZ extends Amaze implements ReaderDzn {

	void data() {
		int w = nextInt(), h = nextInt(), n = nextInt();
		int[] x1 = nextInt1D(), y1 = nextInt1D(), x2 = nextInt1D(), y2 = nextInt1D();
		setDataValues(w, h, n, x1, y1, x2, y2);
	}
}
