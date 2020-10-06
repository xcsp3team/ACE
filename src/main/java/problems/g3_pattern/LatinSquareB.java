/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * All rows, columns and diagonals (including broken ones) must contain different values.
 */
public class LatinSquareB implements ProblemAPI {

	int n; // order
	Clue[] clues;

	class Clue {
		int x, y, value;
	}

	@Override
	public void model() {
		Var[][] x = array("x", size(n, n), dom(range(n)), "x[i][j] is the value at row i and col j of the Latin Square");

		allDifferentMatrix(x);
		instantiation(Stream.of(clues).map(c -> x[c.x][c.y]), Stream.of(clues).mapToInt(c -> c.value)).tag(CLUES);

		block(() -> {
			forall(range(n), i -> allDifferent(diagonalDown(x, i)));
			forall(range(n), i -> allDifferent(diagonalUp(x, i)));
		}).tag(DIAGONALS);
	}
}