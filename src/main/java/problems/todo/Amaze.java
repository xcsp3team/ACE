/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;

// TODO to be finished
public class Amaze implements ProblemAPI {
	int w, h, n;
	int[] x1, y1, x2, y2;

	@Override
	public void model() {
		Var[][] b = array("b", size(w + 2, h + 2), dom(range(-1, n)),
				"b[i][j] is -1 if inoccupied, and the number of a point otherwise. Note the presence of a border.");

		block(() -> {
			instantiation(b[0], -1);
			instantiation(b[w + 1], -1);
			instantiation(columnOf(b, 0), -1);
			instantiation(columnOf(b, h + 1), -1);
		}).note("Cells at the border are inoccupied (-1)");

		block(() -> {
			forall(range(n), i -> equal(b[x1[i]][y1[i]], i));
			forall(range(n), i -> equal(b[x2[i]][y2[i]], i));
		}).note("End points are put on the board");

		block(() -> {
			forall(range(n), i -> exactly(vars(b[x1[i]][y1[i] + 1], b[x1[i] + 1][y1[i]], b[x1[i]][y1[i] - 1], b[x1[i] - 1][y1[i]]), i, 1));
			forall(range(n), i -> exactly(vars(b[x2[i]][y2[i] + 1], b[x2[i] + 1][y2[i]], b[x2[i]][y2[i] - 1], b[x2[i] - 1][y2[i]]), i, 1));
		}).note("End points with exactly one horizontal and one vertical neighbour");

		// TODO To be tested
		forall(range(1, w + 1).range(1, h + 1), (i, j) -> {
			if (IntStream.range(0, n - 1).noneMatch(k -> x1[k] == i && y1[k] == j || x2[k] == i && y2[k] == j))
				ifThen(different(b[i][j], 0), (CtrAlone) count(vars(b[i][j + 1], b[i + 1][j], b[i][j - 1], b[i - 1][j]), b[i][j], EQ, 2).note("oui"))
						.note("coucou");
		});

	}
}