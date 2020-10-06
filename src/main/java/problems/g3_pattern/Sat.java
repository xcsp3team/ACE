/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

import utility.operations.Base;

public class Sat implements ProblemAPI {
	int n, e;
	int[][] clauses;

	private int[][] linksBetween(int[] clause1, int[] clause2) {
		return IntStream.range(0, clause1.length).mapToObj(i -> IntStream.range(0, clause2.length).filter(j -> Math.abs(clause1[i]) == Math.abs(clause2[j]))
				.mapToObj(j -> tuple(clause1[i] > 0 ? i : -i - 1, clause2[j] > 0 ? j : -j - 1))).flatMap(s -> s).toArray(int[][]::new);
	}

	private boolean getAtomValueAt(int[] clause, int phasedLitPos, int value) {
		int pos = phasedLitPos >= 0 ? phasedLitPos : -phasedLitPos - 1;
		return Base.baseValueFor(value, clause.length, 2)[pos] == (phasedLitPos >= 0 ? 1 : 0); // > 0 = positive atom
	}

	private boolean check(int[] clause1, int[] clause2, int a, int b, int[][] links) {
		return Stream.of(links).noneMatch(link -> getAtomValueAt(clause1, link[0], a) != getAtomValueAt(clause2, link[1], b));
	}

	private Table dualTable(int i, int j) {
		int[][] links = linksBetween(clauses[i], clauses[j]);
		return links.length == 0 ? null
				: table().addFrom(range(1, Utilities.power(2, clauses[i].length)).range(1, Utilities.power(2, clauses[j].length)),
						(v1, v2) -> check(clauses[i], clauses[j], v1, v2, links) ? tuple(v1, v2) : null);
	}

	@Override
	public void model() {
		// todo ajouter modele table (1 seul conflit)
		if (modelVariant("clause") || modelVariant("sum")) {
			Var[] x = array("x", size(n), dom(0, 1), "x[i] is the ith propositional variable");
			forall(range(e), i -> {
				Var[] scp = variablesFrom(clauses[i], j -> x[Math.abs(j) - 1]);
				Boolean[] phases = IntStream.of(clauses[i]).mapToObj(j -> j >= 0).toArray(Boolean[]::new);
				if (modelVariant("clause"))
					clause(scp, phases);
				else
					sum(scp, Stream.of(phases).mapToInt(p -> p ? 1 : -1).toArray(), NE, -Stream.of(phases).filter(p -> !p).count());
			});
		}
		if (modelVariant("dual")) { // dual construction [Bacchus, Extending forward checking, 2000]
			Var[] x = array("x", size(e), i -> dom(range(1, Utilities.power(2, clauses[i].length))));
			forall(range(e).range(e), (i, j) -> {
				if (i < j) {
					Table table = dualTable(i, j);
					if (table != null)
						extension(vars(x[i], x[j]), table);
				}
			});
		}
	}
}
