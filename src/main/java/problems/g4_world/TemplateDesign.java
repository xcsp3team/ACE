/**
1 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

// m1s = m1 sans symBreaking
public class TemplateDesign implements ProblemAPI {

	// int nTemplates;
	int nSlots;
	int[] demands;

	private int lb(int v) {
		return (int) Math.ceil(demands[v] * 0.95);
	}

	private int ub(int v) {
		return (int) Math.floor(demands[v] * 1.1);
	}

	@Override
	public void model() {
		int maxDemand = maxOf(demands);
		int nVariations = demands.length, nTemplates = nVariations;

		// int lb = (int) Math.ceil(IntStream.of(demands).sum() / (double) nSlots), ub = 2 * lb;

		Var[][] d = array("d", size(nTemplates, nVariations), dom(range(nSlots + 1)),
				"d[i][j] is the number of occurrences of the jth variation on the ith template");
		Var[] p = array("p", size(nTemplates), dom(range(maxDemand + 1)), "p[i] is the number of printings of the ith template");
		// Var[] u = array("u", size(nTemplates), dom(0, 1), "u[i] is 1 iff the ith template is used");

		forall(range(nTemplates), t -> sum(d[t], EQ, nSlots)).note("all slots of all templates are used");
		// forall(range(nTemplates), t -> equivalence(eq(u[t], 1), gt(p[t], 0))).note("if a template is used, it is printed at least once");

		if (modelVariant(""))
			forall(range(nVariations), v -> sum(p, weightedBy(columnOf(d, v)), IN, range(lb(v), ub(v) + 1)))
					.note("respecting printing bounds for each variation");

		if (modelVariant("aux")) {
			Var[][] pv = array("pv", size(nTemplates, nVariations), (t, v) -> dom(range(ub(v) + 1)),
					"pv[i][j] is the number of printings of the jth variation by using the ith template");

			forall(range(nTemplates).range(nVariations), (t, v) -> equal(mul(p[t], d[t][v]), pv[t][v])).note("linking variables of arrays p and pv");

			forall(range(nVariations), v -> sum(columnOf(pv, v), IN, range(lb(v), ub(v) + 1))).note("respecting printing bounds for each variation v");
		}

		block(() -> {
			forall(range(nTemplates), t -> equivalence(eq(p[t], 0), eq(d[t][0], nSlots)));
			decreasing(p);
		}).tag(SYMMETRY_BREAKING);

		minimize(SUM, treesFrom(range(nTemplates), i -> gt(p[i], 0))).note("minimizing the number of used templates"); // sum(u)
	}
}
