/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Stream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrAlone;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;

import constraints.Constraint;

public class Rlfap implements ProblemAPI {

	int[][] domains; // Map<Integer, int[]> domains;
	RlfapVar[] vars;
	RlfapCtr[] ctrs;
	int[] interferenceCosts;
	int[] mobilityCosts;

	class RlfapVar {
		// int number;
		int domain;
		Integer value;
		Integer mobility;
	}

	class RlfapCtr {
		int x;
		int y;
		String operator;
		int limit;
		int weight;
	}

	private CtrEntity hardCtr(int i, Var[] f) {
		Var x = f[ctrs[i].x], y = f[ctrs[i].y];
		return ctrs[i].operator.equals("=") ? equal(dist(x, y), ctrs[i].limit) : greaterThan(dist(x, y), ctrs[i].limit);
	}

	@Override
	public void model() {
		int n = vars.length, e = ctrs.length;

		Var[] f = array("f", size(n), i -> dom(domains[vars[i].domain]), "f[i] is the frequency of the ith radio link");
		// Map<Integer, Var> mapVars = IntStream.range(0, n).boxed().collect(Collectors.toMap(i -> vars[i].number, i -> f[i]));

		if (modelVariant("feas")) {
			// currently, unary constraints not managed
			int sumOfSoftConstraintWeights = 1;
			List<Constraint> hardConstraints = new LinkedList<>();
			for (RlfapCtr c : ctrs) {
				Var x = f[c.x], y = f[c.y];
				Constraint constraint = (Constraint) ((CtrAlone) (c.operator.equals("=") ? equal(dist(x, y), c.limit) : greaterThan(dist(x, y), c.limit))).ctr;
				constraint.cost = interferenceCosts[c.weight];
				sumOfSoftConstraintWeights += interferenceCosts[c.weight];
				if (c.weight == 0)
					hardConstraints.add(constraint);
			}
			for (Constraint c : hardConstraints)
				c.cost = sumOfSoftConstraintWeights;
		}
		if (modelVariant("span") || modelVariant("card")) { // all constraints are considered to be hard for these problems
			int[] indexes = select(range(n), i -> vars[i].value != null);
			Var[] fixedVars = variablesFrom(indexes, index -> f[index]);
			int[] fixedVals = valuesFrom(indexes, index -> vars[index].value);
			instantiation(fixedVars, fixedVals).note("managing pre-assigned frequencies");

			forall(range(e), i -> hardCtr(i, f)).note("hard constraints on radio-links");

			if (modelVariant("span"))
				minimize(MAXIMUM, f).note("minimizing the largest frequency");
			if (modelVariant("card"))
				minimize(NVALUES, f).note("minimizing the number of used frequencies");
		}
		if (modelVariant("max")) {
			// int[] t = IntStream.range(0, vars.length).filter(i -> vars[i].value != null && vars[i].mobility == 0).toArray();
			// RlfapVar[] t = Stream.of(vars).filter(x -> x.value != null && x.mobility == 0).toArray(RlfapVar[]::new);
			// instantiation(IntStream.of(t).mapToObj(i -> f[t[i]]), IntStream.of(t).map(i -> vars[i].value));

			int[] indexes = select(range(n), i -> vars[i].value != null && vars[i].mobility == 0);
			Var[] fixedVars = variablesFrom(indexes, index -> f[index]);
			int[] fixedVals = valuesFrom(indexes, index -> vars[index].value);
			instantiation(fixedVars, fixedVals);

			forall(range(e), i -> {
				if (ctrs[i].weight == 0)
					hardCtr(i, f);
			});
			Var[][] zbs = new Var[5][];
			for (int i = 1; i <= 4; i++) {
				int cost = mobilityCosts[i];
				int nb = (int) Stream.of(vars).filter(x -> x.value != null && mobilityCosts[x.mobility] == cost).count();
				if (nb > 0) {
					zbs[i] = array("zb" + i, size(nb), j -> dom(0, cost));
					int cnt = 0;
					for (int j = 0; j < vars.length; j++) {
						RlfapVar x = vars[j];
						if (x.value != null && mobilityCosts[x.mobility] == cost) {
							Var w = f[j], z = zbs[i][cnt++];
							equal(ifThenElse(eq(w, x.value), 0, mobilityCosts[x.mobility]), z);
						}
					}
				}
			}
			Var[][] zas = new Var[5][];
			for (int i = 1; i <= 4; i++) {
				int cost = interferenceCosts[i];
				int nb = (int) Stream.of(ctrs).filter(c -> interferenceCosts[c.weight] == cost).count();
				if (nb > 0) {
					zas[i] = array("za" + i, size(nb), j -> dom(0, cost));
					int cnt = 0;
					for (RlfapCtr c : ctrs)
						if (interferenceCosts[c.weight] == cost) {
							Var x = f[c.x], y = f[c.y], z = zas[i][cnt++];
							if (c.operator.equals("="))
								equal(ifThenElse(eq(dist(x, y), c.limit), 0, interferenceCosts[c.weight]), z);
							else
								equal(ifThenElse(gt(dist(x, y), c.limit), 0, interferenceCosts[c.weight]), z);
						}
				}
			}
			minimize(SUM, vars(zbs, zas));
		}
	}
}

// for (RlfapCtr c : ctrs) {
// Var x = mapVars.get(c.x), y = mapVars.get(c.y);
// if (c.equality)
// equal(dist(x, y), c.limit);
// else
// greaterThan(dist(x, y), c.limit);
// }