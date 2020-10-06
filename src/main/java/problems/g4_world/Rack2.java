/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class Rack2 implements ProblemAPI {
	int nRacks;
	RackModel[] rackModels;
	CardType[] cardTypes;

	class RackModel {
		int power, nConnectors, price;
	}

	class CardType {
		int power, demand;
	}

	@Override
	public void model() {
		rackModels = addObject(rackModels, new RackModel(), 0); // we add first a dummy model (0,0,0)
		int nModels = rackModels.length, nTypes = cardTypes.length;
		int[] powers = valuesFrom(rackModels, rackModel -> rackModel.power);
		int[] sizes = valuesFrom(rackModels, rackModel -> rackModel.nConnectors);
		int[] costs = valuesFrom(rackModels, rackModel -> rackModel.price);
		int[] cardPowers = valuesFrom(cardTypes, cardType -> cardType.power);
		int maxCapacity = maxOf(sizes);

		Table table = table().addFrom(range(nModels), i -> tuple(i, powers[i], sizes[i], costs[i]));

		Var[] m = array("m", size(nRacks), dom(range(nModels)), "m[i] is the model used for the ith rack");
		Var[][] nc = array("nc", size(nRacks, nTypes), (i, j) -> dom(range(Math.min(maxCapacity, cardTypes[j].demand) + 1)),
				"nc[i][j] is the number of cards of type j put in the ith rack");
		Var[] p = array("p", size(nRacks), dom(powers), "p[i] is the power of the ith rack");
		Var[] s = array("s", size(nRacks), dom(sizes), "s[i] is the size of the ith rack");
		Var[] c = array("c", size(nRacks), dom(costs), "c[i] is the cost of the ith rack");

		forall(range(nRacks), i -> extension(vars(m[i], p[i], s[i], c[i]), table)).note("linking model with power, size and cost of the ith rack");

		forall(range(nRacks), i -> sum(nc[i], LE, s[i])).note("connector-capacity constraints");
		forall(range(nRacks), i -> sum(nc[i], weightedBy(cardPowers), LE, p[i])).note("power-capacity constraints");
		forall(range(nTypes), i -> sum(columnOf(nc, i), EQ, cardTypes[i].demand)).note("demand constraints");

		block(() -> {
			decreasing(m);
			disjunction(ne(m[0], m[1]), ge(nc[0][0], nc[1][0]));
		}).tag(SYMMETRY_BREAKING);

		minimize(SUM, c).note("minimizing the total cost paid for all racks");
	}
}
