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
import org.xcsp.common.Utilities;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class MisteryShopper implements ProblemAPI {
	int[] visitorGroups; // visitorGroups[i] gives the size of the ith visitor group
	int[] visiteeGroups; // visiteeGroups[i] gives the size of the ith visitee group

	private Table numberPeople(int[] t) {
		Table table = table();
		for (int cnt = 0, i = 0; i < t.length; i++)
			for (int j = 0; j < t[i]; j++)
				table.add(tuple(i, cnt++));
		return table;
	}

	@Override
	public void model() {
		int nVisitors = sumOf(visitorGroups), nVisitees = sumOf(visiteeGroups);
		Utilities.control(nVisitors >= nVisitees, "The number of visitors must be greater than the number of visitees");
		int n = nVisitors, nDummyVisitees = nVisitors - nVisitees;
		if (nDummyVisitees > 0)
			visiteeGroups = addInt(visiteeGroups, nDummyVisitees);
		int nWeeks = visitorGroups.length, nVisitorGroups = visitorGroups.length, nVisiteegroups = visiteeGroups.length;

		Var[][] vr = array("vr", size(n, nWeeks), dom(range(n)), "vr[i][w] is the visitor for the ith visitee at week w");
		Var[][] ve = array("ve", size(n, nWeeks), dom(range(n)), "ve[i][w] is the visitee for the ith visitor at week w");
		Var[][] gr = array("gr", size(n, nWeeks), dom(range(nVisitorGroups)), "gr[i][w] is the visitor group for the ith visitee at week w");
		Var[][] ge = array("ge", size(n, nWeeks), dom(range(nVisiteegroups)), "ge[i][w] is the visitee group for the ith visitor at week w");

		forall(range(nWeeks), w -> allDifferent(columnOf(vr, w))).note("each week, all visitors must be different");
		forall(range(nWeeks), w -> allDifferent(columnOf(ve, w))).note("each week, all visitees must be different");
		forall(range(n), i -> allDifferent(gr[i])).note("the visitor groups must be different for each visitee");
		forall(range(n), i -> allDifferent(ge[i])).note("the visitee groups must be different for each visitor");

		forall(range(nWeeks), w -> channel(columnOf(vr, w), columnOf(ve, w))).note("channeling arrays vr and ve, each week");

		block(() -> {
			lexMatrix(vr, INCREASING);
			if (nDummyVisitees > 0)
				forall(range(nWeeks), w -> strictlyIncreasing(select(columnOf(vr, w), range(nVisitees, n))));
		}).tag(SYMMETRY_BREAKING);

		Table tableForVisitors = numberPeople(visitorGroups), tableForVisitees = numberPeople(visiteeGroups);
		forall(range(n).range(nWeeks), (i, w) -> extension(vars(gr[i][w], vr[i][w]), tableForVisitors)).note("linking a visitor with its group");
		forall(range(n).range(nWeeks), (i, w) -> extension(vars(ge[i][w], ve[i][w]), tableForVisitees)).note("linking a visitee with its group");
	}
}
