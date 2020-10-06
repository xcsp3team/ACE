/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g2_academic;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Range;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

public class SportsScheduling implements ProblemAPI {
	int nTeams;

	private int matchNumber(int team1, int team2) {
		int nPossibleMatches = (nTeams - 1) * nTeams / 2;
		return nPossibleMatches - ((nTeams - team1) * (nTeams - team1 - 1)) / 2 + (team2 - team1 - 1);
	}

	private Table matchs() {
		Table table = table();
		for (int team1 = 0; team1 < nTeams; team1++)
			for (int team2 = team1 + 1; team2 < nTeams; team2++)
				table.add(team1, team2, matchNumber(team1, team2));
		return table;
	}

	@Override
	public void model() {
		int nWeeks = nTeams - 1, nPeriods = nTeams / 2, nPossibleMatches = (nTeams - 1) * nTeams / 2;
		Range allTeams = range(nTeams);

		Var[][] h = array("h", size(nWeeks, nPeriods), dom(allTeams), "h[w][p] is the home team at week w and period p");
		Var[][] a = array("a", size(nWeeks, nPeriods), dom(allTeams), "a[w][p] is the away team at week w and period p");
		Var[][] m = array("m", size(nWeeks, nPeriods), dom(range(nPossibleMatches)), "m[w][p] is the number of the match at week w and period p");

		Table table = matchs();
		forall(range(nWeeks).range(nPeriods), (w, p) -> extension(vars(h[w][p], a[w][p], m[w][p]), table))
				.note("linking variables through ternary table constraints");

		allDifferent(m).note("all matches are different (no team can play twice against another team)");
		forall(range(nWeeks), w -> allDifferent(vars(h[w]), a[w])).note("each week, all teams are different (each team plays each week)");
		forall(range(nPeriods), p -> cardinality(vars(columnOf(h, p), columnOf(a, p)), allTeams, occursEachBetween(1, 2)))
				.note("each team plays at most two times in each period");
		// TODO a tag for negation of dummyWeek

		block(() -> {
			forall(range(nWeeks), w -> exactly1(m[w], takingValue(matchNumber(0, w + 1))))
					.note("the match '0 versus t' (with t strictly greater than 0) appears at week t-1");
			instantiation(m[0], takingValues(range(nPeriods).map(p -> matchNumber(2 * p, 2 * p + 1))))
					.note("the first week is set : 0 vs 1, 2 vs 3, 4 vs 5, etc.");
		}).tag(SYMMETRY_BREAKING);

		block(() -> {
			Var[] hd = array("hd", size(nPeriods), dom(range(nTeams)), "hd[p] is the home team for the dummy match of period p");
			Var[] ad = array("ad", size(nPeriods), dom(range(nTeams)), "ad[p] is the away team for the dummy match of period p");

			allDifferent(vars(hd, ad)).note("all teams are different in the dummy week");
			forall(range(nPeriods), p -> cardinality(vars(columnOf(h, p), columnOf(a, p), hd[p], ad[p]), allTeams, occursEachExactly(2)))
					.note("each team plays two times in each period");
			forall(range(nPeriods), p -> lessThan(hd[p], ad[p]));

			// equal(hd[nPeriods - 1], 0); equal(ad[nPeriods - 1], nTeams - 1);
		}).note("handling dummy week (variables and constraints)").tag("dummy-week");

	}
}
