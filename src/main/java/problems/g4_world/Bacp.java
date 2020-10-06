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
import org.xcsp.modeler.api.ProblemAPI;

public class Bacp implements ProblemAPI {

	int nPeriods;
	int minCredits, maxCredits;
	int minCourses, maxCourses;
	int[] credits;
	int[][] prerequisites;

	private int[][] channelingTable(int c) {
		int[][] tuples = new int[nPeriods][nPeriods + 1];
		for (int p = 0; p < nPeriods; p++) {
			tuples[p][p] = credits[c];
			tuples[p][nPeriods] = p;
		}
		return tuples;
	}

	@Override
	public void model() {
		int nCourses = credits.length, nPrerequisites = prerequisites.length;
		int ubCredits = modelVariant().endsWith("d") ? maxCredits * maxCourses : maxCredits;

		Var[] s = array("s", size(nCourses), dom(range(nPeriods)), "s[c] is the period (schedule) for course c");
		Var[] co = array("co", size(nPeriods), dom(range(minCourses, maxCourses + 1)), "co[p] is the number of courses at period p");
		Var[] cr = array("cr", size(nPeriods), dom(range(minCredits, ubCredits + 1)), "cr[p] is the number of credits at period p");

		if (modelVariant().startsWith("m1")) {
			Var[][] cp = array("cp", size(nCourses, nPeriods), (c, p) -> dom(0, credits[c]),
					"cp[c][p] is 0 if the course c is not planned at period p, the number of credits for c otherwise");

			forall(range(nCourses), c -> extension(vars(cp[c], s[c]), channelingTable(c))).note("channeling between arrays cp and s");
			forall(range(nPeriods), p -> count(s, takingValue(p), EQ, co[p])).note("counting the number of courses in each period");
			forall(range(nPeriods), p -> sum(columnOf(cp, p), EQ, cr[p])).note("counting the number of credits in each period");
		}
		if (modelVariant().startsWith("m2")) {
			Var[][] pc = array("pc", size(nPeriods, nCourses), dom(0, 1), "pc[p][c] is 1 iff the course c is at period p");

			forall(range(nPeriods).range(nCourses), (p, c) -> equivalence(pc[p][c], eq(s[c], p))).tag(CHANNELING); // use extension for minitrack
			forall(range(nCourses), c -> sum(columnOf(pc, c), EQ, 1)).note("ensuring that each course is assigned to a period");
			forall(range(nPeriods), p -> sum(pc[p], EQ, co[p])).note("counting the number of courses in each period");
			forall(range(nPeriods), p -> sum(pc[p], credits, EQ, cr[p])).note("counting the number of credits in each period");
		}
		forall(range(nPrerequisites), i -> lessThan(s[prerequisites[i][0]], s[prerequisites[i][1]])).note("handling prerequisites");

		if (modelVariant().endsWith("d")) {
			Var mincr = var("mincr", dom(rangeClosed(minCredits, ubCredits)), "mincr is the minimum number of credits over the periods");
			Var maxcr = var("maxcr", dom(rangeClosed(minCredits, ubCredits)), "maxcr is the maximum number of credits over the periods");
			// Var distcr = var("distcr", dom(range(ubCredits + 1)), "distcr is the maximal distance in term of credits");
			minimum(cr, mincr);
			maximum(cr, maxcr);
			// equal(distcr, sub(maxcr, mincr));
			minimize(sub(maxcr, mincr)).note("minimizing the maximal distance in term of credits"); // distcr);
		} else
			minimize(MAXIMUM, cr).note("minimizing the maximum number of credits in periods");
		decisionVariables(s);
	}
}

// return IntStream.range(0, nPeriods).mapToObj(p1 -> IntStream.range(0, nPeriods + 1).map(p2 -> p2 == nPeriods ? p1 : p2 == p1 ? credits[c] :
// 0).toArray()).toArray(int[][]::new);
// range(nPeriods).range(nPeriods + 1).map((p1, p2) -> p2 == nPeriods ? p1 : p2 == p1 ? credits[c] : 0);