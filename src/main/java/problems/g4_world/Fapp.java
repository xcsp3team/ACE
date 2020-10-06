/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;
import org.xcsp.modeler.implementation.NotData;

// noGroupAtAllForExtension must be set to true in Compiler ; uncompactDomainFor must be set to true too
// m2s is m2 but without undefined variables (as in ext model)
public class Fapp implements ProblemAPI {

	int[][] domains; // Map<Integer, int[]> domains;
	Route[] routes;
	HardCtr[] hards;
	SoftCtr[] softs;

	class Route {
		int domain;
		int polarization;

		int[] polarizationValues() {
			return polarization == 0 ? vals(0, 1) : polarization == 1 ? vals(1) : vals(0);
		}
	}

	class HardCtr {
		int route1;
		int route2;
		boolean frequency;
		boolean equality;
		int gap;
	}

	class SoftCtr {
		int route1;
		int route2;
		int[] eqRelaxations;
		int[] neRelaxations;
	}

	@NotData
	Map<String, int[][]> cacheForTables = new HashMap<>();

	private CtrEntity imperativeConstraint(Var[] f, Var[] p, HardCtr c) {
		int i = c.route1, j = c.route2;
		if (c.frequency) {
			if (c.gap == 0)
				return c.equality ? equal(f[i], f[j]) : different(f[i], f[j]);
			return c.equality ? equal(dist(f[i], f[j]), c.gap) : different(dist(f[i], f[j]), c.gap);
		}
		return c.equality ? equal(p[i], p[j]) : different(p[i], p[j]);
	}

	private int[][] tableForRelaxableRadioelectricCtr(SoftCtr c, boolean shortVersion) {
		int i = c.route1, j = c.route2;
		String key = routes[i].domain + "*" + routes[j].domain + "*" + routes[i].polarization + "*" + routes[j].polarization + "*"
				+ Utilities.join(c.eqRelaxations) + "*" + Utilities.join(c.neRelaxations);
		if (cacheForTables.containsKey(key))
			return cacheForTables.get(key);
		Set<Integer> setForShortVersion = new HashSet<>();
		Set<int[]> table = new TreeSet<>(Utilities.lexComparatorInt);
		for (int fi : domains[routes[i].domain])
			for (int fj : domains[routes[j].domain]) {
				int dist = Math.abs(fi - fj);
				if (shortVersion && setForShortVersion.contains(dist))
					continue;
				for (int pol = 0; pol < 4; pol++) {
					int pi = pol < 2 ? 0 : 1;
					int pj = pol == 1 || pol == 3 ? 1 : 0;
					if (routes[i].polarization == 1 && pi == 0 || routes[j].polarization == 1 && pj == 0)
						continue;
					if (routes[i].polarization == -1 && pi == 1 || routes[j].polarization == -1 && pj == 1)
						continue;
					int[] t = pi == pj ? c.eqRelaxations : c.neRelaxations;
					for (int k = 0; k <= 11; k++) {
						if (k == 11 || dist >= t[k]) { // for k=11, we suppose t[k] = 0
							int sum = IntStream.range(0, k - 1).map(l -> dist >= t[l] ? 0 : 1).sum();
							if (shortVersion)
								table.add(tuple(dist, pi, pj, k, k == 0 || dist >= t[k - 1] ? 0 : 1, k <= 1 ? 0 : sum));
							else
								table.add(tuple(fi, fj, pi, pj, k, k == 0 || dist >= t[k - 1] ? 0 : 1, k <= 1 ? 0 : sum));
						}
					}
				}
				setForShortVersion.add(dist);
			}
		// if (shortVersion && (fileName.endsWith("05-0350") || fileName.endsWith("16-0260")))
		// table.add(tuple(STAR_INT, STAR_INT, STAR_INT, 11, STAR_INT, STAR_INT));
		int[][] t = table.toArray(new int[0][]);
		cacheForTables.put(key, t);
		return t;
	}

	private int[] distances(int i, int j) {
		int[] dom1 = domains[routes[i].domain], dom2 = domains[routes[j].domain];
		return IntStream.of(dom1).flatMap(f1 -> IntStream.of(dom2).map(f2 -> Math.abs(f1 - f2))).toArray(); // no need for distinct().sorted() as done
																											// by dom()
	}

	private boolean[][] buildSoftLinks() {
		boolean[][] softLinks = new boolean[routes.length][routes.length];
		for (SoftCtr c : softs) {
			int i = c.route1, j = c.route2;
			softLinks[i][j] = true;
			softLinks[j][i] = true;
		}
		return softLinks;
	}

	@Override
	public void model() {
		boolean[][] softLinks = buildSoftLinks();
		int n = routes.length, nHards = hards == null ? 0 : hards.length, nSofts = softs.length;
		Var[] f = array("f", size(n), i -> dom(domains[routes[i].domain]), "f[i] is the frequency of the ith radio-link");
		Var[] p = array("p", size(n), i -> dom(routes[i].polarizationValues()), "p[i] is the polarization of the ith radio-link");
		Var k = var("k", dom(range(12)), "k is the relaxation level to be optimized");
		Var[] v1 = array("v1", size(nSofts), dom(0, 1),
				"v1[q] is 1 iff the qth pair of radio-electric compatibility constraints is violated when relaxing another level");
		Var[] v2 = array("v2", size(nSofts), dom(range(11)),
				"v2[q] is the number of times the qth pair of radio-electric compatibility constraints is violated when relaxing more than one level");

		forall(range(nHards), q -> imperativeConstraint(f, p, hards[q])).note("imperative constraints"); // intension to extension for
																											// minitrack

		if (modelVariant("")) {
			forall(range(nSofts), q -> {
				int i = softs[q].route1, j = softs[q].route2;
				extension(vars(f[i], f[j], p[i], p[j], k, v1[q], v2[q]), tableForRelaxableRadioelectricCtr(softs[q], false));
			}).note("soft radio-electric compatibility constraints");
		}
		if (modelVariant("short")) {
			Var[][] d = array("d", size(n, n), (i, j) -> dom(distances(i, j)).when(i < j && softLinks[i][j]),
					"d[i][j] is the distance between the ith and the jth frequencies (for i < j when a soft link exists)");
			forall(range(n).range(n), (i, j) -> {
				if (i < j && softLinks[i][j])
					intension(eq(d[i][j], dist(f[i], f[j])));
			}).note("computing intermediary distances");
			forall(range(nSofts), q -> {
				int i = softs[q].route1, j = softs[q].route2;
				extension(vars(i < j ? d[i][j] : d[j][i], p[i], p[j], k, v1[q], v2[q]), tableForRelaxableRadioelectricCtr(softs[q], true));
			}).note("soft radio-electric compatibility constraints");
		}
		if (modelVariant("ext")) {
			int[] t = IntStream.range(0, n).flatMap(i -> IntStream.range(0, n).filter(j -> i < j && softLinks[i][j]).map(j -> i * n + j)).toArray();
			// System.out.println("T=" + Kit.join(t));
			Var[] d = array("d", size(t.length), ind -> dom(distances(t[ind] / n, t[ind] % n)),
					"d[i] is the distance between the ith pair of linked frequencies");
			forall(range(t.length), ind -> {
				extension(eq(d[ind], dist(f[t[ind] / n], f[t[ind] % n]))); // intension to extension for minitrack
			}).note("computing intermediary distances");
			forall(range(nSofts), q -> {
				int i = softs[q].route1, j = softs[q].route2;
				int ij = i < j ? i * n + j : j * n + i;
				int pos = Utilities.indexOf(ij, t);
				extension(vars(d[pos], p[i], p[j], k, v1[q], v2[q]), tableForRelaxableRadioelectricCtr(softs[q], true));
			}).note("soft radio-electric compatibility constraints");
		}
		Var[] vars = vars(k, v1, v2);
		minimize(SUM, vars, weightedBy(vals(10 * nSofts * nSofts, repeat(10 * nSofts, nSofts), repeat(1, nSofts))));
	}
}
