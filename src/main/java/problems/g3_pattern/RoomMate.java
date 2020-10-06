/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g3_pattern;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import constraints.Constraint;
import constraints.hard.extension.CtrExtensionSmart;
import constraints.hard.extension.structures.SmartTuple;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public class RoomMate implements ProblemAPI {
	int[][] preferences;

	@NotData
	int[][] rank; // rank[i][j] = k <-> ith guy ranks jth guy as kth choice

	@NotData
	int[][] pref; // pref[i][k] = j <-> ith guy has jth guy as kth choice

	private Constraint smart1(Var[] x, int i) {
		SmartTuple[] smartTuples = IntStream.range(0, preferences[i].length).mapToObj(k -> {
			List<XNodeParent<? extends IVar>> list = new ArrayList<>();
			list.add(le(x[i], k));
			for (int l = 0; l < k; l++) {
				int j = pref[i][l];
				list.add(lt(x[j], rank[j][i]));
			}
			return new SmartTuple(list);
		}).toArray(SmartTuple[]::new);
		return new CtrExtensionSmart(((Problem) imp()), (Variable[]) x, smartTuples);
	}

	private int[][] table(int i) {
		int[][] table = new int[preferences[i].length][];
		for (int k = 0; k < table.length; k++) {
			table[k] = Kit.repeat(STAR, preferences.length);
			int j = pref[i][k];
			table[k][i] = rank[i][j];
			table[k][j] = rank[j][i];
		}
		return table; // extension(x, table);
	}

	private void buildAuxiliaryDataStructures(int n) {
		pref = new int[n][n];
		rank = new int[n][n];
		for (int i = 0; i < n; i++) {
			for (int k = 0; k < preferences[i].length; k++) {
				int j = preferences[i][k] - 1; // because we start at 0
				rank[i][j] = k;
				pref[i][k] = j;
			}
			rank[i][i] = preferences[i].length;
			pref[i][preferences[i].length] = i;
		}
	}

	@Override
	public void model() {
		int n = preferences.length;
		buildAuxiliaryDataStructures(n);

		Var[] x = array("x", size(n), i -> dom(range(preferences[i].length)), "x[i] is the value of k, meaning that j = pref[i][k] is the paired agent");

		if (modelVariant("")) {
			forall(range(n).range(n), (i, k) -> {
				if (k < preferences[i].length)
					implication(gt(x[i], rank[i][pref[i][k]]), lt(x[pref[i][k]], rank[pref[i][k]][i]));
			});
			forall(range(n).range(n), (i, k) -> {
				if (k < preferences[i].length)
					implication(eq(x[i], rank[i][pref[i][k]]), eq(x[pref[i][k]], rank[pref[i][k]][i]));
			});
		}
		if (modelVariant("smart")) {
			forall(range(n), i -> ((Problem) imp()).addCtr(smart1(x, i)));
			forall(range(n), i -> extension(x, table(i)));
		}
	}
}
