/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problem;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import utility.Kit;
import utility.sets.SetSparse;
import variables.Variable;
import variables.Variable.VariableInteger;

public final class IdentificationAllDifferent {
	private Problem pb;

	private int[][] allNeighbours; // allNeighbours[x][i] is the ith variable y involved with x in a binary irreflexive constraint

	private int[] degrees;

	private int[] levels; // levels[x] is, when negative, the (negation of) the number of the clique to which it belongs to

	public int nBuiltCliques;

	private int[] tmp;

	private SetSparse set;

	private int[][] computeIrreflexivesNeigbours(int nVariables, List<Constraint> constraints) {
		Set<Integer>[] neighbours = Stream.of(pb.variables).map(x -> new TreeSet<>()).toArray(TreeSet[]::new);
		for (Constraint c : constraints)
			if (c.scp.length == 2 && c.isIrreflexive()) {
				neighbours[c.scp[0].num].add(c.scp[1].num);
				neighbours[c.scp[1].num].add(c.scp[0].num);
			}
		return Kit.intArray2D(neighbours);
	}

	private int countNeighboursAtLevel(int[] neighbours, int level) {
		return (int) IntStream.of(neighbours).filter(j -> levels[j] == level).count();
	}

	private int buildClique(int cliqueId) {
		int level = 0;
		int cliqueSize = 0;
		int num = -1;
		for (int i = 0; i <= set.limit; i++)
			if (num == -1 || degrees[set.dense[i]] > degrees[num])
				num = set.dense[i];
		while (num != -1) {
			levels[num] = -cliqueId; // we put num in the current clique
			tmp[cliqueSize++] = num;
			set.remove(num);
			int[] neighbours = allNeighbours[num];
			for (int j : neighbours)
				if (levels[j] == level)
					levels[j] = level + 1; // we keep them for the rest of the selection process
			level += 1;
			for (int j : neighbours)
				if (levels[j] == level)
					degrees[j] = countNeighboursAtLevel(allNeighbours[j], level);
			num = -1;
			for (int j : neighbours)
				if (levels[j] == level && (num == -1 || degrees[j] > degrees[num]))
					num = j;
		}
		for (int i = 0; i <= set.limit; i++)
			levels[set.dense[i]] = 0;
		return cliqueSize;
	}

	public IdentificationAllDifferent(Problem pb) {
		this.pb = pb;
		this.allNeighbours = computeIrreflexivesNeigbours(pb.variables.length, pb.stuff.collectedCtrsAtInit);
		this.degrees = IntStream.range(0, pb.variables.length).map(i -> allNeighbours[i].length).toArray();
		this.levels = new int[pb.variables.length];
		this.tmp = new int[pb.variables.length];
		this.set = new SetSparse(pb.variables.length, true);
		for (int k = 1; k <= pb.rs.cp.settingCtrs.inferAllDifferentNb; k++) {
			int cliqueSize = buildClique(k);
			if (cliqueSize <= pb.rs.cp.settingCtrs.inferAllDifferentSize)
				break;
			VariableInteger[] scp = IntStream.range(0, cliqueSize).mapToObj(i -> pb.variables[tmp[i]]).sorted().toArray(VariableInteger[]::new);
			pb.allDifferent(scp);
			nBuiltCliques++;
			display(k, cliqueSize);
			assert controlClique(scp, pb.stuff.collectedCtrsAtInit);
			for (int i = 0; i <= set.limit; i++)
				degrees[set.dense[i]] = countNeighboursAtLevel(allNeighbours[set.dense[i]], 0); // reinitialization of degrees
		}
	}

	private boolean controlClique(Variable[] vars, List<Constraint> constraints) {
		for (int i = 0; i < vars.length; i++)
			for (int j = i + 1; j < vars.length; j++) {
				Variable x = vars[i], y = vars[j];
				Kit.control(constraints.stream().anyMatch(c -> c.scp.length == 2 && c.isIrreflexive() && c.involves(x, y)),
						() -> "not a clique with " + x + " " + y);
			}
		return true;
	}

	private void display(int cliqueId, int cliqueSize) {
		System.out.println(" clique " + cliqueId + " of size " + cliqueSize + " {"
				+ (IntStream.range(0, levels.length).filter(i -> levels[i] == -cliqueId).mapToObj(i -> "" + pb.variables[i]).collect(Collectors.joining(" ")))
				+ "}");
	}
}
