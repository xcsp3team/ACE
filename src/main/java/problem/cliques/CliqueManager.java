/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package problem.cliques;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import constraints.Constraint;
import dashboard.Output;
import problem.Problem;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public class CliqueManager {
	private Problem pb;

	private int nCliques;

	public Clique[][] cliques; // 1D = constraint num; 2D=order

	public CliqueManager(Problem pb) {
		this.pb = pb;
		Kit.control(Constraint.nPairsOfCtrsWithSimilarScopeIn(pb.constraints) == 0);
		fixCliques();
		// displayCliques(false);
		// Resolution.getInstance().setUseOptimalSupportManager(false); // true; // remains true iff all constraints
		// have optimal support units
		// Constraint[] constraints = problem.constraints;
		// for (int i = 0; useOptimalSupportManager && i < constraints.length; i++)
		// if (constraints[i].getSupportUnits() == null || !(constraints[i].getSupportUnits()[0] instanceof
		// SupportUnitOptimal))
		// useOptimalSupportManager = false;
		// System.out.println("useOptimalSupportManager=" + useOptimalSupportManager);
	}

	public void fixCliques() {
		nCliques = 0;
		List<Clique>[] cliquesLists = new LinkedList[pb.constraints.length];
		for (int i = 0; i < cliquesLists.length; i++)
			cliquesLists[i] = new LinkedList<>();
		for (Constraint c1 : pb.constraints) {
			if (c1.scp.length != 2)
				continue;
			for (Variable x : pb.variables) {
				if (c1.involves(x))
					continue;
				Constraint c2 = c1.scp[0].firstBinaryConstraintWith(x);
				if (c2 == null || c2.num < c1.num)
					continue;
				Constraint c3 = c1.scp[1].firstBinaryConstraintWith(x);
				if (c3 == null || c3.num < c1.num)
					continue;
				if (c2.num > c3.num) {
					Constraint tmp = c2;
					c2 = c3;
					c3 = tmp;
				}
				Clique clique = new Clique(c1, c2, c3);
				cliquesLists[c1.num].add(clique);
				cliquesLists[c2.num].add(clique);
				cliquesLists[c3.num].add(clique);
				nCliques++;
			}
		}
		int nbConstraintsInvolvedInCliques = 0;
		cliques = new Clique[pb.constraints.length][];
		for (Constraint ctr : pb.constraints) {
			Arrays.sort(cliques[ctr.num] = cliquesLists[ctr.num].toArray(new Clique[cliquesLists[ctr.num].size()]));
			for (int i = 0; i < cliques[ctr.num].length; i++)
				cliques[ctr.num][i].setPosition(ctr, i);
			if (cliquesLists[ctr.num].size() > 0)
				nbConstraintsInvolvedInCliques++;
		}
		Kit.log.fine("nbConstraintsInvolvedInCliques=" + nbConstraintsInvolvedInCliques + Output.DATA_SEPARATOR + "nbCliques=" + nCliques);
	}

	public static int getPathSupport(Variable x, Variable y, int a, int b, Variable z, int idxStart3, Constraint c1, Constraint c2) {
		int[] tuple1 = c1.tupleManager.localTuple;
		int vap1 = c1.scp[0] == x ? 0 : 1, bro1 = vap1 == 0 ? 1 : 0;
		tuple1[vap1] = a;

		int[] tuple2 = c2.tupleManager.localTuple;
		int vap2 = c2.scp[0] == y ? 0 : 1, bro2 = vap2 == 0 ? 1 : 0;
		tuple2[vap2] = b;

		Domain dom3 = z.dom;

		if (idxStart3 == -1)
			idxStart3 = dom3.first();
		else if (!dom3.isPresent(idxStart3))
			idxStart3 = dom3.next(idxStart3);

		// if (elements.getNbPresentElements() - start > delta) continue;
		for (int idx3 = idxStart3; idx3 != -1; idx3 = dom3.next(idx3)) {
			tuple1[bro1] = idx3;
			tuple2[bro2] = idx3;
			if (c1.checkIndexes(tuple1) && c2.checkIndexes(tuple2))
				return idx3;
		}
		return -1;
	}

	public int getPathSupport(Constraint c, int[] tuple, Clique clique, int start) {
		Variable x = c.scp[0], y = c.scp[1], z = clique.setWorkingSet(x, y);
		return getPathSupport(x, y, tuple[0], tuple[1], z, start, clique.wrk1, clique.wrk2);
	}

	public boolean isPathConsistent(Variable x, Variable y, int a, int b, Clique[] cliques) {
		for (Clique clique : cliques) {
			Variable var3 = clique.setWorkingSet(x, y);
			if (getPathSupport(x, y, a, b, var3, -1, clique.wrk1, clique.wrk2) == -1)
				return false;
		}
		return true;
	}

	public boolean isPathConsistent(Constraint c, int[] tuple) {
		assert c.scp.length == 2;
		return isPathConsistent(c.scp[0], c.scp[1], tuple[0], tuple[1], cliques[c.num]);
	}

	public void displayCliques(boolean restricted) {
		System.out.println("Cliques :");
		for (Constraint c : pb.constraints) {
			System.out.println("Cliques from " + c);
			for (Clique clique : cliques[c.num])
				if (!restricted || clique.c1 == c)
					System.out.println("  clique = " + clique);
		}
		System.out.println("  => " + nCliques + " cliques");
	}

}

// public boolean isPathConsistent(Variable variable1, Variable variable2, int[] support, Path[] pathes,
// SupportManagerOptimal supportManager)
// {
// int index1 = support[0];
// int index2 = support[1];
// assert variable1.domain.getElements().has(index1) && variable2.domain.getElements().has(index2);
//
// for (Path path : pathes)
// {
// Constraint constraint1 = path.edge1;
// Constraint constraint2 = path.edge2;
// Variable variable3 = path.variable3;
// Elements elements = variable3.domain.getElements();
//
// int start1 = supportManager.getLastSupportFromBrotherOf(constraint1, variable1, index1);
// int start2 = supportManager.getLastSupportFromBrotherOf(constraint2, variable2, index2);
// int start = Math.max(start1, start2);
// if (start == -1)
// start = elements.getFirstPreent();
// else if (!variable3.domain.getElements().has(start))
// start = elements.getFirstElementStrictlyGreaterThan(start);
//
// while (start != -1)
// {
// if (supportManager.getLastSupportFromBrotherOf(constraint1, variable3, start) > index1
// || supportManager.getLastSupportFromBrotherOf(constraint2, variable3, start) > index2)
// {
// // System.out.println("je passe");
// start = elements.getNextPresent(start);
// }
// else
// break;
// }
//
// // if (domain.getCurrentSize() - realStart > delta) continue;
//
// assert start == -1 || variable3.domain.getElements().has(start);
// boolean found = false;
// for (int index3 = start; !found && index3 != -1; index3 = elements.getNextPresent(index3))
// if (constraint1.seekSupport(variable1, index1, variable3, index3) && constraint2.seekSupport(variable2, index2,
// variable3, index3))
// {
// // lastThirdNodeSupport[index][i]=index3;
// found = true;
// }
// if (!found)
// return false;
// }
// return true;
// }
