/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.order1;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.xcsp.common.Utilities;

import constraints.Constraint;
import constraints.hard.extension.CtrExtensionRPWC;
import constraints.hard.extension.structures.Table;
import search.Solver;
import utility.Kit;
import variables.Variable;

public final class MaxRPWC extends AC {

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	/**
	 * The time counter specific to maxRPWC.
	 */
	private int specificTime;

	/**
	 * The value of the specific time of maxRPWC, at the last backtrack of the solver.
	 */
	public int lastBacktrackSpecificTime;

	public int incrementSpecificTime() {
		return ++specificTime;
	}

	private int[] t1, t2; // temporary arrays

	/**********************************************************************************************
	 * Intern classes
	 *********************************************************************************************/

	public class Intersection {
		public CtrExtensionRPWC[] ctrs;
		private int[][] sharedPositions; // positions of the shared variables in the scope of each constraint
		private Node root;
		private int size; // number of shared variables

		private Intersection(CtrExtensionRPWC c1, CtrExtensionRPWC c2, int[] vaps1, int[] vaps2) {
			this.ctrs = new CtrExtensionRPWC[] { c1, c2 };
			this.sharedPositions = new int[][] { vaps1, vaps2 };
			this.root = new Node(c1.scp[vaps1[0]].dom.initSize());
			this.size = vaps1.length;
			assert controlSharedVariables();
			// we build the trie
			for (int i = 0; i < ctrs.length; i++)
				for (int[] tuple : ((Table) ctrs[i].extStructure()).tuples)
					root.add(tuple, i, 0);
		}

		private boolean controlSharedVariables() {
			for (int[] positions : sharedPositions)
				if (positions.length != size)
					return false;
			for (int j = 0; j < size; j++)
				for (int i = 1; i < ctrs.length; i++)
					if (ctrs[0].scp[sharedPositions[0][j]] != ctrs[i].scp[sharedPositions[i][j]])
						return false;
			return true;
		}

		public Leaf getLeafFor(int[] tuple, int source) {
			Node node = root;
			for (int vap : sharedPositions[source])
				node = node.childs[tuple[vap]];
			return (Leaf) node;
		}

		@Override
		public String toString() {
			return ctrs[0] + " " + ctrs[1] + " " + Kit.join(sharedPositions[0]) + " - " + Kit.join(sharedPositions[1]) + "\n";
		}

		public class Node {
			private Node[] childs;

			protected Node() {}

			protected Node(int nbChilds) {
				childs = new Node[nbChilds];
			}

			protected void add(int[] tuple, int source, int i) {
				int idx = tuple[sharedPositions[source][i]];
				if (childs[idx] == null)
					childs[idx] = i == size - 1 ? new Leaf() : new Node(ctrs[source].scp[sharedPositions[source][i + 1]].dom.initSize());
				childs[idx].add(tuple, source, i + 1);
			}

			protected void display(int[] collect, int position) {
				for (int i = 0; i < childs.length; i++)
					if (childs[i] != null) {
						collect[position] = i;
						childs[i].display(collect, position + 1);
					}
			}
		}

		public class Leaf extends Node {
			public int[] stamps;

			protected Leaf() {
				stamps = Kit.repeat(-1, ctrs.length);
			}

			@Override
			protected void add(int[] tuple, int source, int i) {
				stamps[source] = 0;
			}

			@Override
			protected void display(int[] collect, int pos) {
				Kit.log.finer(Kit.join(collect, pos) + " stamps=" + Kit.join(stamps));
			}
		}
	}

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	private Intersection intersectionOf(CtrExtensionRPWC c1, CtrExtensionRPWC c2) {
		t1 = t1 == null ? new int[solver.pb.stuff.maxCtrArity()] : t1;
		t2 = t2 == null ? new int[solver.pb.stuff.maxCtrArity()] : t2;
		int cnt = 0;
		if (Variable.areNumsStrictlyIncreasing(c1.scp) && Variable.areNumsStrictlyIncreasing(c2.scp)) {
			for (int i = 0, j = 0; i < c1.scp.length && j < c2.scp.length;)
				if (c1.scp[i].num < c2.scp[j].num)
					i++;
				else if (c1.scp[i].num > c2.scp[j].num)
					j++;
				else {
					t1[cnt] = i++;
					t2[cnt++] = j++;
				}
		} else {
			for (int i = 0; i < c1.scp.length; i++) {
				int j = Utilities.indexOf(c1.scp[i], c2.scp);
				if (j != -1) {
					t1[cnt] = i;
					t2[cnt++] = j;
				}
			}
		}
		return cnt > 1 ? new Intersection(c1, c2, Arrays.copyOf(t1, cnt), Arrays.copyOf(t2, cnt)) : null;
	}

	public MaxRPWC(Solver solver) {
		super(solver);
		Constraint[] ctrs = solver.pb.constraints;
		List<Intersection>[] lists = new List[ctrs.length];
		int cnt = 0;
		for (int i = 0; i < ctrs.length; i++)
			if (ctrs[i] instanceof CtrExtensionRPWC)
				for (int j = i + 1; j < ctrs.length; j++)
					if (ctrs[j] instanceof CtrExtensionRPWC) {
						Intersection intersection = intersectionOf((CtrExtensionRPWC) ctrs[i], (CtrExtensionRPWC) ctrs[j]);
						if (intersection != null) {
							cnt++;
							for (CtrExtensionRPWC c : intersection.ctrs) {
								if (lists[c.num] == null)
									lists[c.num] = new ArrayList<>();
								lists[c.num].add(intersection);
							}
						}
					}
		for (Constraint c : ctrs)
			if (c instanceof CtrExtensionRPWC && lists[c.num] != null)
				((CtrExtensionRPWC) c).addIntersections(lists[c.num]);
		Kit.log.info("Nb pairs of intersecting constraints : " + cnt + "\n");
	}

	private boolean test = false;

	@Override
	public boolean runAfterAssignment(Variable x) {
		if (super.runAfterAssignment(x) == false)
			return false;
		if (test) {
			queue.fill();
			return propagate();
		}
		return true;
	}

	@Override
	public boolean runAfterRefutation(Variable x) {
		lastBacktrackSpecificTime = incrementSpecificTime();
		return super.runAfterRefutation(x);
	}
}
