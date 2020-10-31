/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package propagation.soft.pfc;

import java.util.Arrays;

import org.xcsp.common.Types.TypeFramework;

import constraints.Constraint;
import heuristics.variables.HeuristicVariablesDynamic;
import interfaces.TagExperimental;
import interfaces.TagMaximize;
import search.Solver;
import search.backtrack.SolverBacktrack;
import utility.Kit;
import utility.operations.CombinatorOfTwoInts;
import variables.Variable;
import variables.domains.Domain;

public class RDAC extends RDACAbstract {

	public static class DDegOnDomOffset extends HeuristicVariablesDynamic implements TagExperimental, TagMaximize {

		public DDegOnDomOffset(SolverBacktrack solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			RDAC maxCSP = (RDAC) (solver.propagation);
			return maxCSP.getAicOffsetOf(x) * x.ddegOnDom();
		}
	}

	public static class OffsetThenDom extends HeuristicVariablesDynamic implements TagExperimental {

		private CombinatorOfTwoInts combinator;

		public OffsetThenDom(SolverBacktrack solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			this.combinator = new CombinatorOfTwoInts(solver.pb.stuff.maxDomSize());
		}

		@Override
		public double scoreOf(Variable x) {
			RDAC maxCSP = (RDAC) (solver.propagation);
			return combinator.combinedLongValueFor(maxCSP.getAicOffsetOf(x), x.dom.size());
		}
	}

	/** aic[x][a] is the number of constraints with no support for (x,a) */
	public final int[][] aic;

	public int getAicOffsetOf(Variable x) {
		int[] t = aic[x.num];
		Domain dom = x.dom;
		int bestIndex = dom.first();
		int bestOffset = Integer.MAX_VALUE; // offset between two best values
		for (int idx = dom.next(bestIndex); idx != -1; idx = dom.next(idx)) {
			if (t[idx] < t[bestIndex]) {
				bestOffset = t[bestIndex] - t[idx];
				bestIndex = idx;
			} else
				bestOffset = Math.min(bestOffset, t[idx] - t[bestIndex]);
		}
		return bestOffset;
	}

	public RDAC(Solver solver) {
		super(solver);
		Kit.control(solver.pb.settings.framework == TypeFramework.MAXCSP, () -> "MaxCSP is not indicated in your configuration");
		aic = Variable.litterals(solver.pb.variables).intArray();
		partitionOfConstraints = new PartitionOfConstraintsMax(solver);
	}

	public final class PartitionOfConstraintsMax extends PartitionOfConstraints {

		protected PartitionOfConstraintsMax(Solver solver) {
			super(solver);
		}

		@Override
		protected double evaluate(Constraint c, Variable x, boolean incremental) {
			int vap = c.positionOf(x);
			long[] mc = minCosts[c.num][vap];

			int nbInconsistentValues = 0;
			Domain dom = x.dom;
			if (!incremental) {
				if (reviser.mustBeAppliedTo(c, x)) {
					for (int a = dom.first(); a != -1; a = dom.next(a))
						if ((mc[a] = c.findArcSupportFor(vap, a) ? 0 : c.cost) > 0) {
							nbInconsistentValues++;
							aic[x.num][a]++;
						}
				} else
					Arrays.fill(mc, 0);
			} else {
				if (reviser.mustBeAppliedTo(c, x)) {
					for (int a = dom.first(); a != -1; a = dom.next(a))
						if (mc[a] > 0)
							nbInconsistentValues++;
						else if ((mc[a] = c.findArcSupportFor(vap, a) ? 0 : c.cost) > 0) {
							nbInconsistentValues++;
							aic[x.num][a]++;
						}
				}
			}
			return nbInconsistentValues / (double) dom.size();
		}

		@Override
		protected void updateStructures(Constraint c, Variable x) {
			int vap = c.positionOf(x);
			long[] mc = minCosts[c.num][vap];
			if (reviser.mustBeAppliedTo(c, x)) {
				Domain dom = x.dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					if (mc[a] > 0)
						continue;
					if (!c.findArcSupportFor(vap, a)) {
						mc[a] = c.cost;
						aic[x.num][a]++;
					}
				}
			}
		}

		/**
		 * returns a value equivalent to ic_ia + dac_ia where i is the given variable and a the given index
		 */
		@Override
		public long computeSumMinCostsOf(Variable x, int a) {
			assert !x.isAssigned();
			long cnt = 0;
			for (int cnum = first[x.num]; cnum != -1; cnum = next[cnum])
				cnt += minCosts[cnum][ctrs[cnum].positionOf(x)][a];
			return cnt;
		}
	}

	@Override
	public void init(boolean incremental) {
		if (!incremental)
			for (int i = 0; i < aic.length; i++)
				Arrays.fill(aic[i], 0);
		super.init(incremental);
	}

	@Override
	protected void updateStructuresFromRemovals() {
		while (queue.size() > 0) {
			Variable x = queue.pickAndDelete(0);
			for (Constraint c : x.ctrs) {
				if (c.futvars.size() == 0)
					continue;
				Variable partitionVariable = solver.pb.variables[partitionOfConstraints.membership[c.num]];
				long[] t = sumMinCosts[partitionVariable.num];
				for (int j = 0; j < c.scp.length; j++) {
					Variable y = c.scp[j];
					if (y.isAssigned() || y == x)
						continue;
					long[] mc = minCosts[c.num][j];
					// System.out.println("revise " + constraint + " " + variable);
					if (reviser.mustBeAppliedTo(c, y)) {
						Domain dom = y.dom;
						for (int a = dom.first(); a != -1; a = dom.next(a)) {
							if (mc[a] > 0)
								continue;
							if (!c.findArcSupportFor(j, a)) {
								mc[a] = c.cost;
								aic[y.num][a]++;
								if (y == partitionVariable)
									t[a] += c.cost;
							}
						}
					}
				}
			}
		}
	}

	@Override
	public boolean control() {
		if (!super.control())
			return false;
		for (Variable x : solver.pb.variables)
			if (!x.isAssigned())
				for (int idx = x.dom.first(); idx != -1; idx = x.dom.next(idx)) {
					int cnt = 0;
					for (Constraint c : x.ctrs)
						if (minCosts[c.num][c.positionOf(x)][idx] > 0)
							cnt++;
					Kit.control(cnt == aic[x.num][idx], () -> "aic badly initialized ");
				}
		return true;
	}
}
