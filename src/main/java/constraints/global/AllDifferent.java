/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static java.util.stream.Collectors.joining;
import static utility.Kit.control;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import constraints.global.Matcher.MatcherAllDifferent;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagPostponableFiltering;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This constraint AllDifferent ensures that all values assigned to the variables of its scope are all different. This class is the root class of several
 * filtering algorithms for the constraint AllDifferent.
 * 
 * @author Christophe Lecoutre and Vincent Perradin (for the complete algorithm)
 */
public abstract class AllDifferent extends ConstraintGlobal implements TagSymmetric {

	@Override
	public boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < t.length; i++)
			for (int j = i + 1; j < t.length; j++)
				if (t[i] == t[j])
					return false;
		return true;
	}

	/**
	 * Builds a constraint AllDifferent for the specified problem
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public AllDifferent(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 2);
	}

	/**********************************************************************************************
	 * AllDifferentComplete
	 *********************************************************************************************/

	/**
	 * A complete filtering algorithm enforcing (G)AC.
	 * 
	 * @author Vincent Perradin
	 */
	public static class AllDifferentComplete extends AllDifferent
			implements TagAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic, TagPostponableFiltering {

		@Override
		public void restoreBefore(int depth) {
			matcher.restoreAtDepthBefore(depth);
		}

		/**
		 * The object used to compute a maximal matching, and to delete inconsistent values
		 */
		private final Matcher matcher;

		public AllDifferentComplete(Problem pb, Variable[] scp) {
			super(pb, scp);
			this.matcher = new MatcherAllDifferent(this);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (matcher.findMaximumMatching() == false)
				return x.dom.fail();
			matcher.removeInconsistentValues(); // no more possible failure at this step
			return true;
		}
	}

	/**********************************************************************************************
	 * AllDifferentPermutation
	 *********************************************************************************************/

	/**
	 * A specific filtering algorithm for permutations (the number of values is equal to the number of variables).
	 */
	public static final class AllDifferentPermutation extends AllDifferent implements TagNotAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic {

		/**
		 * @param vars
		 *            an array of variables
		 * @return true if any instantiation with different values on the specified variables represents a permutation
		 */
		public static final boolean isElligible(Variable... vars) {
			return vars[0].dom.initSize() == vars.length && Variable.haveSameDomainType(vars);
		}

		@Override
		public void afterProblemConstruction(int n) {
			super.afterProblemConstruction(n);
			this.unfixedVars = new SetSparseReversible(scp.length, n + 1);
			this.unfixedIdxs = new SetSparseReversible(scp[0].dom.initSize(), n + 1);
		}

		@Override
		public void restoreBefore(int depth) {
			unfixedVars.restoreLimitAtLevel(depth);
			unfixedIdxs.restoreLimitAtLevel(depth);
		}

		private SetSparseReversible unfixedVars, unfixedIdxs;

		private Variable[] sentinels1, sentinels2;

		public AllDifferentPermutation(Problem pb, Variable[] scp) {
			super(pb, scp);
			control(pb.head.control.global.permutation && isElligible(scp));
			int d = scp[0].dom.initSize();
			// scp[0] and scp[-1] are the sentinels that are set arbitrarily initially
			this.sentinels1 = IntStream.range(0, d).mapToObj(a -> scp[0]).toArray(Variable[]::new);
			this.sentinels2 = IntStream.range(0, d).mapToObj(a -> scp[scp.length - 1]).toArray(Variable[]::new);
		}

		private Variable findSentinel(int a, Variable otherSentinel) {
			for (int i = unfixedVars.limit; i >= 0; i--) {
				Variable x = scp[unfixedVars.dense[i]];
				if (x != otherSentinel && x.dom.contains(a))
					return x;
			}
			return null;
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int depth = problem.solver.depth();
			int[] dense = unfixedVars.dense;
			for (int i = unfixedVars.limit; i >= 0; i--) {
				Domain dx = scp[dense[i]].dom;
				if (dx.size() == 1) {
					int a = dx.single();
					unfixedVars.remove(dense[i], depth);
					unfixedIdxs.remove(a, depth);
					for (int j = unfixedVars.limit; j >= 0; j--) {
						Domain dy = scp[dense[j]].dom;
						if (dy.contains(a)) {
							if (dy.remove(a) == false)
								return false;
							if (dy.size() == 1)
								i = Math.max(i, j + 1); // +1 because i-- before a new iteration
						}
					}
				}
				// to do something if x.dom.size() == 2 ?
			}

			for (int i = unfixedIdxs.limit; i >= 0; i--) {
				int a = unfixedIdxs.dense[i];
				if (!sentinels1[a].dom.contains(a)) {
					Variable x = findSentinel(a, sentinels2[a]);
					if (x != null)
						sentinels1[a] = x;
					else {
						x = sentinels2[a];
						if (x.dom.reduceTo(a) == false)
							return false;
						unfixedVars.remove(positionOf(x), depth);
						unfixedIdxs.remove(a, depth);
					}
				}
				assert sentinels1[a].dom.size() > 1 : sentinels1[a] + " " + a + " " + sentinels1[a].dom.size();
				if (!sentinels2[a].dom.contains(a)) {
					Variable x = findSentinel(a, sentinels1[a]);
					if (x != null)
						sentinels2[a] = x;
					else {
						x = sentinels1[a];
						x.dom.reduceTo(a);
						unfixedVars.remove(positionOf(x), depth);
						unfixedIdxs.remove(a, depth);
					}
				}
			}
			return true;
		}
	}

	/**********************************************************************************************
	 * AllDifferentWeak and AllDifferentExceptWeak
	 *********************************************************************************************/

	public static class AllDifferentWeak extends AllDifferent implements TagNotAC { // not call filtering-complete

		/**
		 * A temporary set used to collect values, during filtering
		 */
		private Set<Integer> values;

		public AllDifferentWeak(Problem pb, Variable[] scp, boolean stronger) {
			super(pb, scp);
			this.values = stronger ? new LinkedHashSet<>() : null;
		}

		public AllDifferentWeak(Problem pb, Variable[] scp) {
			this(pb, scp, false);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x.dom.size() == 1) {
				// ensures basic filtering (like a clique of binary constraints)
				int v = x.dom.singleValue();
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (y != x && y.dom.removeValueIfPresent(v) == false)
						return false;
				}
			}
			if (values == null)
				return true;
			// checking trivial inconsistency (less values than variables)
			values.clear();
			int nPastVariables = scp.length - futvars.size();
			for (int i = futvars.limit; i >= 0; i--) {
				Domain dom = scp[futvars.dense[i]].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a))
					values.add(dom.toVal(a));
				if (nPastVariables + values.size() >= scp.length)
					return true;
			}
			return x.dom.fail();
		}

	}

	public static final class AllDifferentExceptWeak extends AllDifferent implements TagNotAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic {

		@Override
		public void afterProblemConstruction(int n) {
			super.afterProblemConstruction(n);
			this.treated = new SetSparseReversible(scp.length, n + 1, false);
		}

		@Override
		public void restoreBefore(int depth) {
			treated.restoreLimitAtLevel(depth);
		}

		@Override
		public boolean isSatisfiedBy(int[] t) {
			if (exceptValues == null)
				return super.isSatisfiedBy(t);
			for (int i = 0; i < t.length; i++) {
				if (Utilities.indexOf(t[i], exceptValues) != -1)
					continue;
				for (int j = i + 1; j < t.length; j++)
					if (t[i] == t[j])
						return false;
			}
			return true;
		}

		/**
		 * The values that must be ignored
		 */
		private int[] exceptValues;

		/**
		 * A temporary set used to collect values, during filtering
		 */
		private Set<Integer> values;

		private SetSparseReversible treated;

		private boolean stronger;

		public AllDifferentExceptWeak(Problem pb, Variable[] scp, int[] exceptValues, boolean stronger) {
			super(pb, scp);
			control(exceptValues == null || exceptValues.length > 0);
			this.exceptValues = exceptValues;
			this.values = new LinkedHashSet<>();
			this.stronger = stronger;
			if (exceptValues != null)
				defineKey(exceptValues);
		}

		@Override
		public boolean runPropagator(Variable x) {
			int depth = problem.solver.depth();
			values.clear();
			if (x.assigned() && !treated.contains(positionOf(x)) && (exceptValues == null || Utilities.indexOf(x.dom.singleValue(), exceptValues) == -1)) {
				values.add(x.dom.singleValue());
				treated.add(positionOf(x), depth);
			}
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (y.dom.size() == 1 && !treated.contains(positionOf(y))
						&& (exceptValues == null || Utilities.indexOf(y.dom.singleValue(), exceptValues) == -1)) {
					if (values.contains(y.dom.singleValue()))
						return y.dom.fail();
					values.add(y.dom.singleValue());
					treated.add(positionOf(y), depth);
				}
			}
			if (values.size() > 0) {
				// ensures basic filtering (like a clique of binary constraints)
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (y.dom.size() > 1 && y.dom.removeValuesIn(values) == false)
						return false;
				}
			}
			if (!stronger)
				return true;
			// checking trivial inconsistency (less values than variables)
			values.clear();
			int nPastVariables = scp.length - futvars.size();
			if (exceptValues != null)
				for (int i = futvars.limit + 1; i < scp.length; i++) // past variables
					if (Utilities.indexOf(scp[futvars.dense[i]].dom.singleValue(), exceptValues) != -1)
						nPastVariables--; // because assigned to an ignored value
			for (int i = futvars.limit; i >= 0; i--) {
				Domain dom = scp[futvars.dense[i]].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a)) {
					int v = dom.toVal(a);
					if (exceptValues == null || Utilities.indexOf(v, exceptValues) == -1)
						values.add(v);
				}
				if (nPastVariables + values.size() >= scp.length)
					return true;
			}
			return x.dom.fail();
		}
	}

	/**********************************************************************************************
	 * AllDifferentCounting (Experimental)
	 *********************************************************************************************/

	public static final class AllDifferentCounting extends AllDifferent implements TagNotAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic {

		@Override
		public void afterProblemConstruction(int n) {
			super.afterProblemConstruction(n);
			unfixedVars = new SetSparseReversible(scp.length, n + 1);
		}

		@Override
		public void restoreBefore(int depth) {
			unfixedVars.restoreLimitAtLevel(depth);
		}

		private SetSparse[] sets;
		private SetSparse workingDomSet;
		private SetSparse workingVarSet;
		private SetSparse encounteredSizes;

		private SetSparseReversible unfixedVars;

		public AllDifferentCounting(Problem pb, Variable[] scp) {
			super(pb, scp);
			control(Variable.haveSameDomainType(scp) && scp[0].dom.initSize() < 1000); // hard coding
			this.sets = IntStream.range(0, scp[0].dom.initSize() + 1).mapToObj(i -> new SetSparse(scp.length)).toArray(SetSparse[]::new);
			this.workingDomSet = new SetSparse(scp[0].dom.initSize());
			this.workingVarSet = new SetSparse(scp.length);
			this.encounteredSizes = new SetSparse(scp[0].dom.initSize() + 1);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			for (int i = 0; i < encounteredSizes.size(); i++)
				sets[encounteredSizes.dense[i]].clear();
			assert Stream.of(sets).allMatch(s -> s.isEmpty());
			encounteredSizes.clear();

			// we first filter future (i.e., non explicitly assigned) variables wrt new fixed (i.e., domain-singleton)
			// variables
			for (int i = unfixedVars.limit; i >= 0; i--) {
				int p = unfixedVars.dense[i];
				if (scp[p].dom.size() > 1)
					continue;
				Variable x = scp[p];
				int v = x.dom.singleValue();
				for (int j = futvars.limit; j >= 0; j--) {
					Variable y = scp[futvars.dense[j]];
					if (y != x && y.dom.removeValueIfPresent(v) == false)
						return false;
				}
				unfixedVars.remove(p, problem.solver.depth());
			}

			// sort variables
			for (int i = unfixedVars.limit; i >= 0; i--) {
				int p = unfixedVars.dense[i];
				sets[scp[p].dom.size()].add(p);
				encounteredSizes.add(scp[p].dom.size());
			}
			control(sets[0].isEmpty());

			for (int i = sets[1].limit; i >= 0; i--) { // TODO try to manage all new fixed variables
				int p = sets[1].dense[i];
				Variable x = scp[p];
				int v = x.dom.singleValue();
				for (int j = futvars.limit; j >= 0; j--) {
					Variable y = scp[futvars.dense[j]];
					if (y == x)
						continue;
					if (!y.dom.removeValueIfPresent(v))
						return false;
				}
				unfixedVars.remove(p, problem.solver.depth());
			}
			workingDomSet.clear();
			workingVarSet.clear();
			// displaySizes();

			for (int i = sets[2].limit; i >= 0; i--) {
				int x = sets[2].dense[i];
				int v = scp[x].dom.firstValue(), w = scp[x].dom.lastValue();
				for (int j = i - 1; j >= 0; j--) {
					int y = sets[2].dense[j];
					if (scp[y].dom.containsValue(v) && scp[y].dom.containsValue(w)) {
						for (int k = unfixedVars.limit; k >= 0; k--) {
							int z = unfixedVars.dense[k];
							if (z != x && z != y)
								if (scp[z].dom.removeValueIfPresent(v) == false || scp[z].dom.removeValueIfPresent(w) == false)
									return false;
						}
					}
				}
			}
			for (int i = 2; i < sets.length; i++) { // traversal to be improved TODO
				for (int j = sets[i].limit; j >= 0; j--) {
					int x = sets[i].dense[j];
					workingVarSet.add(x);
					Domain dom = scp[x].dom;
					for (int a = dom.first(); a != -1; a = dom.next(a))
						workingDomSet.add(a); // dom.toVal(a));
					if (workingDomSet.size() < workingVarSet.size())
						return false;
					if (workingDomSet.size() == workingVarSet.size()) {
						for (int k = workingVarSet.limit + 1; k < workingVarSet.capacity(); k++)
							if (scp[workingVarSet.dense[k]].dom.remove(workingDomSet, true) == false) // removeValuesIn(workingDomSet) == false)
								return false;
					}
					if (workingDomSet.size() > unfixedVars.size())
						return true;
				}
			}
			return true;
		}

		void displaySizes() {
			Kit.log.info(IntStream.range(2, sets.length).filter(i -> sets[i].size() != 0).mapToObj(i -> i + ":" + sets[i].size()).collect(joining(" ")));
		}
	}

}
