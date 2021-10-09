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

import static utility.Kit.control;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import constraints.ConstraintGlobal;
import constraints.global.Matcher.MatcherAllDifferent;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import interfaces.Tags.TagNotAC;
import interfaces.Tags.TagSymmetric;
import problem.Problem;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Domain;
import variables.Variable;

public abstract class AllDifferent extends ConstraintGlobal implements TagSymmetric {

	/**
	 * @param vars
	 *            an array of variables
	 * @return true if one could post an AllDifferent constraint on the specified variables that would represent a
	 *         permutation
	 */
	public static final boolean isPermutationElligible(Variable... vars) {
		return vars[0].dom.initSize() == vars.length && Variable.haveSameDomainType(vars);
	}

	@Override
	public boolean isSatisfiedBy(int[] t) {
		for (int i = 0; i < t.length; i++)
			for (int j = i + 1; j < t.length; j++)
				if (t[i] == t[j])
					return false;
		return true;
	}

	public AllDifferent(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	/**********************************************************************************************
	 * AllDifferentComplete
	 *********************************************************************************************/

	public static class AllDifferentComplete extends AllDifferent implements TagAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic {

		@Override
		public void restoreBefore(int depth) {
			matcher.restoreAtDepthBefore(depth);
		}

		private Matcher matcher;

		public AllDifferentComplete(Problem pb, Variable[] scp) {
			super(pb, scp);
			this.matcher = new MatcherAllDifferent(this);
		}

		// int cnt;

		@Override
		public boolean runPropagator(Variable x) {
			// if (cnt++ % 1000 == 0)
			// System.out.println(this + " " + cnt);
			if (matcher.findMaximumMatching() == false)
				return x.dom.fail();
			matcher.removeInconsistentValues(); // no more possible failure at this step
			return true;
		}
	}

	/**********************************************************************************************
	 * AllDifferentPermutation
	 *********************************************************************************************/

	public static final class AllDifferentPermutation extends AllDifferent implements TagNotAC, ObserverOnBacktracksSystematic {

		private SetSparseReversible unfixedVars, unfixedIdxs;

		private Variable[] residues1, residues2;

		@Override
		public void restoreBefore(int depth) {
			unfixedVars.restoreLimitAtLevel(depth);
			unfixedIdxs.restoreLimitAtLevel(depth);
		}

		@Override
		public void afterProblemConstruction() {
			super.afterProblemConstruction();
			unfixedVars = new SetSparseReversible(scp.length, problem.variables.length + 1);
			unfixedIdxs = new SetSparseReversible(scp[0].dom.initSize(), problem.variables.length + 1);
		}

		private Variable findAnotherWatchedUnifxedVariable(int idx, Variable otherWatchedVariable) {
			int[] dense = unfixedVars.dense;
			for (int i = unfixedVars.limit; i >= 0; i--) {
				Variable var = scp[dense[i]];
				if (var != otherWatchedVariable && var.dom.contains(idx))
					return var;
			}
			return null;
		}

		public AllDifferentPermutation(Problem pb, Variable[] scp) {
			super(pb, scp);
			control(settings.recognizePermutations && isPermutationElligible(scp));
			residues1 = new Variable[scp[0].dom.initSize()];
			residues2 = new Variable[scp[0].dom.initSize()];
			Arrays.fill(residues1, scp[0]);
			Arrays.fill(residues2, scp[scp.length - 1]);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			int level = problem.solver.depth();
			int[] dense = unfixedVars.dense;
			for (int i = unfixedVars.limit; i >= 0; i--) {
				Variable x = scp[dense[i]];
				if (x.dom.size() == 1) {
					int a = x.dom.single();
					unfixedVars.remove(dense[i], level);
					unfixedIdxs.remove(a, level);
					for (int j = unfixedVars.limit; j >= 0; j--) {
						Variable y = scp[dense[j]];
						Domain dy = y.dom;
						if (dy.contains(a)) {
							if (!dy.remove(a))
								return false;
							if (dy.size() == 1) {
								// System.out.println("moving from " + i + " to " + (j+1));
								i = Math.max(i, j + 1); // +1 because i-- before a new iteration
							}
						}
					}
				}
				// else if (variable.domain.getCurrentSize() == 2) {
				// int first = variable.domain.getFirstValidIndex();
				// cnt++;
				// }
			}

			dense = unfixedIdxs.dense;
			for (int i = unfixedIdxs.limit; i >= 0; i--) {
				int a = dense[i];
				if (!residues1[a].dom.contains(a)) {
					Variable x = findAnotherWatchedUnifxedVariable(a, residues2[a]);
					if (x != null)
						residues1[a] = x;
					else {
						x = residues2[a];
						if (x.dom.reduceTo(a) == false)
							return false;
						unfixedVars.remove(positionOf(x), level);
						unfixedIdxs.remove(a, level);
					}
				}
				assert residues1[a].dom.size() > 1 : residues1[a] + " " + a + " " + residues1[a].dom.size();

				if (!residues2[a].dom.contains(a)) {
					Variable x = findAnotherWatchedUnifxedVariable(a, residues1[a]);
					if (x != null)
						residues2[a] = x;
					else {
						x = residues1[a];
						x.dom.reduceTo(a);
						unfixedVars.remove(positionOf(x), level);
						unfixedIdxs.remove(a, level);
					}
				}
			}
			return true;
		}
	}

	/**********************************************************************************************
	 * AllDifferentWeak
	 *********************************************************************************************/

	public static final class AllDifferentWeak extends AllDifferent implements TagNotAC { // not call filtering-complete
		private Set<Integer> set;

		private int mode = 0; // TODO hard coding

		public AllDifferentWeak(Problem problem, Variable[] scope) {
			super(problem, scope);
			set = mode == 0 ? null : new HashSet<>();
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x.dom.size() == 1) {
				int v = x.dom.singleValue();
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (y != x && y.dom.removeValueIfPresent(v) == false)
						return false;
				}
			}
			if (set == null)
				return true;
			set.clear();
			int nPastVariables = scp.length - futvars.size();
			for (int i = futvars.limit; i >= 0; i--) {
				Domain dom = scp[futvars.dense[i]].dom;
				for (int a = dom.first(); a != -1; a = dom.next(a))
					set.add(dom.toVal(a));
				if (nPastVariables + set.size() >= scp.length)
					return true;
			}
			return nPastVariables + set.size() >= scp.length;
		}

	}

	public static class AllDifferentExceptWeak extends AllDifferent implements TagNotAC { // not call filtering-complete

		@Override
		public boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < t.length; i++) {
				if (Utilities.indexOf(t[i], exceptValues) != -1)
					continue;
				for (int j = i + 1; j < t.length; j++)
					if (t[i] == t[j])
						return false;
			}
			return true;
		}

		private int[] exceptValues;

		public AllDifferentExceptWeak(Problem pb, Variable[] scp, int[] exceptValues) {
			super(pb, scp);
			this.exceptValues = exceptValues;
			defineKey(exceptValues);
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x.dom.size() == 1) {
				int v = x.dom.singleValue();
				if (Utilities.indexOf(v, exceptValues) != -1)
					return true;
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (y != x && y.dom.removeValueIfPresent(v) == false)
						return false;
				}
			}
			return true;
		}
	}

	/**********************************************************************************************
	 * AllDifferentCounting (Experimental)
	 *********************************************************************************************/

	public static final class AllDifferentCounting extends AllDifferent implements TagNotAC, TagCallCompleteFiltering, ObserverOnBacktracksSystematic {

		@Override
		public void restoreBefore(int depth) {
			unfixedVars.restoreLimitAtLevel(depth);
		}

		@Override
		public void afterProblemConstruction() {
			super.afterProblemConstruction();
			unfixedVars = new SetSparseReversible(scp.length, problem.variables.length + 1);
		}

		private SetSparse[] sets;
		private SetSparse workingDomSet;
		private SetSparse workingVarSet;
		private SetSparse encounteredSizes;

		private SetSparseReversible unfixedVars;

		public AllDifferentCounting(Problem pb, Variable[] scp) {
			super(pb, scp);
			control(Variable.haveSameDomainType(scp) && scp[0].dom.initSize() < 1000); // current use restrictions
			sets = IntStream.range(0, scp[0].dom.initSize() + 1).mapToObj(i -> new SetSparse(scp.length)).toArray(SetSparse[]::new);
			workingDomSet = new SetSparse(scp[0].dom.initSize());
			workingVarSet = new SetSparse(scp.length);
			encounteredSizes = new SetSparse(scp[0].dom.initSize() + 1);
		}

		@Override
		public boolean runPropagator(Variable dummy) {
			for (int i = 0; i < encounteredSizes.size(); i++)
				sets[encounteredSizes.dense[i]].clear();
			control(Stream.of(sets).allMatch(s -> s.isEmpty())); // TODO to be changed in assert
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
				int vapFixed = sets[1].dense[i];
				Variable x = scp[vapFixed];
				int v = x.dom.singleValue();
				for (int j = futvars.limit; j >= 0; j--) {
					Variable y = scp[futvars.dense[j]];
					if (y == x)
						continue;
					if (!y.dom.removeValueIfPresent(v))
						return false;
				}
				unfixedVars.remove(vapFixed, problem.solver.depth());
			}
			workingDomSet.clear();
			workingVarSet.clear();
			// displaySizes();

			// for (int i = 0; i < sets[2].getSize(); i++) {
			// int vapi = sets[2].get(i);
			// int idx1 = scp[vapi].dom.getFirstIdx();
			// int idx2 = scp[vapi].dom.getLastIdx();
			// for (int j = i + 1; j < sets[2].getSize(); j++) {
			// int vapj = sets[2].get(j);
			// Domain domy = scp[vapj].dom;
			// if (domy.isPresentIdx(idx1) && domy.isPresentIdx(idx2)) {
			// for (int k = unfixedVariables.getLimit(); k >= 0; k--) {
			// int vap = unfixedVariables.get(k);
			// if (vap != vapi && vap != vapj)
			// if (scp[vap].dom.removeIdx(idx1, false) == false || scp[vap].dom.removeIdx(idx2, false) == false)
			// return false;
			//
			// }
			//
			// }
			//
			// }
			// }
			for (int i = 2; i < sets.length; i++) { // traversal to be improved TODO
				for (int j = sets[i].limit; j >= 0; j--) {
					int vap = sets[i].dense[j];
					workingVarSet.add(vap);
					Domain dom = scp[vap].dom;

					for (int idx = dom.first(); idx != -1; idx = dom.next(idx)) {
						// Kit.prn("idx=" +idx);
						workingDomSet.add(idx);
					}

					if (workingDomSet.size() < workingVarSet.size())
						return false;
					if (workingDomSet.size() == workingVarSet.size()) {
						for (int k = workingVarSet.limit + 1; k < workingVarSet.capacity(); k++)
							if (scp[workingVarSet.dense[k]].dom.remove(workingDomSet, true) == false)
								return false;
					}
					if (workingDomSet.size() > unfixedVars.size())
						return true;
				}
			}
			return true;
		}

		void displaySizes() {
			String s = IntStream.range(2, sets.length).filter(i -> sets[i].size() != 0).mapToObj(i -> i + ":" + sets[i].size())
					.collect(Collectors.joining(" "));
			Kit.log.info(s);
		}
	}

	/**********************************************************************************************
	 * AllDifferentBound (Experimental)
	 *********************************************************************************************/

	public static final class AllDifferentBound extends AllDifferent implements ObserverOnBacktracksSystematic, TagNotAC { // not
																															// call
																															// filtering-complete

		@Override
		public void restoreBefore(int depth) {
			fixedIdxs.restoreLimitAtLevel(depth);
			storer.restoreAtDepthBefore(depth);
		}

		@Override
		public void afterProblemConstruction() {
			super.afterProblemConstruction();
			fixedIdxs = new SetSparseReversible(scp[0].dom.initSize(), problem.variables.length + 1, false);
			storer = new HallIntervalStored(scp[0].dom.initSize(), problem.variables.length + 1);

		}

		int timing; // because time exists in Constraint
		int d;

		long nDecisionsAtLastCall;

		SetSparseReversible fixedIdxs;

		BoundReasoner minReasoner;
		BoundReasoner maxReasoner;

		HallIntervalStored storer;

		int[] storedMins, storedMaxs;

		class Fixed2 {
			int ftime;
			int cnt;
			int[] collectedVarPositions;

			Fixed2() {
				collectedVarPositions = new int[scp.length];
			}

			boolean isPresent() {
				return ftime == AllDifferentBound.this.timing;
			}

			void addCollectedVarsToSet(SetSparse set) {
				for (int i = 0; i < cnt; i++)
					set.add(collectedVarPositions[i]);
			}

			// boolean isAlwaysAbsent(int k) {
			// for (int i = 0; i < cnt; i++)
			// if (scp[collectedVarPositions[i]].dom.isPresent(k))
			// return false;
			// return true;
			// }

			void add(int x) {
				if (!isPresent()) {
					ftime = AllDifferentBound.this.timing;
					cnt = 0;
				}
				assert !Utilities.contains(collectedVarPositions, x, 0, cnt - 1);
				collectedVarPositions[cnt++] = x;
			}

			@Override
			public String toString() {
				return !isPresent() ? "" : "time=" + ftime + " cnt=" + cnt + " vars=" + Kit.join(collectedVarPositions, cnt);
			}

		}

		class Fixed1 {
			int ftime;
			int from;
			int to;

			final Fixed2[] edges;

			Fixed1(int possibleFrom, int possibleTo) {
				edges = IntStream.range(0, d).mapToObj(i -> possibleFrom <= i && i <= possibleTo ? new Fixed2() : null).toArray(Fixed2[]::new);
			}

			boolean isPresent() {
				return ftime == AllDifferentBound.this.timing;
			}

			void add(int bnd, int x) {
				if (!isPresent()) {
					ftime = AllDifferentBound.this.timing;
					from = scp.length;
					to = -1;
				}
				if (bnd < from)
					from = bnd;
				if (bnd > to)
					to = bnd;
				edges[bnd].add(x);
			}

			@Override
			public String toString() {
				return !isPresent() ? ""
						: "from=" + from + " to=" + to + "\n\t" + IntStream.rangeClosed(from, to).filter(i -> edges[i].isPresent())
								.mapToObj(i -> i + ": " + edges[i]).collect(Collectors.joining("\n\t"));
			}
		}

		abstract class BoundReasoner {
			SetSparse collectedVars;
			SetSparse absentIdxs;

			final Fixed1[] fixed1;

			int from, to;

			BoundReasoner() {
				this.collectedVars = new SetSparse(scp.length);
				this.absentIdxs = new SetSparse(scp.length);
				this.fixed1 = new Fixed1[d];
				if (this instanceof MinBoundReasoner)
					IntStream.range(0, d - 1).forEach(i -> fixed1[i] = new Fixed1(i + 1, d - 1));
				else
					IntStream.range(1, d).forEach(i -> fixed1[i] = new Fixed1(0, i - 1));
			}

			void initialize() {
				from = scp.length;
				to = -1;
				for (int i = futvars.limit; i >= 0; i--) {
					int x = futvars.dense[i];
					if (scp[x].dom.size() == 1)
						continue;
					int first = scp[x].dom.first(), last = scp[x].dom.last();
					int a = this instanceof MinBoundReasoner ? first : last;
					int b = a == first ? last : first;
					if (a < from)
						from = a;
					if (a > to)
						to = a;
					fixed1[a].add(b, x);
				}
			}

			int nFixedBetween(int a, int b) {
				int nb = 0;
				for (int k = a; k <= b; k++)
					if (fixedIdxs.contains(k))
						// if (isAlwaysAbsent(k))
						nb++;
				return nb;
			}

			boolean isAlwaysAbsent(int k) {
				for (int i = collectedVars.limit; i >= 0; i--)
					if (scp[collectedVars.dense[i]].dom.contains(k))
						return false;
				return true;

			}

			void collectAbsentBetween(int a, int b) {
				// absentIdxs.clear();
				for (int k = a; k <= b; k++)
					if (!fixedIdxs.contains(k) && isAlwaysAbsent(k))
						absentIdxs.add(k);
			}

			abstract boolean findIntervals(Variable x);

			@Override
			public String toString() {
				return "minToMax=" + (this instanceof MinBoundReasoner) + " from=" + from + " to=" + to + "\n" + IntStream.rangeClosed(from, to)
						.filter(i -> fixed1[i].isPresent()).mapToObj(i -> i + "-> " + fixed1[i]).collect(Collectors.joining("\n\n"));
			}

			boolean remove(Domain dom, int from, int to) {
				for (int a = from; a <= to; a++)
					if (!absentIdxs.contains(a) && dom.removeIfPresent(a) == false)
						return false;
				return true;
			}

		}

		class MinBoundReasoner extends BoundReasoner {
			@Override
			boolean findIntervals(Variable x) {
				for (int a = to; a >= from; a--) {
					Fixed1 f1 = fixed1[a];
					if (f1.isPresent()) {
						collectedVars.clear();
						int nFixed = 0;
						int start = a;
						for (int b = f1.from; b <= f1.to; b++) {
							Fixed2 edge = f1.edges[b];
							if (edge.isPresent()) {
								edge.addCollectedVarsToSet(collectedVars);
								nFixed += nFixedBetween(start, b);
								start = b + 1;
								absentIdxs.clear();
								// collectAbsentBetween(a, b);
								int nVals = (b - a + 1) - nFixed - absentIdxs.size();

								// note that no collected vars can be assigned (because edges only involve unfixed vars)
								if (collectedVars.size() > nVals) {
									return x.dom.fail();
								}
								if (nVals < scp.length && collectedVars.size() == nVals && !storer.matrix[a][b]) {
									storer.add(a, b, problem.solver.depth());
									int nValuesBefore = problem.nValueRemovals;
									for (int i = futvars.limit; i >= 0; i--) {
										int y = futvars.dense[i];
										if (!collectedVars.contains(y)) // if outside the hall set
											if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
												return false;
									}
									int nRemoved = problem.nValueRemovals - nValuesBefore;
								}
							}
						}
						int nV = (f1.to - a + 1) - nFixed - absentIdxs.size();
						if (nV + 1 < collectedVars.size())
							continue;
						int b = f1.to;
						for (int aa = a + 1; aa < b; aa++) {
							f1 = fixed1[aa];
							if (f1.isPresent()) {
								Fixed2 edge = f1.edges[b];
								if (edge.isPresent()) {
									edge.addCollectedVarsToSet(collectedVars);
									absentIdxs.clear();
									collectAbsentBetween(a, b);
									int nVals = (b - a + 1) - nFixed - absentIdxs.size();
									// note that no collected vars can be assigned (because edges only involve unfixed
									// vars)
									if (collectedVars.size() > nVals) {
										return x.dom.fail();
									}
									if (nVals < scp.length && collectedVars.size() == nVals && !storer.matrix[a][b]) {
										storer.add(a, b, problem.solver.depth());
										int nValuesBefore = problem.nValueRemovals;
										for (int i = futvars.limit; i >= 0; i--) {
											int y = futvars.dense[i];
											if (!collectedVars.contains(y)) // if outside the hall set
												if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
													return false;
										}
										int nRemoved = problem.nValueRemovals - nValuesBefore;
									}
								}
							}
						}

					}
				}
				return true;
			}
		}

		class MaxBoundReasoner extends BoundReasoner {
			@Override
			boolean findIntervals(Variable x) {
				for (int b = from; b <= to; b++) {
					Fixed1 f1 = fixed1[b];
					if (f1.isPresent()) {
						collectedVars.clear();
						int nFixed = 0;
						int end = b;
						for (int a = f1.to; a >= f1.from; a--) {
							assert a < b;
							Fixed2 edge = f1.edges[a];
							if (edge.isPresent()) {
								edge.addCollectedVarsToSet(collectedVars);
								nFixed += nFixedBetween(a, end);
								end = a - 1;
								absentIdxs.clear();
								// collectAbsentBetween(a, b);
								int nVals = (b - a + 1) - nFixed - absentIdxs.size();

								if (collectedVars.size() > nVals) {
									return x.dom.fail();
								}
								if (nVals < scp.length && collectedVars.size() == nVals && !storer.matrix[a][b]) {
									storer.add(a, b, problem.solver.depth());
									int nValuesBefore = problem.nValueRemovals;
									for (int i = futvars.limit; i >= 0; i--) {
										int y = futvars.dense[i];
										if (!collectedVars.contains(y)) // if outside the hall set
											if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
												return false;
									}
									int nRemoved = problem.nValueRemovals - nValuesBefore;
								}

							}
						}
						int nV = (b - f1.from + 1) - nFixed - absentIdxs.size();
						if (nV + 1 < collectedVars.size())
							continue;
						int a = f1.from;
						for (int bb = b - 1; bb > a; bb--) {
							f1 = fixed1[bb];
							if (f1.isPresent()) {
								Fixed2 edge = f1.edges[a];
								if (edge.isPresent()) {
									edge.addCollectedVarsToSet(collectedVars);
									absentIdxs.clear();
									collectAbsentBetween(a, b);
									int nVals = (b - a + 1) - nFixed - absentIdxs.size();

									// note that no collected vars can be assigned (because edges only involve unfixed
									// vars)
									if (collectedVars.size() > nVals) {
										return x.dom.fail();
									}
									if (nVals < scp.length && collectedVars.size() == nVals && !storer.matrix[a][b]) {
										storer.add(a, b, problem.solver.depth());
										int nValuesBefore = problem.nValueRemovals;
										for (int i = futvars.limit; i >= 0; i--) {
											int y = futvars.dense[i];
											if (!collectedVars.contains(y)) // if outside the hall set
												if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
													return false;
										}
										int nRemoved = problem.nValueRemovals - nValuesBefore;
									}
								}
							}
						}

					}
				}
				return true;
			}
		}

		class HallIntervalStored {
			boolean[][] matrix;

			ArrayList<Integer>[] t;

			void restoreAtDepthBefore(int depth) {
				ArrayList<Integer> list = t[depth];
				for (int i = 0; i < list.get(0); i++) {
					assert matrix[list.get(i * 2 + 1)][list.get(i * 2 + 2)] == true;
					matrix[list.get(i * 2 + 1)][list.get(i * 2 + 2)] = false;
				}
				list.clear();
				list.add(0);
			}

			HallIntervalStored(int d, int nLevels) {
				matrix = new boolean[d][d];
				t = IntStream.range(0, nLevels).mapToObj(i -> new ArrayList<>(Arrays.asList(0))).toArray(ArrayList[]::new);
			}

			void add(int a, int b, int level) {
				assert matrix[a][b] == false;
				matrix[a][b] = true;
				ArrayList<Integer> list = t[level];
				list.set(0, list.get(0) + 1);
				list.add(a);
				list.add(b);
			}

			@Override
			public String toString() {
				String s = IntStream.rangeClosed(0, problem.solver.depth()).mapToObj(i -> t[i]).filter(l -> l.size() > 0).map(l -> l.toString())
						.collect(Collectors.joining(" "));
				return s;
			}

		}

		public AllDifferentBound(Problem pb, Variable[] scp) {
			super(pb, scp);
			Kit.control(Variable.haveSameDomainType(scp));
			d = scp[0].dom.initSize();
			minReasoner = new MinBoundReasoner();
			maxReasoner = new MaxBoundReasoner();
			storedMins = Stream.of(scp).mapToInt(x -> x.dom.first()).toArray();
			storedMaxs = Stream.of(scp).mapToInt(x -> x.dom.last()).toArray();
		}

		@Override
		public boolean runPropagator(Variable x) {
			if (x.dom.size() == 1) {
				int a = x.dom.single();
				if (!fixedIdxs.contains(a))
					fixedIdxs.add(a, problem.solver.depth());
				int v = x.dom.singleValue();
				for (int i = futvars.limit; i >= 0; i--) {
					Variable y = scp[futvars.dense[i]];
					if (y == x)
						continue;
					if (!y.dom.removeValueIfPresent(v))
						return false;
				}
			}
			int pos = positionOf(x);
			if (x.dom.first() == storedMins[pos] && x.dom.last() == storedMaxs[pos])
				return true;
			// boolean b = nDecisionsAtLastCall == pb.solver.stats.nDecisions;
			// if (b)
			// return true;
			// System.out.println(this + ": Called at " + pb.solver.stats.nDecisions);
			nDecisionsAtLastCall = problem.solver.stats.nDecisions;
			timing++;
			minReasoner.initialize();
			maxReasoner.initialize();

			// System.out.println("\n----\nTIME = " + time);
			// System.out.println(minReasoner);
			// // System.out.println(maxReasoner);
			// for (Variable y : scp)
			// y.display(false);
			// System.out.println("Fixed=" + fixedIdxs);
			if (minReasoner.findIntervals(x) == false)
				return false;
			if (maxReasoner.findIntervals(x) == false)
				return false;
			for (int i = futvars.limit; i >= 0; i--) {
				int y = futvars.dense[i];
				storedMins[y] = scp[y].dom.first();
				storedMaxs[y] = scp[y].dom.last();
			}
			// System.out.println("NB=" + nb);
			return true;
		}

	}

}
