/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.global;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.TagFilteringPartialAtEachCall;
import interfaces.TagGACUnguaranteed;
import problem.Problem;
import sets.SetSparse;
import sets.SetSparseReversible;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public class AllDifferentBound extends AllDifferentAbstract implements ObserverBacktrackingSystematic, TagGACUnguaranteed, TagFilteringPartialAtEachCall {

	static int nb = 0;

	int time;
	int d;

	long nDecisionsAtLastCall;

	SetSparseReversible fixedIdxs;

	BoundReasoner minReasoner;
	BoundReasoner maxReasoner;

	HallIntervalStored storer;

	int[] storedMins, storedMaxs;

	@Override
	public void restoreBefore(int depth) {
		fixedIdxs.restoreLimitAtLevel(depth);
		storer.restoreAtDepthBefore(depth);
	}

	@Override
	public void onConstructionProblemFinished() {
		super.onConstructionProblemFinished();
		fixedIdxs = new SetSparseReversible(scp[0].dom.initSize(), false, pb.variables.length + 1);
		storer = new HallIntervalStored(scp[0].dom.initSize(), pb.variables.length + 1);

	}

	class Fixed2 {
		int time;
		int cnt;
		int[] collectedVarPositions;

		Fixed2() {
			collectedVarPositions = new int[scp.length];
		}

		boolean isPresent() {
			return time == AllDifferentBound.this.time;
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
				time = AllDifferentBound.this.time;
				cnt = 0;
			}
			assert !Utilities.contains(collectedVarPositions, x, 0, cnt - 1);
			collectedVarPositions[cnt++] = x;
		}

		@Override
		public String toString() {
			return !isPresent() ? "" : "time=" + time + " cnt=" + cnt + " vars=" + Kit.join(collectedVarPositions, cnt);
		}

	}

	class Fixed1 {
		int time;
		int from;
		int to;

		final Fixed2[] edges;

		Fixed1(int possibleFrom, int possibleTo) {
			edges = IntStream.range(0, d).mapToObj(i -> possibleFrom <= i && i <= possibleTo ? new Fixed2() : null).toArray(Fixed2[]::new);
		}

		boolean isPresent() {
			return time == AllDifferentBound.this.time;
		}

		void add(int bnd, int x) {
			if (!isPresent()) {
				time = AllDifferentBound.this.time;
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
				if (fixedIdxs.isPresent(k))
					// if (isAlwaysAbsent(k))
					nb++;
			return nb;
		}

		boolean isAlwaysAbsent(int k) {
			for (int i = collectedVars.limit; i >= 0; i--)
				if (scp[collectedVars.dense[i]].dom.isPresent(k))
					return false;
			return true;

		}

		void collectAbsentBetween(int a, int b) {
			// absentIdxs.clear();
			for (int k = a; k <= b; k++)
				if (!fixedIdxs.isPresent(k) && isAlwaysAbsent(k))
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
				if (!absentIdxs.isPresent(a) && dom.removeIfPresent(a) == false)
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
								storer.add(a, b, pb.solver.depth());
								int nValuesBefore = pb.nValuesRemoved;
								for (int i = futvars.limit; i >= 0; i--) {
									int y = futvars.dense[i];
									if (!collectedVars.isPresent(y)) // if outside the hall set
										if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
											return false;
								}
								int nRemoved = pb.nValuesRemoved - nValuesBefore;
								nb += nRemoved;
								// if (nRemoved == 0)
								// System.out.println("BBBB=" + nRemoved);
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
								// note that no collected vars can be assigned (because edges only involve unfixed vars)
								if (collectedVars.size() > nVals) {
									return x.dom.fail();
								}
								if (nVals < scp.length && collectedVars.size() == nVals && !storer.matrix[a][b]) {
									storer.add(a, b, pb.solver.depth());
									int nValuesBefore = pb.nValuesRemoved;
									for (int i = futvars.limit; i >= 0; i--) {
										int y = futvars.dense[i];
										if (!collectedVars.isPresent(y)) // if outside the hall set
											if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
												return false;
									}
									int nRemoved = pb.nValuesRemoved - nValuesBefore;
									nb += nRemoved;
									// if (nRemoved == 0)
									// System.out.println("BBBB=" + nRemoved);
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
								storer.add(a, b, pb.solver.depth());
								int nValuesBefore = pb.nValuesRemoved;
								for (int i = futvars.limit; i >= 0; i--) {
									int y = futvars.dense[i];
									if (!collectedVars.isPresent(y)) // if outside the hall set
										if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
											return false;
								}
								int nRemoved = pb.nValuesRemoved - nValuesBefore;
								nb += nRemoved;
								// if (nRemoved > 0)
								// System.out.println("BBBB1=" + nRemoved);
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

								// note that no collected vars can be assigned (because edges only involve unfixed vars)
								if (collectedVars.size() > nVals) {
									return x.dom.fail();
								}
								if (nVals < scp.length && collectedVars.size() == nVals && !storer.matrix[a][b]) {
									storer.add(a, b, pb.solver.depth());
									int nValuesBefore = pb.nValuesRemoved;
									for (int i = futvars.limit; i >= 0; i--) {
										int y = futvars.dense[i];
										if (!collectedVars.isPresent(y)) // if outside the hall set
											if (scp[y].dom.size() > 1 && remove(scp[y].dom, a, b) == false)
												return false;
									}
									int nRemoved = pb.nValuesRemoved - nValuesBefore;
									nb += nRemoved;
									// if (nRemoved > 0)
									// System.out.println("BBBB2=" + nRemoved);
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
			String s = IntStream.rangeClosed(0, pb.solver.depth()).mapToObj(i -> t[i]).filter(l -> l.size() > 0).map(l -> l.toString())
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
			int a = x.dom.unique();
			if (!fixedIdxs.isPresent(a))
				fixedIdxs.add(a, pb.solver.depth());
			int v = x.dom.uniqueValue();
			for (int i = futvars.limit; i >= 0; i--) {
				Variable y = scp[futvars.dense[i]];
				if (y == x)
					continue;
				if (!y.dom.removeValueIfPresent(v))
					return false;
			}
		}
		// if (true)
		// return true;
		// System.out.println(this + ": befCalled at " + pb.solver.stats.nDecisions);
		int pos = positionOf(x);
		if (x.dom.first() == storedMins[pos] && x.dom.last() == storedMaxs[pos])
			return true;
		// boolean b = nDecisionsAtLastCall == pb.solver.stats.nDecisions;
		// if (b)
		// return true;
		// System.out.println(this + ": Called at " + pb.solver.stats.nDecisions);
		nDecisionsAtLastCall = pb.solver.stats.nDecisions;
		time++;
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
