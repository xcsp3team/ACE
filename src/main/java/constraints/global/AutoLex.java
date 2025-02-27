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

import constraints.ConstraintGlobal;
import interfaces.Tags;
import interfaces.Tags.TagNotSymmetric;
import interfaces.Tags.TagPostponableFiltering;
import org.xcsp.common.Utilities;
import problem.Problem;
import propagation.AC;
import variables.Domain;
import variables.Variable;

import java.util.Arrays;
import java.util.stream.IntStream;

import static org.xcsp.common.predicates.XNodeParent.*;
import static utility.Kit.control;

/**
 * Implements an AutoLex / Lyndon words constraint on a list of binary variables
 * @author Guillaume Derval
 */
public class AutoLex {
	/**
	 * This field indicates if the ordering between the two lists must be strictly respected; if true then we have to
	 * enforce <= (le), otherwise we have to enforce < (lt)
	 */
	protected final boolean strictOrdering;

	protected Problem problem;
	protected Variable[] scp;
	//private int cutSinceBeginning = 0;
	private final long[][][][] innerlexTime;
	private final int[][] forcedPairsQueue;
	private int nForcedPairs;

	private final int[] additionalPattern;
	private final int[] forbiddenPattern;

	private final long ALWAYS_TRUE = -10;

    public AutoLex(Problem pb, Variable[] scp, int[] additionalPattern, boolean strictOrdering) {
		this.problem = pb;
		this.scp = scp;
		this.strictOrdering = strictOrdering;

		// NB: this assumes that the variables are all binary!
		// for non-binary inputs we will be better off with a HashSet.
		innerlexTime = new long[scp.length][2][scp.length][2];
		forcedPairsQueue = new int[scp.length][2];
		nForcedPairs = 0;

		if(strictOrdering)
			problem.intension(lt(scp[0], scp[scp.length-1]));
		else
			problem.intension(le(scp[0], scp[scp.length-1]));

		for	(int l = 2; l < scp.length; l++) {
			Variable[] list1 = Arrays.stream(scp).limit(l).toArray(Variable[]::new);
			Variable[] list2 = Arrays.stream(scp).skip(scp.length-l).limit(l).toArray(Variable[]::new);

			LexicographicVar sublex = new LexicographicVar(pb, list1, list2);
			pb.post(sublex);
		}

		control(additionalPattern[0] == 0, "the pattern must always begin with 0");
		for(int i = 0; i < additionalPattern.length; i++) {
			control(additionalPattern[i] >= 0, "negative pattern is forbidden");
			control(additionalPattern[i] < scp.length, "pattern loops");
			if (i != additionalPattern.length - 1)
				control(additionalPattern[i] < additionalPattern[i+1], "pattern must be ordered");
		}
		this.additionalPattern = additionalPattern;
		this.forbiddenPattern = computeForbiddenPattern();

		System.out.println(Arrays.toString(forbiddenPattern));
		for(int i = 0; i < scp.length; i++) {
			for(int j: forbiddenPattern) {
				ensureNeed(i, 1, (i + j) % scp.length, 0, ALWAYS_TRUE);
			}
		}
	}

	private int[] computeForbiddenPattern() {
		boolean[] used = new boolean[scp.length];
		int[] forbidden = new int[scp.length];
		int fLength = 0;
        for (int j : additionalPattern) used[j] = true;
		for(int i = 1; i < scp.length; i++)
			for (int j : additionalPattern)
				if(used[(i+j) % scp.length]) {
					forbidden[fLength] = i;
					fLength += 1;
					break;
				}
		return Arrays.stream(forbidden).limit(fLength).toArray();
	}

	/**
	 * Empty the inner propagation queue. Must be done after each of the subconstraints have been run.
	 * We maintain this queue separately to avoid interacting with the subconstraint while they propagate.
	 * @return false if the node is infeasible
	 */
	protected boolean emptyQueue() {
		for(int i = 0; i < nForcedPairs; i++) {
			int var = forcedPairsQueue[i][0];
			int val = forcedPairsQueue[i][1];
			//if(scp[var].dom.containsValue(1-val)) {
			//	cutSinceBeginning += 1;
			//	System.out.println("CUTS SINCE BEGINNING: " + cutSinceBeginning);
			//}
			if (!scp[var].dom.removeValueIfPresent(1-val))
				return false;
		}
		nForcedPairs = 0;
		return true;
	}

	private boolean clauseIsSet(int var1, int val1, int var2, int val2, long nodeNumber) {
		return innerlexTime[var1][val1][var2][val2] == nodeNumber || innerlexTime[var1][val1][var2][val2] == ALWAYS_TRUE;
	}

	/**
	 * ensures var1 = val1 OR var2 = val2
	 */
	private void insert2Clause(int var1, int val1, int var2, int val2, long nodeNumber) {
		if(var1 > var2) {
			insert2Clause(var2, val2, var1, val1, nodeNumber);
			return;
		}

		if(var1 == var2) {
			if(val1 == val2) {
				forcedPairsQueue[nForcedPairs][0] = var1;
				forcedPairsQueue[nForcedPairs][1] = val1;
				nForcedPairs++;
			}
			return;
		}

		if(!clauseIsSet(var1, val1, var2, val2, nodeNumber)) {
			innerlexTime[var1][val1][var2][val2] = nodeNumber;
			if(clauseIsSet(var1, val1, var2, 1-val2, nodeNumber)) {
				// we have
				// var1 = val1 OR var2 = val2
				// AND
				// var1 = val1 OR var2 = 1 - val2
				// thus
				// var1 = val1
				forcedPairsQueue[nForcedPairs][0] = var1;
				forcedPairsQueue[nForcedPairs][1] = val1;
				nForcedPairs++;
			}

			if(clauseIsSet(var1, 1-val1, var2, val2, nodeNumber)) {
				// we have
				// var1 = val1 OR var2 = val2
				// AND
				// var1 = 1 - val1 OR var2 = val2
				// thus
				// var2 = val2
				forcedPairsQueue[nForcedPairs][0] = var2;
				forcedPairsQueue[nForcedPairs][1] = val2;
				nForcedPairs++;
			}
		}
	}

	/**
	 * ensures var1 = val1 => var2 = val2 and verifies the forbidden pattern
	 */
	protected void ensureNeed(int var1, int val1, int var2, int val2) {
		long nodeNumber = problem.solver.stats.safeNumber();
		assert nodeNumber != ALWAYS_TRUE;
		ensureNeed(var1, val1, var2, val2, nodeNumber);
	}

	protected void ensureNeed(int var1, int val1, int var2, int val2, long nodeNumber) {
		// var1 = val1 => var2 = val2
		// <=>
		// var1 = 1 - val1 OR var2 = val2
		insert2Clause(var1, 1 - val1, var2, val2, nodeNumber);
	}

	/**
	 * This is the standard LexicographicVar but with additional calls to ensureNeed.
	 */
	public class LexicographicVar extends ConstraintGlobal implements Tags.TagAC, Tags.TagCallCompleteFiltering, TagNotSymmetric, TagPostponableFiltering {
		public boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < half; i++) {
				int v = t[i], w = t[half+i];
				if (v < w)
					return true;
				if (v > w)
					return false;
			}
			return !strictOrdering;
		}

		/**
		 * A first list (actually array) of variables
		 */
		private final Variable[] list1;

		/**
		 * A second list (actually array) of variables
		 */
		private final Variable[] list2;

		/**
		 * pos1[i] is the position of the variable list1[i] in the constraint scope
		 */
		private final int[] pos1;

		/**
		 * pos2[i] is the position of the variable list2[i] in the constraint scope
		 */
		private final int[] pos2;

		/**
		 * The size of the lists (half of the scope size if no variable occurs several times)
		 */
		private final int half;

		/**
		 * A time counter used during filtering
		 */
		private long lex_time;

		/**
		 * lex_times[x] gives the time at which the variable (at position) x has been set (pseudo-assigned)
		 */
		private final long[] lex_times;

		/**
		 * lex_vals[x] gives the value of the variable (at position) x set at time lex_times[x]
		 */
		private final int[] lex_vals;

		/**
		 * Build a constraint Lexicographic for the specified problem over the two specified lists of variables
		 *
		 * @param list1
		 *            a first list of variables
		 * @param list2
		 *            a second list of variables
		 */
		public LexicographicVar(Problem pb, Variable[] list1, Variable[] list2) {
			super(pb, pb.vars(list1, list2));
			defineKey(strictOrdering);

			this.half = list1.length;
			this.list1 = list1;
			this.list2 = list2;
			control(1 < half && half == list2.length);
			this.pos1 = IntStream.range(0, half).map(i -> Utilities.indexOf(list1[i], AutoLex.this.scp)).toArray();
			this.pos2 = IntStream.range(0, half).map(i -> Utilities.indexOf(list2[i], AutoLex.this.scp)).toArray();
			this.lex_times = new long[AutoLex.this.scp.length];
			this.lex_vals = new int[AutoLex.this.scp.length];
		}

		private boolean set(int p, int v) {
			if(!AutoLex.this.scp[p].dom.containsValue(v))
				return false;

			lex_times[p] = lex_time;
			lex_vals[p] = v;

			if(v == 1) {
				for (int i : forbiddenPattern) {
					int pi = (p + i) % AutoLex.this.scp.length;
					if(lex_times[pi] != lex_time) {
						lex_times[pi] = lex_time;
						lex_vals[pi] = 0;

						if(!AutoLex.this.scp[pi].dom.containsValue(0))
							return false;
					}
					else if(lex_vals[pi] != 0)
						return false;
				}
			}

			return true;
		}

		private boolean isConsistentPair(int decisionVarPos, int alpha, int v) {
			lex_time++;
			if(!set(pos1[alpha], v))
				return false;
			if(!set(pos2[alpha], v))
				return false;

			for (int i = alpha + 1; i < half; i++) {
				int x = pos1[i], y = pos2[i];
				int minx = lex_times[x] == lex_time ? lex_vals[x] : list1[i].dom.firstValue();
				int maxy = lex_times[y] == lex_time ? lex_vals[y] : list2[i].dom.lastValue();
				if (minx == 0 && maxy == 1)
					return true;
				if (minx == 1 && maxy == 0)
					return false;

				assert minx == maxy;
				int value = minx;

				if(!set(x, value))
					return false;
				if(!set(y, value))
					return false;

				ensureNeed(decisionVarPos, v, x, value);
				ensureNeed(decisionVarPos, v, y, value);
			}
			return !strictOrdering;
		}

		public boolean runPropagator(Variable dummy) {
			boolean out = innerPropagator();
			// the queue must ALWAYS be emptied
			boolean queue = emptyQueue();
			return out && queue;
		}

		private boolean innerPropagator() {
			int alpha = 0;
			while (alpha < half) {
				Domain dom1 = list1[alpha].dom, dom2 = list2[alpha].dom;
				if (!AC.enforceLE(dom1, dom2)) // enforce (AC on) x <= y (list1[alpha] <= list2[alpha])
					return false;
				if (dom1.size() == 1 && dom2.size() == 1) {
					if (dom1.singleValue() < dom2.singleValue())
						return entail();
					assert dom1.singleValue() == dom2.singleValue();
					alpha++;
				}
				else {
					int min1 = dom1.firstValue(), min2 = dom2.firstValue();
					assert min1 <= min2;
					// happens on cases {a={0,1} b={0,1}} and {a={0} b={0,1}}
					if (min1 == min2) {
						assert min1 == 0;

						ensureNeed(pos2[alpha], 0, pos1[alpha], 0);
						if(!isConsistentPair(pos2[alpha], alpha, 0))
							if (!dom2.removeValue(0))
								return false;
					}

					int max1 = dom1.lastValue(), max2 = dom2.lastValue();
					assert max1 <= max2;
					// happens on cases {a={0,1} b={0,1}} and {a={0,1} b={1}}
					if (max1 == max2) {
						assert max1 == 1;
						ensureNeed(pos1[alpha], 1, pos2[alpha], 1);
						if (!isConsistentPair(pos1[alpha], alpha, 1))
							if (!dom1.removeValue(1))
								return false;
					}
					assert dom1.firstValue() < dom2.lastValue();
					return true;
				}
			}
			assert alpha == half;

			return !strictOrdering;
		}
	}
}
