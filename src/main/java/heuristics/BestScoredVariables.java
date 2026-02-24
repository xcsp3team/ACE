/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import java.util.stream.IntStream;

import problem.Problem;
import sets.SetSparse.SetSparseCnt;
import solver.Solver;
import variables.Variable;

/**
 * This is the abstract root class used for identifying and recording the best scored variables, to be used by variable ordering heuristics.
 * 
 * @author Christophe Lecoutre
 *
 */
public abstract class BestScoredVariables {

	protected final Solver solver;

	/**
	 * The time at which the process of identifying the best scored variables starts.
	 */
	protected int time;

	/**
	 * True if we must prefer the variable with the lowest score, instead of the variable with the highest score
	 */
	protected boolean minimization;

	public BestScoredVariables(Solver solver) {
		this.solver = solver;
	}

	public abstract void reset();

	public BestScoredVariables beforeIteration(int time, boolean minimization) {
		this.time = time;
		this.minimization = minimization;
		return this;
	}

	protected abstract boolean considerImplem(Variable x, double s);

	/**
	 * Considers the specified variable with the specified score: compares it with the current best scored variable, and updates it if necessary.
	 * 
	 * @param x
	 *            a variable
	 * @param s
	 *            the score of the variable
	 * @return true if x becomes the new best scored variable
	 */
	public boolean consider(Variable x, double s) {
		if (solver.head.control.varh.discardAux && x.isAuxiliaryVariableIntroducedBySolver()) {
			assert x.id().startsWith(Problem.AUXILIARY_VARIABLE_PREFIX);
			return false;
		}
		return considerImplem(x, s);
	}

	public abstract Variable firstVariable();

	public abstract Variable secondVariable(int newTime);

	public void update(boolean consistent) {
		if (consistent && solver.propagation.queue.collected.size() == 0) { // if consistent and no value removal
			Variable x = solver.futVars.lastPast();
			boolean singletonVariable = x.dom.lastRemovedLevel() != solver.depth();
			if (!singletonVariable) {
				solver.stats.nImpactlessAssignments++;
				if (solver.head.control.varh.impactless)
					solver.heuristic.newImpactlessAssignment(x, x.dom.single());
			}
		}
	}

	/**
	 * Useful to record the best variable(s) out of a set, when considering a score computed for each of them
	 */
	public static class BestScoredSimple extends BestScoredVariables {

		/**
		 * The current best (and second best) variable, i.e., the variable with the current best score; used during an iteration over all variables
		 */
		private Variable fstVariable, sndVariable;

		/**
		 * The score of the current best (and second best) variable
		 */
		private double fstScore, sndScore;

		public BestScoredSimple(Solver solver) {
			super(solver);
		}

		public BestScoredVariables beforeIteration(int time, boolean minimization) {
			super.beforeIteration(time, minimization);
			this.fstVariable = null;
			this.fstScore = minimization ? Double.MAX_VALUE : Double.NEGATIVE_INFINITY;
			this.sndVariable = null;
			return this;
		}

		public void reset() {
			this.fstVariable = null;
			this.sndVariable = null;
		}

		public Variable second(int newTime) {
			if (sndVariable != null && this.time + 1 == newTime)
				return sndVariable;
			return null;
		}

		@Override
		protected boolean considerImplem(Variable x, double s) {
			if ((minimization && s < fstScore) || (!minimization && s > fstScore)) {
				sndVariable = fstVariable;
				sndScore = fstScore;
				fstVariable = x;
				fstScore = s;
				return true;
			}
			if (sndVariable == null || (minimization && s < sndScore) || (!minimization && s > sndScore)) {
				sndVariable = x;
				sndScore = s;
			}
			return false;
		}

		public Variable firstVariable() {
			return fstVariable;
		}

		public Variable secondVariable(int newTime) {
			if (sndVariable != null && this.time + 1 == newTime)
				return sndVariable;
			return null;
		}

		// public void update(boolean consistent) {
		// super.update(consistent);
		// }

		public boolean betterThan(double previousScore) {
			return minimization ? fstScore < previousScore : fstScore > previousScore;
		}
	}

	public static class BestScoredStacked extends BestScoredVariables {

		private final int lastPossibleLimit;

		private Store store1;

		private Store store2;

		class Store {

			private Variable[] vars;

			private double[] scores;

			private int limit;

			Store(int capacity) {
				this.vars = new Variable[capacity];
				this.scores = new double[capacity];
				this.limit = -1;
			}

			void reset() {
				this.limit = -1;
			}

			boolean considerImplem(Variable x, double score) {
				if (limit != -1 && score < scores[limit])
					return false;
				for (int i = 0; i <= limit; i++) {
					if (score > scores[i]) {
						for (int j = Math.min(limit, lastPossibleLimit - 1); j >= i; j--) {
							vars[j + 1] = vars[j];
							scores[j + 1] = scores[j];
						}
						vars[i] = x;
						scores[i] = score;
						if (limit < lastPossibleLimit)
							limit++;
						return i == 0;
					}
				}
				if (limit < lastPossibleLimit) {
					limit++;
					vars[limit] = x;
					scores[limit] = score;
				}
				return limit == 0;
			}

			public String toString() {
				return limit == -1 ? "{}"
						: IntStream.range(0, limit + 1).mapToObj(i -> "(" + vars[i] + "," + scores[i] + ")").reduce("", (a, b) -> a + " " + b);
			}
		}

		public BestScoredStacked(Solver solver, int capacity) {
			super(solver);
			this.lastPossibleLimit = capacity - 1;
			this.store1 = new Store(capacity);
			this.store2 = new Store(capacity);
		}

		public BestScoredVariables beforeIteration(int time, boolean minimization) {
			super.beforeIteration(time, minimization);
			reset();
			return this;
		}

		public void reset() {
			store1.reset();
			store2.reset();
		}

		@Override
		protected boolean considerImplem(Variable x, double score) {
			return store1.considerImplem(x, score);
		}

		public Variable firstVariable() {
			return store1.limit == -1 ? null : store1.vars[0];
		}

		public Variable secondVariable(int newTime) {
			if (store1.limit >= 1 && this.time + 1 == newTime)
				return store1.vars[1];
			return null;
		}

		public void update(boolean consistent) {
			super.update(consistent);
			// System.out.println("updatingggg " + consistent + " " + store1 + " " + store1.limit);
			// System.out.println(" -> " + solver.problem.variables[0] + " " + solver.heuristic.scoreOptimizedOf(solver.problem.variables[0]) + " " +
			// solver.problem.variables[0].dom.size());
			if (!consistent || store1.limit == -1)
				reset();
			else {
				SetSparseCnt collected = solver.propagation.queue.passedBy;
				double limitScore = store1.scores[store1.limit]; // the worst score of those being currently recorded (and computed at last call)
				store2.reset();
				// we first copy the current stored variables
				for (int i = 0; i <= store1.limit; i++) {
					Variable x = store1.vars[i];
					if (x.dom.size() == 1)
						continue;
					if (collected.contains(x.num))
						collected.cnts[x.num] = -1; // to know later that the variable has already been added
					store2.considerImplem(x, solver.heuristic.scoreOptimizedOf(x));
					// control(added , "pb with " + x + " " + limitScore + " vs " + solver.heuristic.scoreOptimizedOf(x) + " " + store1 + " -- " + store2);
				}
				for (int i = 0; i <= collected.limit; i++) {
					int num = collected.dense[i];
					if (collected.cnts[num] == -1)
						continue;
					Variable x = solver.problem.variables[num];
					if (x.dom.size() == 1)
						continue;
					double score = solver.heuristic.scoreOptimizedOf(x);
					if (score <= limitScore)
						continue;
					store2.considerImplem(x, score);
				}
				Store tmp = store1;
				store1 = store2;
				store2 = tmp;
				// System.out.println("updatingggg2 " + consistent + " " + store1);
			}
		}
	}

	public static class BestScoredCyclic extends BestScoredVariables { // TODO unfinished

		private Variable fstVariable, sndVariable;

		private double fstScore, sndScore;

		public UpdateStack updateStack;

		private int stackMaxSize;

		public class UpdateStack {

			private static final int MAX = 50;

			public Variable[] cyclicVariables;

			public double[] cyclicScores;

			public int size; // modulo

			public void reset() {
				this.size = 0;
			}

			public UpdateStack() {
				this.cyclicVariables = new Variable[MAX];
				this.cyclicScores = new double[MAX];
				this.size = 0;
			}

			public void add(Variable x, double score) {
				cyclicVariables[size % MAX] = x;
				cyclicScores[size % MAX] = score;
				size++;
			}

			public Variable stackedVariableFor(int newTime) {
				int gap = newTime - time + 1; // -1 because the last variable is also recorded
				if (gap >= MAX || gap > size)
					return null;
				int idx = (size - gap + MAX) % MAX;
				return cyclicVariables[idx];
			}
		}

		public BestScoredCyclic(Solver solver, int updateStackLength) {
			super(solver);
			this.stackMaxSize = updateStackLength;
			if (updateStackLength > 0)
				updateStack = new UpdateStack();
		}

		public BestScoredVariables beforeIteration(int time, boolean minimization) {
			this.time = time;
			this.fstVariable = null;
			this.fstScore = minimization ? Double.MAX_VALUE : Double.NEGATIVE_INFINITY;
			this.minimization = minimization;
			this.sndVariable = null;
			if (updateStack != null)
				updateStack.reset();
			return this;
		}

		public void reset() {
			this.fstVariable = null;
			this.sndVariable = null;
			if (updateStack != null)
				this.updateStack.reset();
		}

		public Variable firstVariable() {
			return fstVariable;
		}

		public Variable secondVariable(int newTime) {
			if (sndVariable != null && this.time + 1 == newTime)
				return sndVariable;
			return null;
		}

		public Variable second2(int newTime) {
			if (updateStack == null || newTime - this.time > stackMaxSize)
				return null;
			// if (updateStack != null && this.time + 1 == newTime) {
			assert stackMaxSize != 1 || updateStack.stackedVariableFor(newTime) == sndVariable : " " + updateStack.stackedVariableFor(newTime) + " vs "
					+ sndVariable;
			return updateStack.stackedVariableFor(newTime);
			// }
			// return null;
		}

		@Override
		protected boolean considerImplem(Variable x, double s) {
			if ((minimization && s < fstScore) || (!minimization && s > fstScore)) {
				sndVariable = fstVariable;
				sndScore = fstScore;
				fstVariable = x;
				fstScore = s;
				if (updateStack != null)
					updateStack.add(x, s);
				return true;
			}
			if (sndVariable == null || (minimization && s < sndScore) || (!minimization && s > sndScore)) {
				sndVariable = x;
				sndScore = s;
			}
			return false;
		}
	}
}
