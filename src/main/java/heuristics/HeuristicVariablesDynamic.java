/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package heuristics;

import static utility.Enums.ConstraintWeighting.CACD;
import static utility.Enums.ConstraintWeighting.CHS;
import static utility.Enums.ConstraintWeighting.VAR;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.LongStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.global.Sum;
import constraints.global.Sum.SumSimple;
import constraints.global.Sum.SumWeighted;
import interfaces.Observers.ObserverOnAssignments;
import interfaces.Observers.ObserverOnConflicts;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Tags.TagMaximize;
import sets.SetDense;
import solver.Solver;
import utility.Enums.Branching;
import utility.Enums.SingletonStrategy;
import utility.Kit;
import utility.Kit.CombinatorOfTwoInts;
import variables.Domain;
import variables.Variable;

/**
 * This class gives the description of a dynamic variable ordering heuristic. <br>
 * It means that at each step of the search, this kind of object is solicited in order to determine which variable has
 * to be selected according to the current state of the problem.
 */
public abstract class HeuristicVariablesDynamic extends HeuristicVariables {

	public HeuristicVariablesDynamic(Solver solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
	}

	private int lastDepthWithOnlySingletons = Integer.MAX_VALUE;

	@Override
	protected final Variable bestUnpriorityVariable() {
		assert solver.futVars.size() > 0;

		if (solver.head.control.solving.branching != Branching.BIN) {
			Variable x = solver.decisions.varOfLastDecisionIf(false);
			if (x != null)
				return x;
		}
		if (settings.lc > 0) {
			Variable x = solver.lastConflict.priorityVariable();
			if (x != null) {
				return x;
			}
		}
		bestScoredVariable.reset(false);
		if (settings.singleton == SingletonStrategy.LAST) {
			if (solver.depth() <= lastDepthWithOnlySingletons) {
				lastDepthWithOnlySingletons = Integer.MAX_VALUE;
				for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
					if (x.dom.size() != 1)
						bestScoredVariable.update(x, scoreOptimizedOf(x));
				}
				// for (int e = solver.futVars.first; e != -1; e = solver.futVars.nexts[e]) {
				// Variable x = solver.problem.variables[e];
				// if (x.dom.size() != 1)
				// bestScoredVariable.update(x, scoreOptimizedOf(x));
				// }
				// solver.futVars.execute(x -> {
				// if (x.dom.size() != 1)
				// bestScoredVariable.update(x, scoreOptimizedOf(x));
				// });
			}
			if (bestScoredVariable.variable == null) {
				lastDepthWithOnlySingletons = solver.depth();
				return solver.futVars.first();
			}
		} else {
			boolean first = settings.singleton == SingletonStrategy.FIRST;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (first && x.dom.size() == 1)
					return x;
				bestScoredVariable.update(x, scoreOptimizedOf(x));
			}
			if (bestScoredVariable.variable == null) {
				return solver.futVars.first(); // if discardAux was set to true
			}
		}
		return bestScoredVariable.variable;

	}

	// ************************************************************************
	// ***** Subclasses for classical dynamic heuristics
	// ************************************************************************

	public static final class Ddeg extends HeuristicVariablesDynamic implements TagMaximize {

		public Ddeg(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.ddeg();
		}
	}

	public static final class DdegOnDom extends HeuristicVariablesDynamic implements TagMaximize {

		public DdegOnDom(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.ddegOnDom();
		}
	}

	public static final class Dom extends HeuristicVariablesDynamic {

		public Dom(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.dom.size();
		}
	}

	public static final class DomThenDeg extends HeuristicVariablesDynamic {
		private CombinatorOfTwoInts combinator;

		public DomThenDeg(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			this.combinator = new CombinatorOfTwoInts(solver.problem.features.maxVarDegree());
		}

		@Override
		public double scoreOf(Variable x) {
			return combinator.combinedMaxMinLongValueFor(x.dom.size(), x.deg());
		}
	}

	// ************************************************************************
	// ***** Subclasses for Wdeg variants
	// ************************************************************************

	/**
	 * The subclasses of this class allow us to define the heuristics wdeg and wdeg/dom. There exists four variants for
	 * each of these two heuristics: VAR, UNIT, CACD and CHS.
	 */
	public static abstract class WdegVariant extends HeuristicVariablesDynamic
			implements ObserverOnRuns, ObserverOnAssignments, ObserverOnConflicts, TagMaximize {

		/**
		 * Constants used by CHS
		 */
		private static final double SMOOTHING = 0.995, ALPHA0 = 0.1, ALPHA_LIMIT = 0.06, ALPHA_DECREMENT = 0.000001;

		/**
		 * indicates the number of times a wipe-out occurred
		 */
		private int time;

		/**
		 * ctime[c] indicates the last time a wipe-out occurred for constraint c (not used by VAR)
		 */
		private int[] ctime;

		/**
		 * vscores[x] is the score (weight) of variable x (not used by CHS)
		 */
		public double[] vscores;

		/**
		 * cscores[c] is the score (weight) of constraint c (not used by VAR)
		 */
		public double[] cscores;

		/**
		 * cvscores[c][x] is the score (weight) of variable x in constraint c (used by UNIT and CACD)
		 */
		private double[][] cvscores;

		/**
		 * field used by CHS
		 */
		private double alpha;

		@Override
		public void beforeRun() {
			if (runReset() || (solver.restarter.numRun - solver.solutions.lastRun) % solver.head.control.restarts.varhSolResetPeriod == 0) {
				System.out.println("    ...resetting weights (nValues: " + Variable.nValidValuesFor(solver.problem.variables) + ")");
				reset();
			}
			alpha = ALPHA0;
			if (settings.weighting == CHS) { // smoothing
				for (int i = 0; i < cscores.length; i++)
					cscores[i] *= (Math.pow(SMOOTHING, time - ctime[i]));
			}
		}

		@Override
		public void afterAssignment(Variable x, int a) {
			if (settings.weighting != VAR && settings.weighting != CHS)
				for (Constraint c : x.ctrs)
					if (c.futvars.size() == 1) {
						int y = c.futvars.dense[0]; // the other variable whose score must be updated
						vscores[c.scp[y].num] -= cvscores[c.num][y];
					}
		}

		@Override
		public void afterUnassignment(Variable x) {
			if (settings.weighting != VAR && settings.weighting != CHS)
				for (Constraint c : x.ctrs)
					if (c.futvars.size() == 2) { // since a variable has just been unassigned, it means that there was
													// only one future variable
						int y = c.futvars.dense[0]; // the other variable whose score must be updated
						vscores[c.scp[y].num] += cvscores[c.num][y];
					}
		}

		@Override
		public void whenWipeout(Constraint c, Variable x) {
			time++;
			if (settings.weighting == VAR)
				vscores[x.num]++;
			else if (c != null) {
				if (settings.weighting == CHS) {
					double r = 1.0 / (time - ctime[c.num]);
					double increment = alpha * (r - cscores[c.num]);
					cscores[c.num] += increment;
					alpha = Double.max(ALPHA_LIMIT, alpha - ALPHA_DECREMENT);
				} else {
					double increment = 1;
					cscores[c.num] += increment; // just +1 in that case (can be useful for other objects, but not
													// directly for wdeg)
					SetDense futvars = c.futvars;
					for (int i = futvars.limit; i >= 0; i--) {
						Variable y = c.scp[futvars.dense[i]];
						if (settings.weighting == CACD) { // in this case, the increment is not 1 as for UNIT
							Domain dom = y.dom;
							boolean test = false; // EXPERIMENTAL ; this variant does not seem to be interesting
							if (test) {
								int depth = solver.depth();
								int nRemoved = 0;
								for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
									if (dom.removedLevelOf(a) != depth)
										break;
									nRemoved++;
								}
								increment = 1.0 / (futvars.size() * (dom.size() + nRemoved));
							} else
								increment = 1.0 / (futvars.size() * (dom.size() == 0 ? 0.5 : dom.size()));
						}
						vscores[y.num] += increment;
						cvscores[c.num][futvars.dense[i]] += increment;
					}
				}
				ctime[c.num] = time;
			}
		}

		@Override
		public void whenBacktrack() {
		}

		public WdegVariant(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			this.ctime = settings.weighting != VAR ? new int[solver.problem.constraints.length] : null;
			this.vscores = settings.weighting != CHS ? new double[solver.problem.variables.length] : null;
			this.cscores = settings.weighting != VAR ? new double[solver.problem.constraints.length] : null;
			this.cvscores = settings.weighting != VAR && settings.weighting != CHS
					? Stream.of(solver.problem.constraints).map(c -> new double[c.scp.length]).toArray(double[][]::new)
					: null;

			boolean b = false; // EXPERIMENTAL
			if (b && solver.problem.optimizer != null && solver.problem.optimizer.ctr instanceof Sum) {
				Sum c = (Sum) solver.problem.optimizer.ctr;
				int[] coeffs = c instanceof SumSimple ? null : ((SumWeighted) c).coeffs;
				long[] gaps = IntStream.range(0, c.scp.length).mapToLong(i -> Math.abs((coeffs == null ? 1 : coeffs[i]) * c.scp[i].dom.distance())).toArray();
				long minGap = LongStream.of(gaps).min().getAsLong();
				for (int i = 0; i < c.scp.length; i++) {
					vscores[c.scp[i].num] += 1 + gaps[i] - minGap; // Math.log(1 + gaps[i] - minGap) / Math.log(2);
				}
			}
		}

		@Override
		public void reset() {
			time = 0;
			if (ctime != null)
				Arrays.fill(ctime, 0);
			if (vscores != null)
				Arrays.fill(vscores, 0);
			if (cscores != null)
				Arrays.fill(cscores, 0);
			if (cvscores != null)
				for (double[] t : cvscores)
					Arrays.fill(t, 0);
		}

	}

	/**
	 * The heuristic wdeg (with its four variants: VAR, UNIT, CACD, CHS)
	 */
	public static class Wdeg extends WdegVariant {

		public Wdeg(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			if (settings.weighting == CHS) {
				double d = 0;
				for (Constraint c : x.ctrs)
					if (c.futvars.size() > 1)
						d += cscores[c.num];
				return d;
			}
			return vscores[x.num];
		}
	}

	/**
	 * The heuristic wdeg/dom (with its four variants: VAR, UNIT, CACD, CHS)
	 */
	public static class WdegOnDom extends WdegVariant {

		public WdegOnDom(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			if (settings.weighting == CHS) {
				double d = 0;
				for (Constraint c : x.ctrs)
					if (c.futvars.size() > 1)
						d += cscores[c.num];
				return d / x.dom.size();
			}
			return vscores[x.num] / x.dom.size();
		}
	}

	// ************************************************************************
	// ***** Subclasses for Activity/Impact
	// ************************************************************************

	public static abstract class ActivityImpactAbstract extends HeuristicVariables implements ObserverOnRuns {
		protected Variable lastVar; // if null, either just after pre-processing, or singleton variable
		protected int lastDepth = -1;
		protected int[] lastSizes;

		protected double alpha;

		@Override
		public void beforeRun() {
			lastVar = null;
			lastDepth = -1;
			for (int i = 0; i < solver.problem.variables.length; i++)
				lastSizes[i] = solver.problem.variables[i].dom.size();
		}

		public ActivityImpactAbstract(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			this.lastSizes = Stream.of(solver.problem.variables).mapToInt(x -> x.dom.size()).toArray();
			Kit.control(solver.head.control.solving.branching == Branching.BIN);
			Kit.control(solver.head.control.restarts.varhResetPeriod != 0);
		}

		protected abstract void update();

		@Override
		protected Variable bestUnpriorityVariable() {
			assert lastVar != null || solver.depth() > lastDepth : lastVar + " " + solver.depth() + " " + lastDepth;
			if (lastVar != null)
				update();
			bestScoredVariable.reset(true);
			solver.futVars.execute(x -> {
				if (x.dom.size() > 1 || settings.singleton != SingletonStrategy.LAST) {
					lastSizes[x.num] = x.dom.size();
					bestScoredVariable.update(x, scoreOptimizedOf(x));
				}
			});
			if (bestScoredVariable.variable == null) {
				assert settings.singleton == SingletonStrategy.LAST || solver.head.control.varh.discardAux;
				return solver.futVars.first();
			}
			lastVar = bestScoredVariable.variable.dom.size() == 1 ? null : bestScoredVariable.variable;
			lastDepth = solver.depth();
			return bestScoredVariable.variable;
		}
	}

	public static final class Activity extends ActivityImpactAbstract {
		private double[] activities;

		@Override
		public void beforeRun() {
			super.beforeRun();
			if (runReset()) {
				Kit.log.info("Reset of activities");
				Arrays.fill(activities, 0);
			}
		}

		public Activity(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			alpha = 0.99; // alpha as an aging decay
			activities = new double[solver.problem.variables.length];
		}

		@Override
		protected void update() {
			if (solver.depth() > lastDepth) { // the last positive decision succeeded
				solver.futVars.execute(x -> activities[x.num] = x.dom.size() != lastSizes[x.num] ? activities[x.num] + 1 : activities[x.num] * alpha);
			} else
				activities[lastVar.num] += 2; // because the last positive decision failed, so a big activity
		}

		@Override
		public double scoreOf(Variable x) {
			return -activities[x.num] / x.dom.size(); // minus because we have to minimize
		}
	}

	public static final class Impact extends ActivityImpactAbstract {
		private double[] impacts;

		@Override
		public void beforeRun() {
			super.beforeRun();
			if (runReset()) {
				Kit.log.info("Reset of impacts");
				Arrays.fill(impacts, 0);
			}
		}

		public Impact(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			alpha = 0.1;
			impacts = new double[solver.problem.variables.length];
		}

		@Override
		protected void update() {
			double impact = 1;
			if (solver.depth() > lastDepth) // the last positive decision succeeded
				for (Variable x : solver.futVars)
					impact *= x.dom.size() / (double) lastSizes[x.num];
			else
				impact = 0; // because the last positive decision failed, so a big impact (0 is the strongest impact
							// value)
			impacts[lastVar.num] = (1 - alpha) * impacts[lastVar.num] + alpha * impact;
			assert 0 <= impact && impact <= 1 && 0 <= impacts[lastVar.num] && impacts[lastVar.num] <= 1;
		}

		@Override
		public double scoreOf(Variable x) {
			return impacts[x.num]; // note that 0 as value is the strongest impact value (we minimize)
		}

	}

}
