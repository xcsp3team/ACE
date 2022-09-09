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

import static heuristics.HeuristicVariablesDynamic.WdegVariant.ConstraintWeighting.CACD;
import static heuristics.HeuristicVariablesDynamic.WdegVariant.ConstraintWeighting.CHS;
import static heuristics.HeuristicVariablesDynamic.WdegVariant.ConstraintWeighting.VAR;
import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.Stream;

import constraints.Constraint;
import interfaces.Observers.ObserverOnAssignments;
import interfaces.Observers.ObserverOnConflicts;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Tags.TagMaximize;
import sets.SetDense;
import solver.Solver;
import solver.Solver.Branching;
import utility.Kit;
import variables.Domain;
import variables.Variable;

/**
 * This is the root class for building dynamic variable ordering heuristics. It means that at each step of the search,
 * such heuristic is solicited in order to determine which variable has to be selected according to the current state of
 * the problem.
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicVariablesDynamic extends HeuristicVariables {

	/**
	 * Three strategies to deal with fixed variables (i.e., variables with singleton domains) while not being explicitly
	 * assigned by the solver
	 */
	public enum SingletonStrategy {
		ANY, FIRST, LAST;
	}

	public HeuristicVariablesDynamic(Solver solver, boolean anti) {
		super(solver, anti);
	}

	private int lastDepthWithOnlySingletons = Integer.MAX_VALUE;

	@Override
	protected Variable bestUnpriorityVariable() {
		assert solver.futVars.size() > 0;
		if (solver.head.control.solving.branching != Branching.BIN) { // if not binary branching
			Variable x = solver.decisions.varOfLastDecisionIf(false);
			if (x != null)
				return x;
		}
		if (options.lc > 0) { // if last-conflict mode
			Variable x = solver.lastConflict.priorityVariable();
			if (x != null) {
				return x;
			}
		}
		bestScoredVariable.reset(false);
		if (options.singleton == SingletonStrategy.LAST) {
			if (solver.depth() <= lastDepthWithOnlySingletons) {
				lastDepthWithOnlySingletons = Integer.MAX_VALUE;
				for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
					if (options.connected && x.firstAssignedNeighbor() == null)
						continue;
					// if (x.ctrs.length <= 1)
					// continue;
					if (x.dom.size() != 1)
						bestScoredVariable.consider(x, scoreOptimizedOf(x));
				}
			}
			if (bestScoredVariable.variable == null) {
				lastDepthWithOnlySingletons = solver.depth();
				return solver.futVars.first();
			}
		} else {
			boolean first = options.singleton == SingletonStrategy.FIRST;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (first && x.dom.size() == 1)
					return x;
				bestScoredVariable.consider(x, scoreOptimizedOf(x));
			}
			if (bestScoredVariable.variable == null) {
				return solver.futVars.first(); // possible if discardAux was set to true
			}
		}
		return bestScoredVariable.variable;

	}

	// ************************************************************************
	// ***** Subclasses for classical and failure-based dynamic heuristics
	// ************************************************************************

	public static final class Ddeg extends HeuristicVariablesDynamic implements TagMaximize {

		public Ddeg(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.ddeg();
		}
	}

	public static final class DdegOnDom extends HeuristicVariablesDynamic implements TagMaximize {

		public DdegOnDom(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.ddegOnDom();
		}
	}

	public static final class Dom extends HeuristicVariablesDynamic {

		public Dom(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.dom.size();
		}
	}

	public static final class Regret extends HeuristicVariablesDynamic implements TagMaximize {

		public Regret(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.dom.regretValue();
		}
	}

	public static final class FrOnDom extends HeuristicVariablesDynamic implements TagMaximize {

		public FrOnDom(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.frOnDom();
		}
	}

	public static final class FraOnDom extends HeuristicVariablesDynamic implements TagMaximize {

		public FraOnDom(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			return x.fraOnDom();
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
		 * The four variants for constraint weighting.
		 * <ul>
		 * <li>VAR is a basic variant</li>
		 * <li>UNIT is for classical weighting, as described in "Boosting Systematic Search by Weighting Constraints",
		 * ECAI 2004: 146-150, by F. Boussemart, F. Hemery, C. Lecoutre, and L. Sais.</li>
		 * <li>cacd its variant, as described in "Refining Constraint Weighting", ICTAI 2019: 71-77 by H. Wattez, C.
		 * Lecoutre, A. Paparrizou, and S. Tabary</li>
		 * <li>CHS, as described in "Conflict history based search for constraint satisfaction problem", SAC 2019:
		 * 1117-1122 by D. Habet, and C. Terrioux</li>
		 * </ul>
		 */
		public static enum ConstraintWeighting {
			VAR, UNIT, CACD, CHS;
		}

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
			if (runReset()) {
				Kit.log.config("    ...resetting weights (nValues: " + Variable.nValidValuesFor(solver.problem.variables) + ")");
				reset();
			}
			alpha = ALPHA0;
			if (options.weighting == CHS) { // smoothing
				for (int i = 0; i < cscores.length; i++)
					cscores[i] *= (Math.pow(SMOOTHING, (double) time - ctime[i]));
			}
		}

		@Override
		public void afterAssignment(Variable x, int a) {
			if (options.weighting != VAR && options.weighting != CHS)
				for (Constraint c : x.ctrs)
					if (c.futvars.size() == 1) {
						int y = c.futvars.dense[0]; // the other variable whose score must be updated
						vscores[c.scp[y].num] -= cvscores[c.num][y];
					}
		}

		@Override
		public void afterFailedAssignment(Variable x, int a) {
		}

		@Override
		public void afterUnassignment(Variable x) {
			if (options.weighting != VAR && options.weighting != CHS)
				for (Constraint c : x.ctrs)
					if (c.futvars.size() == 2) {
						// since a variable has just been unassigned, it means that there was only one future variable
						int y = c.futvars.dense[0]; // the other variable whose score must be updated
						vscores[c.scp[y].num] += cvscores[c.num][y];
					}
		}

		@Override
		public void whenWipeout(Constraint c, Variable x) {
			time++;
			if (options.weighting == VAR)
				vscores[x.num]++;
			else if (c != null) {
				if (options.weighting == CHS) {
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
						if (options.weighting == CACD) { // in this case, the increment is not 1 as for UNIT
							Domain dom = y.dom;
							// boolean test = false; // EXPERIMENTAL ; this variant does not seem to be interesting
							// if (test) {
							// int depth = solver.depth();
							// int nRemoved = 0;
							// for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a)) {
							// if (dom.removedLevelOf(a) != depth)
							// break;
							// nRemoved++;
							// }
							// increment = 1.0 / (futvars.size() * (dom.size() + nRemoved));
							// } else
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

		public WdegVariant(Solver solver, boolean anti) {
			super(solver, anti);
			this.ctime = options.weighting != VAR ? new int[solver.problem.constraints.length] : null;
			this.vscores = options.weighting != CHS ? new double[solver.problem.variables.length] : null;
			this.cscores = options.weighting != VAR ? new double[solver.problem.constraints.length] : null;
			this.cvscores = options.weighting != VAR && options.weighting != CHS
					? Stream.of(solver.problem.constraints).map(c -> new double[c.scp.length]).toArray(double[][]::new)
					: null;

			// boolean b = false; // EXPERIMENTAL (code to be finalized or discarded)
			// if (b && solver.problem.optimizer != null && solver.problem.optimizer.ctr instanceof Sum) {
			// Sum c = (Sum) solver.problem.optimizer.ctr;
			// int[] coeffs = c instanceof SumSimple ? null : ((SumWeighted) c).coeffs;
			// long[] gaps = IntStream.range(0, c.scp.length).mapToLong(i -> Math.abs((coeffs == null ? 1 : coeffs[i]) *
			// c.scp[i].dom.distance())).toArray();
			// long minGap = LongStream.of(gaps).min().getAsLong();
			// for (int i = 0; i < c.scp.length; i++) {
			// vscores[c.scp[i].num] += 1 + gaps[i] - minGap; // Math.log(1 + gaps[i] - minGap) / Math.log(2);
			// }
			// }
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
	public static final class Wdeg extends WdegVariant {

		public Wdeg(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			if (options.weighting == CHS) {
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
	public static final class WdegOnDom extends WdegVariant {

		public WdegOnDom(Solver solver, boolean anti) {
			super(solver, anti);
		}

		@Override
		public double scoreOf(Variable x) {
			if (options.weighting == CHS) {
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

	/**
	 * The root class for activity-based and impact-based search heuristics. IMPORTANT: the code is for a basic variant
	 * of such heuristics. Certainly, better implementations or variants are possible.
	 */
	public static abstract class ActivityImpactAbstract extends HeuristicVariables implements ObserverOnRuns {
		protected Variable lastVar; // if null, either just after pre-processing, or singleton variable
		protected int lastDepth = -1;
		protected int[] lastSizes;

		/**
		 * Parameter used in the heuristic
		 */
		protected double alpha;

		@Override
		public void beforeRun() {
			lastVar = null;
			lastDepth = -1;
			for (int i = 0; i < solver.problem.variables.length; i++)
				lastSizes[i] = solver.problem.variables[i].dom.size();
		}

		public ActivityImpactAbstract(Solver solver, boolean anti) {
			super(solver, anti);
			this.lastSizes = Stream.of(solver.problem.variables).mapToInt(x -> x.dom.size()).toArray();
			control(solver.head.control.solving.branching == Branching.BIN);
			control(solver.head.control.restarts.varhResetPeriod != 0);
		}

		protected abstract void update();

		@Override
		protected Variable bestUnpriorityVariable() {
			assert lastVar != null || solver.depth() > lastDepth : lastVar + " " + solver.depth() + " " + lastDepth;
			if (lastVar != null)
				update();
			bestScoredVariable.reset(true);
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (x.dom.size() > 1 || options.singleton != SingletonStrategy.LAST) {
					lastSizes[x.num] = x.dom.size();
					bestScoredVariable.consider(x, scoreOptimizedOf(x));
				}
			}
			if (bestScoredVariable.variable == null) {
				assert options.singleton == SingletonStrategy.LAST || solver.head.control.varh.discardAux;
				return solver.futVars.first();
			}
			lastVar = bestScoredVariable.variable.dom.size() == 1 ? null : bestScoredVariable.variable;
			lastDepth = solver.depth();
			return bestScoredVariable.variable;
		}
	}

	/**
	 * Activity-based search heuristic is described in "Activity-Based Search for Black-Box Constraint Programming
	 * Solvers", CPAIOR 2012: 228-243 by L. Michel, and P. Van Hentenryck. Here, this is a basic variant. Certainly,
	 * better implementations or variants are possible.
	 */
	public static final class Activity extends ActivityImpactAbstract {

		/**
		 * activities[x] gives the current activity of variable x
		 */
		private double[] activities;

		@Override
		public void beforeRun() {
			super.beforeRun();
			if (runReset()) {
				Kit.log.info("Reset of activities");
				Arrays.fill(activities, 0);
			}
		}

		public Activity(Solver solver, boolean anti) {
			super(solver, anti);
			alpha = 0.99; // alpha as an aging decay
			activities = new double[solver.problem.variables.length];
		}

		@Override
		protected void update() {
			if (solver.depth() > lastDepth) { // the last positive decision succeeded
				for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
					activities[x.num] = x.dom.size() != lastSizes[x.num] ? activities[x.num] + 1 : activities[x.num] * alpha;
			} else
				activities[lastVar.num] += 2; // because the last positive decision failed, so a big activity
		}

		@Override
		public double scoreOf(Variable x) {
			return -activities[x.num] / x.dom.size(); // minus because we have to minimize
		}
	}

	/**
	 * Impact-based search heuristic is described in "Impact-Based Search Strategies for Constraint Programming", CP
	 * 2004: 557-571 by P. Refalo. Here, this is a basic variant. Certainly, better implementations or variants are
	 * possible.
	 */
	public static final class Impact extends ActivityImpactAbstract {

		/**
		 * impacts[x] gives the current impact of variable x
		 */
		private double[] impacts;

		@Override
		public void beforeRun() {
			super.beforeRun();
			if (runReset()) {
				Kit.log.info("Reset of impacts");
				Arrays.fill(impacts, 0);
			}
		}

		public Impact(Solver solver, boolean anti) {
			super(solver, anti);
			alpha = 0.1;
			impacts = new double[solver.problem.variables.length];
		}

		@Override
		protected void update() {
			double impact = 1;
			if (solver.depth() > lastDepth) // the last positive decision succeeded
				for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x))
					impact *= x.dom.size() / (double) lastSizes[x.num];
			else
				impact = 0; // because the last positive decision failed, so a big impact (0 is the strongest one)
			impacts[lastVar.num] = (1 - alpha) * impacts[lastVar.num] + alpha * impact;
			assert 0 <= impact && impact <= 1 && 0 <= impacts[lastVar.num] && impacts[lastVar.num] <= 1;
		}

		@Override
		public double scoreOf(Variable x) {
			return impacts[x.num]; // note that 0 as value is the strongest impact value (we minimize)
		}

	}

}
