/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.LongStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.global.Sum;
import constraints.global.Sum.SumSimple;
import constraints.global.Sum.SumWeighted;
import interfaces.Observers.ObserverAssignment;
import interfaces.Observers.ObserverConflicts;
import interfaces.Observers.ObserverRuns;
import interfaces.Tags.TagMaximize;
import sets.SetDense;
import solver.Solver;
import utility.Enums.EBranching;
import utility.Enums.ESingleton;
import utility.Enums.EWeighting;
import utility.Kit;
import utility.Kit.CombinatorOfTwoInts;
import variables.Domain;
import variables.Variable;

/**
 * This class gives the description of a dynamic variable ordering heuristic. <br>
 * It means that at each step of the search, this kind of object is solicited in order to determine which variable has to be selected according to the current
 * state of the problem.
 */
public abstract class HeuristicVariablesDynamic extends HeuristicVariables {

	public HeuristicVariablesDynamic(Solver solver, boolean antiHeuristic) {
		super(solver, antiHeuristic);
	}

	private int lastDepthWithOnlySingletons = Integer.MAX_VALUE;

	@Override
	protected final Variable bestUnpriorityVar() {
		assert solver.futVars.size() > 0;

		if (solver.head.control.solving.branching != EBranching.BIN) {
			Variable x = solver.dr.varOfLastDecisionIf(false);
			if (x != null)
				return x;
		}
		if (settings.lc > 0) {
			Variable x = solver.lastConflict.lastConflictPriorityVar();
			if (x != null) {
				return x;
			}
		}
		bestScoredVariable.reset(false);
		if (settings.singleton == ESingleton.LAST) {
			if (solver.depth() <= lastDepthWithOnlySingletons) {
				lastDepthWithOnlySingletons = Integer.MAX_VALUE;
				solver.futVars.execute(x -> {
					if (x.dom.size() != 1)
						bestScoredVariable.update(x, scoreOptimizedOf(x));
				});
			}
			if (bestScoredVariable.variable == null) {
				lastDepthWithOnlySingletons = solver.depth();
				return solver.futVars.first();
			}
		} else {
			boolean first = settings.singleton == ESingleton.FIRST;
			for (Variable x = solver.futVars.first(); x != null; x = solver.futVars.next(x)) {
				if (first && x.dom.size() == 1)
					return x;
				bestScoredVariable.update(x, scoreOptimizedOf(x));
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

	public static abstract class WdegVariant extends HeuristicVariablesDynamic implements ObserverRuns, ObserverAssignment, ObserverConflicts, TagMaximize {

		private int time; // corresponds to the number of times a wipe-out occurred
		private int[] ctime; // ctime[i] corresponds to the last time a wipe-out occurred for constraint i

		public double[] vscores; // the score of all variables
		public double[] cscores; // the score of constraints (mainly used for CHS)

		double[][] cvscores;

		final double SMOOTHING = 0.995;
		final double ALPHA0 = 0.1, ALPHA_LIMIT = 0.06, ALPHA_DECREMENT = 0.000001; // for CHS
		double alpha; // for CHS

		@Override
		public void reset() {
			time = 0;
			Arrays.fill(ctime, 0);
			Arrays.fill(vscores, 0);
			Arrays.fill(cscores, 0);
			for (double[] t : cvscores)
				Arrays.fill(t, 0);
		}

		@Override
		public void beforeRun() {
			if (solver.restarter.runMultipleOf(solver.head.control.restarts.dataResetPeriod)
					|| (solver.restarter.numRun > 0 && (solver.restarter.numRun - solver.solManager.lastSolutionRun) % 30 == 0)) { // hard coding
				System.out.println("    ...resetting weights");
				reset();
				// solver.restarter.nRestartsSinceLastReset = 0;
			}
			alpha = ALPHA0;
			if (settings.weighting == EWeighting.CHS) { // smoothing
				for (int i = 0; i < cscores.length; i++)
					cscores[i] *= (Math.pow(SMOOTHING, time - ctime[i]));
			}
		}

		@Override
		public void afterAssignment(Variable x, int a) {
			if (settings.weighting != EWeighting.VAR && settings.weighting != EWeighting.CHS)
				for (Constraint c : x.ctrs)
					if (c.futvars.size() == 1) {
						int y = c.futvars.dense[0]; // the other variable whose score must be updated
						vscores[c.scp[y].num] -= cvscores[c.num][y];
					}
		}

		@Override
		public void afterUnassignment(Variable x) {
			if (settings.weighting != EWeighting.VAR && settings.weighting != EWeighting.CHS)
				for (Constraint c : x.ctrs)
					if (c.futvars.size() == 2) { // since a variable has just been unassigned, it means that there was only one future variable
						int y = c.futvars.dense[0]; // the other variable whose score must be updated
						vscores[c.scp[y].num] += cvscores[c.num][y];
					}
		}

		@Override
		public void whenWipeout(Constraint c, Variable x) {
			time++;
			if (settings.weighting == EWeighting.VAR)
				vscores[x.num]++;
			else if (c != null) {
				if (settings.weighting == EWeighting.CHS) {
					double r = 1.0 / (time - ctime[c.num]);
					double increment = alpha * (r - cscores[c.num]);
					cscores[c.num] += increment;
					// SetDense futvars = c.futvars;
					// for (int i = futvars.limit; i >= 0; i--) {
					// Variable y = c.scp[futvars.dense[i]];
					// vscores[y.num] += increment;
					// cvscores[c.num][futvars.dense[i]] += increment;
					// }

					// cscores[c.num] = (1 - alpha) * cscores[c.num] + alpha * (1.0 / (time - ctime[c.num]));
					alpha = Double.max(ALPHA_LIMIT, alpha - ALPHA_DECREMENT);
				} else {
					double increment = 1;
					cscores[c.num] += increment; // just +1 in that case (can be useful for other objects, but not directly for wdeg)
					SetDense futvars = c.futvars;
					for (int i = futvars.limit; i >= 0; i--) {
						Variable y = c.scp[futvars.dense[i]];
						if (settings.weighting == EWeighting.CACD) { // in this case, the increment is not 1 as for UNIT
							Domain dom = y.dom;
							boolean test = false; // hard coding ; this variant does not seem to be interesting
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

		public WdegVariant(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
			this.ctime = new int[solver.problem.constraints.length];
			this.vscores = new double[solver.problem.variables.length];
			this.cscores = new double[solver.problem.constraints.length];
			this.cvscores = Stream.of(solver.problem.constraints).map(c -> new double[c.scp.length]).toArray(double[][]::new);

			boolean b = false; // temporary
			if (b && solver.problem.optimizer != null && solver.problem.optimizer.ctr instanceof Sum) {
				Sum c = (Sum) solver.problem.optimizer.ctr;
				int[] coeffs = c instanceof SumSimple ? null : ((SumWeighted) c).coeffs;
				long[] gaps = IntStream.range(0, c.scp.length).mapToLong(i -> Math.abs((coeffs == null ? 1 : coeffs[i]) * c.scp[i].dom.intervalValue()))
						.toArray();
				long minGap = LongStream.of(gaps).min().getAsLong();
				for (int i = 0; i < c.scp.length; i++) {
					vscores[c.scp[i].num] += 1 + gaps[i] - minGap; // Math.log(1 + gaps[i] - minGap) / Math.log(2);
					// System.out.println("socre of " + c.scp[i] + " : " + vscores[c.scp[i].num]);
				}
			}
		}

	}

	public static class Wdeg extends WdegVariant {

		public Wdeg(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			if (settings.weighting == EWeighting.CHS) {
				double d = 0;
				for (Constraint c : x.ctrs)
					if (c.futvars.size() > 1)
						d += cscores[c.num];
				return d;
			}
			return vscores[x.num];
		}
	}

	public static class WdegOnDom extends WdegVariant {

		public WdegOnDom(Solver solver, boolean antiHeuristic) {
			super(solver, antiHeuristic);
		}

		@Override
		public double scoreOf(Variable x) {
			if (settings.weighting == EWeighting.CHS) {
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

	public static abstract class ActivityImpactAbstract extends HeuristicVariables implements ObserverRuns {
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
			Kit.control(solver.head.control.solving.branching == EBranching.BIN);
			Kit.control(solver.head.control.restarts.dataResetPeriod != 0);
		}

		protected abstract void update();

		@Override
		protected Variable bestUnpriorityVar() {
			assert lastVar != null || solver.depth() > lastDepth : lastVar + " " + solver.depth() + " " + lastDepth;
			if (lastVar != null)
				update();
			bestScoredVariable.reset(true);
			solver.futVars.execute(x -> {
				if (x.dom.size() > 1 || settings.singleton != ESingleton.LAST) {
					lastSizes[x.num] = x.dom.size();
					bestScoredVariable.update(x, scoreOptimizedOf(x));
				}
			});
			if (bestScoredVariable.variable == null) {
				assert settings.singleton == ESingleton.LAST;
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
			if (solver.restarter.runMultipleOf(solver.head.control.restarts.dataResetPeriod)) {
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
			if (solver.restarter.runMultipleOf(solver.head.control.restarts.dataResetPeriod)) {
				Kit.log.info("Reset of impacts");
				// for (int i = 0; i < solver.problem.variables.length; i++) impacts[i] = solver.problem.variables[i].getStaticDegree(); // TODO
				// better init ?
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
				impact = 0; // because the last positive decision failed, so a big impact (0 is the strongest impact value)
			impacts[lastVar.num] = (1 - alpha) * impacts[lastVar.num] + alpha * impact;
			assert 0 <= impact && impact <= 1 && 0 <= impacts[lastVar.num] && impacts[lastVar.num] <= 1;
		}

		@Override
		public double scoreOf(Variable x) {
			return impacts[x.num]; // note that 0 as value is the strongest impact value (we minimize)
		}

	}

}
