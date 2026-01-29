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

import java.util.Arrays;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.modeler.entities.VarEntities.VarArray;

import constraints.Constraint;
import constraints.global.Extremum.ExtremumCst;
import constraints.global.NValues.NValuesCst;
import constraints.global.NValues.NValuesCst.NValuesCstLE;
import constraints.global.Sum;
import constraints.global.Sum.SumSimple;
import constraints.global.Sum.SumWeighted;
import dashboard.Control.OptionsValh;
import heuristics.HeuristicValuesDirect.First;
import heuristics.HeuristicValuesDirect.Last;
import heuristics.HeuristicValuesDirect.Vals;
import heuristics.HeuristicValuesDynamic.Bivs;
import interfaces.Tags.TagExperimental;
import optimization.ObjectiveUnary.ObjectiveVariable;
import problem.Problem;
import problem.Problem.Term;
import solver.Solver;
import utility.Kit;
import utility.Reflector;
import variables.Domain;
import variables.DomainInfinite;
import variables.Variable;

/**
 * This is the class for building value ordering heuristics. A value ordering heuristic is attached to a variable and allows us to select (indexes of) values.
 *
 * @author Christophe Lecoutre
 */
public abstract class HeuristicValues extends Heuristic {

	/*************************************************************************
	 ***** Static members
	 *************************************************************************/

	/**
	 * Builds and returns a value ordering heuristic to be used for the specified variable
	 *
	 * @param x
	 *            a variable
	 * @return a value ordering heuristic for the specified variable
	 */
	public static final HeuristicValues buildFor(Variable x) {
		if (x.heuristic != null)
			return x.heuristic; // already built by some objects, so we do not change it
		OptionsValh options = x.problem.head.control.valh;
		String className = x.dom instanceof DomainInfinite ? First.class.getName() : options.clazz;
		Set<Class<?>> classes = x.problem.head.availableClasses.get(HeuristicValues.class);
		HeuristicValues heuristic = Reflector.buildObject(className, classes, x, options.anti);
		if (heuristic instanceof Bivs && !((Bivs) heuristic).canBeApplied())
			heuristic = new First(x, options.anti); // we change because Bivs cannot be applied
		return heuristic;
	}

	public static Variable[] prioritySumVars(Variable[] scp, int[] coeffs) {
		assert coeffs == null || IntStream.range(0, coeffs.length - 1).allMatch(i -> coeffs[i] <= coeffs[i + 1]);
		int LIM = 415; // hard coding
		Term[] terms = new Term[Math.min(scp.length, 2 * LIM)];
		if (terms.length == scp.length)
			for (int i = 0; i < terms.length; i++)
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * (long) scp[i].dom.distance(), scp[i]);
		else {
			for (int i = 0; i < LIM; i++)
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * (long) scp[i].dom.initDistance(), scp[i]);
			for (int i = 0; i < LIM; i++)
				terms[LIM + i] = new Term((coeffs == null ? 1 : coeffs[scp.length - 1 - i]) * (long) scp[scp.length - 1 - i].dom.distance(),
						scp[scp.length - 1 - i]);
		}
		// we discard terms of small coeffs
		// terms = Stream.of(terms).filter(t -> t.coeff < -2 || t.coeff > 2).sorted().toArray(Term[]::new);
		if (terms.length > 0) {
			Variable[] t = Stream.of(terms).map(term -> term.variable).toArray(Variable[]::new);
			Variable[] tt = t.length > LIM ? Arrays.copyOfRange(t, t.length - LIM, t.length) : t;
			return IntStream.range(0, tt.length).mapToObj(i -> tt[tt.length - 1 - i]).toArray(Variable[]::new);
		}
		return null;
	}

	/**
	 * Possibly modifies the value ordering heuristics of some variables according to the objective function (constraint), and returns the variables that must
	 * be considered as being priority for search, or null.
	 *
	 * TODO: EXPERIMENTAL (code to be finalized)
	 *
	 * @param problem
	 *            a problem
	 * @return the variables that must be considered as being priority for search, or null
	 */
	public static Variable[] possibleOptimizationInterference(Problem problem) {
		if (problem.optimizer == null)
			return null;
		Constraint c = ((Constraint) problem.optimizer.ctr);
		boolean minimization = problem.optimizer.minimization;
		if (problem.head.control.valh.optValHeuristic) {
			if (c instanceof Sum) {
				long[] t = IntStream.range(0, c.scp.length)
						.mapToLong(i -> (c instanceof SumWeighted ? ((SumWeighted) c).coeffs[i] : 1) * c.scp[i].dom.distance()).toArray();
				System.out.println("jjjjj " + Kit.join(t));
				for (int i = 0; i < c.scp.length; i++)
					c.scp[i].specificWeight = 1 / Math.max(1, Math.abs(t[i]));
			}
			return null;
		}

		if (!problem.head.control.valh.optValHeuristic) // experimental
			return null;
		boolean strong = true; // hard coding
		if (c instanceof ObjectiveVariable) {
			Variable x = c.scp[0];
			x.heuristic = minimization ? new First(x, false) : new Last(x, false);
			return new Variable[] { x };
		}
		if (c instanceof ExtremumCst) {
			if (strong)
				for (Variable x : c.scp)
					x.heuristic = minimization ? new First(x, false) : new Last(x, false); // the boolean is dummy
			return null;
		}
		if (c instanceof NValuesCst) {
			assert c instanceof NValuesCstLE;
			if (strong)
				for (Variable x : c.scp) {
					x.heuristic = new Vals(x, false);
					((Vals) x.heuristic).variablesOfInterest = c.scp;
				}
			return null;
		}
		if (c instanceof SumWeighted || c instanceof SumSimple) {
			for (Variable x : c.scp)
				x.heuristic = minimization ? new First(x, false) : new Last(x, false); // the boolean is dummy
			return c.scp;
			// int[] coeffs = c instanceof SumSimple ? null : ((SumWeighted) c).coeffs;
			// Variable[] vars = prioritySumVars(c.scp, coeffs);
			// if (vars != null) {
			// for (Variable x : vars) {
			// int coeff = coeffs == null ? 1 : coeffs[c.positionOf(x)];
			// boolean f = minimization && coeff >= 0 || !minimization && coeff < 0;
			// x.heuristic = f ? new First(x, false) : new Last(x, false); // the boolean is dummy
			// }
			// return vars; }
		}
		return null;
	}

	/*************************************************************************
	 ***** Fields and Methods
	 *************************************************************************/

	/**
	 * The variable to which this value ordering heuristic is attached
	 */
	protected final Variable x;

	/**
	 * The domain of the variable x (redundant field)
	 */
	protected final Domain dx;

	/**
	 * The options concerning the value ordering heuristics
	 */
	protected OptionsValh options;

	/**
	 * Builds a value ordering heuristic for the specified variable
	 *
	 * @param x
	 *            the variable to which this object is attached
	 * @param anti
	 *            indicates if one must take the reverse ordering of the natural one
	 */
	public HeuristicValues(Variable x, boolean anti) {
		super(anti);
		this.x = x;
		this.dx = x.dom;
		this.options = x.problem.head.control.valh;
	}

	/**
	 * Returns either the variables of the array to which x belongs or all problem variables (if x does not belong to an array)
	 *
	 * @return either the variables of the array to which x belongs or all problem variables
	 */
	public Variable[] variablesOfInterest() {
		VarArray va = x.problem.varEntities.varToVarArray.get(x);
		return va != null ? (Variable[]) va.flatVars : x.problem.variables;
	}

	/**
	 * Returns the (raw) score of the specified value index. This is the method to override for defining a new heuristic.
	 *
	 * @param a
	 *            a value index
	 * @return the (raw) score of the specified value index
	 */
	protected abstract double scoreOf(int a);

	/**
	 * Searches and returns the preferred value index in the current domain of x, according to the heuristic
	 *
	 * @return the preferred value index in the current domain of x
	 */
	protected abstract int computeBestValueIndex();

	/**
	 * Returns the preferred value index in the current domain of x according to the heuristic. Meta-reasoning techniques such as warm starting, run progress
	 * saving and solution saving are checked first before considering the heuristic selection criterion.
	 *
	 * @return the preferred value index in the current domain of x
	 */
	public final int bestValueIndex() {
		Solver solver = x.problem.solver;
		if (solver.solutions.found == 0) {
			if (solver.warmStarter != null) {
				int a = solver.warmStarter.valueIndexOf(x);
				if (a != -1 && dx.contains(a))
					return a;
			} else if (solver.runProgressSaver != null) {
				int a = solver.runProgressSaver.valueIndexOf(x);
				if (a != -1) {
					if (options.antiRunProgressSaving) {
						// only coded wrt First as heuristic
						if (dx.size() == 1 || dx.first() != a)
							return dx.first();
						else
							return dx.next(dx.first());
					} else if (dx.contains(a))
						return a;
				}
			} else if (solver.sticking != null) {
				int a = solver.sticking[x.num];
				if (a != -1 && dx.contains(a)) {
					if (options.stickingMode == 2)
						solver.sticking[x.num] = -1;
					return a;
				}
			}
		} else { // at least one solution has been found
			int numRun = solver.restarter.numRun;
			if (options.solutionSaving > 0 && numRun >= options.solutionSavingStart) { // && !(this instanceof Bivs2) && numRun >= options.solutionSavingStart)
																						// {
				// note that solution saving may break determinism of search trees because it depends in which order domains
				// are pruned (and become singleton or not)
				if (options.solutionSaving == 1 || numRun == 0 || numRun % options.solutionSaving != 0) {
					// every k runs, we do not use solution saving, where k is the value of solutionSaving (if k > 1)
					// int a = -1; if (x == solver.impacting) a = dx.first(); else
					int nb = solver.restarter.howManyRunsSincelastSolution();
					// System.out.println(nb);
					// boolean followEvenObj = !options.solutionSavingExceptObj && !(nb > 12 && nb % 2 == 0);
					// boolean followEvenObj = (nb == -1 || (numRun / 12) % 2 == 1); // nb <= 12 || (nb /12) %2 == 0);
					// if (!followEvenObj)
					// System.out.println(nb);
					if (!options.solutionSavingExceptObj || x.problem.optimizer == null || !((Constraint) x.problem.optimizer.ctr).involves(x)) {
						int a = solver.solutions.last.idxs[x.num];
						if (dx.contains(a)) // && (!priorityVar || solver.rs.random.nextDouble() < 0.5))
							return a;
					}
				}
			}
			// if (solver.sticking != null) {
			// int a = solver.sticking[x.num];
			// if (a != -1 && dx.contains(a)) {
			// solver.sticking[x.num] = -1;
			// return a;
			// }
			// }
		}
		return computeBestValueIndex();
	}

	/*************************************************************************
	 ***** Static Heuristics
	 *************************************************************************/

	/**
	 * This is the class for building static value ordering heuristics. It means that, for such heuristics, all values are definitively ordered at construction.
	 */
	public static abstract class HeuristicValuesStatic extends HeuristicValues {

		/**
		 * The set of indexes (of values) increasingly ordered by this static heuristic (the first one is the best one).
		 */
		protected int[] fixed;

		public HeuristicValuesStatic(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		protected final int computeBestValueIndex() {
			for (int a : fixed)
				if (dx.contains(a))
					return a;
			return dx.first(); // we return the first index otherwise (in case, fixed is incomplete) new AssertionError("The domain is empty");
		}

		public static final class Arbitrary extends HeuristicValuesStatic {

			public Arbitrary(Variable x, boolean anti, int[] fixed) {
				super(x, anti);
				this.fixed = fixed;
			}

			public Arbitrary(Variable x, int[] fixed) {
				this(x, false, fixed);
			}

			@Override
			protected double scoreOf(int a) {
				return 0; // dummy method
			}

		}

		public static abstract class HeuristicValuesStaticInitiallyComputed extends HeuristicValuesStatic {

			public HeuristicValuesStaticInitiallyComputed(Variable x, boolean anti) {
				super(x, anti);
				// we build an ordered map with entries of the form (a, heuristic score of a multiplied by the optimization
				// coefficient) for every a
				Map<Integer, Double> map = IntStream.range(0, dx.initSize()).filter(a -> dx.contains(a)).boxed()
						.collect(Collectors.toMap(a -> a, a -> scoreOf(a) * multiplier));
				map = Kit.sort(map, (e1, e2) -> e1.getValue() > e2.getValue() ? -1 : e1.getValue() < e2.getValue() ? 1 : e1.getKey() - e2.getKey());
				this.fixed = map.entrySet().stream().mapToInt(e -> e.getKey()).toArray();
			}
		}

		public static final class Srand extends HeuristicValuesStaticInitiallyComputed {

			public Srand(Variable x, boolean anti) {
				super(x, anti);
			}

			@Override
			public double scoreOf(int a) {
				return x.problem.head.random.nextDouble();
			}
		}

		public static final class LetterFrequency extends HeuristicValuesStaticInitiallyComputed implements TagExperimental {

			// Static order according to the frequency of letters in French; 'a' is the 3rd most frequent letter, 'b' is
			// the 17th most frequent letter,..., 'z' is the 23th most frequent letter. This corresponds to the order: e
			// s a i t n r u l o d c p m v q f b g h j x y z w k
			private static int[] fr = { 2, 17, 11, 10, 0, 16, 18, 19, 3, 20, 25, 8, 13, 5, 9, 12, 15, 6, 1, 4, 7, 14, 24, 21, 22, 23 };

			public LetterFrequency(Variable x, boolean anti) {
				super(x, anti);
			}

			@Override
			public double scoreOf(int a) {
				return fr[a];
			}
		}
	}

	/*************************************************************************
	 ***** Experimental
	 *************************************************************************/

	public static int cntCBval = 0;

	public static class CBVal extends HeuristicValues {

		public CBVal(Variable x, boolean anti) {
			super(x, anti);
		}

		@Override
		protected final int computeBestValueIndex() {
			Constraint best = null;
			double bestScore = -1;
			for (Constraint c : x.ctrs) {
				if (c.ignored || x.problem.solver.isEntailed(c))
					continue;
				if (c.wdeg() > bestScore) {
					best = c;
					bestScore = c.wdeg();
				}
			}
			if (best == null)
				return x.dom.first();
			int a = best.giveMostPromisingValueIndexFor(x, options.antiCBval);
			if (a != -1)
				cntCBval++;
			return a == -1 ? x.dom.first() : a;
		}

		@Override
		protected double scoreOf(int a) {
			throw new UnsupportedOperationException();
		}

	}

}
