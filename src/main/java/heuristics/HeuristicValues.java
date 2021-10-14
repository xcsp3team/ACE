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

import java.util.Arrays;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import constraints.Constraint;
import constraints.global.Extremum.ExtremumCst;
import constraints.global.NValues.NValuesCst;
import constraints.global.NValues.NValuesCst.NValuesCstLE;
import constraints.global.Sum.SumSimple;
import constraints.global.Sum.SumWeighted;
import dashboard.Control.OptionsValh;
import heuristics.HeuristicValuesDirect.First;
import heuristics.HeuristicValuesDirect.Last;
import heuristics.HeuristicValuesDirect.Values;
import heuristics.HeuristicValuesDynamic.Bivs;
import heuristics.HeuristicValuesDynamic.Bivs2;
import interfaces.Tags.TagExperimental;
import optimization.ObjectiveVariable;
import problem.Problem;
import problem.Problem.Term;
import solver.Solver;
import utility.Kit;
import utility.Reflector;
import variables.Domain;
import variables.DomainInfinite;
import variables.Variable;

/**
 * This is the class for building value ordering heuristics. A value ordering heuristic is attached to a variable and
 * allows us to select (indexes of) values.
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

	private static Variable[] prioritySumVars(Variable[] scp, int[] coeffs) {
		assert coeffs == null || IntStream.range(0, coeffs.length - 1).allMatch(i -> coeffs[i] <= coeffs[i + 1]);
		int LIM = 3; // hard coding
		Term[] terms = new Term[Math.min(scp.length, 2 * LIM)];
		if (terms.length == scp.length)
			for (int i = 0; i < terms.length; i++)
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * scp[i].dom.distance(), scp[i]);
		else {
			for (int i = 0; i < LIM; i++)
				terms[i] = new Term((coeffs == null ? 1 : coeffs[i]) * scp[i].dom.distance(), scp[i]);
			for (int i = 0; i < LIM; i++)
				terms[LIM + i] = new Term((coeffs == null ? 1 : coeffs[scp.length - 1 - i]) * scp[scp.length - 1 - i].dom.distance(), scp[scp.length - 1 - i]);
		}
		// we discard terms of small coeffs
		terms = Stream.of(terms).filter(t -> t.coeff < -2 || t.coeff > 2).sorted().toArray(Term[]::new);
		if (terms.length > 0) {
			Variable[] t = Stream.of(terms).map(term -> term.obj).toArray(Variable[]::new);
			Variable[] tt = t.length > LIM ? Arrays.copyOfRange(t, t.length - LIM, t.length) : t;
			return IntStream.range(0, tt.length).mapToObj(i -> tt[tt.length - 1 - i]).toArray(Variable[]::new);
		}
		return null;
	}

	/**
	 * Possibly modifies the value ordering heuristics of some variables according to the objective function
	 * (constraint), and returns the variables that must be considered as being priority for search, or null.
	 * EXPERIMENTAL (code to be finalized)
	 * 
	 * @param problem
	 *            a problem
	 * @return the variables that must be considered as being priority for search, or null
	 */
	public static Variable[] possibleOptimizationInterference(Problem problem) {
		if (problem.optimizer == null || !problem.head.control.valh.optValHeuristic) // experimental
			return null;
		boolean strong = false; // hard coding
		Constraint c = ((Constraint) problem.optimizer.ctr);
		boolean minimization = problem.optimizer.minimization;
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
				for (Variable x : c.scp)
					x.heuristic = new Values(x, false, c.scp);
			return null;
		}
		if (c instanceof SumWeighted || c instanceof SumSimple) {
			int[] coeffs = c instanceof SumSimple ? null : ((SumWeighted) c).coeffs;
			Variable[] vars = prioritySumVars(c.scp, coeffs);
			if (vars != null) {
				for (Variable x : vars) {
					int coeff = c instanceof SumSimple ? 1 : coeffs[c.positionOf(x)];
					boolean f = minimization && coeff >= 0 || !minimization && coeff < 0;
					System.out.println("before " + x + " " + x.heuristic);
					x.heuristic = f ? new First(x, false) : new Last(x, false); // the boolean is dummy
					System.out.println("after " + x.heuristic);
				}
				return vars;
			}
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
	 * Returns the (raw) score of the specified value index. This is the method to override for defining a new
	 * heuristic.
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
	 * Returns the preferred value index in the current domain of x according to the heuristic. Meta-reasoning
	 * techniques such as warm starting, run progress saving and solution saving are checked first before considering
	 * the heuristic selection criterion.
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
				if (a != -1 && dx.contains(a))
					return a;
			}
		} else if (options.solutionSaving > 0 && !(this instanceof Bivs2)) {
			// note that solution saving may break determinism of search trees because it depends in which order domains
			// are pruned (and become singleton or not)
			if (options.solutionSaving == 1 || solver.restarter.numRun == 0 || solver.restarter.numRun % options.solutionSaving != 0) {
				// every k runs, we do not use solution saving, where k is the value of solutionSaving (if k > 1)
				// int a = -1; if (x == solver.impacting) a = dx.first(); else
				int a = solver.solutions.last[x.num];
				if (dx.contains(a)) // && (!priorityVar || solver.rs.random.nextDouble() < 0.5))
					return a;
			}
		}
		return computeBestValueIndex();
	}

	/*************************************************************************
	 ***** HeuristicValuesStatic
	 *************************************************************************/

	/**
	 * This is the class for building static value ordering heuristics. It means that, for such heuristics, all values
	 * are definitively ordered at construction.
	 */
	public static abstract class HeuristicValuesStatic extends HeuristicValues {

		/**
		 * The set of indexes (of values) increasingly ordered by this static heuristic (the first one is the best one).
		 */
		private final int[] fixed;

		public HeuristicValuesStatic(Variable x, boolean anti) {
			super(x, anti);
			// we build an ordered map with entries of the form (a, heuristic score of a multiplied by the optimization
			// coefficient) for every a
			Map<Integer, Double> map = IntStream.range(0, dx.initSize()).filter(a -> dx.contains(a)).boxed()
					.collect(Collectors.toMap(a -> a, a -> scoreOf(a) * multiplier));
			map = Kit.sort(map, (e1, e2) -> e1.getValue() > e2.getValue() ? -1 : e1.getValue() < e2.getValue() ? 1 : e1.getKey() - e2.getKey());
			this.fixed = map.entrySet().stream().mapToInt(e -> e.getKey()).toArray();
		}

		@Override
		protected final int computeBestValueIndex() {
			for (int a : fixed)
				if (dx.contains(a))
					return a;
			throw new AssertionError("The domain is empty");
		}

		public static final class Srand extends HeuristicValuesStatic {

			public Srand(Variable x, boolean anti) {
				super(x, anti);
			}

			@Override
			public double scoreOf(int a) {
				return x.problem.head.random.nextDouble();
			}
		}

		public static final class LetterFrequency extends HeuristicValuesStatic implements TagExperimental {

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

}