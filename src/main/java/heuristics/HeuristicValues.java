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

import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import dashboard.Control.SettingValh;
import heuristics.HeuristicValuesDirect.First;
import heuristics.HeuristicValuesDynamic.Bivs;
import heuristics.HeuristicValuesDynamic.Bivs2;
import interfaces.Tags.TagExperimental;
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
		SettingValh settings = x.problem.head.control.valh;
		String className = x.dom instanceof DomainInfinite ? First.class.getName() : settings.clazz;
		Set<Class<?>> classes = x.problem.head.availableClasses.get(HeuristicValues.class);
		HeuristicValues heuristic = Reflector.buildObject(className, classes, x, settings.anti);
		if (heuristic instanceof Bivs && settings.bivsDistance < 2) { // limited form of Bivs according to the distance
			int distance = x.distanceWithObjective();
			if (distance == 2 || (distance == 1 && settings.bivsDistance == 0))
				heuristic = new First(x, settings.anti);
		}
		return heuristic;
	}

	/**
	 * The variable to which this value ordering heuristic is attached
	 */
	protected final Variable x;

	/**
	 * The domain of the variable x (redundant field)
	 */
	protected final Domain dx;

	/**
	 * The setting options concerning the value ordering heuristics
	 */
	protected SettingValh settings;

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
		this.settings = x.problem.head.control.valh;
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
		} else if (settings.solutionSaving > 0 && !(this instanceof Bivs2)) {
			// note that solution saving may break determinism of search trees because it depends in which order domains
			// are pruned (and become singleton or not)
			if (settings.solutionSaving == 1 || solver.restarter.numRun == 0 || solver.restarter.numRun % settings.solutionSaving != 0) {
				// every k runs, we do not use solution saving, where k is the value of solutionSaving (if k > 1)
				// int a = -1; if (x == solver.impacting) a = dx.first(); else
				int a = solver.solutions.last[x.num];
				if (dx.contains(a)) // && (!priorityVar || solver.rs.random.nextDouble() < 0.5))
					return a;
			}
		}
		return computeBestValueIndex();
	}

	// ************************************************************************
	// ***** HeuristicValuesFixed
	// ************************************************************************

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