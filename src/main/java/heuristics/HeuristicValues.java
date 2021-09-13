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
 * This class gives the description of a value ordering heuristic. <br>
 * A value ordering heuristic is attached to a variable and allows selecting (indexes of) values.
 */
public abstract class HeuristicValues extends Heuristic {

	public static final HeuristicValues buildFor(Variable x) {
		if (x.heuristic != null)
			return x.heuristic; // already built by some objects, we do not change it
		SettingValh settings = x.problem.head.control.valh;
		String className = x.dom instanceof DomainInfinite ? First.class.getName() : settings.heuristic;
		Set<Class<?>> classes = x.problem.head.availableClasses.get(HeuristicValues.class);
		HeuristicValues heuristic = Reflector.buildObject(className, classes, x, settings.anti);
		if (heuristic instanceof Bivs) {
			if (settings.bivsDistance < 2) {
				int distance = x.distanceWithObjective();
				if (distance == 2 || (distance == 1 && settings.bivsDistance == 0))
					heuristic = new First(x, settings.anti);
			}
		}
		return heuristic;
	}

	/** The variable that uses this value ordering heuristic. */
	protected final Variable x;

	/** The domain of the variable that uses this value ordering heuristic. Redundant field. */
	protected final Domain dx;

	protected SettingValh settings;

	public HeuristicValues(Variable x, boolean antiHeuristic) {
		super(antiHeuristic);
		this.x = x;
		this.dx = x.dom;
		this.settings = x.problem.head.control.valh;
		// this.priorityVar = x.pb.priorityVars != null && Kit.isPresent(x, x.pb.priorityVars);
	}

	/**
	 * Returns the (raw) score of the specified value index. This is usually the method to be overridden in order to define a new heuristic.
	 */
	protected abstract double scoreOf(int a);

	/**
	 * Returns the (index of the) preferred value in the domain of the variable.
	 */
	protected abstract int identifyBestValueIndex();

	public int bestIndex() {
		Solver solver = x.problem.solver;
		if (solver.solutions.found == 0) {
			if (settings.warmStart.length() > 0) {
				int a = solver.warmStarter.valueOf(x);
				if (a != -1 && dx.contains(a))
					return a;
			} else if (settings.runProgressSaving) {
				int a = solver.runProgressSaver.valueOf(x);
				if (a != -1 && dx.contains(a))
					return a;
			}
		} else if (settings.solutionSaving && !(this instanceof Bivs2)) {
			if (solver.restarter.numRun % settings.solutionSavingGap != 0) { // every k runs, we do not use solution saving
				// int a = -1;
				// if (x == solver.impacting)
				// a = dx.first();
				// else
				int a = solver.solutions.last[x.num];
				if (dx.contains(a)) // && (!priorityVar || solver.rs.random.nextDouble() < 0.5))
					return a;
			}
		}
		return identifyBestValueIndex();
	}

	// ************************************************************************
	// ***** HeuristicValuesFixed
	// ************************************************************************

	/**
	 * This class gives the description of a fixed/static value ordering heuristic. <br>
	 * It means that all values are definitively ordered at construction.
	 */
	public static abstract class HeuristicValuesFixed extends HeuristicValues {
		/** The set of (indexes of) values increasingly ordered by this static heuristic (the first one is the best one). */
		private final int[] fixed;

		public HeuristicValuesFixed(Variable x, boolean antiHeuristic) {
			super(x, antiHeuristic);
			// we build an ordered map with entries of the form (a, heuristic score of a multiplied by the optimization coefficient) for every a
			Map<Integer, Double> map = IntStream.range(0, dx.initSize()).filter(a -> dx.contains(a)).boxed()
					.collect(Collectors.toMap(a -> a, a -> scoreOf(a) * multiplier));
			map = Kit.sort(map, (e1, e2) -> e1.getValue() > e2.getValue() ? -1 : e1.getValue() < e2.getValue() ? 1 : e1.getKey() - e2.getKey());
			this.fixed = map.entrySet().stream().mapToInt(e -> e.getKey()).toArray();
		}

		@Override
		protected final int identifyBestValueIndex() {
			assert dx.size() > 0 : "The domain is empty";
			for (int a : fixed)
				if (dx.contains(a))
					return a;
			throw new AssertionError();
		}

		public static class LetterFrequency extends HeuristicValuesFixed implements TagExperimental {

			// Static order according to the frequency of letters in French; 'a' is the 3rd most frequent letter, 'b' is the 17th most frequent
			// letter,..., 'z' is the 23th most frequent letter. This corresponds to the order: e s a i t n r u l o d c p m v q f b g h j x y z w k
			private static int[] letterPositionsFr = { 2, 17, 11, 10, 0, 16, 18, 19, 3, 20, 25, 8, 13, 5, 9, 12, 15, 6, 1, 4, 7, 14, 24, 21, 22, 23 };

			public LetterFrequency(Variable x, boolean antiHeuristic) {
				super(x, antiHeuristic);
			}

			@Override
			public double scoreOf(int a) {
				return letterPositionsFr[a];
			}
		}

		public static final class Srand extends HeuristicValuesFixed {

			public Srand(Variable x, boolean antiHeuristic) {
				super(x, antiHeuristic);
			}

			@Override
			public double scoreOf(int a) {
				return x.problem.head.random.nextDouble();
			}
		}

	}

}