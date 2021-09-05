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

import interfaces.Tags.TagMaximize;
import propagation.Queue;
import variables.Variable;

/**
 * A revision ordering heuristic is attached to the propagation queue (set) that contains variables. <br />
 * It is used by the solver (actually, the propagation object) to select a variable in order to pursue constraint propagation.
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicRevisions extends Heuristic {

	/**
	 * The queue (propagation set) to which the revision ordering heuristic is attached.
	 */
	protected final Queue queue;

	/**
	 * Builds a revision ordering heuristic, to be used with the specified queue.
	 * 
	 * @param queue
	 *            a queue containing variables used during propagation
	 * @param antiHeuristic
	 *            indicates if one should take the reverse ordering of the natural one
	 */
	public HeuristicRevisions(Queue queue, boolean antiHeuristic) {
		super(antiHeuristic);
		this.queue = queue;
	}

	/**
	 * Returns the position of the preferred variable in the queue
	 * 
	 * @return a position in the queue
	 */
	public abstract int bestPosition();

	// ************************************************************************
	// ***** HeuristicRevisionsDirect
	// ************************************************************************

	public static abstract class HeuristicRevisionsDirect extends HeuristicRevisions {

		public HeuristicRevisionsDirect(Queue queue, boolean dummy) {
			super(queue, dummy);
		}

		// ************************************************************************
		// ***** Subclasses
		// ************************************************************************

		public final static class First extends HeuristicRevisionsDirect {

			public First(Queue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestPosition() {
				return 0;
			}
		}

		public final static class Last extends HeuristicRevisionsDirect {

			public Last(Queue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestPosition() {
				return queue.limit;
			}
		}

		public final static class Rand extends HeuristicRevisionsDirect {

			public Rand(Queue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestPosition() {
				return queue.propagation.solver.head.random.nextInt(queue.size());
			}
		}

	}

	// ************************************************************************
	// ***** HeuristicRevisionDynamic
	// ************************************************************************

	public static abstract class HeuristicRevisionsDynamic extends HeuristicRevisions {

		public HeuristicRevisionsDynamic(Queue queue, boolean antiHeuristic) {
			super(queue, antiHeuristic);
		}

		/**
		 * Returns the (raw) score of the specified variable (which is present in in the propagation queue). It is usually the method to overridde in order to
		 * define a new heuristic.
		 * 
		 * @param x
		 *            a variable
		 * @return the score of the specified variable according to the heuristic
		 */
		protected abstract double scoreOf(Variable x);

		@Override
		public int bestPosition() {
			int pos = 0;
			double bestScore = scoreOf(queue.var(0)) * multiplier;
			for (int i = 1; i <= queue.limit; i++) {
				double score = scoreOf(queue.var(i)) * multiplier;
				if (score > bestScore) {
					pos = i;
					bestScore = score;
				}
			}
			return pos;
		}

		// ************************************************************************
		// ***** Subclasses
		// ************************************************************************

		public final static class Dom extends HeuristicRevisionsDynamic {

			public Dom(Queue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.dom.size();
			}
		}

		public final static class Ddeg extends HeuristicRevisionsDynamic implements TagMaximize {

			public Ddeg(Queue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.ddeg();
			}
		}

		public final static class DdegOnDom extends HeuristicRevisionsDynamic implements TagMaximize {

			public DdegOnDom(Queue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.ddegOnDom();
			}
		}

		public final static class Wdeg extends HeuristicRevisionsDynamic implements TagMaximize {

			public Wdeg(Queue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.wdeg();
			}
		}

		public final static class WdegOnDom extends HeuristicRevisionsDynamic implements TagMaximize {

			public WdegOnDom(Queue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.wdegOnDom();
			}
		}

		public final static class Lexico extends HeuristicRevisionsDynamic {

			public Lexico(Queue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.num;
			}
		}
	}

}