/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package heuristics.revisions;

import heuristics.Heuristic;
import interfaces.TagMaximize;
import propagation.PropagationQueue;
import variables.Variable;

/**
 * A revision ordering heuristic is attached to a propagation set and involves selecting an element among those contained in it. NB : do not modify
 * the name of this class as it is used by reflection.
 */
public abstract class HeuristicRevisions extends Heuristic {

	/**
	 * The queue (propagation set) to which the revision ordering heuristic is attached.
	 */
	protected final PropagationQueue queue;

	public HeuristicRevisions(PropagationQueue queue, boolean antiHeuristic) {
		super(antiHeuristic);
		this.queue = queue;
	}

	/**
	 * Returns the position of the preferred element in the queue.
	 */
	public abstract int bestPosition();

	// ************************************************************************
	// ***** HeuristicRevisionsDirect
	// ************************************************************************

	public static abstract class HeuristicRevisionsDirect extends HeuristicRevisions {

		public HeuristicRevisionsDirect(PropagationQueue queue, boolean dummy) {
			super(queue, dummy);
		}

		// ************************************************************************
		// ***** Subclasses
		// ************************************************************************

		public final static class First extends HeuristicRevisionsDirect {

			public First(PropagationQueue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestPosition() {
				return 0;
			}
		}

		public final static class Last extends HeuristicRevisionsDirect {

			public Last(PropagationQueue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestPosition() {
				return queue.limit;
			}
		}

		public final static class Rand extends HeuristicRevisionsDirect {

			public Rand(PropagationQueue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestPosition() {
				return queue.propagation.solver.rs.random.nextInt(queue.size());
			}
		}

	}

	// ************************************************************************
	// ***** HeuristicRevisionDynamic
	// ************************************************************************

	public abstract static class HeuristicRevisionsDynamic extends HeuristicRevisions {

		public HeuristicRevisionsDynamic(PropagationQueue queue, boolean antiHeuristic) {
			super(queue, antiHeuristic);
		}

		/**
		 * Returns the (raw) score of the element in the queue at the specified position. It is usually the method to be overridden in order to define
		 * a new heuristic.
		 */
		protected abstract double scoreOf(Variable x);

		@Override
		public int bestPosition() {
			int pos = 0;
			double bestScore = scoreOf(queue.var(0)) * scoreCoeff;
			for (int i = 1; i <= queue.limit; i++) {
				double score = scoreOf(queue.var(i)) * scoreCoeff;
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

			public Dom(PropagationQueue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.dom.size();
			}
		}

		public final static class DDeg extends HeuristicRevisionsDynamic implements TagMaximize {

			public DDeg(PropagationQueue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.ddeg();
			}
		}

		public final static class DDegOnDom extends HeuristicRevisionsDynamic implements TagMaximize {

			public DDegOnDom(PropagationQueue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.ddegOnDom();
			}
		}

		public final static class WDeg extends HeuristicRevisionsDynamic implements TagMaximize {

			public WDeg(PropagationQueue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.wdeg();
			}
		}

		public final static class WDegOnDom extends HeuristicRevisionsDynamic implements TagMaximize {

			public WDegOnDom(PropagationQueue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.wdegOnDom();
			}
		}

		public final static class Lexico extends HeuristicRevisionsDynamic {

			public Lexico(PropagationQueue queue, boolean antiHeuristic) {
				super(queue, antiHeuristic);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.num;
			}
		}
	}

}