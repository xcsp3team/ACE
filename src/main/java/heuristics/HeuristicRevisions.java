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
 * This is the root class for building revision ordering heuristics. A revision ordering heuristic is attached to the propagation queue (i.e., set used to guide
 * propagation). It is used by the solver (actually, the propagation object) to iteratively select variables (from the propagation queue) in order to perform
 * constraint propagation.
 * 
 * @author Christophe Lecoutre
 */
public abstract class HeuristicRevisions extends Heuristic {

	/**
	 * The queue (propagation set) to which the revision ordering heuristic is attached
	 */
	protected final Queue queue;

	protected final int limit;

	/**
	 * Builds a revision ordering heuristic, to be used with the specified queue
	 * 
	 * @param queue
	 *            a queue containing variables and used during propagation
	 * @param anti
	 *            indicates if one must take the reverse ordering of the natural one
	 */
	public HeuristicRevisions(Queue queue, boolean anti) {
		super(anti);
		this.queue = queue;
		this.limit = queue.propagation.solver.head.control.revh.revisionQueueLimit;
	}

	/**
	 * @return the position of the preferred variable in the queue, according to the heuristic
	 */
	public abstract int bestInQueue();

	/*************************************************************************
	 ***** HeuristicRevisionsDirect
	 *************************************************************************/

	/**
	 * This is the root class for building direct revision ordering heuristics, i.e., heuristics for which we directly know which element (variable position in
	 * the queue) has to be returned (without searching)
	 */
	public static abstract class HeuristicRevisionsDirect extends HeuristicRevisions {

		public HeuristicRevisionsDirect(Queue queue, boolean dummy) {
			super(queue, dummy); // dummy because has no influence with such heuristics
		}

		// ************************************************************************
		// ***** Subclasses
		// ************************************************************************

		public final static class First extends HeuristicRevisionsDirect {

			public First(Queue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestInQueue() {
				return 0;
			}
		}

		public final static class Last extends HeuristicRevisionsDirect {

			public Last(Queue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestInQueue() {
				return queue.limit;
			}
		}

		public final static class Rand extends HeuristicRevisionsDirect {

			public Rand(Queue queue, boolean dummy) {
				super(queue, dummy);
			}

			@Override
			public int bestInQueue() {
				return queue.propagation.solver.head.random.nextInt(queue.size());
			}
		}

	}

	/*************************************************************************
	 ***** HeuristicRevisionsDynamic
	 *************************************************************************/

	/**
	 * This is the root class for building dynamic revision ordering heuristics.
	 */
	public static abstract class HeuristicRevisionsDynamic extends HeuristicRevisions {

		public HeuristicRevisionsDynamic(Queue queue, boolean anti) {
			super(queue, anti);
		}

		/**
		 * Returns the (raw) score of the specified variable (which is present in in the propagation queue). This is the method to override for defining a new
		 * dynamic heuristic.
		 * 
		 * @param x
		 *            a variable
		 * @return the (raw) score of the specified variable, according to the heuristic
		 */
		protected abstract double scoreOf(Variable x);

		@Override
		public int bestInQueue() {
			if (queue.size() > limit)
				return 0;

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

			private int second = -1, secondDomSize = 0;

			public Dom(Queue queue, boolean anti) {
				super(queue, anti);
			}

			@Override
			public int bestInQueue() {
				// if (queue.size() > limit)
				// return 0;
				// System.out.println("gggg " + queue.size());

				// if (second != -1 && queue.size() > 35 && second < queue.size()) {
				// int i = second;
				// second = -1;
				// return i;
				// }

				int bestSize = queue.var(0).dom.size();
				if (bestSize <= queue.domSizeLowerBound)
					return 0; // because it is not possible to do better
				int pos = 0;

				if (queue.propagation.solver.head.control.revh.testr)
					// for (int i = 1; i <= queue.limit; i++) {
					for (int i = queue.limit; i >= 1; i--) {
						int otherSize = queue.var(i).dom.size();
						if (otherSize < bestSize) {
							// second = pos; secondDomSize = bestSize;
							if (otherSize <= queue.domSizeLowerBound) {
								assert otherSize == queue.domSizeLowerBound;
								return i; // because it is not possible to do better
							}
							pos = i;
							bestSize = otherSize;
						}
						// else if (otherSize < secondDomSize) {
						// second = i;
						// secondDomSize = otherSize;
						// }
					}
				else
					for (int i = 1; i <= queue.limit; i++) {
						int otherSize = queue.var(i).dom.size();
						if (otherSize < bestSize) {
							// second = pos; secondDomSize = bestSize;
							if (otherSize <= queue.domSizeLowerBound) {
								assert otherSize == queue.domSizeLowerBound;
								return i; // because it is not possible to do better
							}
							pos = i;
							bestSize = otherSize;
						}
						// else if (otherSize < secondDomSize) {
						// second = i;
						// secondDomSize = otherSize;
						// }
					}

				queue.domSizeLowerBound = bestSize; // we can update the bound (even if it may remain an approximation)
				return pos;
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.dom.size();
			}
		}

		public final static class Ddeg extends HeuristicRevisionsDynamic implements TagMaximize {

			public Ddeg(Queue queue, boolean anti) {
				super(queue, anti);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.ddeg();
			}
		}

		public final static class DdegOnDom extends HeuristicRevisionsDynamic implements TagMaximize {

			public DdegOnDom(Queue queue, boolean anti) {
				super(queue, anti);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.ddegOnDom();
			}
		}

		public final static class Wdeg extends HeuristicRevisionsDynamic implements TagMaximize {

			public Wdeg(Queue queue, boolean anti) {
				super(queue, anti);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.wdeg();
			}
		}

		public final static class WdegOnDom extends HeuristicRevisionsDynamic implements TagMaximize {

			public WdegOnDom(Queue queue, boolean anti) {
				super(queue, anti);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.wdegOnDom();
			}
		}

		public final static class Lexico extends HeuristicRevisionsDynamic {

			public Lexico(Queue queue, boolean anti) {
				super(queue, anti);
			}

			@Override
			protected double scoreOf(Variable x) {
				return x.num;
			}
		}
	}

}