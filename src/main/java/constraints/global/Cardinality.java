/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package constraints.global;

import static utility.Kit.control;

import constraints.ConstraintGlobal;
import constraints.global.Matcher.MatcherCardinality;
import interfaces.Observers.ObserverOnBacktracks.ObserverOnBacktracksSystematic;
import interfaces.Tags.TagAC;
import interfaces.Tags.TagCallCompleteFiltering;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public abstract class Cardinality extends ConstraintGlobal implements ObserverOnBacktracksSystematic {

	protected Matcher matcher;

	@Override
	public void restoreBefore(int depth) {
		matcher.restoreAtDepthBefore(depth);
	}

	@Override
	public int[] symmetryMatching() {
		return Kit.range(1, scp.length); // TODO to be defined more precisely
	}

	public Cardinality(Problem problem, Variable[] scope) {
		super(problem, scope);
	}

	@Override
	public boolean runPropagator(Variable x) {
		if (!matcher.findMaximumMatching())
			return x.dom.fail();
		matcher.removeInconsistentValues();
		return true;
	}

	public static final class CardinalityConstant extends Cardinality implements TagAC, TagCallCompleteFiltering {

		@Override
		public boolean isSatisfiedBy(int[] t) {
			for (int i = 0; i < values.length; i++) {
				int nOccurrences = 0;
				for (int j = 0; j < t.length; j++)
					if (t[j] == values[i])
						nOccurrences++;
				if (nOccurrences < minOccs[i] || nOccurrences > maxOccs[i])
					return false;
			}
			return true;
		}

		/**
		 * The values that must be counted
		 */
		private final int[] values;

		/**
		 * minOccs[i] is the required minimal number of occurrences of the value values[i]
		 */
		private final int[] minOccs;

		/**
		 * maxOccs[i] is the required maximal number of occurrences of the value values[i]
		 */
		private final int[] maxOccs;

		public CardinalityConstant(Problem pb, Variable[] scp, int[] values, int[] minOccs, int[] maxOccs) {
			super(pb, scp);
			control(values.length == minOccs.length && values.length == maxOccs.length);
			this.values = values;
			this.minOccs = minOccs;
			this.maxOccs = maxOccs;
			this.matcher = new MatcherCardinality(this, scp, values, minOccs, maxOccs);
			defineKey(values, minOccs, maxOccs);
		}

		public CardinalityConstant(Problem pb, Variable[] scp, int[] values, int[] nOccs) {
			this(pb, scp, values, nOccs, nOccs);
		}

		public CardinalityConstant(Problem pb, Variable[] scp, int[] values, int minOccs, int maxOccs) {
			this(pb, scp, values, Kit.repeat(minOccs, values.length), Kit.repeat(maxOccs, values.length));
		}
	}

}
