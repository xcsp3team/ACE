package constraints.global;

import static utility.Kit.control;

import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

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

	public static class CardinalityConstant extends Cardinality implements TagCallCompleteFiltering, TagAC {
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

		private int[] values;
		private int[] minOccs;
		private int[] maxOccs;

		public CardinalityConstant(Problem pb, Variable[] scp, int[] values, int[] minOccs, int[] maxOccs) {
			super(pb, scp);
			control(values.length == minOccs.length && values.length == maxOccs.length);
			this.values = values;
			this.minOccs = minOccs;
			this.maxOccs = maxOccs;
			defineKey();
			matcher = new MatcherCardinality(this, scp, values, minOccs, maxOccs);
		}

		public CardinalityConstant(Problem problem, Variable[] scope, int[] values, int[] nOccs) {
			this(problem, scope, values, nOccs, nOccs);
		}

		// constructor for allDiff except 0
		public CardinalityConstant(Problem problem, Variable[] scope, int zeroValue) {
			super(problem, scope);
			this.values = Kit.sort(Kit.intArray(Variable.setOfvaluesIn(scope)));
			this.minOccs = Kit.repeat(0, values.length);
			int position = Utilities.indexOf(zeroValue, values);
			control(position >= 0);
			this.maxOccs = IntStream.range(0, values.length).map(i -> i == position ? Integer.MAX_VALUE : 1).toArray();
			this.matcher = new MatcherCardinality(this, scope, values, minOccs, maxOccs);
			defineKey();
		}

	}
}
