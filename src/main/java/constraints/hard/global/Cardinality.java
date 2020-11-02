package constraints.hard.global;

import static org.xcsp.modeler.definitions.IRootForCtrAndObj.map;

import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import constraints.hard.CtrGlobal;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public abstract class Cardinality extends CtrGlobal implements ObserverBacktrackingSystematic {

	public static class CardinalityConstant extends Cardinality implements TagFilteringCompleteAtEachCall, TagGACGuaranteed, ICtrCardinality {
		@Override
		public boolean checkValues(int[] t) {
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
			Kit.control(values.length == minOccs.length && values.length == maxOccs.length);
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
			this.maxOccs = Kit.repeat(1, values.length);
			int position = Utilities.indexOf(zeroValue, values);
			Kit.control(position >= 0);
			maxOccs[position] = Integer.MAX_VALUE;
			defineKey();
			matcher = new MatcherCardinality(this, scope, values, minOccs, maxOccs);
		}

		@Override
		public Map<String, Object> mapXCSP() {
			String o = IntStream.range(0, minOccs.length).mapToObj(i -> minOccs[i] == maxOccs[i] ? minOccs[i] + "" : minOccs[i] + ".." + maxOccs[i])
					.collect(Collectors.joining(" "));
			return map(SCOPE, scp, LIST, compact(scp), VALUES, Kit.join(values), CLOSED, null, OCCURS, o);
		}

	}

	protected Matcher matcher;

	@Override
	public void restoreBefore(int depth) {
		matcher.restoreAtDepthBefore(depth);
	}

	@Override
	public int[] defineSymmetryMatching() {
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
}
