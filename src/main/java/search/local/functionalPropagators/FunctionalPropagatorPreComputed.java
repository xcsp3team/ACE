package search.local.functionalPropagators;

import org.xcsp.common.enumerations.EnumerationCartesian;

import constraints.CtrHard;
import utility.Kit;
import variables.Variable;

public class FunctionalPropagatorPreComputed extends FunctionalPropagator {

	protected int[] encodedOutputs;

	int[][] buildArraysWithCurrentIndexes(Variable[] vars) {
		int[][] m = new int[vars.length][];
		for (int i = 0; i < m.length; i++)
			m[i] = vars[i].dom.indexes();
		return m;
	}

	public FunctionalPropagatorPreComputed(CtrHard constraint, int outputPos, int encodingSize) {
		super(constraint, outputPos);
		// Kit.pr("Constraint : ");
		// constraint.display(false);
		// Kit.prn("Output pos : " + outputPos);
		encodedOutputs = Kit.repeat(-1, encodingSize);

		int[][] tuples = new EnumerationCartesian(buildArraysWithCurrentIndexes(constraint.scp), false).toArray();
		for (int[] tuple : tuples) {
			if (constraint.checkIndexes(tuple)) {
				int key = encode(tuple);
				if (encodedOutputs[key] == -1)
					encodedOutputs[key] = tuple[outputPos];
				else
					encodedOutputs[key] = UNDECIDABLE;
				// Kit.pr("Encoded tuple ");
				// for (int i = 0; i < tuple.length; i++)
				// Kit.pr(constraint.getScope(i).domain.toValue(tuple[i]) + " ");
				// Kit.prn(" as key " + key + " index is " + encodedOutputs[key] + ".");
				// if (key < 0)
				// Kit.prn("NEGATIVE KEY : " + key);
				// else if (encodedOutputs[key] < 0)
				// Kit.prn("NEGATIVE INDEX : " + encodedOutputs[key]);
				// else if (!constraint.getScope(outputPos).domain.hasIndex(encodedOutputs[key]))
				// Kit.prn("INDEX NOT IN DOMAIN : " + encodedOutputs[key]);
				// else
				// if (encodedOutputs[key] >= 0)
				// Kit.prn("Result : " + constraint.getScope(outputPos).domain.toValue(encodedOutputs[key]));
			}

		}
	}

	protected int encode(int[] tuple) {
		int key = 0;
		int base = 1;
		for (int i = 0; i < tuple.length; i++) {
			if (i != outputPos) {
				key += tuple[i] * base;
				base *= ctr.scp[i].dom.initSize();
			}
		}
		return key;
	}

	@Override
	protected int getOutputVal(int[] tuple) {
		return encodedOutputs[encode(tuple)];
	}

}
