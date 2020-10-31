package search.local.functionalPropagators;

import constraints.Constraint;
import variables.domains.Domain;

public class FunctionalPropagatorDirect extends FunctionalPropagator {

	public FunctionalPropagatorDirect(Constraint constraint, int outputPos) {
		super(constraint, outputPos);
	}

	@Override
	protected int getOutputVal(int[] tuple) {
		Domain dom = ctr.scp[outputPos].dom;
		int output = -1;
		for (int idx = 0; idx < dom.initSize(); idx++) {
			tuple[outputPos] = idx;
			if (ctr.checkIndexes(tuple))
				if (output != -1)
					return UNDECIDABLE;
				else
					output = idx;
		}
		assert (output != -1);
		return output;
	}

}
