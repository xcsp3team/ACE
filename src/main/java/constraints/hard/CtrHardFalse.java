package constraints.hard;

import constraints.CtrHard;
import interfaces.FilteringSpecific;
import interfaces.TagFilteringCompleteAtEachCall;
import interfaces.TagGACGuaranteed;
import problem.Problem;
import variables.Variable;

public class CtrHardFalse extends CtrHard implements FilteringSpecific, TagFilteringCompleteAtEachCall, TagGACGuaranteed {

	@Override
	public boolean checkValues(int[] t) {
		return false;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		return false;
	}

	public String message;

	public CtrHardFalse(Problem pb, Variable[] scp, String message) {
		super(pb, scp);
		this.message = message;
	}

}
