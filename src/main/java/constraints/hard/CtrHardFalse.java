package constraints.hard;

import constraints.CtrHard;
import problem.Problem;
import variables.Variable;

public class CtrHardFalse extends CtrHard {

	@Override
	public boolean checkValues(int[] t) {
		return false;
	}

	public String message;

	public CtrHardFalse(Problem pb, Variable[] scp, String message) {
		super(pb, scp);
		this.message = message;
	}

}
