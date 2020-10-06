package constraints.hard;

import constraints.CtrHard;
import problem.Problem;
import variables.Variable;

public class CtrHardTrue extends CtrHard {

	public CtrHardTrue(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	@Override
	public boolean checkValues(int[] t) {
		return true;
	}

}
