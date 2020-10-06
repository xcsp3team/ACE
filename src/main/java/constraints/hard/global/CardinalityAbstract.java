package constraints.hard.global;

import constraints.hard.CtrGlobal;
import interfaces.ObserverBacktracking.ObserverBacktrackingSystematic;
import problem.Problem;
import utility.Kit;
import variables.Variable;

public abstract class CardinalityAbstract extends CtrGlobal implements ObserverBacktrackingSystematic {

	protected Matcher matcher;

	@Override
	public void restoreBefore(int depth) {
		matcher.restoreAtDepthBefore(depth);
	}

	@Override
	public int[] defineSymmetryMatching() {
		return Kit.range(1, scp.length); // TODO to be defined more precisely
	}

	public CardinalityAbstract(Problem problem, Variable[] scope) {
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
