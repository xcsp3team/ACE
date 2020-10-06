package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class AllDifferentExcept0Problem implements ProblemAPI {
	int n;

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(3)));
		allDifferent(x, exceptValue(0));
	}
}
