package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class SimpleObjectiveProblem implements ProblemAPI {

	@Override
	public void model() {
		Var[] x = array("x", size(6), dom(range(-2, 4)));
		Var y = var("y", dom(rangeClosed(-100, 100)));

		allDifferent(x);
		equal(y, min(add(x[0], mul(max(x[1], x[2]), sub(x[3], x[4]))), x[5]));

		maximize(y);
	}
}
