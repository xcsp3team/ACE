package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class MinimumMaximumProblem implements ProblemAPI {

	@Override
	public void model() {
		Var x1 = var("x1", dom(1, 3, 5, 7, 9));
		Var x2 = var("x2", dom(2, 4, 5));
		Var x3 = var("x3", dom(3, 5, 8, 9));
		Var x4 = var("x4", dom(4, 5, 6));
		Var x5 = var("x5", dom(3, 5, 7));

		minimum(vars(x2, x3, x4, x5), x1);
		maximum(vars(x2, x3, x4, x1), x5);
	}
}
