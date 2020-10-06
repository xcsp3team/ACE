package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class GCCProblem implements ProblemAPI {

	@Override
	public void model() {
		Var v = var("v", dom(1, 3, 5, 7, 9));
		Var w = var("w", dom(2, 4, 5));
		Var x = var("x", dom(3, 5, 8, 9));
		Var y = var("y", dom(4, 5, 6));
		Var z = var("z", dom(3, 5, 7));

		cardinality(vars(v, w, x, y, z), vals(1, 2, 3, 4, 5), occurBetween(vals(0, 1, 0, 0, 3), vals(0, 1, 5, 0, 5)));
		maximum(vars(v, w, x, z), y);
	}
}
