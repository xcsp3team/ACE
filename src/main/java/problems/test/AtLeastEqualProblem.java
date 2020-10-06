package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import problem.Problem;

public class AtLeastEqualProblem implements ProblemAPI {
	int n; // test for 8

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(rangeClosed(1, n)));

		allDifferent(x);
		((Problem) imp()).tupleProximityGE(x, vals(rangeClosed(1, n)), 6, true);
	}

}
