package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class ElementVariableProblem implements ProblemAPI {

	int n; // Vector length

	@Override
	public void model() {
		Var[] list = array("x", size(n), dom(0, 1, 2));
		Var index = var("i", dom(range(n)));
		Var result = var("r", dom(0, 1, 2));
		element(list, index, result);
	}
}
