package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.global.SeqBin;
import problem.Problem;
import variables.VariableInteger;

public class SeqBinProblem implements ProblemAPI {

	@Override
	public void model() {
		Var[] t = array("t", size(10), dom(0, 1, 2));
		Var k = var("k", dom(rangeClosed(1, 10)));

		((Problem) imp()).addCtr(new SeqBin(((Problem) imp()), (VariableInteger) k, (VariableInteger[]) t, NE, LE));

		maximize(k);
	}

}
