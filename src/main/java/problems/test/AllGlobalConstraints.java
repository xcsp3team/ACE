package problems.test;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;

public class AllGlobalConstraints implements ProblemAPI {

	@Override
	public void model() {
		Var[] x = array("x", size(100), dom(range(10)));

		extension(vars(x[0], x[1], x[2]), new int[][] { { 2, 3, 6 }, { 3, 7, 2 }, { 5, 1, 4 } });
		extension(vars(x[10], x[11], x[12]), new int[][] { { 0, 3, 6 }, { 1, 3, 2 }, { 4, 1, 4 }, { 7, 7, 1 } }, NEGATIVE);
		extension(vars(x[20], x[21], x[22]), new int[][] { { 0, STAR, 6 }, { 1, 3, 2 }, { 4, 1, STAR }, { STAR, STAR, 1 } });
		equal(x[3], abs(sub(x[5], x[4])));
		allDifferent(select(x, range(50, 70)));
		allDifferent(select(x, range(70, 80)), exceptValue(0));
		among(vars(x[0], x[1], x[10], x[11]), vals(5, 8), 3);

		allEqual(x[0], x[1], x[10], x[11]);
		notAllEqual(select(x, range(15, 25)));
		cardinality(select(x, range(2, 8)), vals(3, 5, 7), occurExactly(1, 2, 3));
		cardinality(select(x, range(22, 28)), vals(2, 4, 6), occurBetween(vals(1, 2, 2), vals(2, 3, 4)));
		Transitions transitions = transitions(
				"(q0,0,q1)(q0,2,q2)(q1,0,q3)(q2,2,q4)(q3,0,q5)(q3,1,q7)(q4,1,q7)(q4,2,q6)(q5,1,q7)(q6,1,q7)(q7,1,q8)(q8,0,q1)(q8,1,q9)(q8,2,q2)(q9,0,q1)(q9,2,q2)");
		Automaton automata = automaton("q0", transitions, "q3", "q4", "q5", "q6", "q8", "q9");
		regular(select(x, range(83, 91)), automata);

		noOverlap(x[14], x[15], 10, 7);
		lessThan(x[24], x[25]);
	}
}
