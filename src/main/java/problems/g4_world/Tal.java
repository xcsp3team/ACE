package problems.g4_world;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.Range;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.common.structures.Table;
import org.xcsp.modeler.api.ProblemAPI;

/**
 * Created on 15 avr. 2013 by Rémi Coletta. Revised by Jean-Philippe Prost and Christophe Lecoutre <br>
 */
public class Tal implements ProblemAPI {
	int maxArity;
	int maxHeight;
	int[] sentence;
	int[][][] grammar; // grammar[i] gives the grammar tuples of arity i
	String[] tokens;
	int[] costs;

	private XNodeParent<IVar> predicate(Var[][] l, Var[][] a, int i, int j, int[] lengths) {
		Range r = range(i != 0 && j == lengths[i] - 1 ? 1 : 0, Math.min(j + 1, maxArity));
		return xor(eq(l[i][j], 0), treesFrom(r, k -> ge(a[i + 1][j - k], k + 1)));
	}

	private Table tableFor(int vectorLength) {
		int arity = vectorLength + 2;
		Table table = table().add(range(arity).map(k -> k == arity - 1 ? 0 : STAR)); // tuple for result (at position 'arity-1') equal to 0
		for (int i = 0; i < vectorLength; i++)
			for (int j = 1; j < tokens.length + 1; j++) {
				int[] tuple = repeat(STAR, arity);
				tuple[0] = i;
				tuple[i + 1] = j;
				tuple[arity - 1] = j;
				table.add(tuple); // range(arity).map(k -> k == 0 ? i : k == i + 1 || k == arity - 1 ? j : STAR));
			}
		return table;
	}

	@Override
	public void model() {
		int nWords = sentence.length, nLevels = nWords * 2, nTokens = tokens.length;
		int[] lengths = valuesFrom(range(nLevels), i -> i == 0 ? nWords : nWords - (int) Math.floor((i + 1) / 2) + 1);

		Var[][] c = array("c", size(nLevels, nWords), (i, j) -> (i == 0 || i % 2 == 1) && j < lengths[i] ? dom(costs) : dom(0),
				"c[i][j] is the cost of the jth word at the ith level");
		Var[][] l = array("l", size(nLevels, nWords), (i, j) -> j < lengths[i] ? dom(range(nTokens + 1)) : dom(0),
				"l[i][j] is the label of the jth word at the ith level");
		Var[][] a = array("a", size(nLevels, nWords), (i, j) -> i % 2 == 1 && j < lengths[i] ? dom(range(maxArity + 1)) : dom(0),
				"a[i][j] is the arity of the jth word at the ith level");
		Var[][] x = array("x", size(nLevels, nWords), (i, j) -> 0 < i && i % 2 == 0 && j < lengths[i] ? dom(range(lengths[i])) : dom(0),
				"x[i][j] is the index of the jth word at the ith level");
		Var[] s = array("s", size(nLevels - 2), i -> dom(range(lengths[i + 1])));

		forall(range(1, nLevels - 1), i -> exactly(select(l[i], j -> j < lengths[i]), takingValue(0), s[i - 1]));
		forall(range(1, nLevels - 1, 2), i -> equal(s[i - 1], s[i]));

		instantiation(c[0], 0).note("on row 0, costs are 0");
		instantiation(l[0], sentence).note("on row 0, the jth label is the jth word of the sentence");
		forall(range(1, nLevels), i -> greaterThan(l[i][0], 0)).note("on column 0, labels are 0");

		forall(range(1, nLevels, 2), p -> greaterThan(a[p][0], 0));
		forall(range(1, nLevels, 2).range(1, nWords), (i, j) -> {
			if (j < lengths[i] && j + maxArity > lengths[i - 1])
				lessEqual(a[i][j], lengths[i - 1] - j);
		});

		forall(range(2, nLevels, 2), i -> {
			equal(x[i][0], 0);
			equal(l[i][0], l[i - 1][0]);
		});

		forall(range(2, nLevels, 2), i -> forall(range(1, lengths[i]), j -> {
			greaterEqual(x[i][j], j);
			implication(eq(l[i][j], 0), eq(x[i][j], lengths[i] - 1));
			implication(gt(l[i][j], 0), gt(x[i][j], x[i][j - 1]));
			implication(eq(l[i][j - 1], 0), eq(l[i][j], 0));

			Var[] vect = select(l[i - 1], k -> k < lengths[i - 1]);
			extension(vars(x[i][j], vect, l[i][j]), tableFor(vect.length));
		}));

		forall(range(1, nLevels, 2), i -> forall(range(lengths[i]), j -> {
			equivalence(eq(l[i][j], 0), eq(a[i][j], 0));

			int nPossibleSons = Math.min(lengths[i - 1] - j, maxArity);
			Var[] scp = vars(a[i][j], l[i][j], select(l[i - 1], range(j, j + nPossibleSons)), c[i][j]);
			extension(scp, grammar[nPossibleSons]);

		})).note("grammar a");

		forall(range(0, nLevels, 2).range(nWords), (i, j) -> {
			if (j < lengths[i])
				intension(predicate(l, a, i, j, lengths));
		});

		if (0 < maxHeight && 2 * maxHeight < l.length)
			equal(l[2 * maxHeight][1], 0); // EPSILON

		minimize(SUM, vars(c));
	}
}

// range(vectorLength)
// .execute(i -> range(1, tokens.length + 1).execute(j -> table.add(range(arity).map(k -> k == 0 ? i : k == i + 1 || k == arity - 1 ? j :
// STAR))));
// private XNodeParent<IVar> predicate(Var label, Var[][] arities, int i, int j, int[] rowsLength) {
// // label[l][c] = 0 OR arity[l+1][col] >=1 OR arity[l+1][col-1] >=2 OR arity[l+1][col-2] >=3 OR...
// int nPossibleFathers = Math.min(j + 1, maxArity);
// // last cell of an even row (except 0) : one less condition
// Object[] t = Stream.concat(Stream.of(eq(label, 0)),
// IntStream.range(i != 0 && j == rowsLength[i] - 1 ? 1 : 0, nPossibleFathers).mapToObj(a -> ge(arities[i + 1][j - a], a + 1))).toArray();
// return xor(t);
// }
