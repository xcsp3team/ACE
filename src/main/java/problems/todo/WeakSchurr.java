/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.util.ArrayList;
import java.util.List;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;

// java abscon.Resolution problems.acad.WeakSchurr 192 5 4 -rc=2 -lc=10 -wrp=5
public class WeakSchurr implements ProblemAPI {
	int n;
	int nDrawers;

	private boolean allNotEqual(int x, int y, int z) {
		return x != y || x != z || y != z;
	}

	private int[][] computeTuples() {
		List<int[]> list = new ArrayList<>();
		for (int i = 1; i <= nDrawers; i++)
			for (int j = 1; j <= nDrawers; j++)
				for (int k = 1; k <= nDrawers; k++)
					if (allNotEqual(i, j, k))
						list.add(new int[] { i, j, k });
		return Kit.intArray2D(list);
	}

	private int[][] computeTuples2() {
		List<int[]> list = new ArrayList<>();
		for (int i = 1; i <= nDrawers; i++)
			for (int j = 1; j <= nDrawers; j++)
				for (int k = 1; k <= nDrawers; k++)
					for (int l = 1; l <= nDrawers; l++)
						for (int m = 1; m <= nDrawers; m++)
							for (int n = 1; n <= nDrawers; n++)
								if (allNotEqual(i, j, k) && allNotEqual(i, k, l) && allNotEqual(j, k, m) && allNotEqual(j, l, n) && allNotEqual(i, m, n))
									list.add(new int[] { i, j, k, l, m, n });
		return Kit.intArray2D(list);
	}

	@SuppressWarnings("unused")
	private int[][] computeTuples3() {
		List<int[]> list = new ArrayList<>();
		for (int x1 = 1; x1 <= nDrawers; x1++)
			for (int y1 = 1; y1 <= nDrawers; y1++)
				for (int z = 1; z <= nDrawers; z++)
					for (int x2 = 1; x2 <= nDrawers; x2++)
						for (int y2 = 1; y2 <= nDrawers; y2++)
							for (int d1 = 1; d1 <= nDrawers; d1++)
								for (int d2 = 1; d2 <= nDrawers; d2++)
									if (allNotEqual(x1, y1, z) && allNotEqual(x2, y2, z) && allNotEqual(x1, d1, y1) && allNotEqual(x2, d1, y2)
											&& allNotEqual(x1, d2, y2) && allNotEqual(x2, d2, y1))
										list.add(new int[] { x1, y1, z, x2, y2, d1, d2 });
		return Kit.intArray2D(list);
	}

	private int[][] computeTuples4() {
		List<int[]> list = new ArrayList<>();
		for (int x = 1; x <= nDrawers; x++)
			for (int y1 = 1; y1 <= nDrawers; y1++)
				for (int z = 1; z <= nDrawers; z++)
					for (int y2 = 1; y2 <= nDrawers; y2++)
						if (allNotEqual(x, y1, z) && allNotEqual(x, y2, y1))
							list.add(new int[] { x, y1, z, y2 });
		return Kit.intArray2D(list);
	}

	@SuppressWarnings("unused")
	private int[][] computeTuples5() {
		List<int[]> list = new ArrayList<>();
		for (int x = 1; x <= nDrawers; x++)
			for (int y1 = 1; y1 <= nDrawers; y1++)
				for (int z = 1; z <= nDrawers; z++)
					for (int y2 = 1; y2 <= nDrawers; y2++)
						for (int y3 = 1; y3 <= nDrawers; y3++)
							if (allNotEqual(x, y1, z) && allNotEqual(x, y2, y1) && allNotEqual(x, y3, y2))
								list.add(new int[] { x, y1, z, y2, y3 });
		return Kit.intArray2D(list);
	}

	private XNodeParent<IVar> predicateModel5(Var[] x, int i, int k) {
		XNodeParent<IVar> s = null;
		for (int j = 2; j < i; j++) {
			XNodeParent<IVar> t = ge(x[j - 1], k);
			s = j == 2 ? t : or(s, t);
		}
		return or(s, le(x[i - 1], k));
	}

	protected void addPattern(Var[] x, int[] t, int nb, int model) {
		int a = t[nb] + 1;
		if (model == 1) { // [a, a+1], [a+3, ..., 2*a], 2*a+2
			for (int i = a; i <= 2 * a; i++)
				if (i != a + 2) {
					intension(eq(x[i - 1], nb + 1));
				}
			intension(eq(x[2 * a + 1], nb + 1));
		} else {// a, [a+2, ..., 2*a+1]
			intension(eq(x[a - 1], nb + 1));
			for (int i = a + 2; i <= 2 * a + 1; i++)
				intension(eq(x[i - 1], nb + 1));
		}
	}

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(rangeClosed(1, nDrawers)));

		forall(range(1, nDrawers), i -> intension(le(x[i - 1], i)));

		if (modelVariant("v1")) {
			int[][] supports = computeTuples();
			forall(range(1, n).range(1, n), (i, j) -> {
				if (i < j && (i + j) <= n)
					extension(vars(x[i - 1], x[j - 1], x[(i + j) - 1]), supports);
			});
		}
		if (modelVariant("v2")) {
			int[][] supports2 = computeTuples2();
			forall(range(1, n).range(1, n), (i, j) -> {
				if (j > i && (2 * i + 2 * j) <= n)
					extension(vars(x[i - 1], x[j - 1], x[(i + j) - 1], x[(2 * i + j) - 1], x[(i + 2 * j) - 1], x[(2 * i + 2 * j) - 1]), supports2);
			});
		}
		if (modelVariant("v3")) {
			int[][] supports4 = computeTuples4();
			forall(range(1, n).range(1, n), (i, j) -> {
				if (j > i && (i + j) <= n && j - i != i)
					extension(vars(x[i - 1], x[j - 1], x[(i + j) - 1], x[j - i - 1]), supports4);
			});
		}
		if (modelVariant("v4"))
			forall(range(1, n).range(1, n), (i, j) -> {
				if (j > i && (i + j) <= n)
					notAllEqual(x[i - 1], x[j - 1], x[(i + j) - 1]);
			});

		if (modelVariant("v5"))
			forall(rangeClosed(3, nDrawers).range(2, nDrawers), (i, k) -> {
				if (k < i)
					intension(predicateModel5(x, i, k));
			});

		int[] t = new int[] { 0, 2, 8, 23, 66, 196 };
		if (modelVariant("v6"))
			forall(range(2, nDrawers).range(197), (i, j) -> {
				if (j >= t[i - 1] + 1 && j <= t[i] && j < n)
					intension(le(x[j - 1], i));
			});

		forall(rangeClosed(2, nDrawers).range(n), (i, j) -> {
			if (j >= 2 * (t[i - 1] + 1) + 3 && j <= 4 * (t[i - 1] + 1) + 2)
				intension(ne(x[j - 1], i));
		}).tag("coupures");

		// addPattern(x,t,2, 1); addPattern(x,t,3,2); addPattern(x,t,4, 1); addPattern(x,t,5, 2);
	}

}
