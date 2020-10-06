/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.IVar.VarSymbolic;
import org.xcsp.common.Types.TypeRank;
import org.xcsp.common.structures.Transitions;
import org.xcsp.modeler.api.ProblemAPI;

public class TestInterface implements ProblemAPI {
	int n;

	@Override
	public void model() {
		String[] names = new String[] { "toto", "titi", "tata" };

		Var yellow = var("yellow", dom(rangeClosed(1, 5)));
		Var green = var("green", dom(rangeClosed(1, 5)));
		Var red = var("red", dom(rangeClosed(1, 5)));
		Var white = var("white", dom(rangeClosed(1, 5)));
		Var blue = var("blue", dom(rangeClosed(1, 5)));

		Var[] x = array("x", size(n), dom(range(n)), "x[i] is the ith value of the series");
		Var[] y = array("y", size(n), dom(range(1, n)), "y[i] is the distance between x[i] and x[i+1]");
		Var[][] z = array("z", size(n, n), dom(range(n)));
		VarSymbolic[] sb = arraySymbolic("sb", size(6), dom(names));
		Var[] b = array("b", size(n), dom(0, 1));

		intension(eq(yellow, green));
		forall(range(n - 1), i -> equal(y[i], dist(x[i], x[i + 1]))).tag(CHANNELING);

		extension(red, vals(1, 3, 4));
		extension(vars(white, blue), table("(1,3)(2,*)"));
		forall(range(n - 1), i -> extension(vars(x[i], x[i + 1]), table("(1,1)(2,2)(1,1)(3,1)(1,3)")));
		extension(vars(white, blue), table().positive(false));
		extension(vars(white, blue), table());

		equal(sb[1], sb[2]);
		equal(sb[3], sb[2]);
		forall(range(6), i -> equal(sb[i], names[0]));
		extension(sb[0], names[2], names[0]);
		extension(vars(sb[1], sb[2]), tableSymbolic(tuple(names[1], names[2]), tuple(names[2], names[0]), tuple(names[1], names[2]), tuple("*", names[2]),
				tuple(names[0], names[2])));

		Transitions transitions = transitions(
				"(q0,0,q1)(q0,2,q2)(q1,0,q3)(q2,2,q4)(q3,0,q5)(q3,1,q7)(q4,1,q7)(q4,2,q6)(q5,1,q7)(q6,1,q7)(q7,1,q8)(q8,0,q1)(q8,1,q9)(q8,2,q2)(q9,0,q1)(q9,2,q2)");
		regular(x, automaton("q0", transitions, "q3", "q4", "q5", "q6", "q8", "q9"));

		mdd(vars(y[0], y[1], y[2]), transitions("(r,0,n1)(r,1,n2)(r,2,n3)(n1,2,n4)(n2,2,n4)(n3,0,n5)(n4,0,t)(n5,0,t)"));

		allDifferent(x);
		allDifferent(y, exceptValues(1, 2));
		allDifferentList(x, y);
		allDifferentList(z);
		allDifferentMatrix(z);
		allDifferentMatrix(new Var[][] { { x[0], x[2] }, { y[1], y[3] }, { z[0][0], z[0][1] } });
		allDifferent(sb);

		allEqual(yellow, green, red);
		allEqual(y);
		allEqual(z[0][0], z[0][1]);
		allEqual(z[0]);
		allEqual(z);
		allEqual(sb);
		allEqualList(z);

		ordered(x, INCREASING);
		lex(z, STRICTLY_DECREASING);
		ordered(y, DECREASING);
		lexMatrix(z, DECREASING);

		instantiation(vars(yellow, green, red), vals(2, 4, 1));

		sum(x, EQ, 10);
		sum(y, EQ, yellow);
		sum(x, repeat(2, x.length), EQ, 10);
		sum(y, repeat(5, y.length), EQ, yellow);
		sum(x, repeat(1, x.length), EQ, 10);
		sum(y, repeat(1, y.length), EQ, yellow);
		sum(x, y, EQ, red);
		sum(x, y, EQ, y[1]);
		sum(x, IN, range(10, 101));
		sum(x, NOTIN, range(0, 11));
		sum(x, IN, vals(10, 20, 30));
		sum(x, NOTIN, vals(0, 1, 2, 3, 10));
		sum(x, y, IN, vals(10, 20, 30));
		sum(x, y, NOTIN, vals(0, 1, 2, 3, 10));

		count(x, 3, EQ, 2);
		count(x, vals(1, 2, 4), GT, 4);
		count(y, 2, NE, red);
		count(x, vals(1, 2, 4), LT, yellow);
		count(x, yellow, NE, 3);
		count(x, y, LT, yellow);

		count(x, 3, IN, range(2, 5));
		count(x, vals(1, 2, 4), NOTIN, vals(4, 5, 8));
		count(x, vals(1, 2, 4), IN, range(12, 16));
		count(x, yellow, NOTIN, range(0, 11));
		count(x, y, IN, vals(2, 4, 6));
		atLeast(x, 0, 5);
		atMost1(y, 2);
		exactly(x, 1, y[1]);
		among(x, vals(1, 2), 3);

		nValues(x, EQ, 3);
		nValues(y, LT, red);
		nValues(x, IN, range(2, 6));
		nValues(y, NOTIN, vals(2, 5, 7));
		nValues(x, EQ, 3, exceptValue(0));
		nValues(y, NE, 1, exceptValues(0, 1));
		notAllEqual(x);

		cardinality(x, vals(2, 4), occursEachExactly(3));
		cardinality(y, vals(1, 2, 3), true, occurExactly(2, 2, 1));
		cardinality(x, vals(2, 4), occurExactly(z[0][0], z[1][1]));
		cardinality(x, vals(2, 4), true, occurExactly(z[0][0], z[1][1]));
		cardinality(y, vals(2, 4), true, occurBetween(vals(1, 1), vals(3, 4)));
		cardinality(x, vars(y[0], y[2]), occursEachExactly(3));
		cardinality(x, vars(y[0], y[2]), true, occurExactly(vars(z[0][0], z[1][1])));
		cardinality(x, vars(y[1], y[3]), occurBetween(vals(1, 1), vals(3, 4)));

		maximum(x, y[0]);
		maximum(y, condition(LT, 10));
		maximum(x, index(y[1]));
		maximum(y, startIndex(2), index(x[0]), condition(GE, x[1]));

		minimum(x, y[0]);
		minimum(y, condition(LT, 10));
		minimum(x, index(y[1]));
		minimum(y, startIndex(0), index(x[0]), condition(NE, x[1]));

		element(x, red, 2);
		element(x, startIndex(1), index(red), 2);
		element(y, 0, index(red, TypeRank.FIRST), yellow);
		element(vals(2, 4, 5, 7), red, green);
		element(x, 3);
		element(x, red);

		channel(x);
		channel(x, startIndex(1));
		channel(x, y);
		channel(x, startIndex(1), y, startIndex(0));
		channel(x, startIndex(1), y, startIndex(1));
		channel(x, red);
		channel(x, startIndex(1), yellow);

		stretch(x, vals(0, 1), vals(1, 1), vals(2, 3));
		stretch(y, vals(0, 1, 2, 4), vals(1, 1, 0, 0), vals(2, 3, 1, 1), new int[][] { { 1, 2 }, { 0, 1 } });

		noOverlap(x[0], x[1], 3, 2);
		noOverlap(x, range(n).toArray(), false);
		noOverlap(x, y);
		noOverlap(z, range(n).toArray(), range(n).toArray(), range(n).toArray(), range(n).toArray());
		noOverlap(new Var[][] { z[1], z[2] }, range(n).toArray(), range(n).toArray());
		noOverlap(new Var[][] { z[0], z[3] }, range(n).toArray(), range(n).toArray());
		noOverlap(z, z);
		noOverlap(z, transpose(z));
		noOverlap(new Var[][] { z[1], z[2] }, new Var[][] { z[0], z[3] });
		noOverlap(new Var[][] { z[0], z[3] }, new Var[][] { z[1], z[2] });

		cumulative(x, range(n).toArray(), range(n).toArray(), 10);
		cumulative(x, range(n).toArray(), y, range(n).toArray(), condition(LT, 10));
		cumulative(x, range(n).toArray(), y, 20);
		cumulative(x, y, range(n).toArray(), 30);
		cumulative(x, y, y, x, condition(GT, 30));

		circuit(x);
		circuit(y, 2);
		circuit(x, 1, 5);
		circuit(y, x[0]);
		circuit(x, 1, x[1]);

		instantiation(x, range(n));
		instantiation(z, IntStream.range(0, n).mapToObj(i -> range(n).toArray()).toArray(int[][]::new), (i, j) -> i < j);

		clause(vars(b[0], b[1]), vars(b[2]));

		slide(x, range(n - 1), i -> extension(vars(x[i], x[i + 1]), table("(1,2)")));
		slide(x, range(0, n, 2), i -> extension(vars(x[i], x[i + 1]), table("(1,2)")));

		block(() -> {
			Var zz = var("zz", dom(0, 1));
			Var[] tt = array("tt", size(12), dom(0, 1, 2), CLUES);
			different(zz, tt[0]);
			equal(x[0], x[1]);
			equal(y[0], y[1]);
			circuit(y);
			slide(y, range(n - 1), i -> equal(y[i], y[i + 1]));
			circuit(x);
			slide(x, range(n - 1), i -> extension(vars(x[i], y[i + 1]), table("(2,2)(1,1)")));
			equal(y[1], y[2]).note("titi");
		}).note("coucou").tag("retest");

		forall(range(1), i -> different(y[0], 2));
		forall(range(1), i -> different(y[0], 2).tag("eee")).note("test");

		forall(range(3), i -> slide(x, range(n - 1), j -> extension(vars(x[j], x[j + 1]), table("(1,2)"))));

		ifThen(different(x[0], 0), equal(y[1], 4));
		ifThenElse(different(x[0], 0), equal(y[1], 4), channel(x, y));
		circuit(x);
	}
}
