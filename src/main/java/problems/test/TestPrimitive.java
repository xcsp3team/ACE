/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.util.function.Consumer;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;

public class TestPrimitive implements ProblemAPI {

	interface Test2 {
		CtrEntity exec(Object operand1, Object operand2);
	}

	@Override
	public void model() {
		Var[] x = array("x", size(5), dom(-1, 0, 1));
		Var[] y = array("y", size(10), dom(range(1, 8)));

		different(add(y[2], y[1], y[3]), 10);
		different(not(y[2]), y[1]);
		intension(not(eq(y[3], y[2])));
		intension(and(not(not(eq(y[0], 3))), 0));
		intension(abs(sub(y[0], y[1])));
		intension(eq(mul(3, y[3]), 6));
		intension(and(lt(10, y[3]), lt(y[3], 20)));
		intension(or(lt(y[3], 10), gt(y[3], 20)));

		intension(le(sub(x[0], 4), y[3]));

		Consumer<Test2> c1 = (op) -> {
			op.exec(5, x[0]);
			op.exec(x[0], 5);
			op.exec(add(y[4], 5), 8);
			op.exec(8, add(5, y[4]));
			op.exec(sub(y[4], 5), 8);
			op.exec(8, sub(5, y[4]));
			op.exec(8, sub(y[4], 5));
			op.exec(mod(4, y[0]), 10);
			op.exec(12, div(y[4], 2));
			op.exec(10, div(4, y[0]));
			op.exec(dist(5, y[3]), 4);
			op.exec(mul(y[0], 3), 9);
			op.exec(9, mul(3, y[0]));
			op.exec(9, mul(y[0], 3));
			op.exec(add(3, 4, 7), x[0]);
			op.exec(x[0], add(4, 3, 7));
			op.exec(mul(3, 4, 7), x[0]);
		};

		block(() -> c1.accept((op1, op2) -> lessThan(op1, op2))).note("lessThan ");
		block(() -> c1.accept((op1, op2) -> lessEqual(op1, op2))).note("lessEqual");
		block(() -> c1.accept((op1, op2) -> greaterEqual(op1, op2))).note("greaterEqual");
		block(() -> c1.accept((op1, op2) -> greaterThan(op1, op2))).note("greaterThan");
		block(() -> c1.accept((op1, op2) -> equal(op1, op2))).note("equal");
		block(() -> c1.accept((op1, op2) -> different(op1, op2))).note("notEqual");

		block(() -> {
			intension(in(y[3], set(2, 3, 4)));
			intension(in(add(y[3], 2), set(2, 3, 4)));
			intension(in(add(2, y[3]), set(4, 3, 2)));
			intension(in(mod(5, y[3]), set(3, 2, 4)));
		}).note("operator in");

		Consumer<Test2> c2 = (op) -> {
			op.exec(y[3], y[4]);
			op.exec(y[3], y[4]);
			op.exec(y[3], y[2]);
			op.exec(x[0], abs(x[1]));
			op.exec(abs(x[1]), x[0]);
			op.exec(x[0], sub(x[1], 4));
			op.exec(x[0], sub(4, x[1]));
			op.exec(4, sub(x[0], x[1]));
			op.exec(sub(x[1], 4), x[0]);
			op.exec(sub(4, x[1]), x[0]);
			op.exec(sub(4, y[2]), sub(y[1], 3));
			op.exec(sub(y[1], 3), sub(4, y[2]));
			op.exec(add(y[2], 2), add(y[4], 5));
			op.exec(add(2, y[2]), add(5, y[4]));
			op.exec(dist(y[2], 2), y[4]);
			op.exec(y[4], dist(y[2], 2));
			op.exec(pow(y[3], y[4]), 10);
			op.exec(10, pow(y[3], y[4]));
			op.exec(neg(y[2]), y[1]);
			op.exec(sqr(y[2]), y[1]);
			op.exec(not(y[2]), y[1]);
		};
		block(() -> c2.accept((op1, op2) -> lessThan(op1, op2))).note("Bin lessThan");
		block(() -> c2.accept((op1, op2) -> lessEqual(op1, op2))).note("Bin lessEqual");
		block(() -> c2.accept((op1, op2) -> greaterEqual(op1, op2))).note("Bin greaterEqual");
		block(() -> c2.accept((op1, op2) -> greaterThan(op1, op2))).note("Bin greaterThan");
		block(() -> c2.accept((op1, op2) -> equal(op1, op2))).note("Bin equal");
		block(() -> c2.accept((op1, op2) -> different(op1, op2))).note("Bin notEqual");

		Consumer<Test2> c3 = (op) -> {
			op.exec(y[8], abs(sub(y[7], y[6])));
			op.exec(sub(x[1], 4), sub(x[2], x[3]));
			op.exec(add(y[0], y[1]), y[2]);
			op.exec(y[3], sub(y[4], y[5]));
			op.exec(y[3], add(y[4], y[5]));
			op.exec(add(y[3], 10), add(10, y[4], y[5], 6));
			op.exec(y[3], mul(y[4], y[5], 3, 5));
			op.exec(y[1], pow(y[3], y[2]));
		};
		block(() -> c3.accept((op1, op2) -> lessThan(op1, op2))).note("Tern lessThan");
		block(() -> c3.accept((op1, op2) -> lessEqual(op1, op2))).note("Tern lessEqual");
		block(() -> c3.accept((op1, op2) -> greaterEqual(op1, op2))).note("Tern greaterEqual");
		block(() -> c3.accept((op1, op2) -> greaterThan(op1, op2))).note("Tern greaterThan");
		block(() -> c3.accept((op1, op2) -> equal(op1, op2))).note("Tern equal");
		block(() -> c3.accept((op1, op2) -> different(op1, op2))).note("Tern notEqual");

		block(() -> {
			intension(and(x[0], x[1]));
			intension(and(x[0], not(eq(x[1], x[2]))));
			intension(and(gt(y[2], 10), le(y[2], 20)));
			intension(and(lt(y[2], 100), ge(y[2], 1)));
			intension(and(gt(y[2], 10), lt(y[2], 20)));
			intension(and(le(y[2], 100), ge(y[2], 1)));
			intension(and(x[0], not(in(x[1], set(4, 3, 8)))));

			intension(or(x[3], x[4], x[1]));
			intension(iff(x[2], x[1]));
			intension(not(not(eq(x[3], x[4]))));
			equal(x[0], iff(x[1], x[2], x[3]));
			different(x[3], imp(x[1], x[2]));
		}).note("logic");

		block(() -> {
			equal(5, add(y[0], y[1], y[9]), sub(y[2], y[6]), y[8], mul(y[5], y[6]));
			equal(x[0], min(x[1], min(x[2], x[3])));
			equal(add(add(x[1], x[2], min(x[2], x[3]), add(x[3], x[4])), add(add(y[1], y[2]), y[3])), y[2]);
		}).note("other");

	}
}
