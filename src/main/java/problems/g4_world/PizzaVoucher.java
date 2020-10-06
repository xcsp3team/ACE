/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.g4_world;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

public class PizzaVoucher implements ProblemAPI {
	int[] pizzaPrices;
	Voucher[] vouchers;

	class Voucher {
		int payPart, freePart;
	}

	@Override
	public void model() {
		int nPizzas = pizzaPrices.length, nVouchers = vouchers.length;

		Var[] v = array("v", size(nPizzas), dom(rangeClosed(-nVouchers, nVouchers)),
				"v[i] is the voucher used for the ith pizza. " + "0 means that no voucher is used. "
						+ "A negative (resp., positive) value i means that the ith pizza contributes to the the pay (resp., free) part of voucher |i|.");
		Var[] p = array("p", size(nVouchers), i -> dom(0, vouchers[i].payPart), "p[i] is the number of paid pizzas wrt the ith voucher");
		Var[] f = array("f", size(nVouchers), i -> dom(range(vouchers[i].freePart + 1)), "f[i] is the number of free pizzas wrt the ith voucher");
		// Var[] c = array("c", size(nPizzas), i -> dom(0, pizzaPrices[i]), "c[i] is the cost (paid price) of the ith pizza");

		forall(range(nVouchers), i -> count(v, takingValue(-i - 1), EQ, p[i])).note("counting paid pizzas");
		forall(range(nVouchers), i -> count(v, takingValue(i + 1), EQ, f[i])).note("counting free pizzas");
		forall(range(nVouchers), i -> equivalence(eq(f[i], 0), ne(p[i], vouchers[i].payPart)))
				.note("a voucher, if used, must contribute to have at least one free pizza.");
		// forall(range(nPizzas), i -> implication(le(v[i], 0), ne(c[i], 0))).note("a pizza must be paid iff a free voucher part is not used to have
		// it free");

		forall(range(nPizzas).range(nPizzas), (i, j) -> {
			if (i != j && pizzaPrices[i] < pizzaPrices[j])
				disjunction(ge(v[i], v[j]), ne(v[i], neg(v[j])));
		}).note("a free pizza obtained with a voucher must be cheaper than any pizza paid wrt this voucher");

		minimize(SUM, treesFrom(range(nPizzas), i -> le(v[i], 0)), pizzaPrices).note("minimizing summed up costs of pizzas"); // sum(c)

		decisionVariables(v);
	}
}