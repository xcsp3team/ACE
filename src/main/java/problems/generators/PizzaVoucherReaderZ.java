/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderDzn;
import problems.g4_world.PizzaVoucher;

public class PizzaVoucherReaderZ extends PizzaVoucher implements ReaderDzn {

	void data() {
		int nPizzas = nextInt();
		int[] pizzaPrices = nextInt1D();
		int nVouchers = nextInt();
		int[] voucherPayPart = nextInt1D();
		int[] voucherFreePart = nextInt1D();
		Utilities.control(nPizzas == pizzaPrices.length && nVouchers == voucherPayPart.length && nVouchers == voucherFreePart.length, "");
		Stream<Object> vouchers = IntStream.range(0, nVouchers).mapToObj(i -> buildInternClassObject("Voucher", voucherPayPart[i], voucherFreePart[i]));
		setDataValues(pizzaPrices, vouchers);
	}
}
