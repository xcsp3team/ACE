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

public class RKAES1 implements ProblemAPI {
	int n; // Number of rounds
	int objective; // Max objective value

	int KEY_BITS = 128; // Number of bits in the key
	int BLOCK_BITS = 128; // Number of bits in the blocks
	int KC = KEY_BITS / 32; // Number of columns per round of key schedule
	int BC = BLOCK_BITS / 32; // Number of columns per round
	int NBK = KC + n * BC / KC; // Number of variables to represent the components of the key (cf. paper)

	void data() {
		n = imp().askInt("Order (n)");
		objective = imp().askInt("Objective");
	}

	@Override
	public void model() {
		Var[][][] deltaY = array("deltaY", size(n - 1, BC, 4), dom(0, 1), "State before ARK");
		Var[][][] deltaX = array("deltaX", size(n, BC, 4), dom(0, 1), "State after ARK");
		Var[][][] deltaSR = array("deltaSR", size(n, BC, 4), dom(0, 1), "State after ShiftRows");
		Var[][][] deltaK = array("deltaK", size(n, BC, 4), dom(0, 1), "Key");

		Var[][][][] Kcomp = array("Kcomp", size(n, BC, 4, NBK), dom(0, 1), "The components of the key");
		Var[][][][][] eqK = array("eqK", size(4, n, BC, n, BC), dom(0, 1),
				"eqK[i][r1][j1][r2][j2] => The byte values of DeltaK[r1,i,j1] and [r2,i,j2] are equal");
		Var[][] colX = array("colX", size(n, BC), dom(range(5)), "colX[r][j] = The sum for i in 0..3 of DeltaY[r][i][j]");
		Var[][] colSRX = array("colSRX", size(n, BC), dom(range(5)), "colSRX[r][j] = The sum for i in 0..3 of SR(DeltaY)[r][i][j]");
		Var[][] colK = array("colK", size(n, BC), dom(range(5)), "colK[r][j] = The sum for i in 0..3 of DeltaK[r][i][j]");

		Var[][] eqSRX = array("eqSRX", size(n * BC, n * BC), (J, J2) -> BC <= J && J < J2 ? dom(range(5)) : null);
		// VarInteger[][] eqY = array("eqY", size(n * BC, n * BC), (J, J2) -> BC <= J && J < J2 ? dom(range(5)) : null);

		block(() -> {
			forall(range(n).range(BC), (r, j) -> sum(deltaX[r][j], EQ, colX[r][j]));
			forall(range(n).range(BC), (r, j) -> sum(deltaK[r][j], EQ, colK[r][j]));
			forall(range(n).range(BC), (r, j) -> sum(deltaSR[r][j], EQ, colSRX[r][j]));
		}).note("Initialisation of the redundant variables.");

		forall(range(n * BC).range(4).range(NBK), (J, i, k) -> {
			int r = J / BC, j = J % BC;
			if (J < KC)
				equal(Kcomp[r][j][i][k], k == J ? deltaK[r][j][i] : 0);
			else if (J % KC == 0)
				equal(Kcomp[r][j][i][k],
						k == (J / KC) * BC + j ? deltaK[(J - 1) / BC][(J + BC - 1) % BC][(i + 1) % 4] : Kcomp[(J - KC) / BC][(J - KC) % BC][i][k]);
		}).note("Initialization of the components");

		forall(range(1, n).range(BC).range(4), (r, j, i) -> sum(vars(deltaY[r - 1][j][i], deltaK[r][j][i], deltaX[r][j][i]), NE, 1)).note("Add round key");
		forall(range(n).range(BC).range(4), (r, j, i) -> equal(deltaSR[r][j][i], deltaX[r][(j + i) % BC][i])).note("Shiftrows; MDS property");
		forall(range(n - 1).range(BC), (r, j) -> sum(vars(colSRX[r][j], deltaY[r][j]), IN, vals(0, 5, 6, 7, 8))).note("Mixcolumns; MDS property");

		block(() -> {
			forall(range(KC, n * BC).range(4), (J, i) -> {
				int r = J / BC, j = J % BC;
				sum(vars(deltaK[(J - KC) / BC][(J - KC) % BC][i], deltaK[(J - 1) / BC][(J + BC - 1) % BC][J % KC == 0 ? (i + 1) % 4 : i], deltaK[r][j][i]), NE,
						1);
			}).note("Key Sckedule: XOR");

			forall(range(KC, n * BC).range(4), (J, i) -> {
				int r = J / BC, j = J % BC;
				if (J % KC != 0) {
					equal(eqK[i][(J - 1) / BC][(J + BC - 1) % BC][(J - KC) / BC][(J - KC) % BC], not(deltaK[r][j][i])); // eqab
					equal(eqK[i][r][j][(J - KC) / BC][(J - KC) % BC], not(deltaK[(J - 1) / BC][(J + BC - 1) % BC][i])); // eqac
					equal(eqK[i][r][j][(J - 1) / BC][(J + BC - 1) % BC], not(deltaK[(J - KC) / BC][(J - KC) % BC][i])); // eqbc
				}
			}).note("Key Sckedule: eqab eqac eqbc");

			forall(range(KC, n * BC).range(4), (J, i) -> {
				int r = J / BC, j = J % BC;
				sum(vars(Kcomp[r][j][i], deltaK[r][j][i]), NE, 1);
			});

			forall(range(KC, n * BC).range(4).range(NBK), (J, i, k) -> {
				int r = J / BC, j = J % BC;
				if (J % KC != 0) {
					extension(eq(Kcomp[r][j][i][k], ne(mul(Kcomp[(J - KC) / BC][(J - KC) % BC][i][k], deltaK[(J - KC) / BC][(J - KC) % BC][i]),
							mul(Kcomp[(J - 1) / BC][(J + BC - 1) % BC][i][k], deltaK[(J - 1) / BC][(J + BC - 1) % BC][i]))));
				}
			}).note("Key schedule: XOR of the components");
		}).note("Key Schedule");

		forall(range(n * BC).range(n * BC).range(4), (J, J2, i) -> {
			if (J < J2) {
				int r = J / BC, j = J % BC, r2 = J2 / BC, j2 = J2 % BC;
				extension(imp(eq(eqK[i][r][j][r2][j2], 1), eq(deltaK[r][j][i], deltaK[r2][j2][i]))).note("EQ(a,b) implies A=B");
				equal(eqK[i][r][j][r2][j2], eqK[i][r][j][r2][j2]).tag(SYMMETRY_BREAKING);
				sum(vars(deltaK[r][j][i], deltaK[r2][j2][i], eqK[i][r][j][r2][j2]), NE, 0).note("a+b+EQ(a,b) !=0");

				forall(range(NBK), k -> extension(imp(eq(Kcomp[r][j][i][k], Kcomp[r2][j2][i][k]), eq(eqK[i][r][j][r2][j2], 1)))).note("Va=Vb => EQ(a,b)");

			}
		}); // .note("EQ(a,b) => A=B");

		// forall(range(n * BC).range(n * BC).range(4), (J, J2, i) -> {
		// if (J < J2) {
		// int r = J / BC, j = J % BC, r2 = J2 / BC, j2 = J2 % BC;
		// equal(eqK[i][r][j][r2][j2], eqK[i][r][j][r2][j2]);
		// }
		// }).note("Symmetry");

		// forall(range(n * BC).range(n * BC).range(4), (J, J2, i) -> {
		// if (J < J2) {
		// int r = J / BC, j = J % BC, r2 = J2 / BC, j2 = J2 % BC;
		// sum(vars(deltaK[r][j][i], deltaK[r2][j2][i], eqK[i][r][j][r2][j2]), NE, 0);
		// }
		// }).note("a+b+EQ(a,b) !=0");

		forall(range(n * BC).range(n * BC).range(4).range(NBK), (J, J2, i, k) -> {
			if (J < J2) {
				int r = J / BC, j = J % BC, r2 = J2 / BC, j2 = J2 % BC;
				extension(imp(eq(Kcomp[r][j][i][k], Kcomp[r2][j2][i][k]), eq(eqK[i][r][j][r2][j2], 1)));
			}
		}).note("Va=Vb => EQ(a,b)");

		forall(range(n * BC).range(n * BC).range(4).range(n * BC), (J, J2, i, J3) -> {
			if (J < J2) {
				int r = J / BC, j = J % BC, r2 = J2 / BC, j2 = J2 % BC, r3 = J3 / BC, j3 = J3 % BC;
				if (J3 != J && J3 != J2) // TODO A laisser ????
					sum(vars(eqK[i][r][j][r3][j3], eqK[i][r][j][r2][j2], eqK[i][r2][j2][r3][j3]), NE, 2);
			}
		}).note("transitivity");

		forall(range(BC, n * BC).range(n * BC), (J, J2) -> {
			if (J < J2) {
				int r = J / BC, j = J % BC, r2 = J2 / BC, j2 = J2 % BC;
				Var[] t1 = deltaSR[r - 1][j], t2 = deltaSR[r2 - 1][j2];
				extension(eq(eqSRX[J][J2], add(eq(add(t1[0], t2[0]), 0), eq(add(t1[1], t2[1]), 0), eq(add(t1[2], t2[2]), 0), eq(add(t1[3], t2[3]), 0))));
			}
		});

		forall(range(BC, n * BC).range(n * BC), (J, J2) -> {
			if (J < J2) {
				int r = J / BC, j = J % BC, r2 = J2 / BC, j2 = J2 % BC;
				List<XNodeParent<IVar>> list = new ArrayList<>();
				for (int i = 0; i <= 3; i++) {
					list.add(ne(deltaSR[r - 1][j][i], deltaSR[r2 - 1][j2][i]));
					list.add(ne(deltaY[r - 1][j][i], deltaY[r2 - 1][j2][i]));
					list.add(eq(add(eqK[i][r][j][r2][j2], deltaX[r][j][i], deltaX[r2][j2][i]), 0));
					list.add(and(eq(add(eqK[i][r][j][r2][j2], deltaK[r][j][i]), 2), ne(deltaX[r][j][i], deltaX[r2][j2][i])));
				}
				extensionDisjunction(list);
			}
		});

	}
}
