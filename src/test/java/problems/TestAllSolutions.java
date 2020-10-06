package problems;

import static org.junit.Assert.assertEquals;
import static problems.UtilityForTests.runResolution;

import java.net.URL;
import java.util.Collection;
import java.util.LinkedList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.problems.AllInterval;

import executables.Resolution;
import problems.g2_academic.Queens;
import problems.test.AllDifferentExcept0Problem;
import problems.test.AtLeastEqualProblem;
import problems.test.AtMostDistanceSumProblem;
import problems.test.ElementVariableProblem;

@RunWith(Parameterized.class)
public class TestAllSolutions {

	static Collection<Object[]> collection = new LinkedList<>();

	static void add(Object instance, String variant, String data, int nSolutions) {
		String pars = " -s=all -cm -ev";
		if (instance instanceof Class<?>) {
			variant = variant != null ? " -variant=" + variant : "";
			data = data != null ? " -data=" + data : "";
			collection.add(new Object[] { ((Class<?>) instance).getName() + variant + data + pars, nSolutions });
		} else {
			URL url = Resolution.class.getResource(instance + ".xml.lzma");
			Utilities.control(url != null, "not found: " + instance + ".xml.lzma");
			collection.add(new Object[] { url.getPath() + pars, nSolutions });
		}
	}

	static void add(String instance, int nSolutions) {
		add(instance, null, null, nSolutions);
	}

	static void add(Class<?> clazz, int... t) {
		add(clazz, null, t[0] + "", t[1]);
	}

	static void add(Class<?> clazz, String variant, int[] t) {
		add(clazz, variant, t[0] + "", t[1]);
	}

	@Parameters(name = "{index}: {0} has {1} solutions")
	public static Collection<Object[]> data() {
		add("/csp/Agatha", 4);
		add("/csp/Allergy", 1);
		add("/csp/Alpha", 1);
		add("/csp/Alpha-var", 1);
		add("/csp/LabeledDice", 48);
		add("/csp/NFractions", 22);
		add("/csp/Picnic", 1);
		add("/csp/Purdey", 1);
		add("/csp/Sandwich", 8);
		add("/csp/SendMore", 1);
		add("/csp/TrafficLights", 4);
		add("/csp/Zebra", 48);

		add("/csp/AllInterval-10", 148);
		add("/csp/AllInterval-aux-10", 104);
		add("/csp/Bibd-6-0-0-3-8", 494);
		add("/csp/Bibd-aux-6-0-0-3-8", 494);
		add("/csp/ColouredQueens-6", 0);
		add("/csp/CostasArray-10", 2160);
		add("/csp/CryptoPuzzle-carry-SEND-MORE-MONEY", 1);
		add("/csp/CryptoPuzzle-DONALD-GERALD-ROBERT", 1);
		add("/csp/CryptoPuzzle-SEND-MORE-MONEY", 1);
		add("/csp/DeBruijnSequence-2-5", 2048);
		add("/csp/DiamondFree-8", 17);
		add("/csp/Dubois-10", 0);
		add("/csp/Langford-3-10", 10);
		add("/csp/LangfordBin-8", 300);
		add("/csp/MagicSequence-10", 1);
		add("/csp/NumberPartitioning-10", 0);
		add("/csp/NumberPartitioning-8", 1);
		add("/csp/Ortholatin-5", 4);
		// add("/csp/QuasiGroup-aux-v3-8", 12960); // very long
		add("/csp/QuasiGroup-aux-v4-5", 12);
		add("/csp/QuasiGroup-aux-v5-8", 720);
		// add("/csp/QuasiGroup-aux-v7-9", 5040); // long
		// add("/csp/QuasiGroup-base-v3-8", 12960); // very long
		add("/csp/QuasiGroup-base-v4-5", 12);
		add("/csp/QuasiGroup-base-v5-8", 720);
		add("/csp/QuasiGroup-base-v6-8", 1440);
		// add("/csp/QuasiGroup-base-v7-9", 5040); // long
		add("/csp/SchurrLemma-6-6", 39870);
		add("/csp/SchurrLemma-mod-8-8", 141120);
		add("/csp/SocialGolfers-01-4-4-5", 2);
		add("/csp/SocialGolfers-4-4-5", 2);
		add("/csp/SportsScheduling-6", 10);
		add("/csp/SportsScheduling-dummy-6", 10);
		add("/csp/Steiner3-7", 151200);
		add("/csp/Talisman-4-2", 34714);

		add("/csp/Areas-Areas-3-3-3", 7);
		add("/csp/Blackhole-Blackhole", 47232);
		add("/csp/Dominoes-Dominoes_grid1", 128);
		add("/csp/Eternity-Eternity_07x05", 32);
		add("/csp/Eternity-Eternity_example", 32);
		add("/csp/Futoshiki-Futoshiki_futo3_0", 1);
		add("/csp/Kakuro-Kakuro_easy-000", 1);
		add("/csp/Kakuro-table-Kakuro_easy-000", 1);
		add("/csp/LatinSquare2-LatinSquare2_7-2-0", 480);
		add("/csp/Lightup-Lightup_example", 1);
		add("/csp/Lits-Lits-example", 1636);
		add("/csp/MagicSquare-4-None", 7040);
		add("/csp/MarketSplit-MarketSplit_04", 1); // long
		add("/csp/Nonogram-Nonogram_example", 1);
		add("/csp/Nonogram-table-Nonogram_example", 1);
		add("/csp/RoomMate-RoomMate_sr0006", 2);
		add("/csp/Sat-clause-Sat_flat30-16", 1482);
		add("/csp/Sat-dual-Sat_flat30-16", 1482);
		add("/csp/Sat-sum-Sat_flat30-16", 1482);
		add("/csp/Shikaku-Shikaku_grid1", 1);
		add("/csp/Subisomorphism-Subisomorphism_A-01", 1);
		add("/csp/Sudoku-Sudoku_example", 1);
		add("/csp/Sudoku-Sudoku_s13a", 1);
		add("/csp/Sudoku-table-Sudoku_s13a", 1);
		add("/csp/VesselLoading-VesselLoading-inst1", 8);

		add("/csp/CarSequencing-CarSequencing_dingbas", 6);
		add("/csp/CarSequencing-table-CarSequencing_dingbas", 6);
		add("/csp/MisteryShopper-MisteryShopper_04", 501552); // long
		add("/csp/SolitaireBattleship-SolitaireBattleship-battleship_instances-00113", 1);
		add("/csp/SolitaireBattleship-SolitaireBattleship_sb-12-12-5-0", 51);
		add("/csp/Wwtpp-short-Wwtpp_ex04400", 0);
		add("/csp/Wwtpp-Wwtpp_ex04400", 0);

		add("/csp/Domino-200-200", 1);
		add("/csp/Domino-table-200-200", 1);
		add("/csp/Knights-16-4", 8096);
		add("/csp/Pigeons-6", 0);
		add("/csp/Pigeons-dec-6", 0);

		for (int[] t : new int[][] { { 8, 15 }, { 9, 42 }, { 10, 104 }, { 11, 235 }, { 12, 463 } }) // with symmetry breaking
			add(AllInterval.class, t);

		for (int[] t : new int[][] { { 4, 2 }, { 5, 10 }, { 6, 4 }, { 7, 40 }, { 8, 92 }, { 9, 352 }, { 10, 724 }, { 12, 14200 } })
			for (int i = 0; i <= 5; i++)
				add(Queens.class, i == 0 ? "" : "v" + i, t);

		for (int[] t : new int[][] { { 1, 3 }, { 2, 7 }, { 3, 13 }, { 4, 21 }, { 5, 31 }, { 6, 43 } })
			add(AllDifferentExcept0Problem.class, t);

		add(AtLeastEqualProblem.class, 8, 29);
		add(AtMostDistanceSumProblem.class, 8, 41);

		for (int[] t : new int[][] { { 2, 18 }, { 3, 81 }, { 4, 324 }, { 5, 1215 }, { 6, 4374 } })
			add(ElementVariableProblem.class, t);

		return collection;
	}

	@Parameter(0)
	public String args;

	@Parameter(1)
	public int nSolutions;

	@Test
	public void test() {
		assertEquals(nSolutions, runResolution(args, false).solver.solManager.nSolutionsFound);
	}
}
