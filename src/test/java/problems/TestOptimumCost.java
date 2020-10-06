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

import executables.Resolution;
import problems.test.SimpleObjectiveProblem;

@RunWith(Parameterized.class)
public class TestOptimumCost {
	static Collection<Object[]> collection = new LinkedList<>();

	static void add(Object instance, String variant, String data, int value) {
		String pars = " -cm -ev";
		if (instance instanceof Class<?>) {
			variant = variant != null ? " -variant=" + variant : "";
			data = data != null ? " -data=" + data : "";
			collection.add(new Object[] { ((Class<?>) instance).getName() + variant + data + pars, value });
		} else {
			URL url = Resolution.class.getResource(instance + ".xml.lzma");
			Utilities.control(url != null, "not found: " + instance + ".xml.lzma");
			collection.add(new Object[] { url.getPath() + pars, value });
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

	// static Collection<Object[]> dataForFullExploration(Collection<Object[]> collection, int optimum, Class<?> clazz) {
	// collection.add(new Object[] { clazz.getName() + " -s=all -v=0 -ev", optimum });
	// return collection;
	// }

	@Parameters(name = "{index}: {0} has {1} as optimum cost")
	public static Collection<Object[]> data() {

		add("/cop/Photo-aux", 2);
		add("/cop/Photo", 2);
		add("/cop/Recipe", 1700);
		add("/cop/Witch", 1300);

		add("/cop/BoardColoration-8-10", 2);
		add("/cop/ChangeMaking-10", 1);
		add("/cop/ChangeMaking-compact-10", 1);
		// add("/cop/CoinsGrid-10-4", 98); // long
		add("/cop/GolombRuler-8", 34);
		add("/cop/GolombRuler-aux-8", 34);
		add("/cop/GolombRuler-dec-8", 34);
		add("/cop/LowAutocorrelation-16", 24);
		add("/cop/Opd-4-4-4", 4);
		add("/cop/Opd-aux-4-6-4", 3);
		add("/cop/PeacableArmies-m1-6", 5);
		add("/cop/PeacableArmies-m2-6", 5);
		add("/cop/QueenAttacking-6", 0);
		add("/cop/QueenAttacking-aux-6", 0);
		// add("/cop/QueenAttacking-hybrid-6", 0); // long
		add("/cop/QueenAttacking-table-6", 0);
		add("/cop/Ramsey-10", 2);
		add("/cop/StillLife-7-7", 28);
		add("/cop/StillLife-wastage-8-8", 36);
		add("/cop/WaterBucket-8-5-3-4-4-0-8", 7);

		add("/cop/Amaze-Amaze_simple", 12);
		add("/cop/Auction-Auction_example", 54);
		add("/cop/BinPacking-BinPacking_example", 5);
		add("/cop/BinPacking-BinPacking_n1c1w4a", 5);
		add("/cop/BinPacking-table-BinPacking_n1c1w4a", 5);
		add("/cop/Bugs-Bugs_example", 5);
		add("/cop/BusScheduling-BusScheduling_t1", 7);
		add("/cop/Coloring-Coloring_rand1", 2);
		add("/cop/Cutstock-Cutstock_small", 4);
		add("/cop/Fastfood-Fastfood_example", 3050);
		add("/cop/Fastfood-Fastfood_ff01", 3050);
		add("/cop/Fastfood-table-Fastfood_ff01", 3050);
		add("/cop/GraphColoring-GraphColoring_1-fullins-3", 3);
		add("/cop/GraphColoring-GraphColoring_qwhdec-o18-h120-1", 17);
		add("/cop/GraphColoring-sum-GraphColoring_1-fullins-3", 24);
		add("/cop/GraphColoring-sum-GraphColoring_qwhdec-o18-h120-1", 2754);
		add("/cop/GraphMaxAcyclic-cnt-GraphMaxAcyclic_example", 44);
		add("/cop/GraphMaxAcyclic-GraphMaxAcyclic_example", 44);
		add("/cop/HCPizza-HCPizza_tiny", 15);
		add("/cop/Knapsack-Knapsack_20-50-00", 583);
		add("/cop/Mario-Mario_easy-2", 628);
		add("/cop/Mario-table-Mario_easy-2", 628);
		// add("/cop/OpenStacks-m1-OpenStacks_example", 45); // long
		add("/cop/OpenStacks-m2-OpenStacks_example", 45);
		add("/cop/ProgressiveParty-ProgressiveParty_example", 5);
		add("/cop/PseudoBoolean-PseudoBoolean_example", 20);
		add("/cop/Sonet-Sonet_sonet1", 8);
		add("/cop/Sonet-Sonet_sonet3-4", 12);
		add("/cop/TravelingSalesman-table-TravelingSalesman_10-20-0", 47);
		add("/cop/TravelingSalesman-TravelingSalesman_10-20-0", 47);

		add("/cop/Bacp-m1-Bacp_10", 26);
		add("/cop/Bacp-m1-d-Bacp_10", 1);
		add("/cop/Bacp-m2-Bacp_10", 26);
		// add("/cop/Bacp-m2-d-Bacp_10", 1); // very long
		add("/cop/Fapp-Fapp_ex2", 13871);
		add("/cop/Fapp-short-Fapp_ex2", 13871);
		add("/cop/League-League_010-03-04", 92);
		add("/cop/NurseRostering-NurseRostering_00", 1202);
		add("/cop/PizzaVoucher-PizzaVoucher_pizza6", 210);
		add("/cop/QuadraticAssignment-QuadraticAssignment_example", 4776);
		add("/cop/QuadraticAssignment-QuadraticAssignment_qap", 4776);
		add("/cop/Rack-Rack_r2", 1100);
		add("/cop/Rcpsp-Rcpsp_j30-01-01", 43);
		add("/cop/Rlfap-card-Rlfap_card-scen-04", 46);
		add("/cop/Rlfap-span-Rlfap_span-scen-05", 792);
		add("/cop/SchedulingFS-SchedulingFS-Taillard-os-04-04-0", 302);
		// add("/cop/Tal-Tal-frobserved-7-15-11-13-9-1-11-7-4_1", 142); // long
		// add("/cop/TemplateDesign-TemplateDesign_catfood_2", 2); // very long
		add("/cop/TravelingPurchaser-TravelingPurchaser-7-5-30-1", 124);
		add("/cop/TravelingTournament-a2-TravelingTournament_galaxy04", 517);
		add("/cop/TravelingTournament-a3-TravelingTournament_galaxy04", 416);
		// add("/cop/TravelingTournamentWithPredefinedVenues-a2-Ttppv_circ8bbal", 94); // long
		// add("/cop/TravelingTournamentWithPredefinedVenues-a3-Ttppv_circ8bbal", 80); // long
		add("/cop/Warehouse-Warehouse_example", 383);

		add(SimpleObjectiveProblem.class, null, null, 3);

		return collection;
	}

	@Parameter(0)
	public String args;

	@Parameter(1)
	public int optimum;

	@Test
	public void test() {
		assertEquals(optimum, runResolution(args).solver.solManager.bestBound);
	}
}
