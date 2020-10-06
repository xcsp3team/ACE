package problems;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.Range;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.problems.AllInterval;
import org.xcsp.modeler.problems.Blackhole;
import org.xcsp.modeler.problems.BoardColoration;
import org.xcsp.modeler.problems.MagicSequence;
import org.xcsp.modeler.problems.Rack;
import org.xcsp.modeler.problems.Sudoku;
import org.xcsp.modeler.problems.Warehouse;

import problems.g2_academic.Bibd;
import problems.g2_academic.ColouredQueens;
import problems.g2_academic.CoveringArray;
import problems.g2_academic.CryptoPuzzle;
import problems.g2_academic.DeBruijnSequence;
import problems.g2_academic.DiamondFree;
import problems.g2_academic.Dubois;
import problems.g2_academic.GolombRuler;
import problems.g2_academic.GracefulGraph;
import problems.g2_academic.KnightTour;
import problems.g2_academic.Langford;
import problems.g2_academic.LangfordBin;
import problems.g2_academic.LowAutocorrelation;
import problems.g2_academic.MagicHexagon;
import problems.g2_academic.NumberPartitioning;
import problems.g2_academic.Opd;
import problems.g2_academic.Ortholatin;
import problems.g2_academic.PeacableArmies;
import problems.g2_academic.QuasiGroup;
import problems.g2_academic.QueenAttacking;
import problems.g2_academic.Queens;
import problems.g2_academic.Ramsey;
import problems.g2_academic.SchurrLemma;
import problems.g2_academic.SocialGolfers;
import problems.g2_academic.SportsScheduling;
import problems.g2_academic.Steiner3;
import problems.g2_academic.StillLife;
import problems.g3_pattern.GraphColoring;
import problems.g3_pattern.Kakuro;
import problems.g3_pattern.MagicSquare;
import problems.g3_pattern.RectPacking;
import problems.g3_pattern.RoomMate;
import problems.g3_pattern.StripPacking;
import problems.g3_pattern.Subisomorphism;
import problems.g3_pattern.TravelingSalesman;
import problems.g4_world.Bacp;
import problems.g4_world.CarSequencing;
import problems.g4_world.Crossword;
import problems.g4_world.Fapp;
import problems.g4_world.MisteryShopper;
import problems.g4_world.PizzaVoucher;
import problems.g4_world.QuadraticAssignment;
import problems.g4_world.RadarSurveillance;
import problems.g4_world.Rcpsp;
import problems.g4_world.Rlfap;
import problems.g4_world.SolitaireBattleship;
import problems.g4_world.Tal;
import problems.g5_special.DistinctVectors;
import problems.g5_special.Domino;
import problems.g5_special.Hanoi;
import problems.g5_special.Knights;
import problems.g5_special.Pigeons;
import problems.g5_special.PropStress;
import problems.g5_special.QueensKnights;
import problems.generators.Auction_Parser;
import problems.generators.Bacp_Parser;
import problems.generators.Bacp_ParserZ;
import problems.generators.BinPacking_Parser;
import problems.generators.Blackhole_Random;
import problems.generators.BusSchedulingReaderZ;
import problems.generators.CutstockReaderZ;
import problems.generators.Eternity_Parser;
import problems.generators.FappReader;
import problems.generators.Fastfood_ParserZ;
import problems.generators.GraphColoringReader;
import problems.generators.KakuroReader;
import problems.generators.KnapsackRandom;
import problems.generators.LatinSquareReader;
import problems.generators.MagicSquare_Parser;
import problems.generators.MarioReaderZ;
import problems.generators.MarketSplitReader;
import problems.generators.MultiKnapsack_Parser;
import problems.generators.Nonogram_Parser;
import problems.generators.NurseRosteringReader;
import problems.generators.OpenStacks_ParserZ;
import problems.generators.PrizeCollecting_ParserZ;
import problems.generators.PseudoBoolean_Parser;
import problems.generators.QuadraticAssignment_Parser;
import problems.generators.RadarSurveillance_Random;
import problems.generators.RlfapReader;
import problems.generators.SatReader;
import problems.generators.SchedulingFSReader;
import problems.generators.SchedulingJSReader;
import problems.generators.SchedulingOSReader;
import problems.generators.SolitaireBattleshipReader;
import problems.generators.SolitaireBattleshipReaderZ;
import problems.generators.StripPackingReader;
import problems.generators.Sudoku_Parser;
import problems.generators.TppReaderZ;
import problems.generators.TravellingSalesmanRandom;
import problems.generators.VrpReaderZ;
import problems.generators.Warehouse_Parser;
import problems.generators.WwtppReaderZ;
import problems.test.TestSmart;
import problems.tran.RenaultMod;
import utility.Kit;

public final class Series {

	// OR-library at http://people.brunel.ac.uk/~mastjjb/jeb/info.html

	private final static String PATH = "/home/lecoutre/instances/";
	private final static String PATH_MINI = PATH + "minizinc-benchmarks-master/";
	private final static String DZN = ".dzn";
	private final static String MZN = ".mzn";
	private final static String JSON = ".json";
	private final static String DAT = ".dat";
	private final static String XCSP2 = "problems.xcsp2.XCSP2";

	private static FileFilter withExtension(String... suffixes) {
		return f -> Stream.of(suffixes).anyMatch(s -> f.getName().endsWith(s));
	}

	private final static String ALL = "all";
	private final static String TEST = "test";

	private final static String RANDOM = "Random";
	private final static String QRANDOM = "QRandom";

	private final static String ALL_INTERVAL = AllInterval.class.getName();
	private final static String BIBD = Bibd.class.getSimpleName();
	private final static String BLACK_HOLE = Blackhole.class.getSimpleName();
	private final static String CHESSBOARD_COLORATION = BoardColoration.class.getSimpleName();
	private final static String COLOURED_QUEENS = ColouredQueens.class.getName();
	private final static String DISTINCT_VECTORS = DistinctVectors.class.getSimpleName();
	private final static String DOMINO = Domino.class.getSimpleName();
	private final static String DUBOIS = Dubois.class.getSimpleName();
	private final static String GOLOMB = GolombRuler.class.getSimpleName();
	private final static String GRACEFUL = GracefulGraph.class.getSimpleName();
	private final static String HANOI = Hanoi.class.getSimpleName();
	private final static String KNAPSACK = KnapsackRandom.class.getName();
	private final static String KNIGHTS = Knights.class.getSimpleName();
	private final static String KNIGHT_TOUR = KnightTour.class.getSimpleName();
	private final static String LANGFORD = Langford.class.getSimpleName();
	private final static String LOW_AUTOCORRELATION = LowAutocorrelation.class.getSimpleName();
	private final static String ORTHOLATIN = Ortholatin.class.getSimpleName();
	private final static String QUADRATIC_ASSIGNMENT = QuadraticAssignment.class.getSimpleName();
	private final static String QUEEN_ATTACKING = QueenAttacking.class.getSimpleName();
	private final static String QUEENS = Queens.class.getSimpleName();
	private final static String QUEENS_KNIGHTS = QueensKnights.class.getSimpleName();
	private final static String RAMSEY = Ramsey.class.getSimpleName();
	private final static String RECT_PACKING = RectPacking.class.getSimpleName();
	private final static String SCHURR = SchurrLemma.class.getSimpleName();
	private final static String STEINER3 = Steiner3.class.getSimpleName();
	private final static String STRIP_PACKING = StripPacking.class.getSimpleName();

	/*****/

	private final static String RADAR_SURVEILLANCE = RadarSurveillance.class.getSimpleName();
	private final static String ROOM_MATE = RoomMate.class.getSimpleName();
	private final static String SOCIAL_GOLFERS = SocialGolfers.class.getSimpleName();
	private final static String SUBISOMORPHISM = Subisomorphism.class.getSimpleName();
	private final static String TRAVELLING_SALESMAN = TravelingSalesman.class.getSimpleName();
	private final static String WAREHOUSE = Warehouse.class.getSimpleName();

	/*****/

	private final static String BASIC = "Basic";
	private final static String CRYPTO_PUZZLE = CryptoPuzzle.class.getSimpleName();
	private final static String KAKURO = Kakuro.class.getSimpleName();
	private final static String MAGIC_SEQUENCE = MagicSequence.class.getSimpleName();
	private final static String SUDOKU = Sudoku.class.getSimpleName();

	/*****/

	private final static String RENAULT_MOD = RenaultMod.class.getSimpleName();
	private final static String RENAULT = "Renault";
	private final static String CAR_SEQUENCING = CarSequencing.class.getSimpleName();
	private final static String CROSSWORD = Crossword.class.getSimpleName();
	private final static String RLFAP = Rlfap.class.getSimpleName();
	private final static String RLFAP_OLD = "RlfapOld";
	private final static String SPORTS_SCHEDULING = SportsScheduling.class.getSimpleName();
	private final static String RCPSP = Rcpsp.class.getSimpleName();
	private final static String GRAPH_COLORING = GraphColoring.class.getSimpleName();

	/*****/

	private final static String LATIN_SQUARE = LatinSquareReader.class.getName();
	private final static String MAGIC_SQUARE = MagicSquare_Parser.class.getName();
	private final static String MARKET_SPLIT = MarketSplitReader.class.getName();
	private final static String MULTI_KNAPSACK = MultiKnapsack_Parser.class.getName();
	private final static String NONOGRAM = Nonogram_Parser.class.getName();
	private final static String SAT = SatReader.class.getName();

	private final static String DRIVER = "Driver";
	private final static String FISCHER = "Fischer";
	private final static String HAYSTACKS = "Haystacks";
	private final static String PRIMES = "Primes";
	private final static String COSTAS_ARRAY = "CostasArray";
	private final static String PIGEONS_PLUS = "PigeonsPlus";
	private final static String SCHEDULING = "Scheduling";

	private final static String PSEUDO_BOOLEAN = PseudoBoolean_Parser.class.getName();

	/***** New Series on September 2016 */

	private final static String SUPER_SOLUTIONS = "SuperSolutions";
	private final static String QUASI_GROUP = QuasiGroup.class.getName();
	private final static String BIN_PACKING = BinPacking_Parser.class.getName();
	private final static String MAX_CSP = "MaxCSP";
	private final static String MIXED = "Mixed";
	private final static String VRP = VrpReaderZ.class.getName();
	private final static String CUTSTOCK = CutstockReaderZ.class.getName();
	private final static String TPP = TppReaderZ.class.getName();
	private final static String MARIO = MarioReaderZ.class.getName();
	private final static String STILL_LIFE = StillLife.class.getName();
	private final static String OPD = Opd.class.getName();
	private final static String PRIZE_COLLECTING = PrizeCollecting_ParserZ.class.getName();
	private final static String BUS_SCHEDULING = BusSchedulingReaderZ.class.getName();
	private final static String FASTFOOD = Fastfood_ParserZ.class.getName();

	/******** Series for January 2017 in series3rdPass **/

	private final static String PROP_STRESS = PropStress.class.getName();
	private final static String WWTPP = WwtppReaderZ.class.getName();
	private final static String OPEN_STACKS = OpenStacks_ParserZ.class.getName();
	private final static String RACK = Rack.class.getName();
	private final static String COVERING_ARRAY = CoveringArray.class.getName();
	private final static String DE_BRUIJN = DeBruijnSequence.class.getName();
	private final static String DIAMOND_FREE = DiamondFree.class.getName();
	private final static String MAGIC_HEXAGON = MagicHexagon.class.getName();
	private final static String NUMBER_PARTITIONING = NumberPartitioning.class.getName();

	/******** New Series in April 2018 **/
	private final static String AUCTION = Auction_Parser.class.getName();
	private final static String BACP = Bacp.class.getName();
	private final static String ETERNITY = Eternity_Parser.class.getName();
	private final static String MISTERY_SHOPPER = MisteryShopper.class.getName();
	private final static String FAPP = Fapp.class.getName();
	private final static String BATTLESHIP = SolitaireBattleship.class.getName();
	private final static String PEACABLE_ARMIES = PeacableArmies.class.getName();
	private final static String PIGEONS = Pigeons.class.getName();
	private final static String PIZZA_VOUCHER = PizzaVoucher.class.getName();
	private final static String NURSE_ROSTERING = NurseRosteringReader.class.getName();
	private final static String TAL = Tal.class.getName();

	private final static String BAUDOUIN = "Baudouin";

	/********/

	private static boolean dataexport;

	private static String serieName;
	private static File dir, mainDir;

	private static List<String> badCommands = new ArrayList<>();

	private static int[] vals(Object... valsToConcat) {
		return Utilities.collectInt(valsToConcat);
	}

	private static Range rangeC(int minIncluded, int maxIncluded, int step) {
		return new Range(minIncluded, maxIncluded + 1, step);
	}

	private static Range rangeC(int minIncluded, int maxIncluded) {
		return new Range(minIncluded, maxIncluded + 1);
	}

	private static Range range(int length) {
		return new Range(length);
	}

	private static class HandleFlow implements Runnable {

		private InputStream inputStream;

		private HandleFlow(InputStream inputStream) {
			this.inputStream = inputStream;
		}

		@Override
		public void run() {
			try (BufferedReader br = new BufferedReader(new InputStreamReader(inputStream))) {
				for (String line = br.readLine(); line != null; line = br.readLine())
					System.out.println(line);
			} catch (IOException e) {
			}
		}
	}

	private static void execute(String command, File dir) {
		try {
			Process process = Runtime.getRuntime().exec(command, null, dir);
			new Thread(new HandleFlow(process.getInputStream())).start();
			new Thread(new HandleFlow(process.getErrorStream())).start();
			process.waitFor();
		} catch (Exception e) {
			System.out.println("Pb when executing " + command + " " + e);
			badCommands.add(command);
		}
	}

	private static String exportFile = "-export=file";
	// private static String export = " -prepro=no -search=no";

	private static void exec(String commandPart, int xmx, String variantName, String seriesName) {
		// System.out.println(" " + dir);
		File cdir = new File(dir, dir.getName() + "-" + variantName + "-" + seriesName);
		cdir.mkdir();
		String fullCommand = "java" + (xmx != 0 ? " -Xmx" + xmx + "M" : "") + " ac " + commandPart + (dataexport ? " -dataexport" : "")
				+ " -res=false -mbcs=false " + exportFile + " -puc=true -nc=false -alvalb=3 -ea -ev";
		System.out.println(fullCommand);
		// Kit.log.info(fullCommand);
		execute(fullCommand, cdir);
	}

	private static void exec(String commandPart, String variant, String seriesName) {
		exec(commandPart, 0, variant, seriesName);
	}

	private static void exec(String commandPart, int xmx, String seriesName) {
		exec(commandPart, xmx, "m1", seriesName);
	}

	private static void exec(String commandPart, String seriesName) {
		exec(commandPart, 0, seriesName);
	}

	private static void exec(String commandPart, int xmx) {
		exec(commandPart, xmx, "s1");
	}

	private static void exec(String commandPart) {
		exec(commandPart, 0);
	}

	private static void execVariant(String commandPart, String variant, String series) {
		exec(commandPart + " -variant=" + variant, variant, series);
	}

	private static void execVariant(String commandPart, String variant) {
		execVariant(commandPart, variant, "s1");
	}

	private static void execVariant(String commandPart, String variant, int xmx) {
		exec(commandPart + " -variant=" + variant, xmx, variant, "s1");
	}

	private static void executePair(String first, String second, String suffix, File dir) {
		execute("java abscon.Resolution " + first + " " + suffix, dir);
		execute("java abscon.Resolution problems.xcsp3.XCSP3 " + second + " " + suffix, dir);
	}

	private static void test() {
		String prefix = "/home/lecoutre/abssol/seriesFullSept2016/";
		File dir = new File("/home/lecoutre");
		executePair("modeler.problems.acad.AllInterval -data=12", prefix + "AllInterval/AllInterval-m1-s1/AllInterval-012.xml.lzma",
				"-s=all -v=0 -varh=DDegOnDom", dir);
		executePair("modeler.problems.acad.Bibd -data=[6,50,25,3,10] -variant=sum", prefix + "Bibd/Bibd-sum-lex/Bibd-sum-06-050-25-03-10.xml.lzma",
				"-s=all -v=0 -varh=DDegOnDom", dir);
		executePair("problems.acad.Blackhole 4 3 0", prefix + "Blackhole/Blackhole-m1-s04/Blackhole-04-3-00.xml.lzma", "-s=all -v=0 -varh=Memory", dir);
		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/blackHole/BH-4-04/Blackhole-4-04-0_X2.xml.bz2",
				prefix + "Blackhole/Blackhole-xcsp2-s04/Blackhole-4-04-0_X2.xml.lzma", " -varh=DDegOnDom -riv=false", dir);
		executePair("problems.acad.ChessboardColoration  9 9", prefix + "ChessboardColoration/ChessboardColoration-m1-s1/cc-09-09.xml.lzma", "-f=cop -rc=10",
				dir);
		executePair("problems.acad.ColouredQueens 6 ", prefix + "ColouredQueens/ColouredQueens-m1-s1/ColouredQueens-06.xml.lzma", "", dir);
		executePair("problems.acad.DistinctVectors 40 100 24", prefix + "DistinctVectors/DistinctVectors-m1-s3/DistinctVectors-40-100-24.xml.lzma",
				" -v=0 -varh=DDegOnDom", dir);
		executePair("problems.acad.Domino 3000 3000", prefix + "Domino/Domino-m1-s1/Domino-3000-3000.xml.lzma", "", dir);
		executePair("problems.acad.Dubois 18", prefix + "Dubois/Dubois-m1-s1/Dubois-018.xml.lzma", "", dir);
		executePair("problems.acad.GolombRuler  7 500 3", prefix + "GolombRuler/GolombRuler-a3-s1/GolombRuler-07-a3.xml.lzma", " -f=cop -varh=DDegOnDom", dir);
		executePair("problems.acad.GolombRuler  8 500 4", prefix + "GolombRuler/GolombRuler-a4-s1/GolombRuler-08-a4.xml.lzma", " -f=cop -varh=DDegOnDom", dir);
		executePair("problems.acad.GracefulGraph 3 6", prefix + "GracefulGraph/GracefulGraph-m1-s1/Graceful-K03-P06.xml.lzma", "", dir);
		executePair("problems.acad.Hanoi 8", prefix + "Hanoi/Hanoi-m1-s1/Hanoi-08.xml.lzma", "", dir);
		executePair("problems.acad.Knights 25 5", prefix + "Knights/Knights-m1-s1/Knights-025-05.xml.lzma", "", dir);
		executePair("problems.acad.KnightTour 8 1", prefix + "KnightTour/KnightTour-int-s1/KnightTour-08-int.xml.lzma", " -rc=10", dir);
		executePair("problems.acad.KnightTour 12 3", prefix + "KnightTour/KnightTour-ext-s1/KnightTour-12-ext03.xml.lzma", " -rc=10", dir);
		executePair("problems.acad.Langford 2 10", prefix + "Langford/Langford-m1-k2/Langford-2-10.xml.lzma", "", dir);
		executePair("problems.acad.Langford 3 12", prefix + "Langford/Langford-m1-k3/Langford-3-12.xml.lzm", "", dir);
		executePair("problems.acad.Queens 12 0", prefix + "Queens/Queens-m1-s1/Queens-0012.xml.lzma", " -s=all -v=0", dir);
		executePair("problems.acad.QueensKnights 20 3 20 5", prefix + "QueensKnights/QueensKnights-m1-s1/QueensKnights-020-5-add.xml.lzma", "", dir);
		executePair("problems.acad.QueensKnights 20 4 20 5", prefix + "QueensKnights/QueensKnights-m1-s1/QueensKnights-020-5-mul.xml.lzma", "", dir);
		executePair("problems.acad.Ramsey 15", prefix + "Ramsey/Ramsey-m1-s1/Ramsey-15.xml.lzma", " -f=cop -rc=10", dir);
		executePair("problems.acad.RectPacking -1", prefix + "RectPacking/RectPacking-m1-perf/RectPacking-001.xml.lzma", " -rc=10 -st -rn=75", dir);
		executePair("problems.acad.SchurrLemma 15 9 1", prefix + "SchurrLemma/SchurrLemma-m1-s1/Lemma-015-9-mod.xml.lzma", "", dir);
		executePair("problems.acad.SchurrLemma 66 4 0", prefix + "SchurrLemma/SchurrLemma-tr-s1/Lemma-066-4.xml.lzma", "", dir);
		executePair("problems.acad.Steiner3 7", prefix + "Steiner3/Steiner3-m1-s1/Steiner3-7.xml.lzma", " -v=0 -s=5000", dir);
		executePair("problems.tran.Sadeh /home/lecoutre/instances/sadeh/instances/enddr1-10-by-5-2", prefix + "Sadeh/Sadeh-m1-s1/enddr1-10-by-5-2.xml.lzma",
				" -rc=10", dir);
		executePair("problems.tran.GraphDimacs /home/lecoutre/instances/graphColoring/seriesOriginals4XCSP3/mono/1-fullins-5.col",
				prefix + "GraphDimacs/GraphDimacs-m1-mono/1-fullins-5.xml.lzma", " -f=cop -rc=10", dir);
		executePair("problems.tran.GraphDimacs /home/lecoutre/instances/graphColoring/seriesOriginals4XCSP3/fixed/qwhdec-o18-h120-1.col",
				prefix + "GraphDimacs/GraphDimacs-m1-fixed/qwhdec-o18-h120-1.xml.lzma", " -f=cop -rc=10", dir);

		executePair("problems.tran.LatinSquareGP /home/lecoutre/instances/seriesPapers/pesant/LatinSquare/qwh-o30-h374-01.pls",
				prefix + "LatinSquareGP/LatinSquareGP-m1-s1/qwh-o30-h374-01.xml.lzma", " -rc=10 -sing=Last -valh=DRand", dir);
		executePair("problems.tran.LatinSquareGP /home/lecoutre/instances/seriesPapers/PLS-gomez/qwh-o030-h320.pls",
				prefix + "LatinSquare/LatinSquare-m1-gs/qwh-o030-h320.xml.lzma", "", dir);
		executePair("/home/lecoutre/instances/benchmarks2006/bqwh/bqwh-18-141/bqwh-18-141-00_X2.xml.bz2",
				prefix + "LatinSquare/LatinSquare-xcsp2-bqwh18-141/bqwh-18-141-00_X2.xml.lzma", " -varh=DDegOnDom", dir);

		executePair("problems.tran.MagicSquareGP /home/lecoutre/instances/seriesPapers/pesant/MagicSquare/magic9-f10-01.dat",
				prefix + "MagicSquareGP/MagicSquareGP-m1-s1/magic9-f10-01.xml.lzma", " -rc=10 -valh=DRand -sing=Last", dir);
		executePair("problems.tran.MarketSplitGP /home/lecoutre/instances/seriesPapers/pesant/MarketSplit/marketSplit-01.dat",
				prefix + "MarketSplit/MarketSplit-m1-gp/marketSplit-01.xml.lzma", " -rc=10 -varh=DDegOnDom", dir);

		executePair("problems.tran.MultiKnapsackGP /home/lecoutre/instances/seriesPapers/pesant/MultiKnapsack/mknap2-13.dat",
				prefix + "MultiKnapsack/MultiKnapsack-m1-gp/mknap2-13.xml.lzma", "", dir);
		executePair("problems.real.Rlfap /home/lecoutre/instances/rlfap 1 10 -1 -1", prefix + "Rlfap/Rlfap-m1-graphs/graph10.xml.lzma", "", dir);
		executePair("problems.real.Rlfap /home/lecoutre/instances/rlfap 0 11 -1 6", prefix + "Rlfap/Rlfap-m1-scens11/scen11-f06.xml.lzma",
				" -rc=10 -varh=DDegOnDom -lc=3", dir);

		executePair(
				"problems.real.crossword.Crossword 1 /home/lecoutre/instances/crossword/dictionaries/lexDict/lex /home/lecoutre/instances/crossword/grids/herald/h1901 n",
				prefix + "Crossword/Crossword-m1-lex-herald/crossword-m1-lex-h1901.xml.lzma", " -varh=DDegOnDom -rc=10 -lc=3", dir);
		executePair(
				"problems.real.crossword.Crossword 1 /home/lecoutre/instances/crossword/dictionaries/wordsDict/words /home/lecoutre/instances/crossword/grids/puzzle/p22 n",
				prefix + "Crossword/Crossword-m1-words-puzzle/crossword-m1-words-p22.xml.lzma", " -varh=DDegOnDom", dir);
		executePair("problems.real.crossword.Crossword 1 /home/lecoutre/instances/crossword/dictionaries/ukDict/uk vg-5-8 n",
				prefix + "Crossword/Crossword-m1-uk-vg/crossword-m1-uk-vg-5-8.xml.lzma", "", dir);
		executePair("problems.real.crossword.Crossword 1 /home/lecoutre/instances/crossword/dictionaries/ukDict/uk vg-5-8 y",
				prefix + "Crossword/Crossword-m1dw-uk-vg/crossword-m1dw-uk-vg-5-8.xml.lzma", "", dir);
		executePair("problems.real.crossword.Crossword 1 /home/lecoutre/instances/crossword/dictionaries/ogdDict/ogd vg-6-7 n",
				prefix + "Crossword/Crossword-m1-ogd-vg/crossword-m1-ogd-vg-6-7.xml.lzma", "", dir);

		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/composed/composed-75/composed-75-01-80-9.xml.bz2",
				prefix + "Composed/Composed-m1-s75/composed-75-01-80-9.xml.lzma", "", dir);

		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/dimacs/aim-200/aim-200-1-6-sat-1.xml.bz2",
				prefix + "Dimacs/Dimacs-m1-aim200/aim-200-1-6-sat-1.xml.lzma", "", dir);
		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/dimacs/jnh/jnh-220.xml.bz2", prefix + "Dimacs/Dimacs-m1-jnh/jnh-220.xml.lzma",
				"", dir);
		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/dimacs/varDimacs/pret-060-75.xml.bz2",
				prefix + " Dimacs/Dimacs-m1-various/pret-060-75.xml.lzma", " -rc=10 -sing=last -varh=Memory", dir);

		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/ehi/ehi-90/ehi-90-315-71.xml.bz2",
				prefix + "Ehi/Ehi-m1-ehi-90/ehi-90-315-71.xml.lzma", " -varh=DDegOnDom -lc=5", dir);

		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/frb/frbLow/frb-35-17-3.xml.bz2",
				prefix + "Frb/Frb-m1-low/frb-35-17-3.xml.lzma", " -varh=DDegOnDom -nc=false", dir);
		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/geometric/geometric-50-20-d4-75-34.xml.bz2",
				prefix + "Geometric/Geometric-m1-rw/geometric-50-20-d4-75-34.xml.lzma", "", dir);

		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/haystacks/haystacks-06.xml.bz2",
				prefix + "Haystacks/Haystacks-m1-s1/haystacks-06.xml.lzma", "-varh=DDegOnDom", dir);
		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/lard/lard-92-92.xml.bz2", prefix + "Lard/Lard-m1-s1/lard-92-92.xml.lzma", "",
				dir);

		executePair("problems.xcsp2.XCSP2 /home/lecoutre/instances/benchmarks2006/tightness/tightness010/rand-2-40-8-753-100-78.xml.bz2",
				prefix + "Tightness/Tightness-m1-s010/rand-2-40-8-753-100-78.xml.lzma", "", dir);

	}

	// commencer toutes les instances par une majuscule ????

	// intension(not(in(horse, set()))); // for testing empty set (but nothing to do with zebra)

	interface Stringx3Consumer {
		void accept(String s1, String s2, String s3);
	}

	private static void cX2(String dir, String variant, String series) {
		for (File f : new File(PATH + dir).listFiles())
			exec(XCSP2 + " " + f.getAbsolutePath(), variant, series);
	};

	private static void cZn(String dir, String pb) {
		for (File f : new File(PATH_MINI + dir).listFiles(withExtension(DZN)))
			exec(pb + " " + f.getAbsolutePath(), "zinc", "s1");
	};

	public static void main(String[] args) {
		if (args.length != 1 && (args.length != 2 || !args[1].equals("-dataexport"))) {
			System.out.println("Usage : java " + Series.class.getName() + " <seriesName> [-dataexport]");
			return;
		}
		dataexport = args.length == 2 && args[1].toLowerCase().equals("-dataexport");
		serieName = args[0].trim().toLowerCase();

		if (serieName.equals(TEST)) {
			test();
			return;
		}

		if (serieName.equals(ALL)) {
			mainDir = new File(Instant.now().toString().substring(0, 13));
			Kit.control(mainDir.mkdir(), () -> "Directory already present");
		}

		if (dirFor(RANDOM)) {
			cX2("random/marc", "m1", "marc");
			cX2("random/rand-2-23-23", "B", "2-23-23");
			cX2("random/rand-2-24-24", "B", "2-24-24");
			cX2("random/rand-2-25-25", "B", "2-25-25");
			cX2("random/rand-2-26-26", "B", "2-26-26");
			cX2("random/rand-2-27-27", "B", "2-27-27");

			cX2("random/tightness010", "D", "s010");
			cX2("random/tightness020", "D", "s020");
			cX2("random/tightness035", "D", "s035");
			cX2("random/tightness050", "D", "s050");
			cX2("random/tightness065", "D", "s065");
			cX2("random/tightness080", "D", "s080");
			cX2("random/tightness090", "D", "s090");

			cX2("random/frbLow", "RB", "low");
			cX2("random/frbHigh", "RB", "high");

			cX2("random/rand-2-30-15", "RB", "2-30-15");
			cX2("random/rand-2-30-15f", "RB", "2-30-15f");
			cX2("random/rand-2-40-19", "RB", "2-40-19");
			cX2("random/rand-2-40-19f", "RB", "2-40-19f");
			cX2("random/rand-2-50-23", "RB", "2-50-23");
			cX2("random/rand-2-50-23f", "RB", "2-50-23f");

			cX2("random/rand-3-20-20", "RB", "3-20-20");
			cX2("random/rand-3-20-20f", "RB", "3-20-20f");
			cX2("random/rand-3-24-24", "RB", "3-24-24");
			cX2("random/rand-3-24-24f", "RB", "3-24-24f");
			cX2("random/rand-3-28-28", "RB", "3-28-28");
			cX2("random/rand-3-28-28f", "RB", "3-28-28f");

			cX2("random/rand-5-12-12", "m1", "5-12-12");
			cX2("random/rand-5-12-12t", "m1", "5-12-12t");
			cX2("random/rand-7-40-8t", "m1", "7-40-8t");
			cX2("random/rand-8-20-5", "m1", "8-20-5");
			cX2("random/rand-10-20-10", "m1", "10-20-10");
			cX2("random/rand-10-60-20", "m1", "10-60-20");
			cX2("random/rand-15-23-3", "m1", "15-23-3");

			// series from wei
			cX2("random/rand-5-2X-05c", "m1", "5-X2X-05c");
			cX2("random/rand-5-4X-05c", "m1", "5-4X-05c");
			cX2("random/rand-5-8X-05c", "m1", "5-8X-05c");

			cX2("random/rand-5-10-10", "m1", "5-10-10"); // k5 from yves
		}

		if (dirFor(QRANDOM)) {
			cX2("qrandom/bdd-15-21-2", "bdd", "15-21-2");
			cX2("qrandom/bdd-18-21-2", "bdd", "18-21-2");
			cX2("qrandom/mdd-7-25-5", "mdd", "7-25-5");
			cX2("qrandom/mdd-7-25-5-p7", "mdd", "7-25-5-p7");
			cX2("qrandom/mdd-7-25-5-p9", "mdd", "7-25-5-p9");

			cX2("qrandom/composed-25", "composed", "s25");
			cX2("qrandom/composed-75", "composed", "s75");

			cX2("qrandom/ehi-85", "ehi", "s85");
			cX2("qrandom/ehi-90", "ehi", "s90");

			cX2("qrandom/geometric", "geometric", "rw");

			// verifier pourquoi c'est long de charger les variables; trim dans parseExtension ???
			cX2("qrandom/lard", "m1", "lard");

			cX2("seriesPapers/yves/normalized/regular", "reg2ext", "s1");
		}

		// slide(y, x, range(n - 1), i -> equal(y[i], dist(x[i], x[i + 1]))).tag(CHANNELING);
		if (dirFor(ALL_INTERVAL)) {
			IntStream.of(vals(rangeC(5, 20), rangeC(25, 100, 5))).forEach(i -> exec(ALL_INTERVAL + " -data=" + i + " -dataFormat=%03d " + " -iag=true"));
		}

		// java abscon.Resolution problems.acad.Bibd 6 50 25 3 10 -ev -s=all -v=0 -sing=Last -valh=Last => 1366 solutions
		// TODO merger les pars3 et pars5, virer les doublons et les doublons indirects (voir message à cedric)
		if (dirFor(BIBD)) {
			BiConsumer<int[], String> c = (t, s) -> {
				String data = "-data=[" + (t.length == 3 ? t[0] + ",0,0," + t[1] + "," + t[2] : Kit.join(t, ",")) + "]";
				String format = "-dataFormat=" + (t.length == 3 ? "[%02d,,,%02d,%02d]" : "[%02d,%03d,%02d,%02d,%02d]");
				exec(Bibd.class.getName() + " -variant=sc " + data + " " + format, "sc", s);
				exec(Bibd.class.getName() + " -variant=sum " + data + " " + format, "sum", s);
			};

			// series from "Global constraints for lexicographic orderings"
			for (int[] t : new int[][] { { 6, 50, 25, 3, 10 }, { 6, 60, 30, 3, 12 }, { 6, 70, 35, 3, 10 }, { 10, 90, 27, 3, 6 }, { 9, 108, 36, 3, 9 }, { 15, 70, 14, 3, 2 }, { 12, 88, 22, 3, 4 }, { 9, 120, 40, 3, 10 }, { 10, 120, 36, 3, 8 }, { 13, 104, 24, 3, 4 } })
				c.accept(t, "lex");

			// series from "solving strategies for highly symmetric CSPs"
			for (int[] t : new int[][] { { 7, 7, 3, 3, 1 }, { 6, 10, 5, 3, 2 }, { 7, 14, 6, 3, 2 }, { 9, 12, 4, 3, 1 }, { 6, 20, 10, 3, 4 }, { 7, 21, 9, 3, 3 }, { 6, 30, 15, 3, 6 }, { 7, 28, 12, 3, 4 }, { 9, 24, 8, 3, 2 }, { 6, 40, 20, 3, 8 }, { 7, 35, 15, 3, 5 }, { 7, 42, 18, 3, 6 }, { 10, 30, 9, 3, 2 }, { 6, 50, 25, 3, 10 }, { 9, 36, 12, 3, 3 }, { 13, 26, 6, 3, 1 }, { 7, 49, 21, 3, 7 }, { 6, 60, 30, 3, 12 }, { 7, 56, 24, 3, 8 }, { 6, 70, 35, 3, 14 }, { 9, 48, 16, 3, 4 }, { 7, 63, 27, 3, 9 }, { 8, 56, 21, 3, 6 }, { 6, 80, 40, 3, 6 }, { 7, 70, 30, 3, 10 }, { 15, 35, 7, 3, 1 }, { 12, 44, 11, 3, 2 }, { 7, 77, 33, 3, 11 }, { 9, 60, 20, 3, 5 }, { 7, 84, 26, 3, 12 }, { 10, 60, 18, 3, 4 }, { 11, 55, 15, 3, 3 }, { 7, 91, 39, 3, 13 }, { 9, 72, 24, 3, 6 }, { 13, 52, 12, 3, 2 }, { 9, 84, 28, 3, 7 }, { 9, 36, 32, 3, 8 }, { 10, 90, 27, 3, 6 }, { 9, 108, 36, 3, 9 }, { 13, 78, 18, 3, 3 }, { 15, 70, 14, 3, 2 }, { 12, 88, 22, 3, 4 }, { 9, 120, 40, 3, 10 }, { 19, 57, 9, 3, 1 }, { 10, 120, 36, 3, 8 }, { 11, 110, 30, 3, 6 }, { 16, 80, 15, 3, 2 }, { 13, 104, 24, 3, 4 } })
				c.accept(t, "sym");

			// series from "Symmetry Breaking Using Stabilizer"
			for (int[] t : new int[][] { { 8, 4, 6 }, { 7, 3, 10 }, { 6, 3, 10 }, { 6, 3, 12 }, { 12, 6, 5 }, { 13, 4, 2 }, { 9, 3, 9 }, { 9, 3, 10 }, { 11, 5, 4 }, { 16, 6, 3 }, { 16, 4, 1 }, { 10, 3, 6 }, { 19, 9, 4 }, { 12, 3, 4 }, { 10, 3, 8 }, { 13, 3, 4 }, { 16, 6, 2 }, { 15, 3, 1 }, { 15, 3, 2 }, { 15, 5, 2 }, { 25, 9, 3 }, { 25, 5, 1 }, { 21, 5, 1 }, { 22, 7, 2 } })
				c.accept(t, "stab1");

			for (int[] t : new int[][] { { 6, 3, 2 }, { 7, 3, 1 }, { 6, 3, 4 }, { 9, 3, 1 }, { 7, 3, 2 }, { 8, 4, 3 }, { 6, 3, 6 }, { 11, 5, 2 }, { 10, 4, 2 }, { 7, 3, 3 }, { 13, 4, 1 }, { 6, 3, 8 }, { 9, 4, 3 }, { 16, 4, 1 }, { 7, 3, 4 }, { 6, 3, 10 }, { 9, 3, 2 }, { 16, 6, 2 }, { 15, 5, 2 }, { 13, 3, 1 }, { 7, 3, 5 }, { 15, 7, 3 }, { 21, 5, 1 }, { 25, 5, 1 }, { 10, 5, 4 }, { 7, 3, 6 }, { 22, 7, 2 }, { 7, 3, 7 }, { 8, 4, 6 }, { 19, 9, 4 }, { 10, 3, 2 }, { 31, 6, 1 }, { 7, 3, 8 }, { 9, 3, 3 }, { 7, 3, 9 }, { 15, 3, 1 }, { 21, 6, 2 }, { 13, 4, 2 }, { 11, 5, 4 }, { 12, 6, 5 }, { 25, 9, 3 }, { 16, 6, 3 } })
				c.accept(t, "stab2");

			// series from Minizinc in CSPLib
			for (int[] t : new int[][] { { 3, 3, 1 }, { 4, 2, 1 }, { 6, 3, 2 }, { 7, 3, 1 }, { 7, 3, 2 }, { 8, 4, 3 }, { 9, 3, 1 }, { 11, 5, 2 }, { 13, 3, 1 }, { 13, 4, 1 }, { 15, 3, 1 }, { 15, 7, 3 }, { 16, 4, 1 }, { 19, 3, 1 }, { 25, 5, 1 }, { 28, 4, 1 } })
				c.accept(t, "mini");

			// open instances from http://www.csplib.org/Problems/prob028/results/
			for (int[] t : new int[][] { { 46, 69, 9, 6, 1 }, { 51, 85, 10, 6, 1 }, { 61, 122, 12, 6, 1 }, { 22, 33, 12, 8, 4 }, { 40, 52, 13, 10, 3 }, { 46, 69, 15, 10, 3 }, { 65, 80, 16, 13, 3 }, { 81, 81, 16, 16, 3 }, { 49, 98, 18, 9, 3 }, { 55, 99, 18, 10, 3 }, { 85, 102, 18, 15, 3 }, { 39, 57, 19, 13, 6 }, { 61, 122, 20, 10, 3 }, { 46, 92, 20, 10, 4 }, { 45, 75, 20, 12, 5 }, { 57, 76, 20, 15, 5 }, { 57, 133, 21, 9, 3 }, { 40, 60, 21, 14, 7 }, { 85, 105, 21, 17, 4 }, { 45, 90, 22, 11, 5 }, { 45, 66, 22, 15, 7 }, { 55, 132, 24, 10, 4 }, { 69, 92, 24, 18, 6 }, { 51, 85, 25, 15, 7 }, { 51, 75, 25, 17, 8 }, { 55, 135, 27, 11, 5 }, { 55, 99, 27, 15, 7 }, { 57, 84, 28, 19, 9 }, { 57, 76, 28, 21, 10 }, { 85, 85, 28, 28, 9 }, { 34, 85, 30, 12, 10 }, { 58, 87, 30, 20, 10 }, { 56, 88, 33, 21, 12 }, { 78, 117, 33, 22, 9 }, { 64, 96, 33, 22, 11 }, { 97, 97, 33, 33, 11 }, { 69, 102, 34, 23, 11 }, { 46, 161, 35, 10, 7 }, { 51, 85, 35, 21, 14 }, { 64, 80, 35, 28, 15 }, { 69, 138, 36, 18, 9 }, { 52, 104, 36, 18, 12 }, { 49, 84, 36, 21, 15 }, { 55, 90, 36, 22, 14 }, { 70, 105, 36, 24, 12 }, { 85, 85, 36, 36, 15 }, { 75, 111, 37, 25, 12 }, { 58, 116, 38, 19, 12 }, { 76, 114, 39, 26, 13 }, { 66, 99, 39, 26, 15 }, { 57, 152, 40, 15, 10 }, { 65, 104, 40, 25, 15 } })
				c.accept(t, "open"); // 97, 97, 33, 33, 11 pas passé pour Bibd1
		}
		if (dirFor(BLACK_HOLE)) {
			for (int i = 0; i < 20; i++)
				exec(Blackhole_Random.class.getName() + " 4 3 " + i, "s04");
			for (int i = 0; i < 20; i++)
				exec(Blackhole_Random.class.getName() + " 7 3 " + i, "s07");
			for (int i = 0; i < 20; i++)
				exec(Blackhole_Random.class.getName() + " 10 3 " + i, "s10");
			for (int i = 0; i < 20; i++)
				exec(Blackhole_Random.class.getName() + " 13 3 " + i, "s13");

			cX2("benchmarks2006/blackHole/BH-4-04", "xcsp2", "s04");
			cX2("benchmarks2006/blackHole/BH-4-07", "xcsp2", "s07");
			cX2("benchmarks2006/blackHole/BH-4-13", "xcsp2", "s13");
		}
		if (dirFor(CHESSBOARD_COLORATION)) {

			// for (int i : vals(range(5, 20), range(25, 40, 5)))
			// executeExport(BoardColoration.class.getName() + " -variant=int -data=[" + i + "," + i + "] -dataFormat=[%02d,%02d] -f=cop ",
			// 12000, "s1");
			// for (int i : vals(range(5, 20), range(25, 40, 5)))
			// executeExport(BoardColoration.class.getName() + " -variant=int -data=[" + (i - 2) + "," + i + "] -dataFormat=[%02d,%02d] -f=cop
			// ", 8000, "s2");

			for (int i : vals(rangeC(5, 20), rangeC(25, 40, 5)))
				exec(BoardColoration.class.getName() + " -data=[" + i + "," + i + "] -dataFormat=[%02d,%02d] -f=cop ", 12000, "s1");
			for (int i : vals(rangeC(5, 20), rangeC(25, 40, 5)))
				exec(BoardColoration.class.getName() + " -data=[" + (i - 2) + "," + i + "] -dataFormat=[%02d,%02d] -f=cop ", 8000, "s2");
		}
		if (dirFor(COLOURED_QUEENS))
			rangeC(3, 19).execute(i -> exec(COLOURED_QUEENS + " -data=" + i));
		if (dirFor(DISTINCT_VECTORS)) {
			for (int i : new int[] { 5, 10, 20, 50, 100, 200 })
				exec(DistinctVectors.class.getName() + " -data=[30," + i + ",2] -dataFormat=[%02d,%03d,%02d]", "s1");
			for (int i : new int[] { 5, 10, 20, 50 })
				exec(DistinctVectors.class.getName() + " -data=[" + i + ",100,2] -dataFormat=[%02d,%03d,%02d]", "s1");
			for (int i : new int[] { 2, 8, 16, 24, 32, 40 })
				exec(DistinctVectors.class.getName() + " -data=[40,100," + i + "] -dataFormat=[%02d,%03d,%02d]", "s1");
		}
		if (dirFor(DOMINO)) {
			for (int i = 100; i <= 1000; i += 100)
				exec(Domino.class.getName() + " -data=[100," + i + "]");
			for (int i = 100; i <= 1000; i += 100)
				exec(Domino.class.getName() + " -data=[" + i + ",100]");
			for (int i = 100; i < 1000; i += 100)
				exec(Domino.class.getName() + " -data=[" + i + "," + i + "]");
			for (int i = 1000; i <= 10000; i += 1000)
				exec(Domino.class.getName() + " -data=[" + i + "," + i + "]");
		}
		if (dirFor(DUBOIS)) {
			for (int i : vals(rangeC(15, 30), rangeC(35, 100, 5)))
				exec(Dubois.class.getName() + " -data=" + i + " -dataFormat=%03d");
		}
		if (dirFor(GOLOMB)) {
			for (int i = 5; i < 20; i++)
				exec("problems.acad.GolombRuler -data=" + i + " -dataFormat=%02d -variant=a3 -f=cop ", "a3", "s1");
			for (int i = 5; i < 20; i++)
				exec("problems.acad.GolombRuler -data=" + i + " -dataFormat=%02d -variant=a4 -f=cop ", "a4", "s1");
			for (int i = 20; i < 30; i++)
				exec("problems.acad.GolombRuler -data=" + i + " -dataFormat=%02d -variant=a3 -f=cop ", 12000, "a3", "s1");
			for (int i = 20; i < 30; i++)
				exec("problems.acad.GolombRuler -data=" + i + " -dataFormat=%02d -variant=a4 -f=cop ", 12000, "a4", "s1");
		}
		if (dirFor(GRACEFUL))
			for (int i = 2; i < 15; i++)
				for (int j = 2; j < 10; j++)
					exec(GracefulGraph.class.getName() + " -data=[" + i + "," + j + "] -dataFormat=[K%02d,P%02d] ");
		if (dirFor(HANOI))
			for (int i = 3; i < 10; i++)
				exec(Hanoi.class.getName() + " -data=" + i + " -dataFormat=%02d", 8000);
		if (dirFor(KNAPSACK)) {
			range(20).execute(i -> exec(KNAPSACK + " 30 100 " + i + " -f=cop ", "s30"));
			range(20).execute(i -> exec(KNAPSACK + " 40 150 " + i + " -f=cop ", "s40"));
			range(20).execute(i -> exec(KNAPSACK + " 50 200 " + i + " -f=cop ", "s50"));
			range(20).execute(i -> exec(KNAPSACK + " 60 250 " + i + " -f=cop ", "s60"));
		}
		if (dirFor(KNIGHTS))
			for (int i : new int[] { 8, 10, 12, 15, 20, 25, 50, 80, 100 })
				for (int j : new int[] { 5, 9, 25 })
					if (j == 5 || j == 9 && i >= 12 || j == 25 && i >= 50)
						exec(Knights.class.getName() + " -data=[" + i + "," + j + "] -dataFormat=[%03d,%02d] -exai=no -exmo=yes");
		if (dirFor(KNIGHT_TOUR)) {
			for (int i = 4; i <= 17; i++)
				exec(KnightTour.class.getName() + " -data=" + i + " -dataFormat=%02d -variant=int -exai=no -exmo=yes", 12000, "int", "s1");
			for (int i = 4; i <= 17; i++)
				for (int j = 2; j < i; j++)
					if (i % (j - 1) == 0 && (i != 16 || j != 9))
						exec(KnightTour.class.getName() + " -data=" + i + " -dataFormat=%02d -variant=ext" + j + " -exai=no -exmo=yes", 12000, "ext", "s1");
		}
		// Var[] numbers= array("n", dom(0, n - 1), k * n); // each variable at (i) gives the number put at position i in the sequence
		if (dirFor(LANGFORD)) {
			for (int k = 2; k <= 4; k++)
				for (int n : vals(rangeC(2, 25), rangeC(30, 50, 5), rangeC(60, 90, 10)))
					exec(Langford.class.getName() + " -data=[" + k + "," + n + "] -dataFormat=[%01d,%02d]", "k" + k);
			// use double abstraction below
			for (int n : vals(rangeC(2, 25), rangeC(30, 50, 5), rangeC(60, 90, 10)))
				exec(LangfordBin.class.getName() + " -data=" + n + " -dataFormat=%02d", "m2", "s1");
		}
		if (dirFor(LOW_AUTOCORRELATION)) {
			for (int n = 3; n < 100; n++)
				exec(LowAutocorrelation.class.getName() + " -data=" + n + " -dataFormat=%03d -f=cop");
		}
		if (dirFor(ORTHOLATIN)) {
			// for (File f : new File(PATH + "newbench/benchs/correia").listFiles())
			// executeExport(XCSP2 + " " + f.getAbsolutePath(), "s1");
			for (int n = 2; n < 30; n++)
				exec(Ortholatin.class.getName() + " -data=" + n + " -dataFormat=%03d -iag=true");
		}
		if (dirFor(QUADRATIC_ASSIGNMENT)) {
			for (File f : new File(PATH + "qap/data").listFiles())
				exec(QuadraticAssignment_Parser.class.getName() + " " + f.getAbsolutePath() + " -f=cop", 12000);
		}
		if (dirFor(QUEEN_ATTACKING)) {
			for (File f : new File(PATH + "benchmarks2006/queenAttacking").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath() + " -exai=no -exmo=yes", "xcsp2", "s1");
			for (int i = 3; i <= 20; i++)
				exec(QueenAttacking.class.getName() + " -data=" + i + " -dataFormat=%02d -f=cop -exai=no -exmo=yes");
		}
		if (dirFor(QUEENS)) {
			for (int i : vals(rangeC(4, 12), 15, 20, 30, 50, 80, 100, 120, 150, 180, 200, 300, 400, 500, 800, 1000))
				exec("problems.acad.Queens " + i + " 0", 8000);
		}
		if (dirFor(QUEENS_KNIGHTS)) {
			for (int n : new int[] { 8, 10, 12, 15, 20, 25, 50, 80, 100 })
				exec(QueensKnights.class.getName() + " -data=[" + n + "," + n + ",5] -dataFormat=[%03d,%03d,%02d] -variant=add -exai=yes -exmo=yes");
			for (int n : new int[] { 8, 10, 12, 15, 20, 25, 50, 80, 100 })
				exec(QueensKnights.class.getName() + " -data=[" + n + "," + n + ",5] -dataFormat=[%03d,%03d,%02d] -variant=mul -exai=yes -exmo=yes");
		}
		if (dirFor(RAMSEY)) {
			for (int i = 8; i < 51; i++)
				exec(Ramsey.class.getName() + " -data=" + i + " -dataFormat=%02d -f=cop");
		}

		if (dirFor(RECT_PACKING))
			for (File f : new File(PATH + "DataJSON/RectPacking/dataPerf2").listFiles()) // identical pbs : 166-167 168-169 182-183
				exec(RectPacking.class.getName() + " -data=" + f.getAbsolutePath(), "perf");

		if (dirFor(SCHURR)) {
			for (int i : vals(12, 15, 20, 30, 50, 100))
				exec(SchurrLemma.class.getName() + " -data=[" + i + ",9] -dataFormat=[%03d,%01d] -variant=mod", "mod", "s1");
			exec(SchurrLemma.class.getName() + " -data=[23,3] -dataFormat=[%03d,%01d] -variant=nor", "nor", "s1");
			exec(SchurrLemma.class.getName() + " -data=[24,3] -dataFormat=[%03d,%01d] -variant=nor", "nor", "s1");
			exec(SchurrLemma.class.getName() + " -data=[66,4] -dataFormat=[%03d,%01d] -variant=nor", "nor", "s1");
			exec(SchurrLemma.class.getName() + " -data=[67,4] -dataFormat=[%03d,%01d] -variant=nor", "nor", "s1");
		}
		if (dirFor(STEINER3))
			rangeC(5, 14).execute(i -> exec(Steiner3.class.getName() + " -data=" + i + " -dataFormat=%02d", 12000));
		if (dirFor(STRIP_PACKING)) {
			range(21).execute(i -> exec(StripPackingReader.class.getName() + " " + PATH + "tdsp/data/series1.txt " + i, "series1"));
			range(36).execute(i -> exec(StripPackingReader.class.getName() + " " + PATH + "tdsp/data/seriesN.txt " + i, "seriesN"));
			range(36).execute(i -> exec(StripPackingReader.class.getName() + " " + PATH + "tdsp/data/seriesT.txt " + i, "seriesT"));
		}

		/******/

		if (dirFor(RADAR_SURVEILLANCE)) {
			for (int i = 0; i < 50; i++)
				exec(RadarSurveillance_Random.class.getName() + " 8 24 3 2 0 " + i + " -iag=true", "s8-24");
			for (int i = 0; i < 50; i++)
				exec(RadarSurveillance_Random.class.getName() + " 8 30 3 0 0 " + i + " -iag=true", "s8-30");
			for (int i = 0; i < 50; i++)
				exec(RadarSurveillance_Random.class.getName() + " 9 28 4 2 0 " + i + " -iag=true", "s9-28");
		}
		if (dirFor(ROOM_MATE)) {
			for (File f : new File(PATH + "roommate").listFiles())
				exec(RoomMate.class.getName() + "problems.patt.RoomMate " + f.getAbsolutePath() + " -variant=int", 12000, "int", "s1");
		}
		if (dirFor(SOCIAL_GOLFERS)) {
			cX2("benchmarks2006/socialGolfers", "xcsp2", "s1");
			for (int i = 2; i <= 9; i++)
				for (int j = 2; j <= 9; j++)
					for (int k = 3; k <= 9; k++)
						exec("problems.patt.SocialGolfers -data=[" + i + "," + j + "," + k + "] -variant=cp", "cp", "s1");
		}
		if (dirFor(SUBISOMORPHISM)) {
			File[] files = new File(PATH + "isoGraphs/newSIPbenchmarks/LV").listFiles();
			Arrays.sort(files, (f1, f2) -> f1.getName().compareTo(f2.getName()));
			for (int i = 0; i < files.length; i++)
				for (int j = i + 1; j < files.length; j++)
					exec("problems.patt.Subisomorphism " + files[i].getAbsolutePath() + " " + files[j].getAbsolutePath(), "LV");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/scalefree").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "SF");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si2-bvg").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si2-bvg");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si2-m4D").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si2-m4D");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si2-rand").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si2-rand");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si4-bvg").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si4-bvg");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si4-m4D").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si4-m4D");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si4-rand").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si4-rand");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si6-bvg").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si6-bvg");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si6-m4D").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si6-m4D");
			for (File f : new File(PATH + "isoGraphs/newSIPbenchmarks/si/si6-rand").listFiles())
				exec("problems.patt.Subisomorphism " + f.getAbsolutePath() + "/pattern " + f.getAbsolutePath() + "/target", "si6-rand");
		}
		if (dirFor(TRAVELLING_SALESMAN)) { // hard to test
			cX2("benchmarks2006/travellingSalesman/tsp-20", "xcsp2", "s20");
			cX2("benchmarks2006/travellingSalesman/tsp-25", "xcsp2", "s25");
			cX2("seriesPapers/yves/normalized/TSP-20-QUAT", "xcsp2", "s20a4");

			Function<String, String> f = data -> TravellingSalesmanRandom.class.getName() + " " + data + " -dataFormat=[%03d,%02d,%02d] -f=cop ";
			for (int nCities : rangeC(15, 50, 5))
				range(20).execute(seed -> exec(f.apply(nCities + " 30 " + seed), "n" + nCities));
			for (int nCities : vals(75, 100, 150))
				range(20).execute(seed -> exec(f.apply(nCities + " 50 " + seed), "n" + nCities));
		}
		if (dirFor(WAREHOUSE)) {
			for (File f : new File(PATH + "warehouse").listFiles())
				exec(Warehouse_Parser.class.getName() + " " + f.getAbsolutePath() + " -f=cop");
		} // cap81 has to be removed because it is similar to cap101

		/******/

		if (dirFor(BASIC)) {
			exec("problems.puzz.Allergy -iag=true");
			exec("problems.puzz.Change -data=[82,100] -f=cop");
			exec("problems.puzz.Purdey -iag=true");
			exec("problems.puzz.Recipe -f=cop");
			exec("problems.puzz.Dominoes " + PATH + "puzzles/dominoes/txt/grid1.txt -exai=yes -exmo=yes");
			exec("problems.puzz.LabeledDice");
			exec("problems.puzz.Zebra -iag=true");
		}
		if (dirFor(CRYPTO_PUZZLE)) {
			for (String s : new String[] { "donald gerald robert", "summer school coolest", "send more money", "no no yes", "cross roads danger", "europa planets neptune", "comet uranus saturn", "black green orange", "ivory purple violet", "piccolo violin panpipe", " bell flute violin", "kyoto osaka tokyo", "kendo kimono sashimi", "cabbage lettuce eggplant", "pepper potato celery", ""
					+ "basic simula pascal", "ada scala cobol", "monitor network internet", "apple floppy reboot", "okayama yamagata kanazawa", "tottori yamagata yokohama" }) {
				String[] t = s.trim().toUpperCase().split(Constants.REG_WS);
				exec(CryptoPuzzle.class.getName() + " -data=[" + t[0] + "," + t[1] + "," + t[2] + "]");
			}
		}
		if (dirFor(KAKURO)) {
			// for (int i = 0; i < 172; i++)
			// executeExport(KakuroReader.class.getName() + " " + PATH + "kakuro/data/data_generated_easy.ecl " + i + " -variant=ext", "ext",
			// "easy");
			// for (int i = 0; i < 192; i++)
			// executeExport(KakuroReader.class.getName() + " " + PATH + "kakuro/data/data_generated_medium.ecl " + i + " -variant=ext",
			// "ext", "medium");
			// for (int i = 0; i < 187; i++)
			// executeExport(KakuroReader.class.getName() + " " + PATH + "kakuro/data/data_generated_hard.ecl " + i + " -variant=ext", "ext",
			// "hard");

			for (int i = 0; i < 172; i++)
				exec(KakuroReader.class.getName() + " " + PATH + "kakuro/data/data_generated_easy.ecl " + i + " -variant=sumdiff", "sumdiff", "easy");
			for (int i = 0; i < 192; i++)
				exec(KakuroReader.class.getName() + " " + PATH + "kakuro/data/data_generated_medium.ecl " + i + " -variant=sumdiff", "sumdiff", "medium");
			for (int i = 0; i < 187; i++)
				exec(KakuroReader.class.getName() + " " + PATH + "kakuro/data/data_generated_hard.ecl " + i + " -variant=suumdiff", "sumdiff", "hard");

			// TODO other variant 1, with double abstraction ?
		}
		if (dirFor(MAGIC_SEQUENCE)) {
			for (int i : vals(rangeC(3, 20), rangeC(25, 50, 5), rangeC(60, 100, 10), rangeC(120, 200, 20), rangeC(300, 1000, 100), 2000))
				exec(MagicSequence.class.getName() + " -data=" + i + " -dataFormat=%03d -variant=card ", "card", "s1");
			// for (int i : vals(range(3, 20), range(25, 50, 5), range(60, 100, 10), range(120, 200, 20), range(300, 1000, 100), 2000))
			// executeExport(MagicSequence.class.getName() + " -data=" + i + " -dataFormat=%03d -variant=count", 12000, "count", "s1");
		}
		if (dirFor(SUDOKU)) {
			for (File f : new File(PATH + "sudoku/series1").listFiles())
				exec(Sudoku_Parser.class.getName() + " 9 " + f.getAbsolutePath() + " -variant=table", "table", "s1");
			for (File f : new File(PATH + "sudoku/series1").listFiles())
				exec(Sudoku_Parser.class.getName() + " 9 " + f.getAbsolutePath() + " -variant=alldiff", "alldiff", "s1");
		}

		/******/

		if (dirFor(CAR_SEQUENCING)) {
			// toto abstraction on condition ?
			for (File f : new File(PATH + "vincent/carSequencing/jcr").listFiles())
				exec(CarSequencing.class.getName() + " " + f.getAbsolutePath(), "jcr");
			for (File f : new File(PATH + "vincent/carSequencing/gagne").listFiles())
				exec(CarSequencing.class.getName() + " " + f.getAbsolutePath(), "gagne");
		}

		if (dirFor(RENAULT_MOD))
			for (File f : new File(PATH + "modifiedRenault/originals").listFiles())
				exec("problems.tran.RenaultMod " + f.getAbsolutePath());
		if (dirFor(RENAULT)) {
			for (File f : new File(PATH + "helene/xcsp2").listFiles())
				exec(f.getAbsolutePath());
		}
		if (dirFor(RLFAP_OLD)) {
			for (int i = 1; i <= 14; i++)
				exec("problems.real.Rlfap " + PATH + "rlfap 1 " + i + " -1 -1 ", "graphs");
			for (int i : vals(rangeC(1, 9), 11)) // 10 removed because similar to 9
				exec("problems.real.Rlfap " + PATH + "rlfap 0 " + i + " -1 -1 ", "scens");
			for (int[] t : new int[][] { { 2, -1, 24 }, { 2, -1, 25 }, { 8, -1, 10 }, { 8, -1, 11 }, { 9, -1, 9 }, { 9, -1, 10 }, { 12, 0, -1 }, { 12, 1, -1 }, { 13, 0, -1 }, { 13, 1, -1 }, { 14, -1, 27 }, { 14, -1, 28 } })
				exec("problems.real.Rlfap " + PATH + "rlfap 1 " + Kit.join(t), "graphsMod");
			for (int[] t : new int[][] { { 1, -1, 8 }, { 1, -1, 9 }, { 2, -1, 24 }, { 2, -1, 25 }, { 3, -1, 10 }, { 3, -1, 11 }, { 6, 1, 2 }, { 6, 1, -1 }, { 6, 2, -1 }, { 7, 1, 4 }, { 7, 1, 5 }, { 9, 1, 3 } })
				// { 10, 1, 3 } removed because similar to 9
				exec("problems.real.Rlfap " + PATH + "rlfap 0 " + Kit.join(t), "scensMod");
			for (int i = 1; i <= 12; i++)
				exec("problems.real.Rlfap " + PATH + "rlfap 0 11 -1 " + i, "scens11");
			for (int i = 2; i <= 3; i++)
				for (int j = 0; j <= 4; j++)
					if (i != 3 || j != 0)
						exec("problems.real.Rlfap " + PATH + "rlfap " + i + " " + j + " -1 -1 ", "subs");
		}

		// herald h0501 is similar to vg-5-5 and h0504 is equivalent to p04 (puzzle 4)
		if (dirFor(CROSSWORD)) {
			for (String dict : new String[] { "lex", "words", "uk", "ogd", "ogd2008" }) {
				String prefix = "problems.real.crossword.Crossword -data=[" + PATH + "crossword/dictionaries/" + dict + "Dict/" + dict;
				for (File f : new File(PATH + "crossword/grids/herald/").listFiles())
					try {
						exec(prefix + "," + f.getAbsolutePath() + "] -variant=m1", dict + "-herald");
						// executeExport(prefix + " " + f.getAbsolutePath() + " y", "m1dw", dict + "-herald");
					} catch (Exception e) {
						System.err.println("Not possible for " + f.getAbsolutePath());
					}
				for (File f : new File(PATH + "crossword/grids/puzzle/").listFiles())
					try {
						exec(prefix + "," + f.getAbsolutePath() + "] -variant=m1", dict + "-puzzle");
						// executeExport(prefix + " " + f.getAbsolutePath() + " y", "m1dw", dict + "-puzzle");
					} catch (Exception e) {
						System.err.println("Not possible for " + f.getAbsolutePath());
					}
				for (int i = 4; i <= 16; i++)
					for (int j = i; j < i + 5; j++) {
						exec(prefix + ",vg-" + i + "-" + j + "] -variant=m1", dict + "-vg");
						// executeExport(prefix + " vg-" + i + "-" + j + " y", "m1dw", dict + "-vg");
					}
			}
			// variant 2 ???
		}
		if (dirFor(SPORTS_SCHEDULING)) {
			// !!!! use double abstraction when saving
			rangeC(4, 40, 2).execute(i -> exec(SportsScheduling.class.getName() + " -data=" + i + " -dataFormat=%02d"));
		}
		if (dirFor(RCPSP)) {
			for (File f : new File(PATH + "rcpsp/j30").listFiles())
				exec("problems.real.Rcpsp " + f.getAbsolutePath() + " -f=cop", "j30");
			for (File f : new File(PATH + "rcpsp/j60").listFiles())
				exec("problems.real.Rcpsp " + f.getAbsolutePath() + " -f=cop", "j60");
			for (File f : new File(PATH + "rcpsp/j90").listFiles())
				exec("problems.real.Rcpsp " + f.getAbsolutePath() + " -f=cop", "j90");
			for (File f : new File(PATH + "rcpsp/j120").listFiles())
				exec("problems.real.Rcpsp " + f.getAbsolutePath() + " -f=cop", "j120");
		}
		if (dirFor(GRAPH_COLORING)) {
			for (File f : new File(PATH + "graphColoring/seriesOriginals4XCSP3/mono").listFiles())
				exec(GraphColoringReader.class.getName() + " " + f.getAbsolutePath() + " -f=cop", "mono");
			for (File f : new File(PATH + "graphColoring/seriesOriginals4XCSP3/fixed").listFiles())
				exec(GraphColoringReader.class.getName() + " " + f.getAbsolutePath() + " -f=cop", "fixed");
		}

		/******/
		/* STOPPED HERE */
		/******/
		if (dirFor(LATIN_SQUARE)) {
			for (File f : new File(PATH + "seriesPapers/pesant/LatinSquare/").listFiles())
				exec(LATIN_SQUARE + " " + f.getAbsolutePath(), "gp");
			for (File f : new File(PATH + "seriesPapers/PLS-gomez/").listFiles())
				exec(LATIN_SQUARE + " " + f.getAbsolutePath(), "gs");

			cX2("benchmarks2006/bqwh/bqwh-15-106", "xcsp2", "bqwh15-106");
			cX2("benchmarks2006/bqwh/bqwh-18-141", "xcsp2", "bqwh18-141");
			// set originalNames in XCSPBuilderAbscon to true for the following series
			cX2("benchmarks2006/qcp-qwh/QCP-10", "xcsp2", "qcp10"); // eviter la construction des arrays
			cX2("benchmarks2006/qcp-qwh/QCP-15", "xcsp2", "qcp15");
			cX2("benchmarks2006/qcp-qwh/QCP-20", "xcsp2", "qcp20");
			cX2("benchmarks2006/qcp-qwh/QCP-25", "xcsp2", "qcp25");
			cX2("benchmarks2006/qcp-qwh/QWH-10", "xcsp2", "qwh10");
			cX2("benchmarks2006/qcp-qwh/QWH-15", "xcsp2", "qwh15");
			cX2("benchmarks2006/qcp-qwh/QWH-20", "xcsp2", "qwh20");
			cX2("benchmarks2006/qcp-qwh/QWH-25", "xcsp2", "qwh25");
		}
		if (dirFor(MAGIC_SQUARE)) {
			for (File f : new File(PATH + "seriesPapers/pesant/MagicSquare/").listFiles(withExtension(DAT)))
				exec(MAGIC_SQUARE + " " + f.getAbsolutePath() + " -variant=sum", "gp");
			for (int i = 3; i <= 30; i++)
				exec(MagicSquare.class.getName() + " -data=[" + i + ",-] -dataFormat=[%02d,-] -variant=sum", "sum", "s1");
			for (int i = 3; i <= 6; i++)
				exec(MagicSquare.class.getName() + " -data=[" + i + ",-] -dataFormat=[%02d,-] -variant=ext", 12000, "table", "s1");
			for (int i = 3; i <= 30; i++)
				exec(MagicSquare.class.getName() + " -data=[" + i + ",-] -dataFormat=[%02d,-] -variant=mdd", 12000, "mdd", "s1");
		}
		if (dirFor(MARKET_SPLIT)) {
			for (File f : new File(PATH + "seriesPapers/pesant/MarketSplit/").listFiles(withExtension(DAT)))
				exec(MARKET_SPLIT + " " + f.getAbsolutePath(), "gp");
		}
		if (dirFor(MULTI_KNAPSACK)) {
			cX2("benchmarks2006/mknap", "xcsp2", "s1"); // need a hard modification in the code for generating sum
														// instead of intention (in handlerCtr of Compiler)
			// for (File f : new File(PATH + "seriesPapers/pesant/MultiKnapsack/").listFiles(f -> f.getName().indexOf(".dat") != -1))
			// executeExport("problems.tran.MultiKnapsackGP " + f.getAbsolutePath(), "gp");
			// no more available ; we have to keep the generated series : replacing ma by dec ???
			for (File f : new File(PATH + "seriesPapers/pesant/MultiKnapsack/").listFiles(withExtension(DAT)))
				exec(MULTI_KNAPSACK + " " + f.getAbsolutePath(), "opt", "gp"); // opt is important here
		}
		if (dirFor(NONOGRAM)) {
			for (File f : new File(PATH + "seriesPapers/pesant/Nonograms/").listFiles(withExtension(DAT)))
				exec(NONOGRAM + " " + f.getAbsolutePath() + " -variant=table", 10000, "table", "gp");
			for (File f : new File(PATH + "seriesPapers/pesant/Nonograms/").listFiles(withExtension(DAT)))
				exec(NONOGRAM + " " + f.getAbsolutePath() + " -variant=regular ", 10000, "regular", "gp");
		}

		/******/

		if (dirFor(SAT)) {
			for (File f : new File(PATH + "sat/flat200-479").listFiles())
				exec(SAT + " " + f.getAbsolutePath() + " -variant=clause", "clause", "flat200-479");
			for (File f : new File(PATH + "sat/flat200-479").listFiles())
				exec(SAT + " " + f.getAbsolutePath() + " -variant=sum", "sum", "flat200-479");
			for (File f : new File(PATH + "sat/flat200-479").listFiles())
				exec(SAT + " " + f.getAbsolutePath() + " -variant=dual", "dual", "flat200-479");

			cX2("benchmarks2006/dimacs/aim-050", "m1", "aim050");
			cX2("benchmarks2006/dimacs/aim-100", "m1", "aim100");
			cX2("benchmarks2006/dimacs/aim-200", "m1", "aim200");
			cX2("benchmarks2006/dimacs/jnh", "m1", "jnh");
			cX2("benchmarks2006/dimacs/varDimacs", "m1", "various");

			for (File f : new File(PATH + "benchmarks2006/bmc").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath() + " nc=false", "xcsp2", "bmc");
		}
		if (dirFor(DRIVER)) // variables and constraints not in the same order ; 16384 sols for driver9
			for (File f : new File(PATH + "benchmarks2006/driver").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath());
		if (dirFor(FISCHER))
			for (File f : new File(PATH + "benchmarks2006/fischer").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath(), 10000);
		if (dirFor(HAYSTACKS))
			for (File f : new File(PATH + "benchmarks2006/haystacks").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath() + " -exai=no ");
		if (dirFor(PRIMES)) { // need a hard modification in the code for generating sum instead of intention (in handlerCtr of Compiler)
			cX2("benchmarks2006/primes/primes-10", "m1", "p10");
			cX2("benchmarks2006/primes/primes-15", "m1", "p15");
			cX2("benchmarks2006/primes/primes-20", "m1", "p20");
			cX2("benchmarks2006/primes/primes-25", "m1", "p25");
			cX2("benchmarks2006/primes/primes-30", "m1", "p30");
		}
		if (dirFor(COSTAS_ARRAY)) {
			cX2("XCSP2/costasArray", "m1", "s1");
		}
		if (dirFor(PIGEONS_PLUS)) {
			for (File f : new File(PATH + "seriesPapers/pigeonsPlus/xml").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath(), 12000);
		}
		if (dirFor(SCHEDULING)) {
			for (File f : new File(PATH + "scheduling/sadeh/instances").listFiles())
				exec(SchedulingJSReader.Sadeh.class.getName() + " " + f.getAbsolutePath(), "js", "sadeh");
			for (File f : new File(PATH + "scheduling/taillard/fs").listFiles())
				if (!f.getName().equals("fs-500-20.txt"))
					for (int i = 0; i < 10; i++)
						exec(SchedulingFSReader.class.getName() + " " + f.getAbsolutePath() + " " + i, "fs", "taillard");
			for (File f : new File(PATH + "scheduling/taillard/js").listFiles())
				for (int i = 0; i < 10; i++)
					exec(SchedulingJSReader.Taillard.class.getName() + " " + f.getAbsolutePath() + " " + i, "js", "taillard");
			for (File f : new File(PATH + "scheduling/taillard/os").listFiles())
				for (int i = 0; i < 10; i++)
					exec(SchedulingOSReader.Taillard.class.getName() + " " + f.getAbsolutePath() + " " + i, "os", "taillard");

			// for (File f : new File(PATH + "cabinet").listFiles())
			// executeExport(XCSP2 + " " + f.getAbsolutePath(), "xcsp2", "cabinet"); // Need special code in InstanceBuilder3 ;
			// see before Sept 2016
			for (File f : new File(PATH + "scheduling/openShop/os-gp/xcsp2/os-gp").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath(), "xcsp2", "os-gp");
			for (File f : new File(PATH + "scheduling/tamura/cjss").listFiles())
				exec(XCSP2 + " " + f.getAbsolutePath(), "xcsp2", "cjss");

		}
		if (dirFor(PSEUDO_BOOLEAN)) {
			Stringx3Consumer cPB = (dir, variant, series) -> {
				boolean cop = variant.equals("opt");
				for (File f : new File(PATH + "PB-RECUP/" + dir).listFiles())
					exec(PSEUDO_BOOLEAN + " " + f.getAbsolutePath() + (cop ? " -f=cop" : ""), 1200, variant, series);
			};
			cPB.accept("06-sat-small/armies", "dec", "armies");
			cPB.accept("06-sat-small/FPGA_SAT05", "dec", "fpga");
			cPB.accept("06-sat-small/robin", "dec", "robin");
			cPB.accept("06-sat-small/roussel", "dec", "pigeon");
			cPB.accept("06-sat-small/tsp", "dec", "tsp");
			cPB.accept("06-sat-small/wnqueen", "dec", "queen");
			cPB.accept("12-dec-small/ShortestPathBA", "dec", "spba");
			cPB.accept("12-dec-small/ShortestPathNG", "dec", "spng");
			cPB.accept("12-dec-small/ShortestPathTate", "dec", "sptate");
			cPB.accept("06-opt-small/bounded_golomb_rulers", "opt", "bgr");
			cPB.accept("06-opt-small/domset", "opt", "domset");
			cPB.accept("06-opt-small/factor", "opt", "factor");
			cPB.accept("06-opt-small/frb", "opt", "frb");
			cPB.accept("06-opt-small/garden", "opt", "garden");
			cPB.accept("06-opt-small/golomb-rulers", "opt", "gr");
			cPB.accept("06-opt-small/haplotype", "opt", "haplotype"); // very long
			cPB.accept("06-opt-small/logic-synthesis", "opt", "logic-synthesis");
			cPB.accept("06-opt-small/market-split", "opt", "market-split");
			cPB.accept("06-opt-small/miplib", "opt", "mps");
			cPB.accept("06-opt-small/primes-dimacs-cnf", "opt", "dimacs");
			cPB.accept("06-opt-small/radar", "opt", "radar");
			cPB.accept("06-opt-small/routing", "opt", "routing");
			cPB.accept("06-opt-small/vtxcov", "opt", "vtxcov");
			cPB.accept("06-opt-small/ttp", "opt", "ttp");
			cPB.accept("06-opt-small/wnq", "opt", "wnq");
			cPB.accept("09-opt-small/featureSubscription", "opt", "fs");
			cPB.accept("09-opt-small/flexray", "opt", "fx");
			cPB.accept("06-sat-small/dbst", "dec", "dbst"); // very long
		}

		/******** Series for September 2016 in abssol/news **/
		// see LatinSquare QCP QWH as NEW SERIES from xcsp2, cabinet in scheduling, bmc in sat, bibd2,

		if (dirFor(SUPER_SOLUTIONS)) {
			cX2("XCSP2/superSolutions/SuperQueens", "Queens", "s1");
			cX2("XCSP2/superSolutions/SuperSadeh", "Sadeh", "js");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-os-04", "Taillard", "os04");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-os-05", "Taillard", "os05");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-os-07", "Taillard", "os07");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-os-10", "Taillard", "os10");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-os-15", "Taillard", "os15");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-os-20", "Taillard", "os20");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-js-15", "Taillard", "js15");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-js-20", "Taillard", "js20");
			cX2("XCSP2/superSolutions/SuperTaillard/SuperTaillard-js-20-15", "Taillard", "js20-15");
		}
		if (dirFor(QUASI_GROUP)) {
			Consumer<Integer> c = v -> {
				for (int i = 4; i <= 40; i++)
					exec(QUASI_GROUP + " -data=" + i + " -variant=v" + v + " -dataFormat=%02d", "elt", "qg" + v);
			};
			c.accept(3);
			c.accept(4);
			c.accept(5);
			c.accept(7);
		}
		if (dirFor(BIN_PACKING)) {
			BiConsumer<String, String> c = (s1, s2) -> {
				for (File f : new File(PATH + "binPacking/" + s1 + "/" + s2).listFiles())
					exec(BIN_PACKING + " " + f.getAbsolutePath() + " -variant=tab -f=cop", 12000, "tab", s2);
				for (File f : new File(PATH + "binPacking/" + s1 + "/" + s2).listFiles())
					exec(BIN_PACKING + " " + f.getAbsolutePath() + " -variant=mdd -f=cop", 12000, "mdd", s2);
				for (File f : new File(PATH + "binPacking/" + s1 + "/" + s2).listFiles())
					exec(BIN_PACKING + " " + f.getAbsolutePath() + " -variant=sum -f=cop", 12000, "sum", s2);
			};
			c.accept("Falkenauer", "ft"); // ok for 3 variants
			c.accept("Falkenauer", "fu"); // ok for 3 variants
			c.accept("Scholl", "skj1"); // for the moment, only variant 3
			c.accept("Scholl", "skj2"); // for the moment, only variant 3
			c.accept("Scholl", "skj3"); // for the moment, only variant 3
			c.accept("Wascher", "wg"); // bincapacity = 10000 (too large for variant1 and variant2)
			c.accept("Schwerin", "sw100"); // ok for 3 variants (compression in a second phase for the two first variants)
			c.accept("Schwerin", "sw120"); // ok for 3 variants (compression in a second phase for the two first variants)
			c.accept("Schoenfield", "s28"); // only variant 3
			// c.accept("Delorme", "dai"); // Pb memory even for variant 3
			// c.accept("Delorme", "dani"); // Pb memory even for variant 3
			// c.accept("Delorme", "dr"); // random instances ; too many of them
		}

		if (dirFor(MAX_CSP)) {
			BiConsumer<String, String> c = (s1, s2) -> {
				for (File f : new File(PATH + "MaxCSP/" + s1 + (s2.length() > 0 ? "/" + s2 : "")).listFiles())
					exec(XCSP2 + " " + f.getAbsolutePath(), s1, s2.length() > 0 ? s2 : "s1");
			};
			c.accept("cnf", "s2-40");
			c.accept("cnf", "s2-80");
			c.accept("cnf", "s3-40");
			c.accept("cnf", "s3-80");
			c.accept("kbtree", "s5-2");
			c.accept("kbtree", "s9-2");
			c.accept("kbtree", "s9-5");
			c.accept("kbtree", "s9-7");
			c.accept("maxclique", "");
			c.accept("maxcut", "s30");
			c.accept("maxcut", "s40");
			c.accept("maxcut", "s50");
			c.accept("maxcut", "s60");
			c.accept("pedigree", "");
			c.accept("Pi", "s20-10-20-t60");
			c.accept("Pi", "s20-10-20-t70");
			c.accept("Pi", "s30-10-25-t48");
			c.accept("Pi", "s30-10-25-t58");
			c.accept("Pi", "s40-10-08-t60");
			c.accept("planning", "");
			// supprimer MaxCSP-depot01c.xml.lzma MaxCSP-driverlog02c.xml.lzma MaxCSP-driverlog02c.xml.lzma MaxCSP-driverlog05c.xml.lzma
			// MaxCSP-driverlog08c.xml.lzma MaxCSP-logistics01c.xml.lzma MaxCSP-mprime01c.xml.lzma MaxCSP-mprime03c.xml.lzma
			// MaxCSP-mprime04c.xml.lzma MaxCSP-rovers02c.xml.lzma MaxCSP-satellite01c.xml.lzma MaxCSP-zenotravel02c.xml.lzma
			c.accept("random", "completeLoose");
			c.accept("random", "completeTight");
			c.accept("random", "denseLoose");
			c.accept("random", "denseTight");
			c.accept("random", "sparseLoose");
			c.accept("random", "sparseTight");
			c.accept("rlfap", "");
			c.accept("spot5", "");
			c.accept("warehouses", "");
		}
		if (dirFor(MIXED)) {
			cX2("benchmarks2006/nengfa", "xcsp2", "nengfa");
			cX2("benchmarks2006/cril", "xcsp2", "cril");
		}

		if (dirFor(VRP))
			cZn("vrp", VRP);
		if (dirFor(CUTSTOCK))
			cZn("cutstock", CUTSTOCK);
		if (dirFor(TPP))
			cZn("tpp", TPP);
		if (dirFor(MARIO))
			cZn("mario", MARIO);

		if (dirFor(STILL_LIFE)) {
			for (int i = 3; i <= 15; i++)
				for (int j = i; j <= 15; j++)
					exec(STILL_LIFE + " -data=[" + i + "," + j + "] -dataFormat=[%02d,%02d] -f=cop ", "m1", "s1");
			for (int i = 3; i <= 50; i++)
				exec(STILL_LIFE + " -data=[" + i + "," + i + "] -dataFormat=[%02d,-] -variant=wastage -f=cop ", "wst", "s1");
		}
		if (dirFor(OPD)) {
			String suffix = " -dataFormat=[%02d,%03d,%03d] -variant=sum -f=cop"; // variant -sca : bof
			for (int[] t : new int[][] { { 10, 8, 3 }, { 9, 8, 3 }, { 8, 8, 3 }, { 9, 37, 12 }, { 10, 15, 6 }, { 10, 25, 8 }, { 10, 37, 14 }, { 10, 38, 10 }, { 7, 7, 3 }, { 8, 14, 7 }, { 9, 18, 8 }, { 9, 24, 8 }, { 10, 30, 9 }, { 10, 33, 15 }, { 19, 20, 9 }, { 15, 21, 7 }, { 15, 21, 7 }, { 19, 19, 9 }, { 25, 25, 9 }, { 7, 13, 6 }, { 11, 11, 5 }, { 15, 15, 4 }, { 16, 8, 3 }, { 10, 38, 28 }, { 10, 31, 22 }, { 10, 26, 4 }, { 10, 27, 8 }, { 10, 32, 9 }, { 10, 31, 9 }, { 10, 30, 9 }, { 10, 30, 10 }, { 10, 9, 1 }, { 10, 20, 1 }, { 11, 22, 10 }, { 13, 26, 6 } })
				exec(OPD + " -data=[" + t[0] + "," + t[1] + "," + t[2] + "] " + suffix, "sum", "small");
			// 9-35-10 removed from small as it is present in large
			for (int i : vals(rangeC(2, 17), 22, 29, 46, 99))
				exec(OPD + " -data=[" + i + ",350,100] " + suffix, "sum", "large");
			for (int i : vals(rangeC(2, 17), 22, 29, 46, 99))
				exec(OPD + " -data=[" + i + ",35,10] " + suffix, "sum", "large");
			for (int[] t : new int[][] { { 9, 300, 100 }, { 10, 325, 100 }, { 10, 360, 120 }, { 15, 350, 100 }, { 10, 100, 30 } })
				exec(OPD + " -data=[" + t[0] + "," + t[1] + "," + t[2] + "] " + suffix, "sum", "large");
		}
		if (dirFor(PRIZE_COLLECTING)) {
			for (File f : new File(PATH_MINI + "prize-collecting").listFiles(withExtension(DZN)))
				exec(PRIZE_COLLECTING + " " + f.getAbsolutePath(), "jok", "s1");
		}
		if (dirFor(BUS_SCHEDULING)) {
			for (File f : new File(PATH_MINI + "bus_scheduling").listFiles(withExtension(DZN)))
				execVariant(BUS_SCHEDULING + " " + f.getAbsolutePath(), "cnt", 12000);
		}
		if (dirFor(FASTFOOD)) {
			for (File f : new File(PATH_MINI + "fast-food").listFiles(withExtension(DZN)))
				exec(FASTFOOD + " " + f.getAbsolutePath(), "m1", "s1");
		}

		// ************************************************************************
		// ***** Series for January 2017 in series3rdPass
		// ************************************************************************

		if (dirFor(PROP_STRESS)) {
			for (int i : vals(rangeC(20, 100, 20), rangeC(150, 700, 50))) // TODO memory problem from 700
				exec(PROP_STRESS + " -data=" + i + " -dataFormat=%04d", 12000, "m1", "s1");
		}
		if (dirFor(WWTPP)) {
			for (File f : new File(PATH_MINI + "wwtpp-real").listFiles(withExtension(DZN))) {
				execVariant(WWTPP + " " + f.getAbsolutePath(), "ord");
				// executeExportModel(WWTPP + " " + f.getAbsolutePath(), "jok");
				// executeExportModel(WWTPP + " " + f.getAbsolutePath(), "smt");
			}
		}
		if (dirFor(OPEN_STACKS)) {
			// gp-100-1.dzn OUT of memory error
			for (File f : new File(PATH_MINI + "open_stacks").listFiles(f -> f.getName().endsWith(DZN) && !f.getName().equals("gp-100-1.dzn"))) {
				execVariant(OPEN_STACKS + " " + f.getAbsolutePath(), "m1", 12000);
				// execModel(OPEN_STACKS + " " + f.getAbsolutePath(), "m1c", 12000);
				execVariant(OPEN_STACKS + " " + f.getAbsolutePath(), "m2", 12000);
				// execModel(OPEN_STACKS + " " + f.getAbsolutePath(), "m2c", 12000);
			}
		}
		if (dirFor(RACK)) {
			for (File f : new File(PATH + "Rack").listFiles(withExtension(JSON)))
				exec(RACK + " -data=" + f.getAbsolutePath());
		}
		if (dirFor(COVERING_ARRAY)) {
			for (int[] t : new int[][] { { 4, 9 }, { 5, 10 }, { 6, 12 }, { 7, 12 }, { 8, 12 }, { 9, 12 }, { 10, 12 }, { 11, 12 } }) {
				exec(COVERING_ARRAY + " -data=[3," + t[0] + ",2," + (t[1] - 1) + "] -dataFormat=[%01d,%02d,%01d,%02d] ", "dec", "s1");
				exec(COVERING_ARRAY + " -data=[3," + t[0] + ",2," + t[1] + "] -dataFormat=[%01d,%02d,%01d,%02d] ", "dec", "s1");
				// two series with constraint element generated for 2017 competition by commenting out a few statements in Method
				// channel(Var[] list1, int startIndex1, Var[] list2, int startIndex2) of class Problem (let used in names of dirs/files)
			}
		}
		if (dirFor(DE_BRUIJN)) {
			for (int b = 2; b <= 5; b++)
				for (int n = b; n < 10; n++)
					exec(DE_BRUIJN + " -data=[" + b + "," + n + "] -dataFormat=[%02d,%02d]", 12000, "m1", "s1");
		}
		if (dirFor(DIAMOND_FREE)) {
			for (int i : vals(rangeC(4, 40), rangeC(45, 100, 5)))
				exec(DIAMOND_FREE + " -data=" + i + " -dataFormat=%03d", 12000, "m1", "s1");
		}
		if (dirFor(MAGIC_HEXAGON)) {
			for (int[] t : new int[][] { { 2, -3 }, { 2, 0 }, { 2, 3 }, { 3, -29 }, { 3, -24 }, { 3, -19 }, { 3, -14 }, { 3, -9 }, { 3, -4 }, { 3, 1 }, { 3, 6 }, { 3, 11 }, { 3, 16 }, { 3, 21 }, { 3, 26 }, { 4, -60 }, { 4, -53 }, { 4, -46 }, { 4, -39 }, { 4, -32 }, { 4, -25 }, { 4, -18 }, { 4, -11 }, { 4, -4 }, { 4, 3 }, { 4, 10 }, { 4, 17 }, { 4, 24 }, { 5, -93 }, { 5, -84 }, { 5, -75 }, { 5, -66 }, { 5, -57 }, { 5, -48 }, { 5, -39 }, { 5, -30 }, { 5, -21 }, { 5, -12 }, { 5, -3 }, { 5, 6 }, { 5, 15 }, { 5, 24 }, { 5, 33 }, { 6, -155 }, { 6, -144 }, { 6, -133 }, { 6, -122 }, { 6, -111 }, { 6, -100 }, { 6, -89 }, { 6, -78 }, { 6, -67 }, { 6, -56 }, { 6, -45 }, { 6, -34 }, { 6, -23 }, { 6, -12 }, { 6, -1 }, { 6, 10 }, { 6, 21 }, { 6, 32 }, { 6, 43 }, { 6, 54 }, { 7, -193 }, { 7, -180 }, { 7, -167 }, { 7, -154 }, { 7, -141 }, { 7, -128 }, { 7, -115 }, { 7, -102 }, { 7, -89 }, { 7, -76 }, { 7, -63 }, { 7, -50 }, { 7, -37 }, { 7, -24 }, { 7, -11 }, { 7, 2 }, { 7, 15 }, { 7, 28 }, { 7, 41 }, { 7, 54 }, { 7, 67 }, { 7, 80 }, { 8, -189 }, { 8, -174 }, { 8, -159 }, { 8, -144 }, { 8, -129 }, { 8, -114 }, { 8, -99 }, { 8, -84 }, { 8, -69 }, { 8, -54 }, { 8, -39 }, { 8, -24 }, { 8, -9 }, { 8, 6 }, { 8, 21 }, { 8, 36 }, { 8, 51 }, { 8, 66 }, { 8, 81 }, { 8, 96 }, { 9, -193 }, { 9, -176 }, { 9, -159 }, { 9, -142 }, { 9, -125 }, { 9, -108 }, { 9, -91 }, { 9, -74 }, { 9, -57 }, { 9, -40 }, { 9, -23 }, { 9, -6 }, { 9, 11 }, { 9, 28 }, { 9, 45 }, { 9, 62 }, { 9, 79 }, { 9, 96 }, { 9, 113 }, { 9, 130 }, { 10, -192 }, { 10, -173 }, { 10, -154 }, { 10, -135 }, { 10, -116 }, { 10, -97 }, { 10, -78 }, { 10, -59 }, { 10, -40 }, { 10, -21 }, { 10, -2 }, { 10, 17 }, { 10, 36 }, { 10, 55 }, { 10, 74 }, { 10, 93 }, { 10, 112 }, { 10, 131 }, { 10, 150 }, { 10, 169 }, { 11, -186 }, { 11, -165 }, { 11, -144 }, { 11, -123 }, { 11, -102 }, { 11, -81 }, { 11, -60 }, { 11, -39 }, { 11, -18 }, { 11, 3 }, { 11, 24 }, { 11, 45 }, { 11, 66 }, { 11, 87 }, { 11, 108 }, { 11, 129 }, { 11, 150 }, { 11, 171 }, { 11, 192 }, { 12, -198 }, { 12, -175 }, { 12, -152 }, { 12, -129 }, { 12, -106 }, { 12, -83 }, { 12, -60 }, { 12, -37 }, { 12, -14 }, { 12, 9 }, { 12, 32 }, { 12, 55 }, { 12, 78 }, { 12, 101 }, { 12, 124 }, { 12, 147 }, { 12, 170 }, { 12, 193 } })
				exec(MAGIC_HEXAGON + " -data=[" + t[0] + "," + t[1] + "] -dataFormat=[%02d,%04d]", 12000, "m1", "s1");
		}
		if (dirFor(NUMBER_PARTITIONING)) {
			for (int i : vals(rangeC(4, 12, 2), rangeC(16, 200, 4)))
				exec(NUMBER_PARTITIONING + " -data=" + i + " -dataFormat=%03d", 12000, "m1", "s1");
		}

		// ************************************************************************
		// ***** Series of April 2018
		// ************************************************************************

		if (dirFor(AUCTION)) {
			exec(AUCTION + " " + PATH + "auction/example.txt -variant=cnt");
			exec(AUCTION + " " + PATH + "auction/example.txt -variant=sum");
			BiConsumer<String, String> c = (variant, series) -> Stream.of(new File(PATH + "auction/" + series).listFiles())
					.forEach(f -> execVariant(AUCTION + " " + f.getAbsolutePath(), variant, series));
			c.accept("cnt", "cast");
			c.accept("cnt", "sand");
			c.accept("cnt", "groupes");
			c.accept("sum", "cast");
			c.accept("sum", "sand");
			c.accept("sum", "groupes");
		}
		if (dirFor(BACP)) {
			for (File f : new File(PATH + "bacp/dataCompet2018").listFiles())
				execVariant(BACP + " -data=" + f.getAbsolutePath(), "m1");
			for (File f : new File(PATH + "bacp/dataCompet2018").listFiles())
				execVariant(BACP + " -data=" + f.getAbsolutePath(), "m2");
			for (File f : new File(PATH_MINI + "bacp").listFiles(withExtension(MZN)))
				execVariant(Bacp_ParserZ.class.getName() + " " + f.getAbsolutePath(), "m1", "zn");
			for (File f : new File(PATH_MINI + "bacp").listFiles(withExtension(MZN)))
				execVariant(Bacp_ParserZ.class.getName() + " " + f.getAbsolutePath(), "m2", "zn");
			for (File f : new File(PATH + "bacp/ps/instances12").listFiles())
				execVariant(Bacp_Parser.class.getName() + " " + f.getAbsolutePath(), "m1d", "ps");
			for (File f : new File(PATH + "bacp/ps/instances12").listFiles())
				execVariant(Bacp_Parser.class.getName() + " " + f.getAbsolutePath(), "m2d", "ps");
		}
		if (dirFor(BATTLESHIP)) {
			for (int i = 0; i < 303; i++)
				exec(SolitaireBattleshipReader.class.getName() + " " + PATH + "solitaireBattleship/battleship_instances.pl" + " " + i);
			for (File f : new File(PATH + "solitaireBattleship/sb_MiniZinc_Benchmarks").listFiles())
				exec(SolitaireBattleshipReaderZ.class.getName() + " " + f.getAbsolutePath(), "m1", "zinc");
		}
		if (dirFor(ETERNITY)) {
			for (File f : new File(PATH + "eternity/eternityOscar/brendan").listFiles())
				exec(ETERNITY + " " + f.getAbsolutePath());
		}

		if (dirFor(FAPP)) {
			for (File f : new File(PATH + "fapp/allInstances").listFiles())
				exec(FappReader.class.getName() + " " + f.getAbsolutePath() + " -variant=short -positive=v -f=cop", 12000);
		}

		if (dirFor(MISTERY_SHOPPER)) {
			for (File f : new File(PATH + "misteryShopper/dataCompet2018").listFiles())
				exec(MISTERY_SHOPPER + " -data=" + f.getAbsolutePath());
		}
		if (dirFor(NURSE_ROSTERING)) {
			for (File f : new File(PATH + "nurseRostering/24Instances").listFiles())
				exec(NURSE_ROSTERING + " " + f.getAbsolutePath(), 12000);
		}
		if (dirFor(PEACABLE_ARMIES)) {
			for (int i : vals(rangeC(2, 30)))
				execVariant(PEACABLE_ARMIES + " -data=" + i + " -dataFormat=%02d", "m1");
			for (int i : vals(rangeC(2, 30)))
				execVariant(PEACABLE_ARMIES + " -data=" + i + " -dataFormat=%02d", "m2");
		}
		if (dirFor(PIGEONS)) {
			for (int i : vals(rangeC(4, 20), rangeC(25, 50, 5), rangeC(60, 100, 10)))
				execVariant(PIGEONS + " -data=" + i + " -dataFormat=%03d", "int", 12000);
			for (int i : vals(rangeC(4, 20), rangeC(25, 50, 5), rangeC(60, 100, 10)))
				execVariant(PIGEONS + " -data=" + i + " -dataFormat=%03d", "glb", 12000);
		}
		if (dirFor(PIZZA_VOUCHER)) {
			for (File f : new File(PATH + "pizzaVoucher/data").listFiles())
				exec(PIZZA_VOUCHER + " -data=" + f.getAbsolutePath());

		}

		if (dirFor(RLFAP)) {
			for (int i : vals(5))
				exec(RlfapReader.class.getName() + " " + PATH + "rlfap 0 " + i + " -variant=span");
			for (int i : vals(1, 2, 3, 4, 11))
				exec(RlfapReader.class.getName() + " " + PATH + "rlfap 0 " + i + " -variant=card");
			for (int i : vals(6, 7, 8, 9, 10))
				exec(RlfapReader.class.getName() + " " + PATH + "rlfap 0 " + i + " -variant=max");
			for (int i : vals(3, 4, 10))
				exec(RlfapReader.class.getName() + " " + PATH + "rlfap 1 " + i + " -variant=span");
			for (int i : vals(1, 2, 8, 9, 14))
				exec(RlfapReader.class.getName() + " " + PATH + "rlfap 1 " + i + " -variant=card");
			for (int i : vals(5, 6, 7, 11, 12, 13))
				exec(RlfapReader.class.getName() + " " + PATH + "rlfap 1 " + i + " -variant=max");
		}

		if (dirFor(TAL)) {
			for (String s : new String[] { "7 15-11-13-9-1-11-7-4", "7 9-10-12-13-4-16-8", "9 14-13-2", "9 15-11-13-9-10-12", "9 15-5-3-12-10-3-4-11-2-10-3-11-3", "9 15-5-3-12-10-3-4-11-2-10-3", "9 27-35-38-22-15-13-26-28", "9 9-10-12-13-13-9-16-10-15-9-12", "9 9-13-13-10-16-12-15-9-12", "9 9-13-13-16-10-12-9-15-9-12" })
				exec(TAL + " " + PATH + "tal/compiler2solver/fr.observed.tuples " + s + " -1 -f=cop", 1200);
		}
		// TODO pseudo-booleans (quelque series) timetabling tdsp worddesign lineararrangementcop photo

		if (dirFor(BAUDOUIN)) {
			// for (int n = 4; n <= 7; n++)
			// for (int d = 2; d <= 8; d++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + "," + d + "] -variant=element -s4b", 12000, "element");
			// for (int n = 8; n <= 12; n++)
			// for (int d = 2; d <= 3; d++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + "," + d + "] -variant=element -s4b", 12000, "element");
			// for (int n = 3; n <= 5; n++)
			// for (int d = 2; d <= 6; d++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + "," + d + "] -variant=lex -s4b", 12000, "lex");
			// for (int n = 3; n <= 10; n++)
			// for (int d = 2; d <= 6; d++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + "," + d + "] -variant=max -s4b", 12000, "max");
			// for (int n = 3; n <= 10; n++)
			// for (int d = 2; d <= 6; d++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + "," + d + "] -variant=notall -s4b", 12000, "notall");
			// for (int n = 4; n <= 10; n++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + ",4] -variant=atmost1 -s4b", 12000, "atmost1");
			// for (int n = 4; n <= 18; n++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + ",3] -variant=atmost1 -s4b", 12000, "atmost1");
			// for (int n = 4; n <= 8; n++)
			// executeExport(TestSmart.class.getName() + " -data=[" + n + ",3] -variant=distinctv -s4b", 12000, "distinctv");
			for (int n = 4; n <= 7; n++)
				exec(TestSmart.class.getName() + " -data=[" + n + ",4] -variant=distinctv -s4b", 12000, "distinctv");

		}

		System.out.println("Nb bad commands = " + badCommands.size());
		badCommands.stream().forEach(s -> System.out.println("\t" + s));
	}

	private static boolean dirFor(String name) {
		// System.out.println("name=" + name);
		name = name.indexOf(".") != -1 ? name.substring(name.lastIndexOf(".") + 1) : name;
		int pos = name.indexOf("_");
		if (pos != -1)
			name = name.substring(0, pos); // because by convention this is a suffix to be removed (e.g., Random or Parser)
		if (serieName.equals(ALL) || serieName.equals(name.toLowerCase())) {
			dir = new File(mainDir, name.startsWith("X2_") ? name.substring(3) : name);
			dir.mkdir(); //
			return true;
		}
		return false;
	}

	static class Perfect {
		/**
		 * The following table contains all the data for all problem instances from [bouwkamp_duijvestijn_92]. The first number denotes the size of
		 * the master square and the list that follows it the square sizes. The problem number corresponds to the page number in
		 * [bouwkamp_duijvestijn_92]. Problems 166 and 167, 168 and 169, 182 and 183 are identical, but have two non-isomorphic solutions.
		 */
		public static int[][] t = { { 112, 2, 4, 6, 7, 8, 9, 11, 15, 16, 17, 18, 19, 24, 25, 27, 29, 33, 35, 37, 42, 50 }, { 110, 2, 3, 4, 6, 7, 8, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 26, 27, 28, 50, 60 }, { 110, 1, 2, 3, 4, 6, 8, 9, 12, 14, 16, 17, 18, 19, 21, 22, 23, 24, 26, 27, 28, 50, 60 }, { 139, 1, 2, 3, 4, 7, 8, 10, 17, 18, 20, 21, 22, 24, 27, 28, 29, 30, 31, 32, 38, 59, 80 }, { 147, 1, 3, 4, 5, 8, 9, 17, 20, 21, 23, 25, 26, 29, 31, 32, 40, 43, 44, 47, 48, 52, 55 }, { 147, 2, 4, 8, 10, 11, 12, 15, 19, 21, 22, 23, 25, 26, 32, 34, 37, 41, 43, 45, 47, 55, 59 }, { 154, 2, 5, 9, 11, 16, 17, 19, 21, 22, 24, 26, 30, 31, 33, 35, 36, 41, 46, 47, 50, 52, 61 }, { 172, 1, 2, 3, 4, 9, 11, 13, 16, 17, 18, 19, 22, 24, 33, 36, 38, 39, 42, 44, 53, 75, 97 }, { 192, 4, 8, 9, 10, 12, 14, 17, 19, 26, 28, 31, 35, 36, 37, 41, 47, 49, 57, 59, 62, 71, 86 }, { 110, 1, 2, 3, 4, 5, 7, 8, 10, 12, 13, 14, 15, 16, 19, 21, 28, 29, 31, 32, 37, 38, 41, 44 }, { 139, 1, 2, 7, 8, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 24, 26, 27, 28, 32, 33, 38, 59, 80 }, { 140, 1, 2, 3, 4, 5, 8, 10, 13, 16, 19, 20, 23, 27, 28, 29, 31, 33, 38, 42, 45, 48, 53, 54 }, { 140, 2, 3, 4, 7, 8, 9, 12, 15, 16, 18, 22, 23, 24, 26, 28, 30, 33, 36, 43, 44, 47, 50, 60 }, { 145, 1, 2, 3, 4, 6, 8, 9, 12, 15, 20, 22, 24, 25, 26, 27, 29, 30, 31, 32, 34, 36, 61, 84 }, { 180, 2, 4, 8, 10, 11, 12, 15, 19, 21, 22, 23, 25, 26, 32, 33, 34, 37, 41, 43, 45, 47, 88, 92 }, { 188, 2, 4, 8, 10, 11, 12, 15, 19, 21, 22, 23, 25, 26, 32, 33, 34, 37, 45, 47, 49, 51, 92, 96 }, { 208, 1, 3, 4, 9, 10, 11, 12, 16, 17, 18, 22, 23, 24, 40, 41, 60, 62, 65, 67, 70, 71, 73, 75 }, { 215, 1, 3, 4, 9, 10, 11, 12, 16, 17, 18, 22, 23, 24, 40, 41, 60, 66, 68, 70, 71, 74, 76, 79 }, { 228, 2, 7, 9, 10, 15, 16, 17, 18, 22, 23, 25, 28, 36, 39, 42, 56, 57, 68, 69, 72, 73, 87, 99 }, { 257, 2, 3, 9, 11, 14, 15, 17, 20, 22, 24, 28, 29, 32, 33, 49, 55, 57, 60, 63, 66, 79, 123, 134 }, { 332, 1, 15, 17, 24, 26, 30, 31, 38, 47, 48, 49, 50, 53, 56, 58, 68, 83, 89, 91, 112, 120, 123, 129 }, { 120, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 19, 20, 23, 25, 32, 33, 34, 40, 41, 46, 47 }, { 186, 2, 3, 4, 7, 8, 9, 12, 15, 16, 18, 22, 23, 24, 26, 28, 30, 33, 36, 43, 46, 47, 60, 90, 96 }, { 194, 2, 3, 7, 9, 10, 16, 17, 18, 19, 20, 23, 25, 28, 34, 36, 37, 42, 53, 54, 61, 65, 68, 69, 72 }, { 195, 2, 4, 7, 10, 11, 16, 17, 18, 21, 26, 27, 30, 39, 41, 42, 45, 47, 49, 52, 53, 54, 61, 63, 80 }, { 196, 1, 2, 5, 10, 11, 15, 17, 18, 20, 21, 24, 26, 29, 31, 32, 34, 36, 40, 44, 47, 48, 51, 91, 105 }, { 201, 1, 3, 4, 6, 9, 10, 11, 12, 17, 18, 20, 21, 22, 23, 26, 38, 40, 46, 50, 52, 53, 58, 98, 103 }, { 201, 1, 4, 5, 8, 9, 10, 11, 15, 16, 18, 19, 20, 22, 24, 26, 39, 42, 44, 49, 52, 54, 56, 93, 108 }, { 203, 1, 2, 5, 10, 11, 15, 17, 18, 20, 21, 24, 26, 29, 31, 32, 34, 36, 40, 44, 48, 54, 58, 98, 105 }, { 247, 3, 5, 6, 9, 12, 14, 19, 23, 24, 25, 28, 32, 34, 36, 40, 45, 46, 48, 56, 62, 63, 66, 111, 136 }, { 253, 2, 4, 5, 9, 13, 18, 20, 23, 24, 27, 28, 31, 38, 40, 44, 50, 61, 70, 72, 77, 79, 86, 88, 104 }, { 255, 3, 5, 10, 11, 16, 17, 20, 22, 23, 25, 26, 27, 28, 32, 41, 44, 52, 53, 59, 63, 65, 74, 118, 137 }, { 288, 2, 7, 9, 10, 15, 16, 17, 18, 22, 23, 25, 28, 36, 39, 42, 56, 57, 60, 68, 72, 73, 87, 129, 159 }, { 288, 1, 5, 7, 8, 9, 14, 17, 20, 21, 26, 30, 32, 34, 36, 48, 51, 54, 59, 64, 69, 72, 93, 123, 165 }, { 290, 2, 3, 8, 9, 11, 12, 14, 17, 21, 30, 31, 33, 40, 42, 45, 48, 59, 61, 63, 65, 82, 84, 124, 166 }, { 292, 1, 2, 3, 8, 12, 15, 16, 17, 20, 22, 24, 26, 29, 33, 44, 54, 57, 60, 63, 67, 73, 102, 117, 175 }, { 304, 3, 5, 7, 11, 12, 17, 20, 22, 25, 29, 35, 47, 48, 55, 56, 57, 69, 72, 76, 92, 96, 100, 116, 132 }, { 304, 3, 4, 7, 12, 16, 20, 23, 24, 27, 28, 30, 32, 33, 36, 37, 44, 53, 57, 72, 76, 85, 99, 129, 175 }, { 314, 2, 4, 11, 12, 16, 17, 18, 19, 28, 29, 40, 44, 47, 59, 62, 64, 65, 78, 79, 96, 97, 105, 113, 139 }, { 316, 3, 9, 10, 12, 13, 14, 15, 23, 24, 33, 36, 37, 48, 52, 54, 55, 57, 65, 66, 78, 79, 93, 144, 172 }, { 326, 1, 6, 10, 11, 14, 15, 18, 24, 29, 32, 43, 44, 53, 56, 63, 65, 71, 80, 83, 101, 104, 106, 119, 142 }, { 423, 2, 9, 15, 17, 27, 29, 31, 32, 33, 36, 47, 49, 50, 60, 62, 77, 105, 114, 123, 127, 128, 132, 168, 186 }, { 435, 1, 2, 8, 10, 13, 19, 23, 33, 44, 45, 56, 74, 76, 78, 80, 88, 93, 100, 112, 131, 142, 143, 150, 192 }, { 435, 3, 5, 9, 11, 12, 21, 24, 27, 30, 44, 45, 50, 54, 55, 63, 95, 101, 112, 117, 123, 134, 140, 178, 200 }, { 459, 8, 9, 10, 11, 16, 30, 36, 38, 45, 55, 57, 65, 68, 84, 95, 98, 100, 116, 117, 126, 135, 144, 180, 198 }, { 459, 4, 6, 9, 10, 17, 21, 23, 25, 31, 33, 36, 38, 45, 50, 83, 115, 117, 126, 133, 135, 144, 146, 180, 198 }, { 479, 5, 6, 17, 23, 24, 26, 28, 29, 35, 43, 44, 52, 60, 68, 77, 86, 130, 140, 150, 155, 160, 164, 174, 175 }, { 147, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 17, 19, 20, 23, 25, 27, 32, 33, 34, 40, 41, 73, 74 }, { 208, 1, 2, 3, 4, 5, 7, 8, 11, 12, 17, 18, 24, 26, 28, 29, 30, 36, 39, 44, 45, 50, 59, 60, 89, 119 }, { 213, 3, 5, 6, 7, 13, 16, 17, 20, 21, 23, 24, 25, 26, 28, 31, 35, 36, 47, 49, 56, 58, 74, 76, 81, 90 }, { 215, 1, 4, 6, 7, 11, 15, 24, 26, 27, 33, 37, 39, 40, 41, 42, 43, 45, 47, 51, 55, 60, 62, 63, 69, 83 }, { 216, 1, 2, 3, 4, 5, 7, 8, 11, 16, 17, 18, 19, 25, 30, 32, 33, 39, 41, 45, 49, 54, 59, 64, 103, 113 }, { 236, 1, 2, 4, 9, 11, 12, 13, 14, 15, 16, 19, 24, 38, 40, 44, 46, 47, 48, 59, 64, 65, 70, 81, 85, 107 }, { 242, 1, 3, 6, 7, 9, 13, 14, 16, 17, 19, 23, 25, 26, 28, 30, 31, 47, 51, 54, 57, 60, 64, 67, 111, 131 }, { 244, 1, 2, 4, 5, 7, 10, 15, 17, 19, 20, 21, 22, 26, 27, 30, 37, 40, 41, 45, 65, 66, 68, 70, 110, 134 }, { 252, 4, 7, 10, 11, 12, 13, 23, 25, 29, 31, 32, 34, 36, 37, 38, 40, 42, 44, 62, 67, 68, 71, 77, 108, 113 }, { 253, 2, 4, 5, 6, 9, 10, 12, 14, 20, 24, 27, 35, 36, 37, 38, 42, 43, 45, 50, 54, 63, 66, 70, 120, 133 }, { 260, 1, 4, 6, 7, 10, 15, 24, 26, 27, 28, 29, 31, 33, 34, 37, 38, 44, 65, 70, 71, 77, 78, 83, 100, 112 }, { 264, 3, 7, 8, 12, 16, 18, 19, 20, 22, 24, 26, 31, 34, 37, 38, 40, 42, 53, 54, 61, 64, 69, 70, 130, 134 }, { 264, 3, 8, 12, 13, 16, 18, 20, 21, 22, 24, 26, 29, 34, 38, 40, 42, 43, 47, 54, 59, 64, 70, 71, 130, 134 }, { 264, 1, 3, 4, 6, 9, 10, 11, 12, 16, 17, 18, 20, 21, 22, 39, 42, 54, 56, 61, 66, 68, 69, 73, 129, 135 }, { 265, 1, 3, 4, 6, 9, 10, 11, 12, 16, 17, 18, 20, 21, 22, 39, 42, 54, 56, 62, 66, 68, 69, 74, 130, 135 }, { 273, 1, 4, 8, 10, 11, 12, 17, 19, 21, 22, 27, 29, 30, 33, 37, 43, 52, 62, 65, 86, 88, 89, 91, 96, 120 }, { 273, 1, 6, 9, 14, 16, 17, 18, 21, 22, 23, 25, 31, 32, 38, 44, 46, 48, 50, 54, 62, 65, 68, 78, 133, 140 }, { 275, 2, 3, 7, 13, 17, 24, 25, 31, 33, 34, 35, 37, 41, 49, 51, 53, 55, 60, 68, 71, 74, 81, 94, 100, 107 }, { 276, 1, 5, 8, 9, 11, 18, 19, 21, 30, 36, 41, 44, 45, 46, 47, 51, 53, 58, 63, 69, 71, 84, 87, 105, 120 }, { 280, 5, 6, 11, 17, 18, 20, 21, 24, 27, 28, 32, 34, 41, 42, 50, 53, 54, 55, 68, 78, 85, 88, 95, 97, 117 }, { 280, 2, 3, 7, 8, 14, 18, 30, 36, 37, 39, 44, 50, 52, 54, 56, 60, 63, 64, 65, 72, 75, 78, 79, 96, 106 }, { 284, 1, 2, 11, 12, 14, 16, 18, 19, 23, 26, 29, 37, 38, 39, 40, 42, 59, 68, 69, 77, 78, 97, 106, 109, 110 }, { 286, 1, 4, 5, 7, 10, 12, 15, 16, 20, 23, 28, 30, 32, 33, 35, 37, 53, 54, 64, 68, 74, 79, 80, 133, 153 }, { 289, 2, 3, 5, 8, 13, 14, 17, 20, 21, 32, 36, 41, 50, 52, 60, 61, 62, 68, 74, 76, 83, 87, 100, 102, 104 }, { 289, 2, 3, 4, 5, 7, 12, 16, 17, 19, 21, 23, 25, 29, 31, 32, 44, 57, 64, 65, 68, 72, 76, 84, 140, 149 }, { 290, 1, 2, 10, 11, 13, 14, 15, 17, 18, 28, 29, 34, 36, 38, 50, 56, 60, 69, 77, 80, 85, 91, 94, 111, 119 }, { 293, 5, 6, 11, 17, 18, 20, 21, 24, 27, 28, 32, 34, 41, 42, 50, 54, 55, 66, 68, 78, 85, 88, 95, 110, 130 }, { 297, 2, 7, 8, 9, 10, 15, 16, 17, 18, 23, 25, 26, 28, 36, 38, 43, 53, 60, 61, 68, 69, 77, 99, 137, 160 }, { 308, 1, 3, 4, 7, 10, 12, 13, 23, 25, 34, 37, 38, 39, 43, 44, 45, 62, 77, 79, 85, 87, 108, 113, 115, 116 }, { 308, 1, 5, 6, 7, 8, 9, 13, 16, 19, 28, 33, 36, 38, 43, 45, 48, 70, 71, 73, 84, 86, 102, 104, 120, 133 }, { 309, 7, 8, 14, 16, 23, 24, 25, 26, 31, 33, 34, 39, 48, 56, 59, 60, 62, 70, 76, 82, 92, 100, 101, 108, 117 }, { 311, 2, 7, 8, 9, 10, 15, 16, 17, 18, 23, 25, 26, 28, 36, 38, 43, 53, 60, 61, 68, 83, 91, 99, 151, 160 }, { 314, 1, 6, 7, 11, 16, 22, 26, 29, 32, 36, 38, 44, 51, 53, 64, 69, 70, 73, 74, 75, 85, 87, 101, 116, 128 }, { 316, 1, 3, 9, 12, 21, 26, 30, 33, 34, 35, 38, 39, 40, 41, 53, 56, 59, 69, 79, 85, 96, 103, 111, 117, 120 }, { 317, 1, 5, 6, 7, 8, 9, 16, 17, 19, 32, 37, 40, 42, 47, 49, 52, 59, 75, 81, 92, 94, 110, 112, 113, 126 }, { 320, 2, 7, 8, 9, 12, 14, 15, 21, 23, 35, 38, 44, 46, 49, 53, 54, 56, 63, 96, 101, 103, 105, 108, 112, 116 }, { 320, 3, 8, 9, 11, 17, 18, 22, 25, 26, 27, 29, 30, 31, 33, 35, 49, 51, 67, 72, 73, 80, 85, 95, 152, 168 }, { 320, 1, 4, 6, 7, 8, 13, 14, 16, 24, 28, 30, 33, 34, 38, 41, 42, 57, 60, 69, 78, 81, 90, 92, 150, 170 }, { 320, 3, 4, 6, 8, 9, 14, 15, 16, 24, 28, 30, 31, 34, 38, 39, 42, 59, 60, 71, 78, 79, 90, 92, 150, 170 }, { 322, 3, 4, 8, 9, 10, 16, 18, 20, 22, 23, 24, 28, 31, 38, 44, 47, 64, 65, 68, 76, 80, 81, 97, 144, 178 }, { 322, 3, 4, 8, 10, 15, 16, 18, 19, 20, 22, 24, 28, 35, 38, 44, 53, 59, 64, 68, 76, 80, 85, 93, 144, 178 }, { 323, 2, 3, 4, 7, 10, 13, 15, 18, 23, 32, 34, 35, 36, 42, 46, 50, 57, 60, 66, 72, 78, 87, 98, 159, 164 }, { 323, 3, 8, 9, 11, 17, 18, 22, 25, 26, 27, 29, 30, 31, 33, 35, 49, 51, 67, 72, 73, 83, 88, 95, 155, 168 }, { 323, 2, 6, 9, 11, 13, 14, 18, 19, 20, 23, 27, 28, 29, 42, 46, 48, 60, 64, 72, 74, 79, 82, 98, 146, 177 }, { 325, 3, 5, 6, 11, 12, 13, 18, 23, 25, 28, 32, 37, 40, 43, 45, 46, 51, 79, 92, 99, 103, 108, 112, 114, 134 }, { 326, 1, 4, 8, 10, 12, 16, 21, 22, 24, 27, 28, 35, 36, 37, 38, 46, 49, 68, 70, 75, 88, 90, 93, 158, 168 }, { 327, 2, 9, 10, 12, 13, 16, 19, 21, 23, 26, 36, 44, 46, 52, 55, 61, 62, 74, 84, 87, 100, 103, 104, 120, 140 }, { 328, 2, 3, 4, 7, 8, 10, 14, 17, 26, 27, 28, 36, 38, 40, 42, 45, 53, 58, 73, 74, 79, 94, 102, 152, 176 }, { 334, 1, 4, 8, 10, 12, 16, 21, 22, 24, 27, 28, 35, 36, 37, 38, 46, 49, 68, 75, 78, 88, 93, 98, 166, 168 }, { 336, 2, 3, 4, 7, 8, 10, 14, 17, 26, 27, 28, 36, 38, 40, 45, 50, 53, 58, 73, 74, 79, 94, 110, 152, 184 }, { 338, 1, 4, 8, 10, 12, 16, 19, 22, 24, 25, 28, 36, 37, 38, 39, 46, 53, 68, 70, 73, 94, 96, 101, 164, 174 }, { 338, 4, 5, 8, 10, 12, 15, 16, 21, 22, 24, 28, 33, 36, 38, 43, 46, 57, 68, 70, 77, 94, 96, 97, 164, 174 }, { 340, 1, 4, 5, 6, 11, 13, 16, 17, 22, 24, 44, 46, 50, 51, 52, 53, 61, 64, 66, 79, 84, 85, 92, 169, 171 }, { 344, 2, 3, 8, 11, 14, 17, 19, 21, 23, 25, 27, 36, 39, 44, 48, 53, 56, 71, 77, 83, 86, 89, 98, 169, 175 }, { 359, 7, 8, 9, 10, 14, 17, 18, 23, 25, 27, 29, 31, 40, 41, 43, 46, 69, 74, 82, 85, 90, 98, 102, 172, 187 }, { 361, 2, 6, 7, 8, 9, 14, 20, 22, 26, 27, 32, 34, 36, 47, 49, 56, 66, 67, 74, 82, 89, 98, 107, 156, 205 }, { 363, 1, 4, 6, 12, 13, 20, 21, 25, 26, 27, 28, 32, 37, 41, 45, 53, 58, 64, 69, 91, 97, 102, 106, 155, 208 }, { 364, 2, 3, 4, 6, 8, 9, 13, 14, 16, 19, 23, 24, 28, 29, 52, 57, 64, 75, 82, 91, 98, 100, 109, 173, 191 }, { 367, 1, 4, 6, 12, 13, 20, 21, 25, 26, 27, 28, 32, 37, 41, 49, 53, 58, 64, 69, 91, 97, 102, 110, 155, 212 }, { 368, 1, 6, 15, 16, 17, 18, 22, 25, 31, 33, 39, 42, 45, 46, 47, 48, 51, 69, 72, 88, 91, 96, 112, 160, 208 }, { 371, 1, 2, 7, 8, 20, 21, 22, 24, 26, 28, 30, 38, 43, 46, 50, 51, 64, 65, 70, 90, 95, 102, 109, 160, 211 }, { 373, 3, 6, 7, 8, 15, 17, 22, 23, 31, 32, 35, 41, 43, 60, 62, 68, 79, 87, 104, 105, 114, 120, 121, 138, 148 }, { 378, 2, 3, 10, 17, 18, 20, 21, 22, 24, 27, 31, 38, 41, 48, 51, 56, 68, 78, 80, 85, 87, 96, 117, 165, 213 }, { 378, 1, 2, 7, 13, 15, 17, 18, 25, 27, 29, 30, 31, 42, 43, 46, 56, 61, 68, 73, 93, 100, 105, 112, 161, 217 }, { 380, 4, 7, 17, 18, 19, 20, 21, 26, 31, 33, 35, 40, 45, 48, 49, 60, 67, 73, 79, 81, 87, 107, 113, 186, 194 }, { 380, 4, 5, 6, 9, 13, 15, 16, 17, 22, 24, 33, 38, 44, 49, 50, 56, 60, 67, 82, 84, 95, 108, 121, 177, 203 }, { 381, 12, 13, 21, 23, 25, 27, 35, 36, 42, 45, 54, 57, 59, 60, 79, 82, 84, 85, 92, 95, 96, 100, 110, 111, 186 }, { 384, 1, 4, 8, 9, 11, 12, 19, 21, 27, 32, 35, 44, 45, 46, 47, 51, 60, 67, 84, 89, 96, 108, 120, 180, 204 }, { 384, 1, 4, 8, 9, 11, 12, 15, 17, 19, 25, 26, 31, 32, 37, 44, 57, 60, 81, 84, 96, 99, 108, 120, 180, 204 }, { 384, 3, 5, 7, 11, 12, 17, 20, 22, 25, 29, 35, 47, 48, 55, 56, 57, 69, 72, 76, 80, 96, 100, 116, 172, 212 }, { 385, 1, 2, 7, 13, 15, 17, 18, 25, 27, 29, 30, 31, 43, 46, 49, 56, 61, 68, 73, 93, 100, 105, 119, 161, 224 }, { 392, 4, 7, 8, 15, 23, 26, 29, 30, 31, 32, 34, 43, 48, 55, 56, 68, 77, 88, 98, 106, 116, 135, 141, 151, 153 }, { 392, 10, 12, 14, 16, 19, 21, 25, 27, 31, 35, 39, 41, 51, 52, 54, 55, 73, 92, 98, 115, 121, 123, 129, 148, 171 }, { 392, 1, 4, 5, 8, 11, 14, 16, 21, 22, 24, 27, 28, 30, 31, 52, 64, 81, 83, 96, 97, 98, 99, 114, 195, 197 }, { 393, 4, 8, 16, 20, 23, 24, 25, 27, 29, 37, 44, 45, 50, 53, 64, 66, 68, 69, 73, 85, 91, 101, 116, 186, 207 }, { 396, 1, 4, 5, 14, 16, 32, 35, 36, 46, 47, 48, 49, 68, 69, 73, 93, 94, 97, 99, 104, 110, 111, 125, 126, 160 }, { 396, 1, 4, 5, 8, 11, 14, 16, 21, 22, 24, 27, 28, 30, 31, 52, 64, 81, 83, 98, 99, 100, 101, 114, 197, 199 }, { 396, 3, 8, 9, 11, 14, 16, 17, 18, 31, 32, 41, 45, 48, 56, 60, 66, 73, 75, 81, 82, 98, 99, 117, 180, 216 }, { 398, 2, 6, 7, 11, 15, 17, 23, 28, 29, 39, 44, 46, 53, 56, 58, 65, 68, 99, 100, 119, 120, 134, 144, 145, 154 }, { 400, 3, 6, 21, 23, 24, 26, 29, 35, 37, 40, 41, 47, 53, 55, 64, 76, 79, 81, 99, 100, 121, 122, 137, 142, 179 }, { 404, 3, 6, 7, 14, 17, 20, 21, 26, 28, 31, 32, 39, 46, 53, 54, 68, 71, 80, 88, 92, 100, 111, 113, 199, 205 }, { 404, 4, 7, 10, 11, 12, 13, 16, 18, 20, 23, 25, 28, 29, 32, 47, 62, 70, 88, 93, 96, 101, 114, 127, 189, 215 }, { 408, 2, 3, 7, 13, 16, 18, 20, 27, 30, 33, 41, 43, 46, 52, 54, 57, 72, 79, 84, 100, 105, 108, 116, 195, 213 }, { 412, 3, 11, 12, 15, 21, 26, 32, 39, 43, 47, 54, 60, 68, 73, 83, 85, 86, 87, 89, 99, 114, 129, 139, 144, 169 }, { 413, 5, 7, 17, 20, 34, 38, 39, 48, 56, 57, 59, 60, 64, 65, 70, 72, 75, 81, 105, 106, 110, 125, 148, 153, 155 }, { 416, 2, 4, 7, 11, 13, 24, 25, 30, 35, 37, 39, 40, 44, 58, 62, 65, 82, 104, 112, 120, 128, 135, 143, 153, 169 }, { 416, 1, 2, 3, 8, 12, 15, 16, 17, 20, 22, 24, 26, 29, 31, 64, 75, 85, 88, 91, 94, 98, 104, 133, 179, 237 }, { 421, 1, 2, 4, 5, 7, 9, 12, 16, 20, 22, 23, 35, 38, 48, 56, 83, 94, 104, 116, 118, 128, 140, 150, 153, 177 }, { 421, 5, 11, 12, 17, 18, 20, 23, 26, 29, 36, 38, 40, 44, 51, 55, 59, 72, 92, 97, 102, 105, 107, 117, 199, 222 }, { 422, 2, 4, 7, 13, 16, 18, 20, 23, 28, 29, 38, 43, 46, 51, 59, 68, 74, 79, 86, 93, 100, 111, 132, 179, 243 }, { 425, 3, 4, 5, 9, 10, 12, 13, 14, 16, 19, 20, 31, 46, 48, 56, 79, 102, 104, 116, 126, 128, 140, 142, 157, 181 }, { 441, 5, 6, 7, 16, 18, 23, 24, 27, 38, 39, 47, 51, 52, 62, 66, 72, 80, 84, 92, 101, 102, 118, 120, 219, 222 }, { 454, 1, 2, 11, 17, 29, 34, 35, 46, 48, 51, 53, 55, 63, 69, 79, 87, 88, 91, 109, 134, 136, 143, 150, 161, 184 }, { 456, 5, 7, 10, 11, 13, 15, 18, 19, 31, 49, 50, 52, 59, 60, 63, 72, 77, 115, 128, 129, 135, 142, 148, 179, 193 }, { 465, 6, 9, 13, 14, 19, 21, 24, 25, 31, 32, 53, 56, 64, 73, 74, 82, 91, 111, 125, 127, 137, 139, 153, 173, 201 }, { 472, 7, 9, 13, 15, 26, 34, 35, 44, 47, 51, 58, 61, 65, 81, 87, 103, 104, 115, 118, 123, 128, 133, 136, 148, 221 }, { 477, 3, 5, 12, 16, 19, 22, 25, 26, 37, 41, 49, 72, 76, 77, 82, 86, 87, 115, 117, 135, 141, 149, 167, 169, 193 }, { 492, 2, 9, 15, 17, 27, 29, 31, 32, 33, 36, 47, 49, 50, 60, 62, 69, 77, 105, 114, 123, 127, 128, 132, 237, 255 }, { 492, 3, 5, 9, 11, 12, 21, 24, 27, 30, 44, 45, 50, 54, 55, 57, 63, 95, 101, 112, 117, 123, 134, 140, 235, 257 }, { 503, 4, 15, 16, 19, 22, 23, 25, 27, 33, 34, 50, 62, 67, 87, 88, 93, 100, 113, 135, 143, 149, 157, 167, 179, 211 }, { 506, 1, 7, 24, 26, 33, 35, 40, 45, 47, 51, 55, 69, 87, 90, 93, 96, 117, 125, 134, 145, 146, 147, 160, 162, 199 }, { 507, 2, 3, 7, 11, 13, 15, 28, 34, 43, 50, 57, 64, 80, 83, 86, 89, 107, 115, 116, 127, 149, 163, 175, 183, 217 }, { 512, 1, 7, 8, 9, 10, 15, 22, 32, 34, 46, 51, 65, 69, 71, 91, 105, 109, 111, 136, 139, 152, 157, 173, 200, 203 }, { 512, 1, 6, 7, 8, 9, 13, 17, 19, 35, 45, 47, 57, 62, 73, 88, 93, 104, 107, 128, 130, 151, 163, 184, 198, 221 }, { 513, 6, 9, 10, 17, 19, 24, 28, 29, 37, 39, 64, 65, 68, 81, 98, 99, 102, 115, 145, 147, 153, 159, 165, 189, 201 }, { 517, 5, 6, 7, 16, 20, 24, 28, 33, 38, 43, 63, 71, 80, 83, 86, 92, 98, 122, 132, 148, 164, 166, 173, 180, 205 }, { 524, 9, 12, 20, 21, 33, 35, 37, 39, 54, 55, 61, 62, 87, 90, 98, 101, 125, 132, 135, 141, 145, 159, 163, 164, 220 }, { 527, 11, 12, 13, 14, 19, 30, 41, 47, 50, 52, 59, 68, 71, 81, 94, 97, 107, 132, 147, 151, 155, 169, 175, 183, 197 }, { 528, 2, 9, 15, 17, 27, 29, 31, 32, 33, 36, 47, 49, 50, 60, 62, 69, 77, 123, 127, 128, 132, 141, 150, 255, 273 }, { 529, 9, 12, 20, 21, 33, 35, 37, 39, 54, 55, 61, 62, 87, 90, 98, 101, 125, 132, 140, 141, 145, 159, 163, 169, 225 }, { 531, 6, 9, 10, 17, 19, 24, 29, 31, 39, 40, 67, 68, 71, 84, 101, 102, 105, 118, 151, 153, 159, 165, 171, 195, 207 }, { 532, 16, 18, 26, 27, 33, 39, 41, 50, 51, 55, 69, 71, 84, 87, 91, 94, 132, 133, 141, 143, 164, 168, 169, 173, 195 }, { 534, 11, 13, 15, 17, 18, 27, 38, 44, 49, 52, 60, 61, 68, 81, 87, 94, 107, 135, 149, 153, 159, 171, 174, 189, 210 }, { 535, 2, 8, 26, 27, 36, 41, 45, 57, 62, 77, 88, 95, 97, 99, 101, 102, 109, 114, 117, 118, 141, 147, 168, 192, 226 }, { 536, 1, 8, 21, 30, 31, 32, 33, 41, 44, 46, 49, 55, 57, 61, 84, 91, 113, 134, 137, 139, 150, 155, 176, 205, 247 }, { 536, 3, 5, 9, 11, 12, 21, 24, 27, 30, 44, 45, 50, 54, 55, 57, 63, 95, 117, 123, 134, 140, 145, 156, 257, 279 }, { 540, 1, 7, 8, 9, 10, 14, 19, 34, 36, 51, 58, 69, 81, 83, 97, 109, 111, 115, 136, 149, 152, 167, 183, 208, 221 }, { 540, 6, 13, 15, 25, 28, 36, 43, 47, 55, 57, 58, 59, 60, 65, 82, 89, 91, 107, 124, 127, 144, 163, 183, 233, 250 }, { 540, 8, 9, 10, 11, 16, 30, 36, 38, 45, 55, 57, 65, 68, 81, 84, 95, 98, 100, 116, 117, 126, 135, 144, 261, 279 }, { 540, 8, 9, 10, 11, 16, 30, 36, 38, 45, 55, 57, 65, 68, 81, 84, 95, 98, 100, 116, 117, 126, 135, 144, 261, 279 }, { 540, 4, 6, 9, 10, 17, 21, 23, 25, 31, 33, 36, 38, 45, 50, 81, 83, 115, 117, 126, 133, 135, 144, 146, 261, 279 }, { 540, 4, 6, 9, 10, 17, 21, 23, 25, 31, 33, 36, 38, 45, 50, 81, 83, 115, 117, 126, 133, 135, 144, 146, 261, 279 }, { 541, 3, 4, 11, 13, 16, 17, 21, 25, 26, 44, 46, 64, 75, 86, 87, 97, 106, 109, 133, 141, 165, 185, 191, 215, 217 }, { 541, 3, 5, 27, 32, 33, 37, 47, 50, 53, 56, 57, 69, 71, 78, 97, 98, 109, 111, 126, 144, 165, 169, 183, 189, 232 }, { 544, 1, 7, 24, 26, 33, 35, 40, 45, 47, 51, 55, 69, 87, 90, 93, 96, 117, 125, 134, 145, 147, 184, 198, 199, 200 }, { 544, 6, 8, 20, 21, 23, 41, 42, 48, 59, 61, 77, 80, 81, 85, 90, 92, 93, 102, 115, 132, 139, 168, 198, 207, 244 }, { 547, 3, 5, 16, 22, 26, 27, 35, 47, 49, 59, 67, 71, 72, 85, 87, 102, 103, 111, 137, 144, 150, 197, 200, 203, 207 }, { 549, 4, 10, 14, 24, 26, 31, 34, 36, 38, 40, 43, 48, 59, 63, 74, 89, 97, 105, 117, 124, 136, 152, 156, 241, 308 }, { 550, 1, 2, 5, 13, 19, 20, 25, 30, 39, 43, 58, 59, 73, 75, 76, 90, 95, 103, 116, 128, 130, 132, 172, 262, 288 }, { 550, 1, 11, 16, 23, 24, 27, 29, 36, 41, 43, 44, 47, 59, 70, 71, 80, 99, 103, 111, 116, 128, 156, 167, 227, 323 }, { 551, 3, 5, 24, 25, 26, 30, 35, 36, 39, 40, 42, 57, 68, 76, 94, 109, 120, 128, 152, 162, 166, 175, 176, 200, 223 }, { 552, 5, 17, 18, 22, 25, 27, 32, 33, 39, 59, 62, 87, 91, 100, 102, 111, 112, 135, 137, 149, 165, 168, 183, 201, 204 }, { 552, 1, 3, 4, 7, 8, 9, 10, 15, 18, 19, 21, 41, 52, 54, 73, 93, 95, 123, 125, 136, 138, 153, 168, 261, 291 }, { 556, 6, 8, 10, 13, 19, 25, 32, 37, 49, 54, 58, 76, 84, 91, 92, 100, 107, 128, 145, 156, 165, 185, 195, 205, 206 }, { 556, 3, 12, 13, 15, 19, 23, 27, 34, 35, 39, 42, 45, 48, 52, 53, 87, 140, 145, 158, 166, 171, 184, 189, 201, 227 }, { 556, 3, 12, 13, 15, 19, 23, 27, 34, 35, 39, 42, 45, 48, 52, 53, 87, 140, 145, 158, 166, 171, 184, 189, 201, 227 }, { 556, 1, 5, 7, 8, 9, 10, 12, 14, 20, 27, 31, 43, 47, 50, 74, 93, 97, 121, 125, 139, 143, 153, 167, 264, 292 }, { 562, 2, 3, 5, 8, 13, 19, 20, 29, 33, 47, 53, 54, 64, 65, 76, 93, 119, 123, 142, 157, 161, 180, 184, 221, 259 }, { 570, 3, 9, 10, 33, 36, 38, 40, 42, 50, 51, 60, 69, 72, 75, 77, 90, 113, 140, 141, 151, 152, 189, 200, 229, 230 }, { 575, 4, 6, 14, 16, 31, 39, 63, 69, 74, 81, 88, 103, 107, 111, 115, 120, 131, 132, 133, 147, 156, 159, 164, 198, 218 }, { 576, 1, 4, 9, 11, 15, 19, 22, 34, 36, 53, 60, 76, 82, 84, 104, 126, 127, 128, 153, 156, 165, 174, 183, 219, 237 }, { 576, 8, 9, 10, 11, 16, 30, 36, 38, 45, 55, 57, 65, 68, 81, 84, 95, 98, 100, 116, 135, 144, 153, 162, 279, 297 }, { 576, 4, 6, 9, 10, 17, 21, 23, 25, 31, 33, 36, 38, 45, 50, 81, 83, 115, 133, 135, 144, 146, 153, 162, 279, 297 }, { 580, 2, 5, 7, 10, 12, 13, 19, 21, 22, 29, 36, 40, 61, 65, 74, 101, 135, 139, 161, 179, 183, 192, 205, 209, 236 }, { 580, 5, 6, 11, 13, 16, 17, 21, 25, 34, 44, 54, 68, 80, 88, 100, 112, 120, 135, 142, 145, 170, 173, 195, 215, 265 }, { 580, 11, 12, 16, 17, 29, 32, 39, 41, 53, 55, 59, 60, 68, 70, 81, 84, 92, 124, 125, 128, 129, 156, 171, 280, 300 }, { 593, 13, 14, 15, 35, 48, 51, 55, 67, 73, 79, 83, 91, 94, 105, 109, 116, 119, 124, 133, 150, 171, 173, 196, 217, 226 }, { 595, 4, 13, 18, 19, 22, 35, 40, 48, 58, 61, 62, 77, 78, 82, 83, 86, 118, 149, 163, 168, 187, 192, 202, 206, 240 }, { 601, 7, 8, 25, 34, 41, 42, 46, 48, 54, 55, 62, 70, 71, 74, 98, 103, 116, 143, 168, 169, 190, 192, 193, 218, 240 }, { 603, 7, 11, 12, 14, 21, 25, 32, 40, 52, 56, 60, 67, 68, 81, 91, 92, 132, 144, 149, 163, 177, 191, 196, 235, 263 }, { 603, 13, 23, 26, 27, 35, 44, 45, 49, 53, 54, 57, 66, 75, 99, 101, 110, 122, 126, 144, 158, 175, 180, 189, 234, 270 }, { 607, 6, 8, 10, 13, 19, 25, 32, 37, 49, 54, 58, 76, 84, 91, 92, 100, 107, 128, 156, 185, 196, 205, 206, 216, 246 }, { 609, 9, 14, 15, 17, 32, 45, 47, 58, 67, 74, 76, 79, 80, 83, 97, 111, 125, 126, 150, 170, 186, 188, 215, 224, 235 }, { 611, 1, 10, 22, 26, 32, 41, 45, 54, 57, 61, 62, 66, 85, 86, 87, 95, 97, 101, 119, 132, 136, 167, 176, 268, 343 }, { 614, 15, 22, 24, 31, 33, 49, 53, 54, 57, 60, 63, 68, 74, 81, 83, 104, 109, 151, 155, 163, 167, 217, 229, 230, 234 }, { 634, 15, 17, 24, 26, 33, 43, 44, 54, 57, 60, 63, 73, 79, 81, 88, 109, 119, 160, 161, 172, 173, 227, 234, 235, 239 }, { 643, 2, 9, 21, 29, 38, 40, 41, 42, 58, 62, 67, 76, 82, 83, 85, 96, 104, 166, 172, 186, 192, 201, 207, 250, 270 }, { 644, 7, 9, 13, 18, 19, 22, 31, 49, 53, 61, 66, 68, 71, 87, 93, 94, 119, 164, 178, 192, 199, 206, 227, 239, 253 }, { 655, 10, 14, 15, 21, 25, 26, 31, 40, 51, 53, 54, 57, 65, 83, 84, 86, 151, 152, 173, 193, 194, 215, 216, 246, 288 }, { 661, 5, 7, 17, 18, 23, 31, 36, 38, 41, 64, 73, 77, 83, 84, 102, 106, 111, 161, 175, 196, 203, 210, 238, 248, 262 } };
	}

}
