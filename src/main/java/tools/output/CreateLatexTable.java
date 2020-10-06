/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package tools.output;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.StringTokenizer;
import java.util.stream.IntStream;

public class CreateLatexTable {

	static final int TIME_OUT = -1;
	static final int ERROR = -2;
	static final int ABSENT = -3;
	static final int UNRANKED = -4;
	static final int CRASHED = -5;

	private static long deadlineTime = 12000000000L;

	static int PREFIX_LENGTH_FOR_INSTANCES_OF_SIMILAR_PROBLEM = 8;

	private static final String FONTSIZE = "tiny"; // "scriptsize"; // footnotesize";

	private static final String RED = "red";
	private static final String GREEN = "green";
	private static final String BLUE = "blue";
	private static final String GREY = "grey";

	private static final double MODE1_COLOR_OFFSET = 0.25;
	private static final double MODE2_COLOR_OFFSET = 0.45;

	private static final int MAX_INSTANCE_NAME_LENGTH = 40;
	private static final int INSTANCE_NAME_WIDTH = 3; // in cm for multirow

	private static String[] unsolvedNames = { "Uns", "Out", "Err", "Abs" };

	// private static final String[] DEFAULT_SERIES = { "cpu", "ccks", "vcks", "nodes" };

	private static int nbMethods;
	private static int nbSeriesOfMethods;
	private static int nbMetricsPerMethod;
	private static int nbWishedMetricsPerMethod;

	private static int[][] trame; // 1D = data (position); 2D = method (position)

	private static String[] columnsNames;
	private static String[] subcolumnsNames; // useful when nbSeriesOfmethods > 1
	private static String[] rowNames;

	/**
	 * 1D = id of the method; 2D = if 0 nb instances solved, otherwise if equal to i > 0 the number of times the corresponding method was at the ith
	 * rank.
	 */
	private static int[][] statisticsOfSolved;
	private static int[][] statisticsOfUnsolved;

	private static int dataToBeRanked = 0; // -1;
	private static int dataToBeAveraged = 0;
	private static int mode = 2;

	private static boolean onlyFirst = false;
	private static boolean tabular = false;
	private static boolean insertCommas = true;

	private static Stats stats = new Stats();

	private static String columnsFormat() {
		String s = "|c|c|";
		for (int i = 0; i < trame[0].length; i++)
			s += "r|";
		return s;
	}

	private static String header() {
		String inst = "$Instances$";
		String s = "\\hline";
		String spaceBeforeAfterColumnName = ""; // "~ ";

		// String s = "\\cline{1-1} \\cline{3-"+ (trame[0].length + 2) + "}";
		s += trame.length == 1 ? inst : subcolumnsNames == null ? inst + " & " : "\\multirow{" + 2 + "}{" + INSTANCE_NAME_WIDTH + "cm}{" + inst + "} &";

		if (subcolumnsNames == null)
			for (int i = 0; i < columnsNames.length; i++)
				s += " & \\multicolumn{" + 1 + "}{c|}{$" + spaceBeforeAfterColumnName + columnsNames[i] + spaceBeforeAfterColumnName + "$} ";
		else {
			for (int i = 0; i < columnsNames.length; i++)
				s += " & \\multicolumn{" + subcolumnsNames.length + "}{c|}{$" + spaceBeforeAfterColumnName + columnsNames[i] + spaceBeforeAfterColumnName
						+ "$} ";
			s += " \\\\";
			s += "\\cline{3-" + (trame[0].length + 2) + "}";
			s += " & ";
			for (int i = 0; i < columnsNames.length; i++)
				for (int j = 0; j < subcolumnsNames.length; j++)
					s += " & " + subcolumnsNames[j];
		}

		// s += " & \\multicolumn{1}{|c|}{$" + columnsNames[nbColumns-1] + "$} ";
		return s + " \\\\";
	}

	private static String getLatexFormatOf(String color, String s) {
		if (mode == 0)
			return s;
		if (mode == 1)
			return "\\textcolor{" + color + "}{" + s + "}";
		return "\\cellcolor{" + color + "}" + s;

		// return "\\multicolumn{1}{>{\\columncolor{" + color + "}}r}{" + s + "}";
	}

	private static String getLatexColorDefinitionOf(String color, int level) {
		String s = "\\definecolor{" + color + level + "}{rgb}";
		if (color.equals(GREY)) {
			if (level == 1)
				return s + "{0.8,0.8,0.8}";
			if (level == 2)
				return s + "{0.5,0.5,0.5}";
		}
		double offset = (level - 1) * (mode == 1 ? MODE1_COLOR_OFFSET : MODE2_COLOR_OFFSET);
		if (color.equals(RED))
			return s + "{1," + offset + "," + offset + "}";
		if (color.equals(GREEN))
			return s + "{" + offset + ",1," + offset + "}";
		// if (color.equals(BLUE))
		return s + "{" + offset + "," + offset + ",1}";
	}

	private static String insertCommas(String formatedToken) {
		StringBuilder sb = new StringBuilder();
		int cnt = 0;
		for (int i = formatedToken.length() - 1; i >= 0; i--) {
			char c = formatedToken.charAt(i);
			sb.insert(0, c);
			if (c == '.' || c == 'M' || c == 'K')
				cnt = 0;
			else {
				cnt++;
				if (cnt == 3 && i != 0) {
					sb.insert(0, ',');
					cnt = 0;
				}
			}
		}
		return sb.toString();
	}

	private static String format(long d, int rank, int serie) {
		String formatedToken = null;
		if (rank == ABSENT)
			return "Abs";
		if (rank == ERROR)
			return "Err";
		if (rank == TIME_OUT && d != TIME_OUT)
			d = Math.abs(d); // for inverting negative cpu time when timeout

		if (serie == 0) {
			d = d - d % 10;
			if (d > 100000)
				d = d - d % 1000;
			else if (d > 10000)
				d = d - d % 100;
			double dd = d / 1000.0;
			if (rank == TIME_OUT || dd > 100)
				formatedToken = (long) dd + "";
			else
				formatedToken = dd + "";
			// formatedToken = d + "";
		} else {
			if (d > 10000000)
				formatedToken = Math.round(d / 1000000.0) + "M";
			else if (d > 100000)
				formatedToken = Math.round(d / 1000.0) + "K";
			else
				formatedToken = d + "";
		}

		if (insertCommas)
			formatedToken = insertCommas(formatedToken);

		String s = "$" + formatedToken + "$";
		if (rank == TIME_OUT)
			return getLatexFormatOf("grey2", s);
		if (rank == nbMethods)
			return getLatexFormatOf("red1", s);
		if (rank == nbMethods - 1)
			return getLatexFormatOf("red2", s);
		if (rank == nbMethods - 2)
			return getLatexFormatOf("red3", s);
		if (rank == 1)
			return (onlyFirst ? getLatexFormatOf("grey1", s) : getLatexFormatOf("green1", s));
		if (rank == 2)
			return getLatexFormatOf("green2", s);
		if (rank == 3)
			return getLatexFormatOf("green3", s);
		return s;
	}

	private static long getValue(String s, int position) {
		StringTokenizer st = new StringTokenizer(s);
		for (int i = 0; i < position - 1; i++)
			st.nextToken();
		return (long) (Double.parseDouble(st.nextToken()));
		// return Long.parseLong(st.nextToken());
	}

	private static void rank(long[] values, int[] rankings, int rank) {
		long bestValue = Long.MAX_VALUE;
		int bestIndex = -1;
		for (int i = 0; i < values.length; i++) {
			if (rankings[i] != UNRANKED)
				continue; // since already ranked
			if (values[i] < bestValue) {
				bestValue = values[i];
				bestIndex = i;
			}
		}
		if (bestIndex == -1)
			return; // throw new RuntimeException();
		if (bestValue == 0) {
			rankings[bestIndex] = 1;
			statisticsOfSolved[bestIndex][1]++;
		} else {
			rankings[bestIndex] = rank;
			statisticsOfSolved[bestIndex][rank]++;
		}
	}

	private static class Stats {
		// In this context, an easy instance is an instance solved by all selected methods

		private int nbEasyInstances;

		private long[] sumEasyInstances;

		private int nbProblemEasyInstances;

		private long[] sumProblemEasyInstances;

		private int[] nbSolvedProblemInstances; // 1D = method id

		private long[] sumSolvedProblemInstances;

		private String previousLine;

		private int nbProblemInstances;

		private void printLineFor(int nb, long[] t, String head, PrintWriter out) {
			if (previousLine == null)
				return;
			out.println("\\hline");
			// System.out.println(previousLine);
			String problemName = previousLine.substring(0, PREFIX_LENGTH_FOR_INSTANCES_OF_SIMILAR_PROBLEM).replaceAll("_", "\\\\_") + " (" + nbProblemInstances
					+ ") ";
			String result = problemName + " & " + head + " ";
			for (int i = 0; i < t.length; i++)
				result = result + " & " + (nb != 0 ? t[i] / nb : "-") + "(" + nb + ")";
			result = result + " \\\\";
			out.println(result);
			out.println("\\hline");
		}

		private void printLineFor(int[] nb, long[] t, String head, PrintWriter out) {
			// out.println("\\hline");
			String problemName = previousLine.substring(0, PREFIX_LENGTH_FOR_INSTANCES_OF_SIMILAR_PROBLEM).replaceAll("_", "\\\\_") + " (" + nbProblemInstances
					+ ") ";
			String result = problemName + " & " + head + " ";
			for (int i = 0; i < t.length; i++)
				result = result + " & " + (nb[i] != 0 ? t[i] / nb[i] : "-") + "(" + nb[i] + ")";
			result = result + " \\\\";
			out.println(result);
			out.println("\\hline");
		}

		private void printEasyInstances(PrintWriter out) {
			printLineFor(nbEasyInstances, sumEasyInstances, "avgE", out);
		}

		private void printProblemEasyInstances(PrintWriter out) {
			printLineFor(nbProblemEasyInstances, sumProblemEasyInstances, "avgE", out);
		}

		private void printProblemInstances(PrintWriter out) {
			printLineFor(nbSolvedProblemInstances, sumSolvedProblemInstances, "avgT", out);
		}

		private boolean isArrayContainingValuesStrictlyLessThanOnly(final long[] t, final long limit) {
			for (long v : t)
				if (v >= limit)
					return false;
			return true;
		}

		private void manageNewLine(String line, int dataToBeAveraged, PrintWriter out) {
			System.out.println(line);
			// if (dataToBeRanked == -1 || nbSeriesOfMethods != 1)
			if (nbSeriesOfMethods != 1)
				return;
			long[] values = new long[nbMethods];
			for (int i = 0; i < nbMethods; i++)
				values[i] = getValue(line, trame[dataToBeAveraged][i]);

			if (previousLine == null) {
				sumEasyInstances = new long[nbMethods];
				sumSolvedProblemInstances = new long[nbMethods];
				sumProblemEasyInstances = new long[nbMethods];
				nbSolvedProblemInstances = new int[nbMethods];
			}

			boolean easyInstance = dataToBeAveraged != 0
					|| Arrays.stream(values).noneMatch(v -> v < 0) && isArrayContainingValuesStrictlyLessThanOnly(values, deadlineTime);
			boolean newProblem = previousLine != null && !previousLine.startsWith(line.substring(0, PREFIX_LENGTH_FOR_INSTANCES_OF_SIMILAR_PROBLEM));
			newProblem = newProblem
					&& (nbProblemInstances >= 10 || !previousLine.startsWith(line.substring(0, PREFIX_LENGTH_FOR_INSTANCES_OF_SIMILAR_PROBLEM / 2)));

			if (newProblem) {
				if (nbProblemInstances > 1) {
					printProblemEasyInstances(out);
					printProblemInstances(out);
				}
				nbProblemInstances = 0;
				nbProblemEasyInstances = 0;
				Arrays.fill(sumProblemEasyInstances, 0);
				Arrays.fill(sumSolvedProblemInstances, 0);
				Arrays.fill(nbSolvedProblemInstances, 0);
			}
			nbProblemInstances++;
			previousLine = line;
			if (easyInstance) {
				nbEasyInstances++;
				for (int i = 0; i < values.length; i++)
					sumEasyInstances[i] += values[i];
				nbProblemEasyInstances++;
				for (int i = 0; i < values.length; i++)
					sumProblemEasyInstances[i] += values[i];
			}
			for (int i = 0; i < values.length; i++) {
				if (values[i] >= 0 && values[i] < deadlineTime) {
					nbSolvedProblemInstances[i]++;
					sumSolvedProblemInstances[i] += values[i];
				}
			}
		}
	}

	private static int[] rankingOf(String line, int data) {
		// System.out.println("line = " + line + " serie = " + serie);
		int[] rankings = new int[nbMethods];
		Arrays.fill(rankings, UNRANKED);
		if (data != dataToBeRanked || nbSeriesOfMethods > 1)
			return rankings;
		// System.out.println("ranking line " + line + " serie = " + serie);
		long[] values = new long[nbMethods];
		for (int i = 0; i < nbMethods; i++)
			values[i] = getValue(line, trame[data][i]);

		int nbSuccesfulMethods = 0;
		// int nbTimeouts = 0;
		// int nbUnknowns = 0;
		for (int i = 0; i < values.length; i++) {
			if (values[i] == ERROR) {
				rankings[i] = ERROR;
				statisticsOfUnsolved[i][0]++;
				statisticsOfUnsolved[i][2]++;
			} else if (values[i] == ABSENT) {
				rankings[i] = ABSENT;
				statisticsOfUnsolved[i][0]++;
				statisticsOfUnsolved[i][3]++;
			} else if (values[i] < 0 || values[i] >= deadlineTime) {
				System.out.println(values[i] + " " + deadlineTime);
				rankings[i] = TIME_OUT;
				statisticsOfUnsolved[i][0]++;
				statisticsOfUnsolved[i][1]++;
			} else {
				nbSuccesfulMethods++;
				statisticsOfSolved[i][0]++;
			}
		}
		if (onlyFirst)
			rank(values, rankings, 1);
		else
			for (int i = 1; i <= nbSuccesfulMethods; i++)
				rank(values, rankings, i);

		// for (int i=0; i<rankings.length;i++)
		// System.out.print(rankings[i] + " ");
		// System.out.println();

		return rankings;
	}

	private static String getInstanceName(String s) {
		int position1 = s.lastIndexOf(File.separatorChar);
		if (position1 != -1)
			s = s.substring(position1 + 1);
		int position2 = s.lastIndexOf(".xml");
		if (position2 != -1)
			s = s.substring(0, position2);
		if (s.length() > MAX_INSTANCE_NAME_LENGTH)
			s = s.substring(s.length() - MAX_INSTANCE_NAME_LENGTH);
		return (trame.length == 1 ? s : "\\multirow{" + trame.length + "}{" + INSTANCE_NAME_WIDTH + "cm}{" + s + "}");
		//
		// if (instanceName.length() > MAX_INSTANCE_NAME_LENGTH)
		// instanceName = instanceName.substring(instanceName.length() - MAX_INSTANCE_NAME_LENGTH);
		//
		// String s = (serie == 0 ? "$" + instanceName.replaceAll("_", "-") + "$" : " ");
	}

	private static boolean activateLineSelection = false; // TODO

	private static int minimalSelectionTime = 5000; // 2000;

	private static boolean discardLine(String line, int serie) {
		if (!activateLineSelection)
			return false;
		if (serie != 0)
			return false;
		// if (getValue(line, trame[serie][trame[serie].length-1])>=0 && getValue(line,
		// trame[serie][trame[serie].length-1]) < 60000)
		// return true;
		// for (int i = 0; i < trame[serie].length; i++)
		// if (getValue(line, trame[serie][i]) >= 0)
		// return false;

		boolean allTimedOut = true;
		for (int i = 0; allTimedOut && i < trame[serie].length; i++)
			if (getValue(line, trame[serie][i]) < deadlineTime)
				allTimedOut = false;
		if (allTimedOut)
			return true;

		for (int i = 0; i < trame[serie].length; i++)
			if (getValue(line, trame[serie][i]) > minimalSelectionTime)
				return false;
		// getValue(line, trame[serie][trame[serie].length - 1]);

		return true;
	}

	private static boolean discardIndividualInstances = false;

	private static String dealWith(String line, int data) {
		// if (discardLine(line, serie))return null;

		if (discardIndividualInstances)
			return "";

		StringTokenizer st = new StringTokenizer(line);
		String instanceName = getInstanceName(st.nextToken());
		// if (instanceName.length() > MAX_INSTANCE_NAME_LENGTH)
		// instanceName = instanceName.substring(instanceName.length() - MAX_INSTANCE_NAME_LENGTH);

		String s = (data == 0 ? "$" + instanceName.replaceAll("_", "-") + "$" : " ");
		if (trame.length > 1)
			s += " & " + rowNames[data];
		int[] rankings = rankingOf(line, data);

		for (int i = 0; i < trame[data].length; i++)
			s = s + " & " + format(getValue(line, trame[data][i]), (nbSeriesOfMethods > 1 ? Integer.MAX_VALUE : rankings[i]), data);
		return s + " \\\\";
	}

	private static String getStatisticsOfSolved(int rank) {
		String s = (rank == 0 ? " & sol " : " & nb " + rank);
		for (int i = 0; i < statisticsOfSolved.length; i++)
			s = s + " & " + statisticsOfSolved[i][rank];
		return s + " \\\\";
	}

	private static String getStatisticsOfUnsolved(int position) {
		String s = " & " + unsolvedNames[position];
		for (int i = 0; i < statisticsOfUnsolved.length; i++)
			s = s + " & " + statisticsOfUnsolved[i][position];
		return s + " \\\\";
	}

	// private static String totalFor(int rank) {
	// String s = (rank == -1 ? " Total & nb sol " : rank == 0 ? " & nb outs " : rank == trame[0].length + 1 ?
	// " & nb unk " : " & nb " + rank);
	// if (rank == -1)
	// for (int i = 0; i < statisticsOfSolved.length; i++) {
	// int cpt = 0;
	// for (int j = 1; j < statisticsOfSolved[i].length - 1; j++)
	// cpt += statisticsOfSolved[i][j];
	// s = s + " & " + cpt;
	// }
	// else
	// for (int i = 0; i < statisticsOfSolved.length; i++)
	// s = s + " & " + statisticsOfSolved[i][rank];
	// return s + " \\\\";
	// }

	private static void createHorizontalTable(File inFile, File outFile) throws Exception {
		BufferedReader in = new BufferedReader(new FileReader(inFile));
		PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(outFile)));
		out.println(getLatexColorDefinitionOf(GREY, 1));
		out.println(getLatexColorDefinitionOf(GREY, 2));
		for (int i = 1; i <= 3; i++) {
			out.println(getLatexColorDefinitionOf(RED, i));
			out.println(getLatexColorDefinitionOf(GREEN, i));
			out.println(getLatexColorDefinitionOf(BLUE, i));
		}
		out.println();
		if (tabular) {
			out.println("\\begin{table}");
			out.println("{\\" + FONTSIZE);
			out.println("\\begin{center}");
			out.println("\\begin{tabular}{" + columnsFormat() + "}");
			out.println(header());
		} else {
			out.println("{\\" + FONTSIZE);
			out.println("\\begin{center}");
			out.println("\\begin{longtable}{" + columnsFormat() + "}");
			out.println(header());
			out.println("\\endfirsthead");
			out.println(header());
			out.println("\\endhead");
			out.println("\\hline");
			out.println("\\endfoot");
			out.println("\\hline");
			out.println("\\endlastfoot");
		}
		String line = in.readLine();
		line = in.readLine();
		int cpt = 0;
		while (line != null) {
			if (line.trim().equals("") || line.startsWith("#"))
				line = in.readLine();
			else {
				// System.out.println(line);
				int data = cpt % trame.length;
				// if (serie == 0) out.println("\\hline");
				if (!discardLine(line, data)) {
					if (data == dataToBeAveraged)
						stats.manageNewLine(line, data, out);
					String dealtLine = dealWith(line, data);
					if (data == 0 && !CreateLatexTable.discardIndividualInstances)
						out.println("\\hline");
					out.println(dealtLine);
				} else {
					cpt += trame.length - 1;
					data = trame.length - 1;
				}
				line = (data == trame.length - 1 ? in.readLine() : line);
				cpt++;
			}
		}
		if (stats.previousLine != null) {
			stats.printProblemEasyInstances(out);
			stats.printProblemInstances(out);
		}
		out.println("\\hline");
		if (dataToBeRanked != -1 && nbSeriesOfMethods == 1) {
			out.println(getStatisticsOfSolved(0));
			if (onlyFirst)
				out.println(getStatisticsOfSolved(1));
			else {
				// out.println("\\hline");
				for (int i = 1; i <= nbMethods; i++)
					out.println(getStatisticsOfSolved(i));
				// out.println("\\hline");
			}
			out.println("\\hline");
			for (int i = 0; i < unsolvedNames.length; i++)
				out.println(getStatisticsOfUnsolved(i));
			out.println("\\hline");
		}
		if (dataToBeRanked != -1)
			stats.printEasyInstances(out);

		if (tabular) {
			out.println("\\end{tabular}");
			out.println("\\end{center}");
			out.println("}");
			out.println("\\caption{ the caption } \\label{tab:}");
			out.println("\\end{table}");
		} else {
			out.println("\\end{longtable}");
			out.println("\\end{center}");
			out.println("}");
		}
		// out.println("\\end{center}");

		in.close();
		out.close();
	}

	// private static void buildColumnnamesFrom(String line) {
	// List<String> list = new ArrayList<String>();
	// StringTokenizer st = new StringTokenizer(line);
	// st.nextToken(); //
	// while (st.hasMoreTokens()) {
	// String token = st.nextToken();
	// list.add(token.substring(0, token.indexOf(DEFAULT_SERIES[0]) - 1));
	// for (int i = 1; i < DEFAULT_SERIES.length; i++)
	// st.nextToken();
	// }
	// columnsNames = list.toArray(new String[list.size()]);
	// }

	private static File buildInFile(String inputFileName) {
		File inFile = new File(inputFileName);
		assert !inFile.isDirectory() : inputFileName + " is a directory";
		assert inFile.exists() && inFile.length() > 0 : inputFileName + " is not a file that does exist or it is empty";
		return inFile;
	}

	private static File buildOutFile(String inputFileName) {
		int position = inputFileName.lastIndexOf(".");
		String outputFileName = (position == -1 ? inputFileName : inputFileName.substring(0, position)) + ".tex";
		File outFile = new File(outputFileName);
		assert !outFile.isDirectory() : outputFileName + " is a directory";
		return outFile;
	}

	private static int[] buildIntArrayByParsing(int length, String[] ts, int startingIndex) {
		return IntStream.range(0, length).map(i -> Integer.parseInt(ts[i + startingIndex])).toArray();
	}

	// exemple :java abscon.outputs.CreateTable results.dat results.tex 1 11 4 10 9 11 1 2 3 4 5 6 7 8 0 1 2 3 no mid
	// yes 31b 31bS 32b 32bS 33b 33bS 30b 3 cpu ccks vcks nodes
	public static void main(String[] args) throws Exception {
		if (args.length == 0) {
			System.out.println("Usage: " + CreateLatexTable.class.getName()
					+ " <inputFileName> <nbVariants> <nbSeriesOfVariants> (<orderOfSeries>) <nbMetricsPerVariant> <nbSelectedMetrics> <selectedVariants> <selectedMetrics> <columnNames> (<subcolumnNames>) (<rowNames>) [prefixLength [selectionTimeLimit deadlineTime [discardInstances (0/1)]] ] ]");
			System.out.println("The usual case is to have the number of series of variants equal to 1.");
			System.out.println("For selecting methods and data, give the order (from 1) of methods and data to be selected");
			System.out.println("For selecting methods and data, give the order (from 1) of methods and data to be selected");
			return;
		}

		int cnt = 0;
		String inputFileName = args[cnt++];
		File inFile = buildInFile(inputFileName), outFile = buildOutFile(inputFileName);
		nbMethods = Integer.parseInt(args[cnt++]);
		nbSeriesOfMethods = Integer.parseInt(args[cnt++]);
		int[] orderOfSeries = null;
		if (nbSeriesOfMethods > 1) {
			orderOfSeries = buildIntArrayByParsing(nbSeriesOfMethods, args, cnt);
			cnt += nbSeriesOfMethods;
		}
		nbMetricsPerMethod = Integer.parseInt(args[cnt++]);
		nbWishedMetricsPerMethod = Integer.parseInt(args[cnt++]);
		int[] selectionOfMethods = buildIntArrayByParsing(nbMethods, args, cnt);
		cnt += nbMethods;
		System.out.println(
				"firstSelectionOfMethods = " + selectionOfMethods[0] + " lastSelectionOfMethods = " + selectionOfMethods[selectionOfMethods.length - 1]);
		int[] selectionOfData = buildIntArrayByParsing(nbWishedMetricsPerMethod, args, cnt);
		cnt += nbWishedMetricsPerMethod;
		System.out.println("firstSelectionOfData = " + selectionOfData[0] + " lastSelectionOfData = " + selectionOfData[selectionOfData.length - 1]);

		if (nbSeriesOfMethods == 1) {
			trame = new int[nbWishedMetricsPerMethod][nbMethods];
			for (int i = 0; i < trame.length; i++)
				for (int j = 0; j < trame[i].length; j++)
					trame[i][j] = 2 + (nbMetricsPerMethod * (selectionOfMethods[j] - 1)) + (selectionOfData[i] - 1);
		} else {
			trame = new int[nbSeriesOfMethods][(nbMethods / nbSeriesOfMethods) * nbWishedMetricsPerMethod];
			for (int i = 0; i < trame.length; i++)
				for (int j = 0; j < nbMethods / nbSeriesOfMethods; j++)
					for (int k = 0; k < nbWishedMetricsPerMethod; k++) {
						int column = j * nbSeriesOfMethods + (orderOfSeries[i] - 1);
						// System.out.println("column = " + column);
						trame[i][j * nbWishedMetricsPerMethod + k] = 2 + (nbMetricsPerMethod * (selectionOfMethods[column] - 1)) + (selectionOfData[k] - 1);
					}
		}

		columnsNames = new String[nbMethods / nbSeriesOfMethods];
		for (int i = 0; i < columnsNames.length; i++)
			columnsNames[i] = args[cnt++];
		System.out.println("firstColumnName = " + columnsNames[0] + " lastColumnName = " + columnsNames[columnsNames.length - 1]);
		if (nbSeriesOfMethods > 1 && nbWishedMetricsPerMethod > 1) {
			subcolumnsNames = new String[nbWishedMetricsPerMethod];
			for (int i = 0; i < subcolumnsNames.length; i++)
				subcolumnsNames[i] = args[cnt++];
		}

		if (trame.length > 1) {
			rowNames = new String[trame.length];
			for (int i = 0; i < rowNames.length; i++)
				rowNames[i] = "$" + args[cnt++] + "$";
			System.out.println("firstRowName = " + rowNames[0] + " lastRowName = " + rowNames[rowNames.length - 1]);
		}

		if (cnt < args.length)
			PREFIX_LENGTH_FOR_INSTANCES_OF_SIMILAR_PROBLEM = Integer.parseInt(args[cnt++]);
		if (cnt < args.length) {
			activateLineSelection = true;
			minimalSelectionTime = Integer.parseInt(args[cnt++]) * 1000;
		}
		if (cnt < args.length)
			deadlineTime = Integer.parseInt(args[cnt++]) * 1000;
		// System.out.println(deadlineTime);

		if (cnt < args.length)
			CreateLatexTable.discardIndividualInstances = Integer.parseInt(args[cnt++]) == 1;

		statisticsOfSolved = new int[nbMethods][nbMethods + 1];
		statisticsOfUnsolved = new int[nbMethods][unsolvedNames.length + 1];

		createHorizontalTable(inFile, outFile);
	}
}
