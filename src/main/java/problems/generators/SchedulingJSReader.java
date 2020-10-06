/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.Scanner;
import java.util.StringTokenizer;
import java.util.stream.IntStream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.SchedulingJS;
import utility.Kit;

public class SchedulingJSReader extends SchedulingJS implements ReaderTxt {

	// java abscon.Resolution problems.generators.SchedulingJSReader\$Sadeh sadeh/instances/enddr2-10-by-5-4
	public static class Sadeh extends SchedulingJSReader {

		private int extractIntegerFromSecondTokenIn(String line) {
			return Integer.parseInt(line.split("\\s*\\(\\s*[-\\w]+\\s+|\\s*\\)\\s*")[1]);
		}

		private void skipLines(int nLines) {
			for (int i = 0; i < nLines; i++)
				nextLine();
		}

		void data() {
			int n = 10, m = 5;
			int[] relDates = new int[n], dueDates = new int[n];
			int[][] durations = new int[n][m], resources = new int[n][m];

			skipLines(3);
			for (int i = 0; i < n; i++) {
				nextLine();
				dueDates[i] = extractIntegerFromSecondTokenIn(nextLine());
				relDates[i] = extractIntegerFromSecondTokenIn(nextLine());
				skipLines(4);
				for (int j = 0; j < m - 1; j++) {
					StringTokenizer st = new StringTokenizer(nextLine(), " ()");
					st.nextToken();
					Kit.control(Integer.parseInt(st.nextToken().charAt(9) + "") == j && Integer.parseInt(st.nextToken().charAt(9) + "") == j + 1);
				}
				Kit.control(nextLine().trim().equals(")"));
				for (int j = 0; j < m; j++) {
					nextLine();
					durations[i][j] = extractIntegerFromSecondTokenIn(nextLine());
					skipLines(2);
					StringTokenizer st = new StringTokenizer(nextLine(), " ()");
					st.nextToken();
					resources[i][j] = Integer.parseInt(st.nextToken().charAt(8) + "");
					skipLines(2);
				}
				nextLine();
			}
			Object jobs = Utilities
					.convert(IntStream.range(0, n).mapToObj(i -> buildInternClassObject("Job", durations[i], resources[i], relDates[i], dueDates[i])));
			setDataValues(jobs);
		}
	}

	public static class Taillard extends SchedulingJSReader {
		void data() {
			Scanner scanner = scanner();
			int num = imp().askInt("num", range(10));
			IntStream.rangeClosed(0, num).forEach(i -> scanner.findWithinHorizon("ower bound", 0));
			nextLine(); // to skip the rest of the line
			int n = nextInt(); // nJobs
			int m = nextInt(); // nOperations and nMachines
			nextLong(); // time seed, not used here
			nextLong(); // machine seed
			nextInt(); // ub
			nextInt(); // lb
			nextLine();
			nextLine();
			int[][] durations = range(n).range(m).map((i, j) -> nextInt());
			nextLine();
			nextLine();
			int[][] resources = range(n).range(m).map((i, j) -> nextInt() - 1); // -1 for starting machine id at 0
			Object jobs = Utilities.convert(IntStream.range(0, n).mapToObj(i -> buildInternClassObject("Job", durations[i], resources[i], 0, -1)));
			setDataValues(jobs);
		}
	}

	public static class PaperIJCAI extends SchedulingJSReader {
		void data() {
			int n = nextInt(); // nJobs
			int m = nextInt(); // nOperations and nMachines
			int[][] t = range(n).range(m * 2).map((i, j) -> nextInt());
			System.out.println(n + " " + m);
			System.out.println("t " + Kit.join(t));

			// int[][] resources = range(n).range(m).map((i, j) -> nextInt() - 1); // -1 for starting machine id at 0
			Object jobs = Utilities.convert(IntStream.range(0, n)
					.mapToObj(i -> buildInternClassObject("Job", selectFromIndexing(t[i], j -> j % 2 == 1), selectFromIndexing(t[i], j -> j % 2 == 0), 0, -1)));
			setDataValues(jobs);
		}
	}
}
