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
import java.util.StringTokenizer;

import utility.Kit;

public class CreateCactusDataFile {

	private static File buildInFile(String inFileName) {
		File inFile = new File(inFileName);
		assert !inFile.isDirectory() : inFileName + " is a directory";
		assert inFile.exists() && inFile.length() > 0 : inFileName + " is not an existing file or it is empty";
		return inFile;
	}

	private static File buildOutFile(String outFileName) {
		int position = outFileName.lastIndexOf(".");
		String outputFileName = (position == -1 ? outFileName : outFileName.substring(0, position)) + ".cactus.dat";
		File outFile = new File(outputFileName);
		assert !outFile.isDirectory() : outputFileName + " is a directory";
		return outFile;
	}

	public static void main(String[] args) throws Exception {
		if (args.length != 6) {
			System.out.println(
					"Usage: " + CreateCactusDataFile.class.getName() + " <inputFileName> <rangeMax> <rangeDelta> <nbMetrics> <posMetric> <factorMetric>");
			System.out.println("\tFor example, java tools.output.CreateCactusDataFile Data results.dat 1200 1 6 1 1000\n"
					+ "\tfor the range 0..1200 every step of 1, on the basis of a file with 6 metrics per method\n"
					+ "\tthe position of the selected metric being  the first one, and the metric being divided by the factor 1000 ");
			return;
		}
		String inputFileName = args[0];
		try (BufferedReader in = new BufferedReader(new FileReader(buildInFile(inputFileName)));
				PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(buildOutFile(inputFileName))));) {
			int rangeMax = Integer.parseInt(args[1]);
			int rangeDelta = Integer.parseInt(args[2]);
			int nbMetrics = Integer.parseInt(args[3]);
			int posMetric = Integer.parseInt(args[4]);
			int factorMetric = Integer.parseInt(args[5]);

			StringTokenizer st = new StringTokenizer(in.readLine());
			int nbMethods = (st.countTokens() - 1) / nbMetrics;
			st.nextToken(); // skip first column
			String[] heads = new String[nbMethods];
			for (int idMethod = 0; idMethod < heads.length; idMethod++)
				for (int idMetric = 1; idMetric <= nbMetrics; idMetric++) {
					String token = st.nextToken();
					if (idMetric == posMetric)
						heads[idMethod] = token;
				}
			int[][] cnts = new int[rangeMax / rangeDelta + 1][nbMethods];
			for (String line = in.readLine(); line != null; line = in.readLine()) {
				st = new StringTokenizer(line);
				st.nextToken(); // skip first column
				for (int idMethod = 0; idMethod < cnts[0].length; idMethod++)
					for (int idMetric = 1; idMetric <= nbMetrics; idMetric++) {
						String token = st.nextToken();
						if (idMetric == posMetric && Double.parseDouble(token) >= 0) {
							int first = (int) (Math.ceil(Double.parseDouble(token) / (factorMetric * rangeDelta)));
							for (int i = first; i < cnts.length; i++)
								cnts[i][idMethod]++;
						}
					}
			}
			out.println("range " + Kit.join(heads));
			for (int i = 0; i < cnts.length; i++)
				out.println(i + " " + Kit.join(cnts[i]));
		} catch (Exception e) {
			System.exit(1);
		}
	}
}