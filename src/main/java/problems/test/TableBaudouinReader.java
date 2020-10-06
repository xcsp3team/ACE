/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.test;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.extension.structures.SmartTuple;
import utility.Kit;

public class TableBaudouinReader implements ProblemAPI {
	int nVars;
	int[][] bounds;
	int[][] tuples;

	void data() {
		String fileName = imp().askString("Instance filename");
		try {
			if (fileName.endsWith(".lzma")) {
				Process p = Runtime.getRuntime().exec("lzma -d " + fileName);
				p.waitFor();
				p.exitValue();
				p.destroy();
				fileName = fileName.substring(0, fileName.indexOf(".lzma"));
				System.out.println("Test " + fileName);
			}
		} catch (Exception e) {
			Kit.exit("Pb when loading file", e);
		}

		try (Scanner scanner = new Scanner(new File(fileName))) {
			nVars = scanner.nextInt();
			scanner.next();
			bounds = IntStream.range(0, nVars).mapToObj(i -> {
				scanner.next();
				return Stream.of(scanner.next().split("\\.\\.")).mapToInt(tok -> Integer.parseInt(tok)).toArray();
			}).toArray(int[][]::new);
			int nTuples = scanner.nextInt();
			scanner.next();
			tuples = range(nTuples).range(nVars).map((i, j) -> scanner.nextInt());
			// System.out.println("Bounds=" + Kit.join(bounds));
			// System.out.println("Tuples=" + Kit.join(tuples));
		} catch (FileNotFoundException e) {
			Kit.exit("File " + fileName + " not found \n", e);
		}
	}

	@SuppressWarnings("unused")
	private SmartTuple translate(IVar.Var[] x, String[] s) {
		List<XNodeParent<? extends IVar>> restrictions = new ArrayList<>();
		for (int i = 0; i < s.length; i++) {
			String tok = s[i].trim();
			if (tok.equals("*"))
				continue;
			String[] t = tok.split(Constants.REG_WS);
			Object rop = t[1].startsWith("x") ? x[Integer.parseInt(t[1].substring(1))] : Integer.parseInt(t[1]);
			TypeExpr op = null;
			if (t[0].equals("<"))
				op = TypeExpr.LT;
			if (t[0].equals("["))
				op = TypeExpr.LE;
			if (t[0].equals("]"))
				op = TypeExpr.GE;
			if (t[0].equals(">"))
				op = TypeExpr.GT;
			if (t[0].equals("#"))
				op = TypeExpr.NE;
			if (t[0].equals("="))
				op = TypeExpr.EQ;
			restrictions.add(XNodeParent.build(op, x[i], rop));
		}
		return new SmartTuple(restrictions);
	}

	@Override
	public void model() {
		Var[] x = array("x", size(nVars), i -> dom(rangeClosed(bounds[i][0], bounds[i][1])));

		if (modelVariant("tab"))
			extension(x, tuples);
		// if (isModel("smt")) {
		// int[][] domains = IntStream.range(0, nVars).mapToObj(i -> range(bounds[i][0], bounds[i][1]).toArray()).toArray(int[][]::new);
		// String[][] cts = ThanV14.compressTuples(domains, tuples);
		// System.out.println("\n" + Kit.join(cts));
		// SmartTuple[] sts = IntStream.range(0, cts.length).mapToObj(i -> translate(x, cts[i])).toArray(SmartTuple[]::new);
		// ((Problem) imp()).smart(x, sts);
		// }

	}
}