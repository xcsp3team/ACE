/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.util.ArrayList;
import java.util.List;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.PseudoBoolean;

public class PseudoBoolean_Parser extends PseudoBoolean implements ReaderTxt {

	private Object buildLinearObj(String line) {
		String[] toks = line.split("\\s+");
		Utilities.control(toks.length % 2 == 0 && toks[0].equals("min:") && toks[toks.length - 1].equals(";"), "");
		int r = toks.length / 2 - 1;
		int[] coeffs = valuesFrom(range(r), i -> Integer.parseInt(toks[1 + i * 2]));
		int[] nums = valuesFrom(range(r), i -> Integer.parseInt(toks[1 + i * 2 + 1].substring(1)) - 1); // 1 because prefixed by x ; -1 for starting
																										// at 0
		return buildInternClassObject("LinearObj", coeffs, nums);
	}

	private Object buildLinearCtr(String line) {
		String[] toks = line.split("\\s+");
		Utilities.control(toks.length % 2 == 1 && toks[toks.length - 1].equals(";"), "");
		int r = toks.length / 2 - 1;
		int[] coeffs = valuesFrom(range(r), i -> Integer.parseInt(toks[i * 2]));
		int[] nums = valuesFrom(range(r), i -> Integer.parseInt(toks[i * 2 + 1].substring(1)) - 1); // 1 because prefixed by x ; -1 for starting at 0
		String op = toks[toks.length - 3]; // .charAt(0) == '=' ? TypeConditionOperatorRel.EQ : TypeConditionOperatorRel.GE;
		int limit = Integer.parseInt(toks[toks.length - 2]);
		return buildInternClassObject("LinearCtr", coeffs, nums, op, limit);
	}

	void data() {
		String line = nextLine();
		int[] t = Utilities.splitToInts(line, "\\*\\s#variable=\\s?|\\s#constraint=\\s?");
		int n = t[0], e = t[1];
		line = nextLine();
		while (line != null && line.charAt(0) == '*')
			line = nextLine();
		Object obj = line.charAt(0) == 'm' ? buildLinearObj(line) : null;
		List<Object> ctrs = new ArrayList<>();
		if (obj == null)
			ctrs.add(buildLinearCtr(line));
		while (hasNextLine()) {
			line = nextLine();
			if (line.charAt(0) != '*')
				ctrs.add(buildLinearCtr(line));
		}
		Utilities.control(e == ctrs.size(), "Pb when parsing");
		setDataValues(n, e, ctrs, obj);
	}
}
