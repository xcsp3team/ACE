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
import java.util.StringTokenizer;

import org.xcsp.common.Constants;
import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g3_pattern.Kakuro;

public class KakuroReader extends Kakuro implements ReaderTxt {

	void data() {
		scanner(); // put here to ask the filename to the user
		String s = (String) imp().parameters.get(0).getKey();
		imp().parameters.get(0).setValue(s.contains("easy") ? "easy" : s.contains("medium") ? "medium" : "hard");
		int num = imp().askInt("num", "%03d");

		String line = null;
		for (int cnt = 0; cnt <= num; cnt++) {
			line = nextLine();
			while (line != null && !line.startsWith("data"))
				line = nextLine();
		}
		String[] toks = line.split(",");
		int nRows = Integer.parseInt(toks[3]);
		int nCols = Integer.parseInt(toks[4]);
		List<Object> clues = new ArrayList<>();
		nextLine();
		for (int i = 0; i < nRows; i++) {
			StringTokenizer st = new StringTokenizer(nextLine(), Constants.WHITE_SPACE + "[](),");
			List<Object> list = new ArrayList<>();
			for (int j = 0; j < nCols; j++) {
				String[] t = st.nextToken().split("/");
				int x = t.length == 1 ? 0 : t[1].equals("x") ? -1 : Integer.parseInt(t[1]);
				int y = t.length == 1 ? 0 : t[0].equals("x") ? -1 : Integer.parseInt(t[0]);
				list.add(buildInternClassObject("Clue", x, y));
			}
			clues.add(Utilities.convert(list));
		}
		setDataValues(nRows, nCols, clues);
	}
}
