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
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.Fapp;
import utility.Kit;

// noGroupAtAllForExtension must be set to true in Compiler ; uncompactDomainFor must be set to true too
// otherwise it is too inefficient
public class FappReader extends Fapp implements ReaderTxt {

	void data() {
		// loading domains
		Map<Integer, List<Integer>> map = new HashMap<>();
		while (scanner().hasNext("DM")) {
			next();
			int numDom = nextInt(), value = nextInt();
			map.computeIfAbsent(numDom, k -> new ArrayList<>()).add(value);
		}
		int highest = map.keySet().stream().mapToInt(i -> i).max().getAsInt();
		Utilities.control(map.keySet().stream().allMatch(v -> 0 <= v && v <= highest), "Strange");
		int[][] domains = new int[highest + 1][];
		for (int k : map.keySet())
			domains[k] = map.get(k).stream().mapToInt(i -> i).toArray();

		// Map<Integer, int[]> domains = map.entrySet().stream().collect(Collectors.toMap(e -> e.getKey(), e ->
		// Kit.sort(Kit.intArray(e.getValue()))));
		// loading variables
		boolean zeroMode = false;
		List<int[]> list = new ArrayList<>();
		while (scanner().hasNext("TR")) {
			next();
			int numVar = nextInt(), numDom = nextInt();
			int polarisation = nextInt();
			if (list.size() == 0) {
				Kit.control(numVar == 0 || numVar == 1);
				zeroMode = numVar == 0;
			} else
				Kit.control(numVar == list.size() + (!zeroMode ? 1 : 0));
			list.add(new int[] { numVar, numDom, polarisation });
		}
		Utilities.control(zeroMode, "");
		Stream<Object> routes = list.stream().map(t -> buildInternClassObject("Route", t[1], t[2]));

		// loading constraints
		List<int[]> listCI = new ArrayList<>(), listCE = new ArrayList<>(), listCD = new ArrayList<>();
		while (scanner().hasNext()) {
			String s = next();
			if (s.equals("CI"))
				listCI.add(new int[] { nextInt(), nextInt(), next().equals("F") ? 1 : 0, next().equals("E") ? 1 : 0, nextInt() });
			else if (s.equals("CE"))
				listCE.add(IntStream.range(0, 13).map(i -> nextInt()).toArray());
			else
				listCD.add(IntStream.range(0, 13).map(i -> nextInt()).toArray());
		}
		Stream<Object> hards = listCI.stream().map(t -> buildInternClassObject("HardCtr", t[0], t[1], t[2] == 1, t[3] == 1, t[4]));

		int[][] ctrsCE = listCE.stream().toArray(int[][]::new), ctrsCD = listCD.stream().toArray(int[][]::new);
		Kit.control(ctrsCE.length == ctrsCD.length
				&& IntStream.range(0, ctrsCE.length).allMatch(i -> ctrsCE[i][0] == ctrsCD[i][0] && ctrsCE[i][1] == ctrsCD[i][1]));
		Stream<Object> softs = IntStream.range(0, ctrsCE.length).mapToObj(i -> buildInternClassObject("SoftCtr", ctrsCE[i][0], ctrsCE[i][1],
				Arrays.copyOfRange(ctrsCE[i], 2, ctrsCE[i].length), Arrays.copyOfRange(ctrsCD[i], 2, ctrsCD[i].length)));
		setDataValues(domains, routes, hards, softs);
	}
}
