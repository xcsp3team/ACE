/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.stream.Stream;

import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.Rlfap;
import utility.Kit;

public class RlfapReader extends Rlfap implements ReaderTxt {

	void data() {
		String path = imp().askString("path", p -> "");
		int type = imp().askInt("type (0 = Scen ; 1 = Graph ; 2 = Scen06-sub ; 3 = Scen07-sub)", range(4),
				t -> t == 3 ? "scen07-sub" : t == 2 ? "scen06-sub" : t == 1 ? "graph" : "scen");
		int number = imp().askInt("number", range(100), n -> "%02d");
		String prefix = path + File.separatorChar + (type == 3 ? "scen07-sub" : type == 2 ? "scen06-sub" : type == 1 ? "graph" : "scen")
				+ (type < 2 && number < 10 ? "0" : "") + number;

		Map<Integer, int[]> map = new HashMap<>();
		try (Scanner scanner = new Scanner(new File(prefix + ".dom.txt"))) {
			int[] t = Utilities.splitToInts(scanner.nextLine()); // first dummy line
			if (t[0] != 0)
				map.put(t[0], Arrays.copyOfRange(t, 2, t.length)); // for subs instances
			while (scanner.hasNextLine()) {
				t = Utilities.splitToInts(scanner.nextLine()); // t[0] is domain num, t[1] is domain card
				map.put(t[0], Arrays.copyOfRange(t, 2, t.length));
			}
		} catch (IOException e) {
			Kit.exit("Problem with file " + prefix + ".dom.txt", e);
		}
		int highest = map.keySet().stream().mapToInt(i -> i).max().getAsInt();
		Utilities.control(map.keySet().stream().allMatch(v -> 0 <= v && v <= highest), "Strange");
		int[][] domains = new int[highest + 1][];
		for (int k : map.keySet())
			domains[k] = map.get(k); // .stream().mapToInt(i -> i).toArray();

		List<int[]> listv = new ArrayList<>();
		readFileLines(prefix + ".var.txt", s -> Utilities.splitToInts(s)).forEach(t -> listv.add(t));
		Stream<Object> vars = listv.stream()
				.map(t -> buildInternClassObject("RlfapVar", t[1], t.length < 3 ? null : t[2], t.length < 3 ? null : t.length == 3 ? 0 : t[3]));

		Map<Integer, Integer> mapVars = new HashMap<>();
		for (int i = 0; i < listv.size(); i++)
			mapVars.put(listv.get(i)[0], i);

		List<int[]> listc = new ArrayList<>();
		readFileLines(prefix + ".ctr.txt", s -> s.split("\\s+")).forEach(tt -> {
			int[] t = new int[6];
			t[0] = mapVars.get(Integer.parseInt(tt[0])); // num of x
			t[1] = mapVars.get(Integer.parseInt(tt[1])); // num of y
			t[2] = (tt[2].charAt(0) - 'A'); // useless field
			t[3] = tt[3].charAt(0) == '>' ? 1 : 0; // operator (0 is = and 1 is >)
			t[4] = Integer.parseInt(tt[4]); // limit
			t[5] = tt.length == 6 ? Integer.parseInt(tt[5]) : 0; // weight
			listc.add(t);
		});
		Stream<Object> ctrs = listc.stream().map(t -> buildInternClassObject("RlfapCtr", t[0], t[1], t[3] == 0 ? "=" : ">", t[4], t[5]));

		int[] interferenceCosts = { 0, 1000, 100, 10, 1 }; // default values, but can be overridden // for a1 to a4
		int[] mobilityCosts = { 0, 1000, 100, 10, 1 }; // default values, but can be overridden // for b1 to b4
		readFileLines(prefix + ".cst.txt", s -> s.split("\\s+")).forEach(t -> {
			if (t[0].charAt(0) == 'a')
				interferenceCosts[Integer.parseInt(t[0].substring(1))] = Integer.parseInt(t[2]);
			if (t[0].charAt(0) == 'b')
				mobilityCosts[Integer.parseInt(t[0].substring(1))] = Integer.parseInt(t[2]);
		});

		setDataValues(domains, vars, ctrs, interferenceCosts, mobilityCosts);
	}
}