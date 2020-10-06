/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Scanner;
import java.util.stream.IntStream;

import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.entities.CtrEntities.CtrEntity;

import utility.Kit;
import variables.VariableInteger;

public class FappCSP implements ProblemAPI {

	String fileName = imp().askString("instanceFileName");
	int relaxationLevel = imp().askInt("Relaxation level (from 0 to 10) : ", range(11));

	boolean zeroMode;
	Map<Integer, int[]> dataDoms;
	int[][] dataVars;
	int[][] ctrsCI, ctrsCE, ctrsCD;
	boolean standAlone = false;

	Map<Integer, int[]> loadDomains(Scanner scanner) {
		Map<Integer, List<Integer>> map = new HashMap<>();
		while (scanner.hasNext("DM")) {
			scanner.next();
			int id = scanner.nextInt(), value = scanner.nextInt();
			List<Integer> list = map.get(id);
			if (list == null)
				map.put(id, list = new ArrayList<>());
			list.add(value);
		}
		Map<Integer, int[]> domains = new HashMap<>();
		for (Entry<Integer, List<Integer>> e : map.entrySet())
			domains.put(e.getKey(), Kit.sort(Kit.intArray(e.getValue())));
		return domains;
	}

	int[][] loadVariables(Scanner scanner) {
		List<int[]> list = new ArrayList<>();
		while (scanner.hasNext("TR")) {
			scanner.next();
			int id = scanner.nextInt();
			int domainId = scanner.nextInt();
			int polarisation = scanner.nextInt();
			if (list.size() == 0) {
				Kit.control(id == 0 || id == 1);
				zeroMode = id == 0;
			} else
				Kit.control(id == list.size() + (!zeroMode ? 1 : 0));
			list.add(new int[] { id, domainId, polarisation });
		}
		return Kit.intArray2D(list);
	}

	void loadConstraints(Scanner scanner) {
		List<int[]> listCI = new ArrayList<>(), listCE = new ArrayList<>(), listCD = new ArrayList<>();
		while (scanner.hasNext()) {
			String s = scanner.next();
			if (s.equals("CI"))
				listCI.add(new int[] { scanner.nextInt(), scanner.nextInt(), scanner.next().equals("F") ? 1 : 0, scanner.next().equals("E") ? 1 : 0, scanner
						.nextInt() });
			else if (s.equals("CE"))
				listCE.add(IntStream.range(0, 13).map(i -> scanner.nextInt()).toArray());
			else
				listCD.add(IntStream.range(0, 13).map(i -> scanner.nextInt()).toArray());

		}
		ctrsCI = Kit.intArray2D(listCI);
		ctrsCE = Kit.intArray2D(listCE);
		ctrsCD = Kit.intArray2D(listCD);
	}

	void data() {
		try (Scanner scanner = new Scanner(new File(fileName))) {
			dataDoms = loadDomains(scanner);
			dataVars = loadVariables(scanner);
			loadConstraints(scanner);
		} catch (IOException e) {
			Kit.exit("Erreur ouverture fichier " + fileName, e);
		}
	}

	int[] buildDomain(int[] frequencies, int polarisation) {
		int[] domain = new int[(polarisation == 0 ? 2 : 1) * frequencies.length];
		if (polarisation < 1)
			for (int i = 0; i < frequencies.length; i++)
				domain[i] = -frequencies[i];
		if (polarisation > -1) {
			int gap = (polarisation == 0 ? frequencies.length : 0);
			for (int i = 0; i < frequencies.length; i++)
				domain[i + gap] = frequencies[i];
		}
		return domain;
	}

	private CtrEntity buildImperativeCtr(Var[] m, int[] t) {
		Var x = m[t[0] + (!zeroMode ? -1 : 0)], y = m[t[1] + (!zeroMode ? -1 : 0)];
		boolean frequencyType = t[2] == 1, equalityType = t[3] == 1;
		int gap = t[4];
		XNodeParent<IVar> predicate;
		if (frequencyType && equalityType && gap == 0)
			predicate = eq(abs(x), abs(y));
		else if (frequencyType && !equalityType && gap == 0)
			predicate = ne(abs(x), abs(y));
		else if (frequencyType && equalityType && gap != 0)
			predicate = eq(dist(abs(x), abs(y)), gap);
		else if (frequencyType && !equalityType && gap != 0)
			predicate = ne(dist(abs(x), abs(y)), gap);
		else if (!frequencyType && equalityType && gap == 0)
			predicate = ge(mul(x, y), 0);
		else if (!frequencyType && !equalityType && gap == 0)
			predicate = le(mul(x, y), 0);
		else
			throw new IllegalArgumentException();
		return intension(predicate);
	}

	private CtrEntity buildRadioCompatibilityCtrWithPolarization(Var[] m, int[] t, int relaxationLevel, boolean equalPolarization) {
		Var x = m[t[0] + (!zeroMode ? -1 : 0)], y = m[t[1] + (!zeroMode ? -1 : 0)];
		int gap = t[2 + relaxationLevel];
		XNodeParent<IVar> predicate = equalPolarization ? or(lt(mul(x, y), "0"), ge(abs(sub(x, y)), gap))
				: or(gt(mul(x, y), "0"), ge(abs(sub(abs(x), abs(y))), gap));
		return intension(predicate);
	}

	@Override
	public void model() {
		Var[] m = standAlone ? IntStream.range(0, dataVars.length).mapToObj(i -> var("x" + i, dom(buildDomain(dataDoms.get(dataVars[i][1]), dataVars[i][2]))))
				.toArray(VariableInteger[]::new) : array("x", size(dataVars.length), i -> dom(buildDomain(dataDoms.get(dataVars[i][1]), dataVars[i][2])));
		// Kit.control(IntStream.range(0, m.length).noneMatch(i -> i != m[i].num), () -> "pb");

		forall(range(ctrsCI.length), i -> buildImperativeCtr(m, ctrsCI[i]));
		forall(range(ctrsCE.length), i -> buildRadioCompatibilityCtrWithPolarization(m, ctrsCE[i], relaxationLevel, true));
		forall(range(ctrsCD.length), i -> buildRadioCompatibilityCtrWithPolarization(m, ctrsCD[i], relaxationLevel, false));
	}
}
