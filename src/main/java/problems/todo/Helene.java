/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.modeler.api.ProblemAPI;

import utility.Kit;
import variables.VariableSymbolic;

public class Helene implements ProblemAPI {

	String fileName = imp().askString("Instance filename");

	Map<Integer, String[]> mapOfDomains; // the domain of each variable (key = variable name; given as an integer)

	void data() {
		Map<Integer, Set<String>> map = new TreeMap<>();
		try (BufferedReader in = new BufferedReader(new FileReader(fileName))) {
			String line;
			for (line = in.readLine().trim(); !line.startsWith("CSP-CONTRAINTES"); line = in.readLine().trim())
				;
			for (line = in.readLine().trim(); line.length() == 0; line = in.readLine().trim())
				;
			for (StringTokenizer st = new StringTokenizer(line, "O=[]," + Constants.WHITE_SPACE); st.hasMoreTokens();)
				map.put(Integer.parseInt(st.nextToken()), new TreeSet<>());
			while (true) {
				for (line = in.readLine().trim(); line != null && line.length() == 0; line = in.readLine().trim())
					;
				if (line == null || line.startsWith("FINCSP"))
					break;
				assert line.startsWith("CONTRAINTE") : "Pb with " + line;
				String[] scope = Kit.split(new StringTokenizer(in.readLine().trim(), "V=[]," + Constants.WHITE_SPACE));
				for (line = in.readLine().trim(); !line.startsWith("FINCONT"); line = in.readLine().trim()) {
					String[] tokens = line.split(Constants.REG_WS);
					for (int i = 0; i < scope.length; i++)
						map.get(Integer.parseInt(scope[i])).add(tokens[i]);
				}
			}
			mapOfDomains = map.entrySet().stream().collect(Collectors.toMap(e -> e.getKey(), e -> e.getValue().toArray(new String[0])));
		} catch (Exception e) {
			Kit.exit(e);
		}
	}

	@Override
	public void model() {
		Map<String, IVar.VarSymbolic> mapOfVariables = mapOfDomains.entrySet().stream().filter(e -> e.getValue().length > 0)
				.collect(Collectors.toMap(e -> "" + e.getKey(), e -> var(String.format("x%03d", e.getKey()), dom(e.getValue()))));

		try (BufferedReader in = new BufferedReader(new FileReader(fileName))) {
			String line;
			for (line = in.readLine().trim(); !line.startsWith("CSP-CONTRAINTES"); line = in.readLine().trim())
				;
			for (line = in.readLine().trim(); line.length() == 0; line = in.readLine().trim())
				;
			while (true) {
				for (line = in.readLine().trim(); line != null && line.length() == 0; line = in.readLine().trim())
					;
				if (line == null || line.startsWith("FINCSP"))
					break;
				assert line.startsWith("CONTRAINTE") : "Pb with " + line;
				VariableSymbolic[] scope = Stream.of(Kit.split(new StringTokenizer(in.readLine().trim(), "V=[]," + Constants.WHITE_SPACE)))
						.map(s -> mapOfVariables.get(s)).toArray(VariableSymbolic[]::new);
				List<String[]> list = new ArrayList<>();
				for (line = in.readLine().trim(); !line.startsWith("FINCONT"); line = in.readLine().trim())
					list.add(line.split(Constants.REG_WS));
				extension(scope, list.toArray(new String[list.size()][]));
			}
		} catch (Exception e) {
			Kit.exit(e);
		}
	}
}