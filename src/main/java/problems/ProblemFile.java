/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.modeler.api.ProblemAPI;

import dashboard.Arguments;
import problem.Problem;

/**
 * Such a problem is one defined from a file (specified by the user as a parameter). It is then necessary to parse the data contained in the file.
 */
public abstract class ProblemFile implements ProblemAPI {
	private List<String> listOfFileNames; // Pb for making it static (see this with ProblemXCSPTest)

	protected String currFileName() {
		return listOfFileNames.get(((Problem) imp()).rs.instanceNumber);
	}

	private List<String> collect(List<String> list, File f) {
		if (f.isDirectory())
			Stream.of(f.listFiles()).forEach(g -> collect(list, g));
		else if (Stream.of(defineSuffixFilters()).anyMatch(suf -> f.getName().endsWith(suf)))
			list.add(f.getAbsolutePath());
		return list;
	}

	public void data() {
		String fileName = imp().askString("File or directory:");
		if (listOfFileNames == null) {
			listOfFileNames = collect(new ArrayList<>(), new File(fileName)).stream().sorted().collect(Collectors.toList());
			// Arrays.sort(listOfFileNames);
			Arguments.nInstancesToSolve = listOfFileNames.size();
		}
		((Problem) imp()).parameters.get(0).setValue(currFileName());
		((Problem) imp()).rs.cp.framework = TypeFramework.CSP;
		((Problem) imp()).rs.cp.setingGeneral.framework = TypeFramework.CSP;
		((Problem) imp()).framework = TypeFramework.CSP;
		System.out.println();
	}

	protected abstract String[] defineSuffixFilters();

	@Override
	public String name() {
		return currFileName();
	}
}