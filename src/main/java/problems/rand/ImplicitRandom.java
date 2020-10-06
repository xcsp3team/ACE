/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.rand;

import java.util.Random;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.intension.CtrHardRandomImplicit;
import problem.Problem;
import tools.random.RandomGeneration.RandomGenerationProp;
import tools.random.RandomGeneration.RandomGenerationProp.TypeList;
import variables.Variable;

/**
 * This class corresponds to implicit random problems, i.e., random problems such that constraints are defined by a predicate as described in: <br>
 * [Lecoutre, Boussemart et Hemery, 03, Implicit Random CSPs, ICTAI'03].
 */
public class ImplicitRandom implements ProblemAPI {

	int n, d, e, r;
	int tightness, seed;
	int macroType;
	boolean repetition, sat;
	String algorithm;

	@Override
	public void model() {
		Random random = sat ? new Random(seed) : null;
		int[] solution = sat ? IntStream.range(0, n).map(i -> random.nextInt(d)).toArray() : null;

		Var[] x = array("x", size(n), dom(range(d)));

		for (int[] scopes : new RandomGenerationProp(n, r, seed).selectSets(e, TypeList.get(macroType), repetition)) {
			Var[] scope = variablesFrom(scopes, i -> x[i]);
			int[] tuple = sat ? valuesFrom(scopes, i -> solution[i]) : null;
			((Problem) imp()).addCtr(new CtrHardRandomImplicit(((Problem) imp()), (Variable[]) scope, (byte) (tightness - 128),
					((Problem) imp()).rs.instanceNumber, algorithm, tuple));
		}
	}

}
