/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.rand;

import java.text.DecimalFormat;
import java.util.Random;
import java.util.function.Predicate;
import java.util.stream.IntStream;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import constraints.Constraint;
import constraints.hard.CtrExtension;
import problem.Problem;
import tools.random.RandomGeneration.RandomGenerationProb;
import tools.random.RandomGeneration.RandomGenerationProp;
import tools.random.RandomGeneration.RandomGenerationProp.TypeList;
import utility.Kit;
import variables.Variable;

/**
 * This class allows us to build to random instances with constraints defined in extension.
 */
public final class ExplicitRandomQuestion implements ProblemAPI {
	@Override
	public String name() {
		String s = "rand-" + r + "-" + n + "-" + d + "-" + e;
		// + (((Problem) imp()).rs.cp.extension.wcnConversion != EWCNConversion.NO ? "-" + ((Problem) imp()).rs.cp.optimizing.upperBound : "");
		if (mode == 1) {
			s += "-t" + new DecimalFormat("000").format(Math.round(tightness * 100));
			double pd = Math.pow(d, r);
			s += "-" + (tightness < (1 - tightness) ? "n" + Math.round(pd * tightness) : "p" + Math.round(pd * (1 - tightness)));
		} else if (mode == 2) {
			long t = Math.round(1000 * tightness);
			s += "-" + (t < 100 ? "0" : "") + t;
		} else
			s += "-" + Math.round(tightness);
		return s + (sat ? "-fcd" : "") + "-" + seed; // + "-" + "t" + new DecimalFormat("000").format(Math.round(tightness *100)) +
														// "t";
	}

	int n, d, e, r;
	int mode;
	double tightness;
	int seed;
	TypeList macroType, microType;
	boolean repetition, sat, sameRels;

	int nKernels;
	int nK, dK, eK, rK;
	int modeK;
	double tightnessK;
	TypeList macroTypeK, microTypeK;

	int nLinks;
	int modeL;
	double tightnessL;

	void data() {
		String tightnessMessage = "Tightness Mode\n  0 : tightness= nb of no goods \n  1 : tightness = proportion of no goods "
				+ "\n  2 : tightness = probability of no goods (real value between 0 and 1) \n  3 : tightness = probability of no goods (integer value between 1 and 255)"
				+ "\n  4 : tightness= nb of supports \n Your choice: ";
		String graphMessage = "  0 : unstructured \n  1 : connected \n  2 : balanced \nYour choice : ";

		n = imp().askInt("nb variables");
		d = imp().askInt("domain size");
		e = imp().askInt("nb constraints");
		r = imp().askInt("arity");
		mode = imp().askInt(tightnessMessage, range(5));
		tightness = imp().askDouble("tightness");
		seed = imp().askInt("seed");
		macroType = TypeList.get(imp().askInt("Constraint Graph Type\n" + graphMessage, range(3)));
		microType = TypeList.get(imp().askInt("Incompatibility Graph Type\n" + graphMessage, range(3)));
		repetition = imp().askBoolean("Possibility of generating several constraints with same signature (yes/no) : ");
		sat = imp().askBoolean("Generation of forced satisfiable instances (yes/no) : ");
		sameRels = imp().askBoolean("Share relations between constraints (yes/no) : ");
		// Kit.control(!sameRels || ((Problem) imp()).rs.cp.extension.wcnConversion == EWCNConversion.NO);

		nKernels = imp().askInt("nbKernels", (Predicate<Integer>) k -> k == 0 || sat == false);
		Kit.control(!sat || nKernels == 0);
		nK = nKernels > 0 ? imp().askInt("nb variables (for kernels)") : 0;
		dK = nKernels > 0 ? imp().askInt("domain size (for kernels)") : 0;
		eK = nKernels > 0 ? imp().askInt("nb constraints (for kernels)") : 0;
		rK = nKernels > 0 ? imp().askInt("arity (for kernels)") : 0;
		modeK = nKernels > 0 ? imp().askInt("tightness mode (for kernels)") : 0;
		tightnessK = nKernels > 0 ? imp().askDouble("tightness -for kernels)") : 0;
		macroTypeK = TypeList.get(nKernels > 0 ? imp().askInt("constraint Graph Type (for kernels)") : 0);
		microTypeK = TypeList.get(nKernels > 0 ? imp().askInt("incompatibility Graph Type (for kernels)") : 0);

		nLinks = nKernels > 0 ? imp().askInt("Nb of links between kernels : ") : 0;
		modeL = nKernels > 0 && nLinks > 0 ? imp().askInt("tightness Mode (for links)") : 0;
		tightnessL = nKernels > 0 && nLinks > 0 ? imp().askDouble("tightness (for links)") : 0;
	}

	@NotData
	Random random = new Random(seed);

	@NotData
	public int[] forcedSolution;

	// introduced as fields for enabling sharing
	@NotData
	boolean positive;

	@NotData
	int[][] tuples;

	private Constraint buildExplicitConstraint(Variable[] scope, int tnessMode, double tightness, long seed, TypeList microType, int[] requiredSupport) {
		int[] nValues = Variable.domSizeArrayOf(scope, true);
		if (tnessMode == 0 || tnessMode == 1) {
			double nConflicts = tnessMode == 0 ? tightness : Variable.nValidTuplesBoundedAtMaxValueFor(scope) * tightness;
			double nSupports = Utilities.nArrangementsFor(nValues).doubleValue() - nConflicts;
			// System.out.println(" NBco=" + nConflicts + " nbSu=" + nSupports);

			Kit.control(nSupports <= Integer.MAX_VALUE || nConflicts <= Integer.MAX_VALUE,
					() -> "The nb of conflicts/supports is greater than Integer.MAX_VALUE");
			int nTuples = (int) (Math.min(nSupports, nConflicts));
			positive = nTuples == nSupports;
			tuples = new RandomGenerationProp(nValues, seed).selectTuples(nTuples, microType, false, true, requiredSupport, positive);
		} else if (tnessMode == 2 || tnessMode == 3) {
			tightness = tnessMode == 2 ? tightness : tightness / 256;
			double selectionLimit = Math.min(tightness, 1 - tightness);
			positive = selectionLimit < tightness;
			tuples = new RandomGenerationProb(nValues, seed).selectTuples(selectionLimit, requiredSupport, positive);
		} else {
			assert tnessMode == 4;
			Kit.control(tightness <= Integer.MAX_VALUE, () -> "Pb with tightness ");
			int nbSupports = (int) tightness;
			positive = true;
			tuples = new RandomGenerationProp(nValues, seed).selectTuples(nbSupports, microType, false, true, requiredSupport, positive);
			// new FineProportionRandomListGenerator(nbValues, seed);
		}

		return CtrExtension.build(((Problem) imp()), scope, tuples, positive, Problem.UNSTARRED);
	}

	@Override
	public void model() {
		Var[] x = array("x", size(n), dom(range(d)), "x[i] is the value of the ith variable");
		Var[][] k = nKernels > 0 ? array("k", size(nKernels, nK), dom(range(dK))) : null;

		forcedSolution = sat ? IntStream.range(0, n).map(i -> random.nextInt(d)).toArray() : null;
		int[][] scopesIds = new RandomGenerationProp(n, r, seed).selectSets(e, macroType, repetition);
		forall(range(e), c -> {
			Var[] scope = variablesFrom(scopesIds[c], id -> x[id]);
			int[] tuple = sat ? valuesFrom(scopesIds[c], id -> forcedSolution[id]) : null;
			if (!sameRels || tuples == null)
				((Problem) imp()).addCtr(buildExplicitConstraint((Variable[]) scope, mode, tightness, random.nextLong(), microType, tuple));
			else
				extension(scope, tuples, positive);
		});
		if (nKernels > 0) {
			RandomGenerationProp r = new RandomGenerationProp(nK, rK, seed);
			for (Var[] y : k) {
				for (int[] scopeIds : r.selectSets(eK, macroTypeK, repetition)) {
					Var[] scope = variablesFrom(scopeIds, id -> y[id]);
					((Problem) imp()).addCtr(buildExplicitConstraint((Variable[]) scope, modeK, tightnessK, random.nextLong(), microTypeK, null));
				}
			}
			Constraint[] linkConstraints = new Constraint[nLinks];
			for (int i = 0; i < nKernels; i++) {
				Var[] y = k[i];
				for (int j = 0; j < nLinks; j++) {
					int[] scopeIds = new int[2];
					while (true) {
						scopeIds[0] = random.nextInt(n);
						scopeIds[1] = random.nextInt(nK);
						if (IntStream.range(0, j)
								.noneMatch(m -> Variable.areSimilarArrays((Variable[]) vars(x[scopeIds[0]], y[scopeIds[1]]), linkConstraints[m].scp)))
							break;
					}
					Var[] scope = vars(x[scopeIds[0]], y[scopeIds[1]]); // fixVariablesOf(x, k, i, j, linkConstraints);
					linkConstraints[j] = buildExplicitConstraint((Variable[]) scope, modeL, tightnessL, random.nextLong(), microType, null);
					((Problem) imp()).addCtr(linkConstraints[j]);
				}
			}
		}
	}
}
