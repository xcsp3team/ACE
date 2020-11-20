package search.local;

import java.util.Collection;
import java.util.List;

import org.xcsp.common.enumerations.EnumerationOfPermutations;

import search.SolutionManager;
import utility.Kit;
import variables.Variable;

public class SolutionOptimizer {

	private static final int MAX_SIZE_FOR_PERMUTATIONS_ENUMERATION = 8;
	private static final int NB_TABU_ITERATIONS = 100;

	private final SolutionManager solManager;
	private List<FunctionalPropagator> costVarsPropagators;
	private Collection<Variable[][]> satPreservingPermutations;
	private boolean areIndependantPermutationSets;

	public SolutionOptimizer(SolutionManager solManager) {
		this.solManager = solManager;
		// StuffOptimization stuffOptimization = solManager.solver.pb.stuff.stuffOptimization;
		// if (!stuffOptimization.collectedSatPreservingPermutationsAtInit.isEmpty()) {
		// for (Variable[][] set : stuffOptimization.collectedSatPreservingPermutationsAtInit)
		// for (int i = 1; i < set.length; i++)
		// for (int j = 0; j < set[i].length; j++)
		// Kit.control(Variable.haveSameDomainType(set[0][j], set[i][j]));
		// costVarsPropagators = FunctionalPropagator.sort(stuffOptimization.collectedCostVarsFunctionalPropagatorsAtInit);
		// satPreservingPermutations = stuffOptimization.collectedSatPreservingPermutationsAtInit;
		// areIndependantPermutationSets = stuffOptimization.areIndependantPermutationSets;
		// }
	}

	public void optimizeCurrentSolution() {
		if (costVarsPropagators == null)
			return;
		if (areIndependantPermutationSets)
			for (Variable[][] permutationSet : satPreservingPermutations)
				optimizeCurrentSolution(permutationSet);
		else
			throw new UnsupportedOperationException(); // TODO
	}

	private void optimizeCurrentSolution(Variable[][] permutationSet) {
		int[][] initialPartialInstantiation = new int[permutationSet.length][permutationSet[0].length];
		for (int i = 0; i < initialPartialInstantiation.length; i++)
			for (int j = 0; j < initialPartialInstantiation[i].length; j++)
				initialPartialInstantiation[i][j] = permutationSet[i][j].dom.unique();
		if (permutationSet.length <= MAX_SIZE_FOR_PERMUTATIONS_ENUMERATION) {
			EnumerationOfPermutations permEnum = new EnumerationOfPermutations(permutationSet.length);
			while (permEnum.hasNext())
				generateAndTestPermutation(permutationSet, initialPartialInstantiation, permEnum.next());
		} else
			runTabuSearch(permutationSet, initialPartialInstantiation);
		// for (Variable var : problem.variables)
		// var.dom.forcedIndex = Resolution.UNDEFINED;
	}

	private long generateAndTestPermutation(Variable[][] sets, int[][] initialPartialInstantiation, int[] permutation) {
		for (int i = 0; i < initialPartialInstantiation.length; i++)
			// for (int j = 0; j < initialPartialInstantiation[i].length; j++)
			// sets[i][j].dom.forcedIndex = initialPartialInstantiation[permutation[i]][j];
			for (FunctionalPropagator propagator : costVarsPropagators)
				propagator.propagate();
		long cost = solManager.solver.problem.optimizer.value();
		if (cost < solManager.bestBound)
			solManager.handleNewSolution(false);
		return cost;
	}

	private void runTabuSearch(Variable[][] permutationSet, int[][] initialPartialInstantiation) {
		int[] permutation = Kit.range(permutationSet.length);
		boolean minimization = solManager.solver.problem.optimizer.minimization;
		int tabuSize = 2 * permutationSet.length;
		int[] tabuIdxs = Kit.repeat(0, tabuSize);
		int[] tabuVals = Kit.repeat(-1, tabuSize);
		for (int i = 0; i < NB_TABU_ITERATIONS; i++) {
			long bestCost = minimization ? Long.MAX_VALUE : Long.MIN_VALUE;
			int bestSwapIdx1 = -1;
			int bestSwapIdx2 = -1;
			for (int j = 0; j < permutation.length; j++)
				for (int k = j + 1; k < permutation.length; k++)
					if (!isTabu(permutation, tabuIdxs, tabuVals, j, k)) {
						Kit.swap(permutation, j, k);
						long currentCost = generateAndTestPermutation(permutationSet, initialPartialInstantiation, permutation);
						if (minimization && currentCost < bestCost || !minimization && currentCost > bestCost) {
							bestCost = currentCost;
							bestSwapIdx1 = j;
							bestSwapIdx2 = k;
						}
						Kit.swap(permutation, j, k);
					}
			tabuIdxs[i * 2 % tabuSize] = bestSwapIdx1;
			tabuIdxs[(i * 2 + 1) % tabuSize] = bestSwapIdx2;
			tabuVals[i * 2 % tabuSize] = permutation[bestSwapIdx1];
			tabuVals[(i * 2 + 1) % tabuSize] = permutation[bestSwapIdx2];
			Kit.swap(permutation, bestSwapIdx1, bestSwapIdx2);
		}
	}

	private boolean isTabu(int[] permutation, int[] tabuIdxs, int[] tabuVals, int j, int k) {
		for (int i = 0; i < tabuIdxs.length; i++)
			if (tabuIdxs[i] == j && tabuVals[i] == permutation[k] || tabuIdxs[i] == k && tabuVals[i] == permutation[j])
				return true;
		return false;
	}
}
