/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package learning;

import java.util.HashMap;
import java.util.Map;
import java.util.zip.Deflater;

import solver.Solver;
import utility.Bit;
import utility.Enums.Stopping;
import utility.Kit;
import utility.Kit.ByteArrayHashKey;
import variables.Variable;

public final class IpsReasonerEquivalence extends IpsReasoner {

	public final Map<ByteArrayHashKey, Integer> mapOfHashKeys;

	private final ByteArrayHashKey[] openNodesKeys;

	private final int[] openNodesSols; // number of solutions

	private final int nBytesPerVariableNum;

	private final Deflater compressor;

	private ByteArrayHashKey currentHashKey;

	private byte[] tmpInput = new byte[50000]; // TODO why this value?

	private byte[] tmpOutput = new byte[20000];

	public int nTooLargeKeys;

	/**
	 * indicates the number of solution inferred by reasoning with IPSs
	 */
	public int nInferredSolutions;

	/**
	 * Builds an object recording IPS and reasoning on them by equivalence
	 * 
	 * @param solver
	 *            the solver to which this object is attached
	 */
	public IpsReasonerEquivalence(Solver solver) {
		super(solver);
		int n = variables.length;
		if (n > 1500) // hard coding
			stopped = true;
		this.mapOfHashKeys = new HashMap<>(2000);
		this.openNodesKeys = new ByteArrayHashKey[n];
		this.openNodesSols = new int[n];
		this.nBytesPerVariableNum = n <= Math.pow(2, 8) ? 1 : n <= Math.pow(2, 16) ? 2 : n <= Math.pow(2, 24) ? 3 : 4;
		this.compressor = settings.ipsCompressionEquivalence != Deflater.NO_COMPRESSION ? new Deflater(settings.ipsCompressionEquivalence) : null;
	}

	@Override
	protected boolean mustStop() {
		if (super.mustStop())
			return true;
		int nGlobalKeys = mapOfHashKeys.size() + nTooLargeKeys;
		return (nGlobalKeys > 1000 && nGlobalKeys > 1000 * nInferences);
	}

	private byte[] compress(int limit) {
		assert limit >= settings.ipsCompressionLimitEquivalence;

		compressor.reset();
		compressor.setInput(tmpInput, 0, limit);
		compressor.finish();
		int count = compressor.deflate(tmpOutput);
		if (!compressor.finished()) {
			byte[] t = new byte[limit];
			System.arraycopy(tmpInput, 0, t, 0, limit);
			return t;
		}
		byte[] t = new byte[count];
		System.arraycopy(tmpOutput, 0, t, 0, count);
		return t;
	}

	private void buildHashKey() {
		Variable[] vars = solver.solutions.limit > 1 ? extractor.extractForAllSolutions() : extractor.extract();
		int keySize = 0;
		for (Variable x : vars) {
			if (keySize + nBytesPerVariableNum + x.dom.initSize() / 8 >= tmpInput.length) {
				keySize = -1;
				break;
			}
			keySize = Bit.convert(x.num, nBytesPerVariableNum, tmpInput, keySize);
			// if (dom.size() == dom.initSize()) continue; // decomment if all solutions are seeked
			keySize = Bit.convert(x.dom.binary(), x.dom.initSize(), tmpInput, keySize);
		}
		if (currentHashKey == null)
			currentHashKey = new ByteArrayHashKey();
		if (keySize == -1) {
			currentHashKey.t = null;
			nTooLargeKeys++;
		} else {
			byte[] t = null;
			if (compressor == null || keySize < settings.ipsCompressionLimitEquivalence) {
				t = new byte[keySize];
				System.arraycopy(tmpInput, 0, t, 0, keySize);
			} else
				t = compress(keySize);
			currentHashKey.t = t;
		}
	}

	@Override
	public boolean whenOpeningNode() {
		if (stopped)
			return true;
		int depth = solver.depth();
		if (depth == variables.length)
			return true;
		buildHashKey();
		if (currentHashKey.t == null) {
			openNodesKeys[depth] = null;
			return true;
		}
		Integer value = mapOfHashKeys.get(currentHashKey);
		if (value != null) {
			nInferences++;
			if (value > 0) {
				nInferredSolutions += value;
				solver.solutions.found += value;
			}
			// else mapOfHashKeys.put(currentHashKey, value - 1);
			return false;
		}
		openNodesKeys[depth] = currentHashKey;
		currentHashKey = null;
		openNodesSols[depth] = (int) solver.solutions.found;
		return true;
	}

	@Override
	public void whenClosingNode() {
		if (stopped)
			return;
		if (mustStop()) {
			Kit.log.info("Stopping use of transposition table (mapSize=" + mapOfHashKeys.size() + ", nbTooLargekeys=" + nTooLargeKeys + ", mem="
					+ Kit.memoryInMb() + ")");
			mapOfHashKeys.clear();
			stopped = true;
			return;
		}
		ByteArrayHashKey hashKey = openNodesKeys[solver.depth()];
		if (hashKey == null)
			return; // since the key was too large and so not recorded
		if (hashKey.t.length == 0)
			solver.stopping = Stopping.FULL_EXPLORATION;
		int nSolutions = (int) solver.solutions.found - openNodesSols[solver.depth()];
		mapOfHashKeys.put(hashKey, nSolutions == 0 ? 0 : nSolutions);
	}

	@Override
	public void displayStats() {
		if (!stopped)
			Kit.log.finer("  mapSize=" + mapOfHashKeys.size() + "  nbInferences=" + nInferences + "  nbInferredSolutions=" + nInferredSolutions + "  usedMem="
					+ Kit.memoryInMb() + "  nbTooLargeKeys=" + nTooLargeKeys);
	}

}

// private void buildS() {
// if (solver.problem.getMaxConstraintArity() == 2)
// return;
//
// tmp = new int[solver.variables.length];
// dependencies = new int[solver.variables.length][];
//
// for (Variable variable : solver.variables) {
// int nbDependencies = 0;
// Arrays.fill(tmp, 0);
// for (Constraint involvingConstraint : variable.ctrs) {
// if (involvingConstraint.getArity() == 2)
// continue;
// for (Variable involvedVariable : involvingConstraint.getInvolvedVariables()) {
// if (involvedVariable == variable)
// continue;
// tmp[involvedVariable.id]++;
// if (tmp[involvedVariable.id] == 2)
// nbDependencies++;
// }
// }
// int[] t = new int[nbDependencies];
// int cpt = 0;
// for (int i = 0; i < tmp.length; i++) {
// if (cpt == nbDependencies)
// break;
// if (tmp[i] > 1)
// t[cpt++] = i;
// }
// dependencies[variable.getId()] = t;
// }
//
// for (int i = 0; i < dependencies.length; i++) {
// Kit.pr("dependencies of " + solver.getVariable(i) + " : ");
// for (int j = 0; j < dependencies[i].length; j++)
// Kit.pr(solver.getVariable(dependencies[i][j]) + " ");
// Kit.prn();
// }
//
// }

// if (mode == 1) {
// String key = buildKey();
// // String key2 = compress(key.getBytes());
//
// Integer value = map1.get(key);
// if (value != null) {
// nbInferences++;
// if (value > 0) {
// nbInferredSolutions += value;
// solver.statistics.incrementNbFoundSolutionsOf(value);
// // Kit.prn(" level = " + level);
// } else {
// // Kit.prn(" nb " + value);
// map1.put(key, value - 1);
// // Kit.prn("new value = " + map.get(key));
// }
// return false;
// }
// currentOpenNodesKeys1[level] = key;
// currentOpenNodesNbFoundSolutions[level] = (int) solver.statistics.getNbFoundSolutions();
// return true;
//
// } else {

// private String buildKey() {
// sb.delete(0, sb.length());
//
// VariableManager variableManager = solver.getVariableManager();
// boolean twoCharacters = (variables.length > 65535 ? true : false);
//
// if (moreThanOneSolution) {
// for (Variable variable : variables) {
// Elements elements = variable.domain.getElements();
// if (elements.getNbPresentElements() == 1)
// continue;
// BitManager.convert(variable.getId(), twoCharacters, sb);
// if (elements.getNbPresentElements() == elements.getMaximumSize())
// continue;
// BitManager.convert(elements.getBinaryRepresentation(), elements.getMaximumSize(), sb);
// }
// } else {
// for (Variable variable = variableManager.getFirstFutureVariable(); variable != null; variable =
// variableManager.getNextFutureVariableAfter(variable)) {
// Elements elements = variable.domain.getElements();
// if (elements.getNbPresentElements() == 1 || elements.getNbPresentElements() == elements.getMaximumSize())
// continue;
//
// BitManager.convert(variable.getId(), twoCharacters, sb);
// BitManager.convert(elements.getBinaryRepresentation(), elements.getMaximumSize(), sb);
// }
// }
// // Kit.prn(" nb = " + sb.length()*2);
// return sb.toString();
// }

// private boolean[] eliminableVariables;
//
// private boolean isFree(Variable variable, Constraint constraint) {
// for (Constraint involvingConstraint : variable.ctrs) {
// if (involvingConstraint == constraint)
// continue;
// if (involvingConstraint.getNbFreeVariables() > 1)
// return false;
// }
// return true;
// }
// private boolean canEliminate(Constraint constraint) {
// int cpt = 0;
// for (Variable variable : constraint.getInvolvedVariables()) {
// if (variable.getCurrentDomainSize() == 1)
// continue;
// if (!isFree(variable, constraint)) {
// if (++cpt > 1)
// return false;
// }
// }
// return true;
// }
//
// private int newBuilding() {
// Arrays.fill(eliminableVariables, true);
// int keySize = 0;
//
// Constraint[] constraints = solver.constraints;
// for (Constraint constraint : constraints) {
// if (canEliminate(constraint))
// continue;
// for (Variable variable : constraint.getInvolvedVariables())
// eliminableVariables[variable.getId()] = false;
// }
// int cpt = 0;
// for (int i = 0; i < eliminableVariables.length; i++) {
// if (eliminableVariables[i])
// continue;
// Elements elements = variables[i].domain.getElements();
// if (elements.getNbPresentElements() == elements.getMaximumSize())
// continue;
// cpt++;
// if (keySize + nbBytesPerVariableId + elements.getMaximumSize() / 8 >= tmpInput.length)
// return -1;
// keySize = BitManager.convert(variables[i].id, nbBytesPerVariableId, tmpInput, keySize);
// keySize = BitManager.convert(elements.getBinaryRepresentation(), elements.getMaximumSize(), tmpInput, keySize);
// }
// // Kit.prn("cpt = " + cpt);
// return keySize;
// }
