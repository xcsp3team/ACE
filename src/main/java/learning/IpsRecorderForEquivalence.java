/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package learning;

import java.util.HashMap;
import java.util.Map;
import java.util.zip.Deflater;

import solver.Solver;
import utility.Bit;
import utility.Enums.EStopping;
import utility.Kit;
import utility.Kit.ByteArrayHashKey;
import variables.Domain;
import variables.Variable;

public final class IpsRecorderForEquivalence extends IpsRecorder {

	private static final Integer zero = new Integer(0);

	private Map<ByteArrayHashKey, Integer> mapOfHashKeys = new HashMap<>(2000);

	private ByteArrayHashKey[] currentOpenNodesKeys;

	private int[] currentOpenNodesNbFoundSolutions;

	private ByteArrayHashKey currentHashKey;

	private boolean moreThanOneSolution;

	private int nBytesPerVariableId;

	private Deflater compressor;

	private byte[] tmpInput = new byte[50000]; // TODO

	private byte[] tmpOutput = new byte[20000];

	public int nTooLargeKeys, nInferredSolutions;

	public int getMapSize() {
		return mapOfHashKeys.size();
	}

	// @Override
	// public void clear() {
	// mapOfHashKeys.clear();
	// }

	public IpsRecorderForEquivalence(Solver solver) {
		super(solver);
		if (variables.length > 1500) // hard coding
			stopped = true;
		currentOpenNodesKeys = new ByteArrayHashKey[variables.length];
		currentOpenNodesNbFoundSolutions = new int[variables.length];
		moreThanOneSolution = solver.solRecorder.limit > 1;
		nBytesPerVariableId = (variables.length <= Math.pow(2, 8) ? 1 : variables.length <= Math.pow(2, 16) ? 2 : variables.length <= Math.pow(2, 24) ? 3 : 4);
		if (settings.compressionLevelForStateEquivalence != Deflater.NO_COMPRESSION)
			compressor = new Deflater(settings.compressionLevelForStateEquivalence);
	}

	@Override
	protected boolean mustStop() {
		if (super.mustStop())
			return true;
		int nGlobalKeys = mapOfHashKeys.size() + nTooLargeKeys;
		return (nGlobalKeys > 1000 && nGlobalKeys > 1000 * nInferences);
	}

	private byte[] compress(int limit) {
		assert limit >= settings.compressionLimitForStateEquivalence;

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
		int[] ids = moreThanOneSolution ? reductionOperator.extractForAllSolutions() : reductionOperator.extract();
		int keySize = 0;
		for (int i = 0; i < ids.length; i++) {
			Variable var = solver.problem.variables[ids[i]];
			Domain dom = var.dom;
			if (keySize + nBytesPerVariableId + dom.initSize() / 8 >= tmpInput.length) {
				keySize = -1;
				break;
			}
			keySize = Bit.convert(var.num, nBytesPerVariableId, tmpInput, keySize);
			// if (elements.getNbPresentElements() == elements.getMaximumSize()) // decomment if all solutions are
			// seeked
			// continue;
			keySize = Bit.convert(dom.binary(), dom.initSize(), tmpInput, keySize);
		}
		if (currentHashKey == null)
			currentHashKey = new ByteArrayHashKey();
		if (keySize == -1) {
			currentHashKey.t = null;
			nTooLargeKeys++;
		} else {
			byte[] t = null;
			if (compressor == null || keySize < settings.compressionLimitForStateEquivalence) {
				t = new byte[keySize];
				System.arraycopy(tmpInput, 0, t, 0, keySize);
			} else
				t = compress(keySize);
			currentHashKey.t = t;
		}
	}

	@Override
	public boolean dealWhenOpeningNode() {
		if (stopped)
			return true;

		int level = solver.depth();
		if (level == variables.length)
			return true;

		buildHashKey();

		if (currentHashKey.t == null) {
			currentOpenNodesKeys[level] = null;
			return true;
		}
		// if (currentHashKey.t.length == 0) Kit.prn("open empty noggod");

		Integer value = mapOfHashKeys.get(currentHashKey);
		if (value != null) {
			nInferences++;
			if (value > 0) {
				nInferredSolutions += value;
				solver.solRecorder.found += value;
			}
			// else mapOfHashKeys.put(currentHashKey, value - 1);
			return false;
		}

		currentOpenNodesKeys[level] = currentHashKey;
		currentHashKey = null;
		currentOpenNodesNbFoundSolutions[level] = (int) solver.solRecorder.found;
		return true;
	}

	@Override
	public void dealWhenClosingNode() {
		if (stopped)
			return;
		if (mustStop()) {
			Kit.log.info("Stopping use of transposition table (mapSize=" + mapOfHashKeys.size() + ", nbTooLargekeys=" + nTooLargeKeys + ", mem="
					+ Kit.memoryInMb() + ")");
			mapOfHashKeys.clear();
			stopped = true;
			// display();
			return;
		}

		ByteArrayHashKey hashKey = currentOpenNodesKeys[solver.depth()];
		if (hashKey == null)
			return; // since the key was too large and so not recorded
		if (hashKey.t.length == 0)
			solver.stopping = EStopping.FULL_EXPLORATION;
		int nSolutions = (int) solver.solRecorder.found - currentOpenNodesNbFoundSolutions[solver.depth()];
		mapOfHashKeys.put(hashKey, nSolutions == 0 ? zero : nSolutions);
	}

	// public boolean dealWhenOpeningRefutationNode() {
	// if (stop)
	// return true;
	//
	// int level = solver.getCurrentDepth();
	// if (level == variables.length)
	// return true;
	//
	// buildHashKey();
	// // solver.problem.displayExhaustively();
	// if (currentHashKey.t == null)
	// return true;
	//
	// Integer value = mapOfHashKeys.get(currentHashKey);
	// if (value != null) {
	// nbInferences++;
	// if (value > 0) {
	// nbInferredSolutions += value;
	// solver.statistics.incrementNbFoundSolutionsOf(value);
	// }
	// // else
	// // mapOfHashKeys.put(currentHashKey, value - 1);
	// return false;
	// }
	// return true;
	// }

	@Override
	public void displayStats() {
		if (!stopped) // && !Data.competitionMode)
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
