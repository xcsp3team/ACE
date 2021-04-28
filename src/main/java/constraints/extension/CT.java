/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.LongStream;

import org.xcsp.common.Constants;

import constraints.extension.structures.Table;
import interfaces.Tags.TagStarred;
import problem.Problem;
import sets.SetDenseReversible;
import utility.Bit;
import variables.Domain;
import variables.Variable;

public class CT extends STR1Optimized implements TagStarred {

	public final static class CT2 extends CT implements TagStarred {

		static final int MASK_COMPRESION_LIMIT = 12;
		static final int MASK_COMPRESION_TRIGGER_SIZE = 300;

		long[] maskCollect = new long[MASK_COMPRESION_LIMIT * 2];

		@Override
		protected void maskCompression(long[][] masks) {
			if (masks[0].length <= MASK_COMPRESION_TRIGGER_SIZE)
				return;
			for (int a = 0; a < masks.length; a++) {
				long[] mask = masks[a];
				int cnt = 0;
				Long defaultWord = null; // uninitialized
				boolean compressible = true;
				for (int i = 0; compressible && i < mask.length; i++) {
					if (mask[i] == 0L && defaultWord == null)
						defaultWord = 0L;
					else if (mask[i] == -1L && defaultWord == null)
						defaultWord = -1L;
					else if (defaultWord == null || mask[i] != defaultWord)
						if (cnt + 1 >= maskCollect.length)
							compressible = false;
						else {
							maskCollect[cnt++] = i;
							maskCollect[cnt++] = mask[i];
						}
				}
				if (compressible) {
					long def = defaultWord == null ? 0 : (long) defaultWord, way = 0L; // way todo
					masks[a] = LongStream.range(0, 2 + cnt).map(i -> i == 0 ? def : i == 1 ? way : maskCollect[(int) i - 2]).toArray();
				}
			}
		}

		public CT2(Problem pb, Variable[] scp) {
			super(pb, scp);
		}

	}

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	protected void maskCompression(long[][] masks) {
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();

		int nWords = (int) Math.ceil(tuples.length / 64.0);
		this.current = new long[nWords];
		this.tmp = new long[nWords];
		this.tmp2 = new long[nWords];
		this.lastWord1Then0 = tuples.length % 64 != 0 ? Bit.bitsA1To(tuples.length % 64) : Bit.ALL_LONG_BITS_TO_1;
		this.lastWord0Then1 = tuples.length % 64 != 0 ? Bit.bitsAt1From(tuples.length % 64) : 0L;
		fillTo1(current);

		this.starred = ((Table) extStructure).starred;
		this.masks = Variable.litterals(scp).longArray(nWords);
		if (!this.starred) {
			for (int x = 0; x < scp.length; x++) {
				long[][] mask = masks[x];
				for (int j = 0; j < tuples.length; j++)
					Bit.setTo1(mask[tuples[j][x]], j);
				maskCompression(mask);
			}
		} else {
			for (int x = 0; x < scp.length; x++) {
				long[][] mask = masks[x];
				for (int j = 0; j < tuples.length; j++)
					if (tuples[j][x] != Constants.STAR)
						Bit.setTo1(mask[tuples[j][x]], j);
					else
						for (int a = 0; a < mask.length; a++)
							Bit.setTo1(mask[a], j);
				maskCompression(mask);
			}
			this.masksS = Variable.litterals(scp).longArray(nWords);
			for (int x = 0; x < scp.length; x++) {
				long[][] mask = masksS[x];
				for (int j = 0; j < tuples.length; j++)
					if (tuples[j][x] != Constants.STAR)
						Bit.setTo1(mask[tuples[j][x]], j);
				maskCompression(mask);
			}
		}

		this.stackedWords = new long[nWords * factorStacked];
		this.stackedIndexes = new int[nWords * factorStacked];
		this.stackStructure = new int[nWords * factorStack];
		this.modifiedWords = new boolean[nWords];

		this.deltaSizes = new int[scp.length];
		this.nonZeros = new SetDenseReversible(current.length, problem.variables.length + 1);
		this.residues = Variable.litterals(scp).intArray();
		this.firstCall = true;
	}

	@Override
	public void restoreBefore(int depth) {
		super.restoreBefore(depth);
		if (topStack != -1 && stackStructure[topStack - 1] == depth) {
			for (int i = stackStructure[topStack] - 1; i >= 0; i--)
				current[stackedIndexes[topStacked - i]] = stackedWords[topStacked - i];
			topStacked -= stackStructure[topStack];
			topStack -= 2;
		}
		nonZeros.restoreLimitAtLevel(depth);
		lastCallNode = -1;
		// if (depth == 0) afterProblemConstruction(); // necessary when using aggressive runs
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	private long[] current; // current table
	private long[][][] masks; // masks[x][a] gives the mask for (x,a)
	private long[][][] masksS; // masksS[x][a] gives the mask* for (x,a) ; useful for short tables

	private long[] tmp, tmp2;
	private long lastWord0Then1, lastWord1Then0;

	int factorStacked = 10, factorStack = 10; // factors used for enlarging arrays when necessary
	long[] stackedWords; // stores the values of the words that have been stacked
	int[] stackedIndexes; // stores the indexes of the words that have been stacked
	int[] stackStructure; // stores, in sequence, pairs (d,nb) with d the depth where nb words have been stacked
	int topStacked = -1, topStack = -1;

	boolean[] modifiedWords; // modifiedWords[i] indicates if the ith word has already been modified (and stored for future use when backtracking)

	int[] deltaSizes; // deltaSizes[x] indicates how many values are in the delta set of x

	public SetDenseReversible nonZeros; // reversible dense set indicating the words that are currently not 0

	private int[][] residues; // residues[x][a] is the index of the word where a support was found the last time for (x,a)

	private boolean firstCall = true;
	private long lastCallNode = -1;

	private boolean starred;

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	public CT(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(decremental);
	}

	private void fillTo1(long[] t) {
		Arrays.fill(t, Bit.ALL_LONG_BITS_TO_1);
		t[t.length - 1] = lastWord1Then0;
	}

	private void fillTo0(long[] t) {
		for (int i = nonZeros.limit; i >= 0; i--)
			t[nonZeros.dense[i]] = 0L;
		t[t.length - 1] = lastWord0Then1;
	}

	private void wordModified(int index, long oldValue) {
		if (modifiedWords[index]) {
			assert stackStructure[topStack - 1] == problem.solver.depth()
					&& IntStream.range(0, stackStructure[topStack]).anyMatch(i -> stackedIndexes[topStacked - i] == index);
			return;
		}
		int depth = problem.solver.depth();
		if (topStack == -1 || stackStructure[topStack - 1] != depth) {
			if (topStack + 3 >= stackStructure.length)
				stackStructure = Arrays.copyOf(stackStructure, current.length * (factorStack *= 2));
			stackStructure[++topStack] = depth;
			stackStructure[++topStack] = 1; // first modified word at this level
		} else
			stackStructure[topStack]++; // another modified word at this level
		if (topStacked + 3 >= stackedWords.length) {
			stackedWords = Arrays.copyOf(stackedWords, current.length * (factorStacked *= 2));
			stackedIndexes = Arrays.copyOf(stackedIndexes, current.length * factorStacked);
		}
		stackedWords[++topStacked] = oldValue;
		stackedIndexes[topStacked] = index;
		modifiedWords[index] = true;
	}

	@Override
	protected void manageLastPastVar() {
		Variable lastPast = problem.solver.futVars.lastPast();
		int x = lastPast == null ? -1 : positionOf(lastPast);
		if (x != -1 && lastSizes[x] != 1) {
			deltaSizes[x] = lastSizes[x] - 1;
			sVal[sValSize++] = x;
			lastSizes[x] = 1;
		}
	}

	@Override
	protected void beforeFiltering() {
		if (lastCallNode != problem.solver.stats.numberSafe()) {
			// Arrays.fill(modifiedWords, false);
			for (int i = nonZeros.limit; i >= 0; i--)
				modifiedWords[nonZeros.dense[i]] = false;
			if (topStack != -1 && stackStructure[topStack - 1] == problem.solver.depth())
				for (int i = stackStructure[topStack] - 1; i >= 0; i--)
					modifiedWords[stackedIndexes[topStacked - i]] = true;
			lastCallNode = problem.solver.stats.numberSafe();
		}
		initRestorationStructuresBeforeFiltering();
		sValSize = sSupSize = 0;
		manageLastPastVar();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			int domSize = doms[x].size();
			if (lastSizes[x] != domSize) {
				deltaSizes[x] = lastSizes[x] - domSize;
				sVal[sValSize++] = x;
				lastSizes[x] = domSize;
			}
			if (domSize > 1)
				sSup[sSupSize++] = x;
		}
		if (sValSize == 1) {
			int x = sVal[0];
			for (int i = 0; i < sSupSize; i++)
				if (sSup[i] == x) {
					sSup[i] = sSup[--sSupSize];
					break;
				}
		}
	}

	private boolean firstCall() {
		firstCall = false;
		lastSizes = lastSizesStack[0];
		lastDepth = 0;
		fillTo0(tmp);
		for (int x = 0; x < scp.length; x++) {
			Domain dom = doms[x];
			for (int a = dom.lastRemoved(); a != -1; a = dom.prevRemoved(a))
				Bit.or2(tmp, !starred ? masks[x][a] : masksS[x][a], nonZeros);
		}
		Bit.inverse(tmp, nonZeros);
		for (int i = nonZeros.limit; i >= 0; i--) {
			int j = nonZeros.dense[i];
			long l = current[j] & tmp[j];
			if (current[j] != l) {
				current[j] = l;
				if (l == 0L)
					nonZeros.removeAtPosition(i, 0);
			}
		}
		for (int x = 0; x < scp.length; x++) {
			Domain dom = doms[x];
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int r = Bit.firstNonNullWord2(current, masks[x][a], nonZeros);
				if (r != -1)
					residues[x][a] = r;
				else if (dom.remove(a) == false)
					return false;
			}
			lastSizes[x] = dom.size();
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable z) {
		// pb.stuff.updateStatsForSTR(set);
		if (firstCall)
			return firstCall();
		beforeFiltering();
		// we compute in tmp the bit vector denoting all deleted tuples (and then we inverse it)
		fillTo0(tmp);
		for (int i = sValSize - 1; i >= 0; i--) {
			int x = sVal[i];
			// long[][] lmasks = masks[x];
			Domain dom = doms[x];
			if (deltaSizes[x] <= dom.size()) {
				for (int cnt = deltaSizes[x] - 1, a = dom.lastRemoved(); cnt >= 0; cnt--) {
					Bit.or2(tmp, !starred ? masks[x][a] : masksS[x][a], nonZeros);
					a = dom.prevRemoved(a);
				}
			} else if (dom.size() == 1) {
				Bit.orInverse2(tmp, masks[x][dom.first()], nonZeros);
			} else {
				fillTo0(tmp2);
				for (int a = dom.first(); a != -1; a = dom.next(a))
					Bit.or2(tmp2, masks[x][a], nonZeros);
				Bit.orInverse2(tmp, tmp2, nonZeros); // Bit.or(tmp, Bit.inverse(tmp2, nonZeros), nonZeros);
			}
		}
		// we update the current table (array 'current') while possibly deleting words at 0 in nonZeros
		int depth = problem.solver.depth();
		for (int i = nonZeros.limit; i >= 0; i--) {
			int j = nonZeros.dense[i];
			long l = current[j] & ~tmp[j]; // we inverse tmp here
			if (current[j] != l) {
				wordModified(j, current[j]);
				current[j] = l;
				if (l == 0L)
					nonZeros.removeAtPosition(i, depth);
			}
		}
		if (nonZeros.size() == 0)
			return z.dom.fail(); // inconsistency detected
		// we update domains (inconsistency is no more possible)
		for (int i = sSupSize - 1; i >= 0; i--) {
			int x = sSup[i];
			Domain dom = doms[x];
			for (int a = dom.first(); a != -1; a = dom.next(a)) {
				int r = residues[x][a];
				if (Bit.nonNullIntersection2(current, masks[x][a], r)) // if ((current[r] & masks[x][a][r]) != 0L)
					continue;
				r = Bit.firstNonNullWord2(current, masks[x][a], nonZeros);
				if (r != -1) {
					residues[x][a] = r;
				} else
					dom.removeSafely(a);
			}
			lastSizes[x] = dom.size();
		}
		return true;
	}

}
