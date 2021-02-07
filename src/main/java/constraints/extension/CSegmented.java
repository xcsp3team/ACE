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
import java.util.stream.Stream;

import constraints.extension.Extension.ExtensionGlobal;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.TableSegmented;
import constraints.extension.structures.TableSegmented.SegmentedTuple;
import constraints.extension.structures.TableSegmented.SegmentedTuple.RestrictionTable;
import problem.Problem;
import propagation.StrongConsistency;
import sets.SetDenseReversible;
import sets.SetSparse;
import variables.Variable;

public final class CSegmented extends ExtensionGlobal {

	/**********************************************************************************************
	 * Restoration
	 *********************************************************************************************/

	private static final int UNINITIALIZED_VALUE = Integer.MAX_VALUE;

	protected int lastDepth;

	protected int[] lastSizes; // lastSizes[x] is the last domain size of dom(x), with x denoting the position of the variable in the constraint scope
	protected int[][] lastSizesStack; // lastSizesStack[d][x] is the last domain size of dom(x) at depth d

	protected void initRestorationStructuresBeforeFiltering() {
		int depth = problem.solver.depth();
		assert depth >= lastDepth && lastDepth >= 0 : depth + " " + lastDepth;
		for (int i = lastDepth + 1; i <= depth; i++)
			System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, lastSizesStack[lastDepth].length);
		lastSizes = lastSizesStack[depth];
		lastDepth = depth;
	}

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		set = new SetDenseReversible(segmentedTuples.length, problem.variables.length + 1);
		Arrays.fill((lastSizesStack = new int[problem.variables.length + 1][scp.length])[0], UNINITIALIZED_VALUE);
		for (SegmentedTuple st : segmentedTuples)
			for (RestrictionTable rt : st.restrictions)
				rt.onConstructionProblemFinished(this.problem);
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));

		for (int i = set.limit; i >= 0; i--) {
			SegmentedTuple splitTuple = segmentedTuples[set.dense[i]];
			for (RestrictionTable restriction : splitTuple.restrictions)
				restriction.restoreBefore(depth);
		}

		// for (SplitTuple splitTuple : splitTuples)
		// for (RestrictionTable restriction : splitTuple.restrictions)
		// restriction.restoreBefore(depth);
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	public final SegmentedTuple[] segmentedTuples;

	protected SetDenseReversible set; // the set of indexes of split tuples, in the current table

	public SetSparse[] unsupported; // unsupported[x] is the set of values in dom(x) with not found support so far (during filtering process)

	protected int sValSize;
	protected int[] sVal; // positions of the variables for which validity must be checked

	protected int sSupSize;
	protected int[] sSup; // positions of the variables for which GAC of values must be checked

	protected long lastCallNode;

	public CSegmented(Problem pb, Variable[] scp, SegmentedTuple... splitTuples) {
		super(pb, scp);
		this.segmentedTuples = splitTuples;
		extStructure = buildExtensionStructure();
		unsupported = IntStream.range(0, scp.length).mapToObj(i -> new SetSparse(scp[i].dom.initSize(), true)).toArray(SetSparse[]::new);
		Stream.of(splitTuples).forEach(st -> st.attach(this));
		sVal = new int[scp.length];
		sSup = new int[scp.length];
		// Stream.of(splitTuples).forEach(st -> System.out.println(st));
	}

	@Override
	public ExtensionStructure buildExtensionStructure() {
		return new TableSegmented(this, segmentedTuples);
	}

	protected void manageLastPastVariable() {
		if (lastCallNode != problem.solver.stats.nAssignments || problem.solver.propagation instanceof StrongConsistency) { // second condition due to Inverse4
			lastCallNode = problem.solver.stats.nAssignments;
			Variable lastPast = problem.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1)
				sVal[sValSize++] = x;
		}
	}

	protected void beforeFiltering() {
		initRestorationStructuresBeforeFiltering();
		sValSize = sSupSize = 0;
		manageLastPastVariable();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			if (scp[x].dom.size() == lastSizes[x]) {
				unsupported[x].limit = lastSizes[x] - 1;
				// // Kit.control(scp[vap].dom.isExactly(supportlesss[vap])); // TODO TO MODIFY AS AN ASSERT
				// // *************************************************
			} else {
				unsupported[x].clear();
				for (int a = scp[x].dom.first(); a != -1; a = scp[x].dom.next(a))
					unsupported[x].add(a);
			}
			sSup[sSupSize++] = x;
			if (lastSizes[x] != scp[x].dom.size()) {
				sVal[sValSize++] = x;
				lastSizes[x] = scp[x].dom.size();
			}
		}
	}

	protected boolean updateDomains() {
		for (int i = 0; i < sSupSize; i++) {
			int x = sSup[i];
			assert !unsupported[x].isEmpty();
			if (scp[x].dom.remove(unsupported[x]) == false) {
				// System.out.println("Failure for " + scp[x]);
				return false;
			}
			unsupported[x].moveElementsAt(lastSizes[x] - 1);
			lastSizes[x] = scp[x].dom.size();
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		int depth = problem.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			SegmentedTuple st = segmentedTuples[set.dense[i]];
			if (st.isValid(sVal, sValSize))
				sSupSize = st.collect(sSup, sSupSize);
			else
				set.removeAtPosition(i, depth);
		}
		if (set.size() == 0)
			return false;
		// System.out.println("size " + set.size());
		return updateDomains();
	}

}
