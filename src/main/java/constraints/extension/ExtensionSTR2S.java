/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package constraints.extension;

import static org.xcsp.common.Constants.STAR;

import java.util.Arrays;
import java.util.stream.Stream;

import constraints.extension.Extension.ExtensionGlobal;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import interfaces.Tags.TagShort;
import problem.Problem;
import propagation.StrongConsistency;
import sets.SetDenseReversible;
import utility.Kit;
import variables.Variable;

// why not using a counter 'time' and replace boolean[][] ac by int[][] ac (we just do time++ instead of Arrays.fill(ac[x],false)
public final class ExtensionSTR2S extends ExtensionGlobal implements TagShort {

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	private final static int UNITIALIZED = -2;

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.tuples = ((Table) extStructure).tuples;
		this.set = new SetDenseReversible(tuples.length, problem.variables.length + 1);
		this.ac = Variable.litterals(scp).booleanArray();
		this.cnts = new int[scp.length];
		this.sVal = new int[scp.length];
		this.sSup = new int[scp.length];

		control(tuples.length > 0);
		if (decremental) {
			this.lastSizesStack = new int[problem.variables.length + 1][scp.length];
			Arrays.fill(lastSizesStack[0], UNITIALIZED);
		} else
			this.lastSizes = Kit.repeat(UNITIALIZED, scp.length);
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
		if (decremental)
			lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));
		else
			Arrays.fill(lastSizes, UNITIALIZED);
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	protected int[][] tuples; // redundant field (reference to tuples in Table)

	public SetDenseReversible set;

	/**
	 * ac[x][a] indicates if a support has been found for (x,a)
	 */
	protected boolean[][] ac;

	/**
	 * cnts[x] is the number of values in the current domain of x with no found support (yet)
	 */
	protected int[] cnts;

	/**
	 * The total number of values over all variables in the scope of this constraint with no found support (yet)
	 */
	protected int cnt;

	protected boolean decremental; // true if we exploit decrementality

	protected int sValSize;
	protected int[] sVal; // positions of the variables for which validity must be checked

	protected int sSupSize;
	protected int[] sSup; // positions of the (future) variables for which some values still must be checked to be AC

	protected long lastCallLimit;

	protected int[] lastSizes; // lastSizes[x] is the domain size of x at the last call
	protected int[][] lastSizesStack; // lastSizesStack[i][x] is the domain size of x at the last call at level i
	protected int lastDepth; // the depth at the last call

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	public ExtensionSTR2S(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.decremental = pb.head.control.extension.decremental;
		Kit.control(scp.length > 1, () -> "Arity must be at least 2");
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	protected void initRestorationStructuresBeforeFiltering() {
		if (decremental) {
			int depth = problem.solver.depth();
			assert 0 <= lastDepth && lastDepth <= depth : depth + " " + lastDepth + " " + this;
			for (int i = lastDepth + 1; i <= depth; i++)
				System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, scp.length);
			lastSizes = lastSizesStack[depth];
			lastDepth = depth;
		}
	}

	protected void manageLastPastVar() {
		if (lastCallLimit != problem.solver.stats.nAssignments || problem.solver.propagation instanceof StrongConsistency) { // second condition due to Inverse4
			lastCallLimit = problem.solver.stats.nAssignments;
			Variable lastPast = problem.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1) {
				sVal[sValSize++] = x;
				lastSizes[x] = 1;
			}
		}
	}

	protected void beforeFiltering() {
		initRestorationStructuresBeforeFiltering();
		sValSize = sSupSize = 0;
		manageLastPastVar();
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			int domSize = doms[x].size();
			cnts[x] = domSize;
			if (lastSizes[x] != domSize) {
				sVal[sValSize++] = x;
				lastSizes[x] = domSize;
			}
			sSup[sSupSize++] = x;
			Arrays.fill(ac[x], false);
		}
		// TODO to experiment the code below
		// if (sValSize == 1) { int x = sVal[0]; for (int i = 0; i < sSupSize; i++) if (sSup[i] == x) { sSup[i] = sSup[--sSupSize]; break; } }
	}

	protected boolean updateDomains() {
		for (int i = sSupSize - 1; i >= 0; i--) {
			int x = sSup[i];
			int nRemovals = cnts[x];
			assert nRemovals > 0;
			if (scp[x].dom.remove(ac[x], nRemovals) == false)
				return false;
			lastSizes[x] = scp[x].dom.size();
		}
		return true;
	}

	protected boolean isValidTuple(int[] tuple) {
		for (int i = sValSize - 1; i >= 0; i--) {
			int x = sVal[i];
			if (tuple[x] != STAR && !doms[x].present(tuple[x]))
				return false;
		}
		return true;
	}

	// private boolean earlyBreak = false;

	@Override
	public boolean runPropagator(Variable dummy) {
		int depth = problem.solver.depth();
		// if (entailedDepth >= depth) return true;
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValidTuple(tuple)) {
				for (int j = sSupSize - 1; j >= 0; j--) {
					int x = sSup[j];
					int a = tuple[x];
					if (a == STAR) {
						cnts[x] = 0;
						sSup[j] = sSup[--sSupSize];
					} else if (!ac[x][a]) {
						ac[x][a] = true;
						if (--cnts[x] == 0)
							sSup[j] = sSup[--sSupSize];
					}
					// if (earlyBreak && sSupSize == 0) {
					// // System.out.println("gain " + i);
					// i = 0;
					// }
				}
			} else
				set.removeAtPosition(i, depth);
		}
		assert controlValidTuples();
		// if (Variable.computeNbValidTuplesFor(scope) == set.size()) { entailedDepth = depth; } // and for short tables ? ??
		return updateDomains();
	}

	private boolean controlValidTuples() {
		int[] dense = set.dense;
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[dense[i]];
			for (int j = tuple.length - 1; j >= 0; j--) {
				if (tuple[j] != STAR && !doms[j].present(tuple[j])) {
					System.out.println(this + " at " + problem.solver.depth() + "\n" + Kit.join(tuple));
					Stream.of(scp).forEach(x -> x.display(true));
					return false;
				}
			}
		}
		return true;
	}

}
