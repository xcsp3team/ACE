package constraints.extension;

import java.util.Arrays;

import problem.Problem;
import propagation.StrongConsistency;
import utility.Kit;
import variables.Variable;

/**
 * This is the root class of optimized STR-based (Simple Tabular Reduction) algorithms, notably STR2 and CT, for filtering extension (table) constraints.
 * 
 * @author Christophe Lecoutre
 *
 */
public abstract class STR1Optimized extends STR1 {

	/**********************************************************************************************
	 * Interfaces
	 *********************************************************************************************/

	private final static int UNITIALIZED = -2;

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.sVal = new int[scp.length];
		this.sSup = new int[scp.length];
		if (settings.decremental) {
			this.lastSizesStack = new int[problem.variables.length + 1][scp.length];
			Arrays.fill(lastSizesStack[0], UNITIALIZED);
		} else
			this.lastSizes = Kit.repeat(UNITIALIZED, scp.length);
	}

	@Override
	public void restoreBefore(int depth) {
		super.restoreBefore(depth);
		if (settings.decremental && depth > 0) // second part (depth > 0) for ensuring that aggressive runs can be used
			lastDepth = Math.max(0, Math.min(lastDepth, depth - 1));
		else
			Arrays.fill(lastSizes, UNITIALIZED);
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	/**
	 * The number of variables for which validity must be checked during the filtering process
	 */
	protected int sValSize;

	/**
	 * The (dense) set of positions of variables for which validity must be checked. Relevant positions are at indexes from 0 to sValSize (excluded).
	 */
	protected int[] sVal;

	/**
	 * The number of variables for which support searching must be done (i.e., variables with some values that still must be checked to be AC)
	 */
	protected int sSupSize;

	/**
	 * The (dense) set of positions of variables for which support searching must be done. Relevant positions are at indexes from 0 to sSupSize (excluded).
	 */
	protected int[] sSup;

	/**
	 * lastSizes[x] is the domain size of x at the last call
	 */
	protected int[] lastSizes;

	/**
	 * lastSizesStack[i][x] is the domain size of x at the last call at level (depth) i
	 */
	protected int[][] lastSizesStack;

	/**
	 * The depth at the last call
	 */
	protected int lastDepth;

	/**
	 * A number used to determine whether the last past variable should be considered for validity testing (and for possibly other roles in subclasses)
	 */
	protected long lastSafeNumber;

	/**********************************************************************************************
	 * Method
	 *********************************************************************************************/

	public STR1Optimized(Problem pb, Variable[] scp) {
		super(pb, scp);
	}

	/**
	 * Makes, before filtering, some initialization with respect to the structures used for restoration
	 */
	protected final void initRestorationStructuresBeforeFiltering() {
		if (settings.decremental) {
			int depth = problem.solver.depth();
			assert 0 <= lastDepth && lastDepth <= depth : depth + " " + lastDepth + " " + this;
			for (int i = lastDepth + 1; i <= depth; i++)
				System.arraycopy(lastSizesStack[lastDepth], 0, lastSizesStack[i], 0, scp.length);
			lastSizes = lastSizesStack[depth];
			lastDepth = depth;
		}
	}

	/**
	 * Makes, before filtering, some initialization with respect to the last variable explicitly assigned by the solver
	 */
	protected void manageLastPastVar() {
		if (lastSafeNumber != problem.solver.stats.safeNumber() || problem.solver.propagation instanceof StrongConsistency) { // 2nd condition due to Inverse4
			lastSafeNumber = problem.solver.stats.safeNumber();
			Variable lastPast = problem.solver.futVars.lastPast();
			int x = lastPast == null ? -1 : positionOf(lastPast);
			if (x != -1) {
				sVal[sValSize++] = x;
				lastSizes[x] = 1;
			}
		}
	}

	@Override
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

	@Override
	protected boolean updateDomains() {
		for (int i = sSupSize - 1; i >= 0; i--) {
			int x = sSup[i];
			int nRemovals = cnts[x];
			assert nRemovals > 0;
			if (doms[x].remove(ac[x], nRemovals) == false)
				return false;
			lastSizes[x] = doms[x].size();
		}
		return true;
	}

}

// @Override
// public void beforeRun() {
// // has been inserted to fix a bug with starred tables
// // java -ea abscon.Resolution problems.real.tal.Tal ~/instances/tal/compiler2solver/fr.observed.tuples 9 27-35-38-22-15-13-26-28 -1
// // -s=all -t=120s -f=cop -ev -varh=DDegOnDom -rs
// // if (decremental)
// // Arrays.fill(lastSizesStack[0], -2);
// // else
// // Arrays.fill(lastSizes, -2);
// // lastDepth = 0;
// }
