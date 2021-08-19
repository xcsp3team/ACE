package constraints.extension;

import java.util.Arrays;

import constraints.ConstraintExtension.ExtensionSpecific;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.Table;
import problem.Problem;
import sets.SetDenseReversible;
import variables.Variable;

/**
 * This is STR (Simple Tabular Reduction), as introduced by Julian Ullmann
 * 
 * @author Christophe Lecoutre
 *
 */
public class STR1 extends ExtensionSpecific {

	/**********************************************************************************************
	 * Impkementing Interfaces
	 *********************************************************************************************/

	@Override
	public void afterProblemConstruction() {
		super.afterProblemConstruction();
		this.tuples = ((Table) extStructure()).tuples;
		this.set = new SetDenseReversible(tuples.length, problem.variables.length + 1);
		this.ac = Variable.litterals(scp).booleanArray();
		this.cnts = new int[scp.length];
		control(tuples.length > 0);
	}

	@Override
	public void restoreBefore(int depth) {
		set.restoreLimitAtLevel(depth);
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	/**
	 * The tuples of the table (redundant field)
	 */
	protected int[][] tuples;

	/**
	 * The reversible dense set storing the indexes (of tuples) of the current table
	 */
	public SetDenseReversible set;

	/**
	 * When used during filtering, ac[x][a] indicates if a support has been found for (x,a)
	 */
	protected boolean[][] ac;

	/**
	 * When used during filtering, cnts[x] is the number of values in the current domain of x with no found support (yet)
	 */
	protected int[] cnts;

	/**
	 * The total number of values over all variables in the scope of this constraint with no found support (yet)
	 */
	protected int cnt;

	/**********************************************************************************************
	 * Methods
	 *********************************************************************************************/

	public STR1(Problem pb, Variable[] scp) {
		super(pb, scp);
		control(scp.length > 1, "Arity must be at least 2");
	}

	@Override
	protected ExtensionStructure buildExtensionStructure() {
		return new Table(this);
	}

	protected void beforeFiltering() {
		cnt = 0;
		for (int i = futvars.limit; i >= 0; i--) {
			int x = futvars.dense[i];
			cnt += (cnts[x] = doms[x].size());
			Arrays.fill(ac[x], false);
		}
	}

	protected boolean updateDomains() {
		for (int i = futvars.limit; i >= 0 && cnt > 0; i--) {
			int x = futvars.dense[i];
			int nRemovals = cnts[x];
			if (nRemovals == 0)
				continue;
			if (doms[x].remove(ac[x], nRemovals) == false)
				return false;
			cnt -= nRemovals;
		}
		return true;
	}

	@Override
	public boolean runPropagator(Variable dummy) {
		int depth = problem.solver.depth();
		beforeFiltering();
		for (int i = set.limit; i >= 0; i--) {
			int[] tuple = tuples[set.dense[i]];
			if (isValid(tuple)) {
				for (int j = futvars.limit; j >= 0; j--) {
					int x = futvars.dense[j];
					int a = tuple[x];
					if (!ac[x][a]) {
						cnt--;
						cnts[x]--;
						ac[x][a] = true;
					}
				}
			} else
				set.removeAtPosition(i, depth);
		}
		return updateDomains();
	}

}
