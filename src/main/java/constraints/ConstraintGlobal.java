package constraints;

import interfaces.SpecificPropagator;
import problem.Problem;
import variables.Variable;

/**
 * The abstract class representing global constraints, which are essentially constraints with a specific form of filtering (propagator).
 * 
 * @author Christophe Lecoutre
 */
public abstract class ConstraintGlobal extends Constraint implements SpecificPropagator {

	/**
	 * Builds a global constraint for the specified problem, and with the specified scope
	 * 
	 * @param pb
	 *            the problem to which the constraint is attached
	 * @param scp
	 *            the scope of the constraint
	 */
	public ConstraintGlobal(Problem pb, Variable[] scp) {
		super(pb, scp);
		this.filteringComplexity = 1;
	}
}