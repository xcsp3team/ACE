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
	 * Defines the key of the constraint from the signature, the type of the domains, and the specified data. Keys are currently used for deciding if two
	 * constraints can share some structures (this is the case when they have the same keys), and also for symmetry-breaking.
	 * 
	 * @param data
	 *            a sequence of objects that must be considered when building the key of the constraint
	 */
	protected final void defineKey(Object... data) {
		StringBuilder sb = signature().append(' ').append(getClass().getSimpleName());
		for (Object obj : data)
			sb.append(' ').append(obj.toString());
		this.key = sb.toString();
	}

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