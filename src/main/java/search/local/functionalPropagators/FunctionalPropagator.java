package search.local.functionalPropagators;

import java.util.List;

import constraints.Constraint;
import variables.Variable;

public abstract class FunctionalPropagator {

	/**********************************************************************************************
	 * Start of static section
	 *********************************************************************************************/

	protected static final int UNDECIDABLE = Integer.MIN_VALUE;
	private static final int MAX_SIZE_FOR_ENCODING = 1000000;

	/**
	 * @param constraint
	 *            : the constraint over which the propagator is built.
	 * @param outputPos
	 *            : the position of the variable which value can be inferred from the values of the others.
	 * @return A FunctionalPropagatorPreComputed if the cartesian product of the domains is small enough, a FunctionalPropagatorDirect otherwise.
	 */
	public static FunctionalPropagator buildFunctionalPropagator(Constraint constraint, int outputPos) {
		int encodingSize = 1;
		for (int i = 0; i < constraint.scp.length; i++)
			if (i != outputPos)
				if (Integer.MAX_VALUE / constraint.scp[i].dom.initSize() < encodingSize)
					return new FunctionalPropagatorDirect(constraint, outputPos);
				else
					encodingSize *= constraint.scp[i].dom.initSize();
		return encodingSize > MAX_SIZE_FOR_ENCODING ? new FunctionalPropagatorDirect(constraint, outputPos)
				: new FunctionalPropagatorPreComputed(constraint, outputPos, encodingSize);
	}

	/**
	 * Sorts the list of functional propagators so that they can be propagated in the list order.
	 */
	public static List<FunctionalPropagator> sort(List<FunctionalPropagator> list) {
		boolean sorted = false;
		while (!sorted) {
			sorted = true;
			for (int i = 0; i < list.size(); i++) {
				FunctionalPropagator first = list.get(i);
				for (int j = i + 1; j < list.size(); j++) {
					FunctionalPropagator second = list.get(j);
					if (first.ctr.involves(second.ctr.scp[second.outputPos])) {
						list.remove(i);
						list.add(first);
						sorted = false;
						break;
					}
				}
				if (!sorted) {
					sorted = true;
					i--;
				}
			}
		}
		return list;
	}

	/**********************************************************************************************
	 * End of static section
	 *********************************************************************************************/

	public final Constraint ctr;
	public final int outputPos;

	public FunctionalPropagator(Constraint constraint, int outputPos) {
		this.ctr = constraint;
		this.outputPos = outputPos;
	}

	/**
	 * @param tuple
	 *            : the current instantiation of the variables in the constraint's scope, the unknown variable can take any value since it is unused
	 * @return the new value of the unknown variable, or UNDECIDABLE if the constraint could not propagate
	 */
	protected abstract int getOutputVal(int[] tuple);

	public void propagate() {
		Variable[] constraintScope = ctr.scp;
		int[] tuple = new int[constraintScope.length];
		for (int i = 0; i < tuple.length; i++)
			tuple[i] = constraintScope[i].dom.unique();
		// int outputVal = getOutputVal(tuple);
		// if (outputVal != UNDECIDABLE)
		// ctr.scp[outputPos].dom.forcedIndex = outputVal;
	}

}
