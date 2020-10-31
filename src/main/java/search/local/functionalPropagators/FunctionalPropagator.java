package search.local.functionalPropagators;

import java.util.List;

import org.xcsp.common.enumerations.EnumerationCartesian;

import constraints.Constraint;
import utility.Kit;
import variables.Variable;
import variables.domains.Domain;

public abstract class FunctionalPropagator {

	public static class FunctionalPropagatorDirect extends FunctionalPropagator {

		public FunctionalPropagatorDirect(Constraint c, int outputPos) {
			super(c, outputPos);
		}

		@Override
		protected int getOutputVal(int[] tuple) {
			Domain dom = c.scp[outputPos].dom;
			int output = -1;
			for (int idx = 0; idx < dom.initSize(); idx++) {
				tuple[outputPos] = idx;
				if (c.checkIndexes(tuple))
					if (output != -1)
						return UNDECIDABLE;
					else
						output = idx;
			}
			assert (output != -1);
			return output;
		}
	}

	public static class FunctionalPropagatorPreComputed extends FunctionalPropagator {

		protected int[] encodedOutputs;

		int[][] buildArraysWithCurrentIndexes(Variable[] vars) {
			int[][] m = new int[vars.length][];
			for (int i = 0; i < m.length; i++)
				m[i] = vars[i].dom.indexes();
			return m;
		}

		public FunctionalPropagatorPreComputed(Constraint c, int outputPos, int encodingSize) {
			super(c, outputPos);
			encodedOutputs = Kit.repeat(-1, encodingSize);

			int[][] tuples = new EnumerationCartesian(buildArraysWithCurrentIndexes(c.scp), false).toArray();
			for (int[] tuple : tuples) {
				if (c.checkIndexes(tuple)) {
					int key = encode(tuple);
					encodedOutputs[key] = encodedOutputs[key] == -1 ? tuple[outputPos] : UNDECIDABLE;
				}
			}
		}

		protected int encode(int[] tuple) {
			int key = 0;
			int base = 1;
			for (int i = 0; i < tuple.length; i++) {
				if (i != outputPos) {
					key += tuple[i] * base;
					base *= c.scp[i].dom.initSize();
				}
			}
			return key;
		}

		@Override
		protected int getOutputVal(int[] tuple) {
			return encodedOutputs[encode(tuple)];
		}
	}

	/**********************************************************************************************
	 * Start of static section
	 *********************************************************************************************/

	static final int UNDECIDABLE = Integer.MIN_VALUE;

	private static final int MAX_SIZE_FOR_ENCODING = 1000000;

	/**
	 * @param c
	 *            : the constraint over which the propagator is built.
	 * @param outputPos
	 *            : the position of the variable which value can be inferred from the values of the others.
	 * @return A FunctionalPropagatorPreComputed if the cartesian product of the domains is small enough, a FunctionalPropagatorDirect otherwise.
	 */
	public static FunctionalPropagator buildFunctionalPropagator(Constraint c, int outputPos) {
		int encodingSize = 1;
		for (int i = 0; i < c.scp.length; i++)
			if (i != outputPos)
				if (Integer.MAX_VALUE / c.scp[i].dom.initSize() < encodingSize)
					return new FunctionalPropagatorDirect(c, outputPos);
				else
					encodingSize *= c.scp[i].dom.initSize();
		return encodingSize > MAX_SIZE_FOR_ENCODING ? new FunctionalPropagatorDirect(c, outputPos)
				: new FunctionalPropagatorPreComputed(c, outputPos, encodingSize);
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
					if (first.c.involves(second.c.scp[second.outputPos])) {
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

	public final Constraint c;
	public final int outputPos;

	public FunctionalPropagator(Constraint c, int outputPos) {
		this.c = c;
		this.outputPos = outputPos;
	}

	/**
	 * @param tuple
	 *            : the current instantiation of the variables in the constraint's scope, the unknown variable can take any value since it is unused
	 * @return the new value of the unknown variable, or UNDECIDABLE if the constraint could not propagate
	 */
	protected abstract int getOutputVal(int[] tuple);

	public void propagate() {
		Variable[] scp = c.scp;
		int[] tuple = new int[scp.length];
		for (int i = 0; i < tuple.length; i++)
			tuple[i] = scp[i].dom.unique();
		// int outputVal = getOutputVal(tuple);
		// if (outputVal != UNDECIDABLE)
		// ctr.scp[outputPos].dom.forcedIndex = outputVal;
	}

}
