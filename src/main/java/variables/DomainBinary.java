package variables;

import java.util.stream.IntStream;

import propagation.Propagation;
import sets.SetLinkedBinary;

/**
 * A binary domain for a variable (from a constraint network).
 * 
 * @author Christophe Lecoutre
 *
 */
public final class DomainBinary extends SetLinkedBinary implements Domain {

	private Variable var;

	private Integer typeIdentifier;

	private Propagation propagation;

	private Boolean indexesMatchValues;

	private int firstValue, secondValue; // typically, 0 and 1

	@Override
	public final Variable var() {
		return var;
	}

	@Override
	public final int typeIdentifier() {
		return typeIdentifier != null ? typeIdentifier : (typeIdentifier = Domain.typeIdentifierFor(firstValue, secondValue));
	}

	@Override
	public final Propagation propagation() {
		return propagation;
	}

	@Override
	public final void setPropagation(Propagation propagation) {
		this.propagation = propagation;
	}

	@Override
	public final boolean indexesMatchValues() {
		return indexesMatchValues != null ? indexesMatchValues : (indexesMatchValues = IntStream.range(0, initSize()).noneMatch(a -> a != toVal(a)));
	}

	/**
	 * Builds a binary domain for the specified variable from the specified values
	 * 
	 * @param var
	 *            the variable to which the domain is associated
	 * @param firstValue
	 *            the first value of the domain
	 * @param secondValue
	 *            the second value of the domain
	 */
	public DomainBinary(Variable var, int firstValue, int secondValue) {
		this.var = var;
		this.firstValue = firstValue;
		this.secondValue = secondValue;
	}

	@Override
	public int toIdx(int v) {
		return v == firstValue ? 0 : v == secondValue ? 1 : -1;
	}

	@Override
	public int toVal(int a) {
		assert a == 0 || a == 1;
		return a == 0 ? firstValue : secondValue;
	}

	@Override
	public Object allValues() {
		return new int[] { firstValue, secondValue };
	}

	@Override
	public String toString() {
		return "dom(" + var() + ")";
	}
}
