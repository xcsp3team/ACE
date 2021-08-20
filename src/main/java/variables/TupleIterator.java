package variables;

import java.util.function.Consumer;
import java.util.function.Predicate;

import constraints.Constraint;

/**
 * This class allows us to iterate over the Cartesian product of the domains of a sequence of variables. For example, it allows us to find the first valid
 * tuple, or the next tuple that follows a specified (or last recorded) one. Each constraint is equipped with such an object. IMPORTANT: iterations are
 * performed with indexes of values, and not directly values.
 * 
 * @author Christophe Lecoutre
 */
public final class TupleIterator {

	/**
	 * The domains on which tuples can be iterated over.
	 */
	private final Domain[] doms;

	/**
	 * Indicates which values must be kept fixed during iteration
	 */
	private final boolean[] fixed;

	/**
	 * A local buffer, used to store a tuple, that is usually used by the object when performing an iteration.
	 */
	public final int[] buffer;

	/**
	 * The tuple that is used in the current iteration. It can be the local tuple or an external tuple (for example, for avoiding bidirectional copies during
	 * search of supports).
	 */
	private int[] currTuple;

	/**
	 * Builds an object that can be used to iterate over the (valid) tuples of the Cartesian product of the specified domains
	 * 
	 * @param doms
	 *            an array of domains
	 */
	public TupleIterator(Domain[] doms) {
		this.doms = doms;
		this.buffer = new int[doms.length];
		this.fixed = new boolean[doms.length];
	}

	private boolean isValidCurrTuple() {
		for (int i = currTuple.length - 1; i >= 0; i--)
			if (!doms[i].contains(currTuple[i]))
				return false;
		return true;
	}

	/**
	 * Sets the given index (of a value) fixed. It means that all valid tuples that will be iterated over will systematically involve the pair (x,a).
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 */
	private void fix(int x, int a) {
		assert doms[x].contains(a) : a + " no more in " + doms[x];
		currTuple[x] = a;
		fixed[x] = true;
	}

	/**
	 * Returns the first valid tuple that can be built. It is assumed that no domain is empty. The specified array becomes the current tuple.
	 * 
	 * @param buffer
	 *            an array where to store the tuple (containing indexes of values instead of values)
	 * @return the first valid tuple that can be built
	 */
	private int[] firstValidTuple(int[] buffer) {
		this.currTuple = buffer;
		for (int i = buffer.length - 1; i >= 0; i--) {
			buffer[i] = doms[i].first();
			fixed[i] = false;
		}
		return buffer;
	}

	/**
	 * Returns the first valid tuple that can be built. It is assumed that no domain is empty.
	 * 
	 * @return the first valid tuple that can be built
	 */
	public int[] firstValidTuple() {
		return firstValidTuple(buffer);
	}

	/**
	 * Returns the first valid tuple that can be built with the specified pair (x,a). The returned tuple is actually the specified one, which also becomes the
	 * current one.
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @param buffer
	 *            an array where to store the tuple (containing indexes of values instead of values)
	 * @return the first valid tuple that can be built with the specified pair (x,a)
	 */
	public int[] firstValidTupleWith(int x, int a, int[] buffer) {
		firstValidTuple(buffer);
		fix(x, a);
		return buffer;
	}

	/**
	 * Returns the first valid tuple that can be built with the specified pair (x,a). The specified index is assumed to be valid.
	 * 
	 * @param x
	 *            a variable
	 * @param a
	 *            an index (of value) for the variable
	 * @return the first valid tuple that can be built with the specified pair (x,a)
	 */
	public int[] firstValidTupleWith(int x, int a) {
		return firstValidTupleWith(x, a, buffer);
	}

	private int[] firstValidTupleWith(int x, int a, int y, int b, int[] buffer) {
		firstValidTuple(buffer);
		fix(x, a);
		fix(y, b);
		return buffer;
	}

	/**
	 * Returns the first valid tuple that can be built with the specified pairs (x,a) and (y,b). The specified indexes are assumed to be valid.
	 * 
	 * @param x
	 *            a first variable
	 * @param a
	 *            an index (of value) for the first variable
	 * @param y
	 *            a second variable
	 * @param b
	 *            an index (of value) for the second variable
	 * @return the first valid tuple that can be built with the specified pairs (x,a) and (y,b)
	 */
	public int[] firstValidTupleWith(int x, int a, int y, int b) {
		return firstValidTupleWith(x, a, y, b, buffer);
	}

	/**
	 * Sets the first available tuple greater than the current one from the given frontier.
	 * 
	 * @param frontier
	 *            modifications of the current tuple are only allowed from frontier (included) to 0
	 * @return the position of the last modified index (the closest to 0), or <code> -1 </code> if there is no more available tuple
	 */
	private int setNextValidTupleBefore(int frontier) {
		for (int i = frontier; i >= 0; i--) {
			if (fixed[i])
				continue;
			int a = doms[i].next(currTuple[i]);
			if (a != -1) {
				currTuple[i] = a;
				return i;
			} else
				currTuple[i] = doms[i].first();
		}
		return -1;
	}

	/**
	 * Sets the first available valid tuple strictly greater than the current one, which is assumed to be valid.
	 * 
	 * @return the position (the closest to 0) of the last modified index, or <code> -1 </code> if there is no more available tuple
	 */
	public final int nextValidTuple() {
		assert isValidCurrTuple();
		return setNextValidTupleBefore(doms.length - 1);
	}

	/**
	 * Sets the first available tuple strictly greater than the current one, which is not assumed to be necessarily valid (hence, the term 'cautiously').
	 * 
	 * @return the position (the closest to 0) of the last modified index, or <code> -1 </code> if there is no more available tuple
	 */
	public final int nextValidTupleCautiously() {
		int arity = doms.length;
		for (int i = 0; i < arity; i++)
			if (!doms[i].contains(currTuple[i])) { // i is the position (the closest to 0) of the first invalid index
				int modifiedPosition = setNextValidTupleBefore(i);
				if (modifiedPosition == -1)
					return -1;
				for (int j = i + 1; j < arity; j++)
					if (!fixed[j])
						currTuple[j] = doms[j].first();
				return modifiedPosition;
			}
		return nextValidTuple();
	}

	/**
	 * Consumes each valid tuple with the specified consumer from the current tuple (included)
	 * 
	 * @param p
	 *            a consumer
	 */
	public final void consumeValidTuples(Consumer<int[]> p) {
		assert isValidCurrTuple();
		do {
			p.accept(currTuple);
		} while (nextValidTuple() != -1);
	}

	/**
	 * Returns true if a valid tuple satisfying the specified constraint can be found from the current tuple (included)
	 * 
	 * @param c
	 *            a constraint
	 * @return true if a valid tuple satisfying the specified constraint can be found from the current tuple (included)
	 */
	public final boolean findValidTupleSatisfying(Constraint c) {
		assert isValidCurrTuple();
		do {
			if (c.checkIndexes(currTuple))
				return true;
		} while (nextValidTuple() != -1);
		return false;
	}

	/**
	 * Returns true if a valid tuple not satisfying the specified constraint can be found from the current tuple (included)
	 * 
	 * @param c
	 *            a constraint
	 * @return true if a valid tuple not satisfying the specified constraint can be found from the current tuple (included)
	 */
	public final boolean findValidTupleNotSatisfying(Constraint c) {
		assert isValidCurrTuple();
		do {
			if (!c.checkIndexes(currTuple))
				return true;
		} while (nextValidTuple() != -1);
		return false;
	}

	/**
	 * Returns true if a valid tuple checking the specified predicate can be found from the current tuple (included)
	 * 
	 * @param p
	 *            a predicate
	 * @return true if a valid tuple checking the specified predicate can be found from the current tuple (included)
	 */
	public final boolean findValidTupleChecking(Predicate<int[]> p) {
		assert isValidCurrTuple();
		do {
			if (p.test(currTuple))
				return true;
		} while (nextValidTuple() != -1);
		return false;
	}

	/**
	 * Returns the number of valid tuples checking the specified predicate
	 * 
	 * @param p
	 *            a predicate
	 * @return the number of valid tuples checking the specified predicate
	 */
	public final long countValidTuplesChecking(Predicate<int[]> p) {
		assert isValidCurrTuple();
		long cnt = 0;
		do {
			if (p.test(currTuple))
				cnt++;
		} while (nextValidTuple() != -1);
		return cnt;
	}

}