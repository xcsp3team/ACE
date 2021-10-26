package sets;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.IntStream;

/**
 * A reversible sparse set is a sparse set that can be handled at different levels (for technical reasons, this class
 * does not inherit from SetSparse but from SetDenseReversible).
 * 
 * @author Christophe Lecoutre
 */
public class SetSparseReversible extends SetDenseReversible {

	/**
	 * The array for checking the presence of an index.
	 */
	public int[] sparse;

	/**
	 * Builds a reversible sparse set with the specified capacity and the specified number of possible levels. The
	 * sparse set is simple, meaning that it is aimed at containing indexes 0, 1, 2, ... Initially, the set is full or
	 * empty depending on the value of the specified boolean.
	 * 
	 * @param capacity
	 *            the capacity of the sparse set
	 * @param nLevels
	 *            the number of different levels at which the set can be handled
	 * @param initiallyFull
	 *            if true, the set is initially full, empty otherwise
	 */
	public SetSparseReversible(int capacity, int nLevels, boolean initiallyFull) {
		super(capacity, nLevels, initiallyFull);
		this.sparse = IntStream.range(0, capacity).toArray();
		control(Arrays.equals(dense, sparse));
	}

	/**
	 * Builds a reversible sparse set with the specified capacity and the specified number of possible levels. The
	 * sparse set is simple, meaning that it is aimed at containing indexes 0, 1, 2, ... Initially, the set is full.
	 * 
	 * @param capacity
	 *            the capacity of the sparse set
	 * @param nLevels
	 *            the number of different levels at which the set can be handled
	 */
	public SetSparseReversible(int capacity, int nLevels) {
		this(capacity, nLevels, true);
	}

	@Override
	public boolean contains(int a) {
		return sparse[a] <= limit;
	}

	@Override
	public boolean add(int a) {
		assert !contains(a) : sparse[a] + " " + limit;
		int i = sparse[a];
		limit++;
		if (i > limit) {
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[b] = i;
			sparse[a] = limit;
		}
		return true;
	}

	/**
	 * Adds the specified element at the specified level
	 * 
	 * @param a
	 *            an element (typically, index of value)
	 * @param level
	 *            the level at which the element is added
	 */
	public void add(int a, int level) {
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		add(a);
	}

	/**
	 * Removes the specified element. IMPORTANT: if this method is called directly, one must manage apart the
	 * information concerning the level at which the element is removed.
	 * 
	 * @param a
	 *            an element (typically, index of value)
	 * @return true if the element has been removed
	 */
	public boolean remove(int a) {
		int i = sparse[a];
		if (i > limit)
			return false; // not removed because not present
		if (i != limit) {
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[a] = limit;
			sparse[b] = i;
		}
		limit--;
		return true; // removed
	}

	@Override
	public int removeAtPosition(int i) {
		assert 0 <= i && i <= limit;
		if (i != limit) {
			int a = dense[i];
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[a] = limit;
			sparse[b] = i;
		}
		limit--;
		return dense[limit + 1];
	}

	/**
	 * Removes the specified element at the specified level
	 * 
	 * @param a
	 *            an element (typically, index of value)
	 * @param level
	 *            the level at which the element is removed
	 */
	public void remove(int a, int level) {
		assert contains(a) : sparse[a] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		remove(a);
	}

	/**
	 * Reduces the set to the specified element at the specified level
	 * 
	 * @param a
	 *            an element (typically, index of value)
	 * @param level
	 *            the level at which the set is reduced to a
	 */
	public void reduceTo(int a, int level) {
		assert contains(a) : sparse[a] + " " + limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int i = sparse[a];
		if (i != 0) {
			int b = dense[0];
			dense[i] = b;
			dense[0] = a;
			sparse[b] = i;
			sparse[a] = 0;
		}
		limit = 0;
	}

	@Override
	public void swapAtPositions(int i, int j) {
		int a = dense[i];
		int b = dense[j];
		dense[i] = b;
		dense[j] = a;
		sparse[b] = i;
		sparse[a] = j;
	}
}
