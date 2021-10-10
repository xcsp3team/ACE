package sets;

import static utility.Kit.control;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import utility.Kit;

/**
 * A sparse set is basically composed of two arrays (of integers) and a limit: at any time, it contains the elements
 * (typically, indexes of values) in the array 'dense' at indexes ranging from 0 to the limit (included). The presence
 * of elements can be checked with the array 'sparse'. Sparse sets are always simple, meaning that values in 'dense' are
 * necessarily indexes 0, 1, 2, ... Besides, we have dense[sparse[value]] = value.
 * 
 * @author Christophe Lecoutre
 */
public class SetSparse extends SetDense {

	/**
	 * The array for checking the presence of an index.
	 */
	public int[] sparse;

	/**
	 * Builds a sparse set with the specified capacity. The sparse set is simple, meaning that it is aimed at containing
	 * indexes 0, 1, 2, ... Initially, the set is full or empty depending on the value of the specified boolean.
	 * 
	 * @param capacity
	 *            the capacity of the sparse set
	 * @param initiallyFull
	 *            if true, the set is initially full, empty otherwise
	 */
	public SetSparse(int capacity, boolean initiallyFull) {
		super(capacity, initiallyFull);
		this.sparse = Kit.range(capacity);
		control(Arrays.equals(dense, sparse));
	}

	/**
	 * Builds a sparse set with the specified capacity. The sparse set is simple, meaning that it is aimed at containing
	 * indexes 0, 1, 2, ... Initially, the set is empty.
	 * 
	 * @param capacity
	 *            the capacity of the sparse set
	 */
	public SetSparse(int capacity) {
		this(capacity, false);
	}

	@Override
	public void increaseCapacity() {
		super.increaseCapacity(); // note that dense.length is the new capacity
		sparse = IntStream.range(0, dense.length).map(i -> i < sparse.length ? sparse[i] : i).toArray();
	}

	@Override
	public boolean contains(int a) {
		return sparse[a] <= limit;
	}

	@Override
	public boolean add(int a) {
		int i = sparse[a];
		if (i <= limit)
			return false; // not added because already present
		limit++;
		if (i > limit) {
			int b = dense[limit];
			dense[i] = b;
			dense[limit] = a;
			sparse[a] = limit;
			sparse[b] = i;
		}
		return true; // added
	}

	@Override
	public void swapAtPositions(int i, int j) {
		int a = dense[i];
		int b = dense[j];
		dense[i] = b;
		dense[j] = a;
		sparse[a] = j;
		sparse[b] = i;
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
	 * Removes the specified index
	 * 
	 * @param a
	 *            an index
	 * @return true if the element has been removed (because present)
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

	/**
	 * Removes all indexes from the specified array/set
	 * 
	 * @param set
	 *            an array of indexes
	 */
	public final void removeAll(int[] set) {
		for (int i = 0; i < set.length; i++)
			remove(set[i]);
	}

	/**
	 * Removes all indexes from the specified set
	 * 
	 * @param set
	 *            a dense set
	 */
	public final void removeAll(SetDense set) {
		for (int i = 0; i < set.size(); i++)
			remove(set.dense[i]);
	}

	/**
	 * Swaps the two specified indexes
	 * 
	 * @param a
	 *            a first index
	 * @param b
	 *            a second index
	 */
	public final void swap(int a, int b) {
		int i = sparse[a];
		int j = sparse[b];
		dense[i] = b;
		dense[j] = a;
		sparse[a] = j;
		sparse[b] = i;
	}

	public final void moveElementsAt(int oldTailLimit) {
		int nSwaps = Math.min(limit + 1, oldTailLimit - limit);
		for (int i = 0; i < nSwaps; i++) {
			int j = oldTailLimit - i;
			int a = dense[i];
			int b = dense[j];
			dense[i] = b;
			dense[j] = a;
			sparse[a] = j;
			sparse[b] = i;
		}

	}

	@Override
	public String toString() {
		return super.toString() + "\nsparse={" + IntStream.range(0, size()).mapToObj(i -> sparse[i] + "").collect(Collectors.joining(",")) + "}";
	}
}
