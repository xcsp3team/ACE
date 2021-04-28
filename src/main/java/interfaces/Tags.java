package interfaces;

public interface Tags {

	/**
	 * Tag for indicating that the code of an object (e.g., a constraint) is experimental
	 */
	interface TagExperimental {
	}

	/**
	 * Tag for indicating that a constraint is completely symmetric
	 */
	interface TagSymmetric {
	}

	/**
	 * Tag for indicating that a constraint is not symmetric at all
	 */
	interface TagNotSymmetric {
	}

	/**
	 * Tag for indicating that a constraint can produce full filtering at each call (not only around the specified event variable)
	 */
	interface TagFilteringCompleteAtEachCall {
	}

	/**
	 * Tag for indicating that a constraint does not guarantee enforcing (G)AC
	 */
	interface TagAC {
	}

	/**
	 * Tag for indicating that a constraint guarantees enforcing (G)AC
	 */
	interface TagNotAC {
	}

	/**
	 * Tag for indicating that a table constraint is negative (i.e., involves conflicts)
	 */
	interface TagNegative {
	}

	/**
	 * Tag for indicating that a table constraint is positive (i.., involves supports)
	 */
	interface TagPositive {
	}

	/**
	 * Tag for indicating that a table constraint is starred (i.e., involves *)
	 *
	 */
	interface TagStarred {
	}

	/**
	 * Tag for indicating that an object (e.g., an heuristic) aims at maximizing something
	 */
	interface TagMaximize {
	}

}
