/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package interfaces;

/**
 * These are the interfaces used as tags.
 * 
 * @author Christophe Lecoutre
 */
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
	interface TagCallCompleteFiltering {
	}

	/**
	 * Tag for indicating that a constraint does not necessarily produce full filtering at each call
	 */
	interface TagNotCallCompleteFiltering {
	}

	/**
	 * Tag for indicating that a constraint guarantees enforcing (G)AC
	 */
	interface TagAC {
	}

	/**
	 * Tag for indicating that a constraint does not guarantee enforcing (G)AC
	 */
	interface TagNotAC {
	}

	/**
	 * Tag for indicating that an object (e.g., a constraint) is able to reason on bounds (of domains).
	 */
	interface TagBoundCompatible {
	}

	/**
	 * Tag for indicating that a constraint can be postponed when filtering (requires a propagator independent of which variables (domains) were recently
	 * reduced)
	 */
	interface TagPostponableFiltering {
	}

	/**
	 * Tag for indicating that a table constraint is negative (i.e., contains conflicts)
	 */
	interface TagNegative {
	}

	/**
	 * Tag for indicating that a table constraint is positive (i.e., contains supports)
	 */
	interface TagPositive {
	}

	/**
	 * Tag for indicating that a constraint may contain starred elements (i.e., may contain *)
	 */
	interface TagStarredCompatible {
	}

	/**
	 * Tag for indicating that an object (e.g., an heuristic) aims at maximizing an expression (variable, sum, maximum, etc.)
	 */
	interface TagMaximize {
	}

}
