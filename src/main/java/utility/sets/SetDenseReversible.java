/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL
 * LIBRE CeCILL which accompanies this distribution, and is available at http://www.cecill.info
 */
package utility.sets;

import java.util.stream.IntStream;

import utility.Kit;

public class SetDenseReversible extends SetDense {
	public final int[] limits;

	public SetDenseReversible(int[] dense, boolean initiallyFull, int nLevels) {
		super(dense, initiallyFull);
		Kit.control(nLevels > 0);
		limits = IntStream.generate(() -> UNINITIALIZED).limit(nLevels).toArray();
	}

	public SetDenseReversible(int capacity, boolean initiallyFull, int nLevels) {
		this(IntStream.range(0, capacity).toArray(), initiallyFull, nLevels);
	}

	public SetDenseReversible(int capacity, int nLevels) {
		this(capacity, true, nLevels);
	}

	public final void storeLimitAtLevel(int level) {
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
	}

	public void restoreLimitAtLevel(int level) {
		if (limits[level] != UNINITIALIZED) {
			limit = limits[level];
			limits[level] = UNINITIALIZED;
		}
	}

	public void moveLimitAtLevel(int gap, int level) {
		assert limit - gap >= -1;
		storeLimitAtLevel(level);
		limit -= gap;
	}

	public void removeAtPosition(int i, int level) {
		assert 0 <= i && i <= limit;
		if (limits[level] == UNINITIALIZED)
			limits[level] = limit;
		int e = dense[i];
		dense[i] = dense[limit];
		dense[limit] = e;
		limit--;
		// For efficiency reasons (method at the heart of propagation), we do not use the following equivalent code:
		// storeLimitAtLevel(level);
		// removeAtPosition(i);
	}
}
