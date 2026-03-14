/*
 * This file is part of the constraint solver ACE (AbsCon Essence).
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS.
 *
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package optimization.linearization;

/**
 * A cut generator inspects the current LP solution and can append valid cuts
 * that tighten the relaxation before the next solve.
 */
public interface LpCutGenerator {

	String name();

	int generateCuts(CutGenerationContext context);
}
