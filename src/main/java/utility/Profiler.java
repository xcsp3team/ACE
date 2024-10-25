/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package utility;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import constraints.Constraint;
import dashboard.Output;
import utility.Kit.Color;

/**
 * This class is about coarse-grained profiling.
 * 
 * @author Christophe Lecoutre
 */
public final class Profiler {

	Map<Class<?>, Long> wcks = new HashMap<>();
	Map<Class<?>, Long> calls = new HashMap<>();

	private long start;

	public void beforeFiltering(Constraint c) {
		start = System.currentTimeMillis();
	}

	public void afterFiltering(Constraint c) {
		if (!wcks.containsKey(c.getClass()))
			wcks.put((Class<?>) c.getClass(), 0L);
		wcks.computeIfPresent((Class<?>) c.getClass(), (k, v) -> v + (System.currentTimeMillis() - start));
		if (!calls.containsKey(c.getClass()))
			calls.put((Class<?>) c.getClass(), 0L);
		calls.computeIfPresent((Class<?>) c.getClass(), (k, v) -> v + 1);

	}

	public void display(Constraint[] constraints) {
		Map<Class<?>, Long> nbs = new HashMap<>();
		for (Constraint c : constraints) {
			if (!nbs.containsKey(c.getClass()))
				nbs.put((Class<?>) c.getClass(), 0L);
			nbs.computeIfPresent((Class<?>) c.getClass(), (k, v) -> v + 1);
		}
		System.out.println("\n" + Output.COMMENT_PREFIX + Color.BLUE.coloring("Profiler"));
		for (Class<?> cl : wcks.keySet()) {
			String byConstraints = wcks.get(cl) + "/" + nbs.get(cl) + " = " + Stopwatch.df1.format(wcks.get(cl) / (double) nbs.get(cl));
//			String byCalls = wcks.get(cl) + "/" + calls.get(cl) + " = "
//					+ (calls.get(cl) == 0 ? "NaN" : Stopwatch.df1.format(wcks.get(cl) / (double) calls.get(cl)));
			System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + cl.getSimpleName() + "\t" + (cl.getSimpleName().length() > 11 ? "" : "\t")
					+ byConstraints + "\t" + "(" + calls.get(cl) + " calls)");
		}
	}

}