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

import java.util.LinkedHashMap;
import java.util.Map;

import constraints.Constraint;
import dashboard.Output;
import utility.Kit.Color;

/**
 * This class is about coarse-grained profiling.
 * 
 * @author Christophe Lecoutre
 */
public final class Profiler {

	Map<Class<?>, Long> wcks = new LinkedHashMap<>();
	Map<Class<?>, Long> calls = new LinkedHashMap<>();

	public long initTime;

	private long start;

	private long varhTime, valhTime, revhTime, backTime, nogoTime, objpTime;
	private long varhCalls, valhCalls, revhCalls, backCalls, nogoCalls, objpCalls;

	public void before() {
		start = System.currentTimeMillis();
	}

	public void afterSelectingVariable() {
		varhTime += System.currentTimeMillis() - start;
		varhCalls++;
	}

	public void afterSelectingValue() {
		valhTime += System.currentTimeMillis() - start;
		valhCalls++;
	}

	public void afterSelectingInQueue() {
		revhTime += System.currentTimeMillis() - start;
		revhCalls++;
	}

	public void afterBacktracking() {
		backTime += System.currentTimeMillis() - start;
		backCalls++;
	}

	public void afterObjPropagator() {
		objpTime += System.currentTimeMillis() - start;
		objpCalls++;
	}

	public void afterFiltering(Constraint c) {
		if (!wcks.containsKey(c.getClass()))
			wcks.put((Class<?>) c.getClass(), 0L);
		wcks.computeIfPresent((Class<?>) c.getClass(), (k, v) -> v + (System.currentTimeMillis() - start));
		if (!calls.containsKey(c.getClass()))
			calls.put((Class<?>) c.getClass(), 0L);
		calls.computeIfPresent((Class<?>) c.getClass(), (k, v) -> v + 1);
	}

	public void afterNogoodFiltering() {
		nogoTime += System.currentTimeMillis() - start;
		nogoCalls++;
	}

	private String buildWith(String name, int size) {
		String s = name;
		for (int i = 0; i < size - name.length(); i++)
			s += " ";
		return s;
	}

	public void display(Constraint[] constraints) {
		Map<Class<?>, Long> nbs = new LinkedHashMap<>();
		for (Constraint c : constraints) {
			if (!nbs.containsKey(c.getClass()))
				nbs.put((Class<?>) c.getClass(), 0L);
			nbs.computeIfPresent((Class<?>) c.getClass(), (k, v) -> v + 1);
		}
		System.out.println("\n" + Output.COMMENT_PREFIX + Color.BLUE.coloring("Profiler"));
		for (Class<?> cl : wcks.keySet()) {
			String byConstraints = wcks.get(cl) + "/" + nbs.get(cl) + " = " + Stopwatch.df1.format(wcks.get(cl) / (double) nbs.get(cl));
			// String byCalls = wcks.get(cl) + "/" + calls.get(cl) + " = "
			// + (calls.get(cl) == 0 ? "NaN" : Stopwatch.df1.format(wcks.get(cl) / (double) calls.get(cl)));
			System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith(cl.getSimpleName(), 30)
					+ buildWith("wck: " + Output.numberFormat.format(wcks.get(cl)), 30)
					// + buildWith("percall: " + Stopwatch.df1.format(wcks.get(cl) / (double) calls.get(cl)), 30)
					+ "(" + Output.numberFormat.format(calls.get(cl)) + " calls, " + Output.numberFormat.format(nbs.get(cl)) + " ctrs)");
		}
		System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("NogooddReasoner", 30) + buildWith("wck: " + Output.numberFormat.format(nogoTime), 30)
				+ "(" + Output.numberFormat.format(nogoCalls) + " calls)");
		System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("ObjPropagator", 30) + buildWith("wck: " + Output.numberFormat.format(objpTime), 30)
				+ "(" + Output.numberFormat.format(objpCalls) + " calls)");
		System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("                      Sum: ", 30)
				+ buildWith("wck: " + Output.numberFormat.format(wcks.values().stream().reduce(0L, (a, v) -> a + v) + nogoTime + objpTime), 30));

		System.out.println();
		System.out
				.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("init", 30) + buildWith("wck: " + Output.numberFormat.format(initTime), 30));
		System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("varh", 30) + buildWith("wck: " + Output.numberFormat.format(varhTime), 30)
				+ "(" + Output.numberFormat.format(varhCalls) + " calls)");
		System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("valh", 30) + buildWith("wck: " + Output.numberFormat.format(valhTime), 30)
				+ "(" + Output.numberFormat.format(valhCalls) + " calls)");
		System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("revh", 30) + buildWith("wck: " + Output.numberFormat.format(revhTime), 30)
				+ "(" + Output.numberFormat.format(revhCalls) + " calls)");
		System.out.println(Output.COMMENT_PREFIX + Output.COMMENT_PREFIX + buildWith("back", 30) + buildWith("wck: " + Output.numberFormat.format(backTime), 30)
				+ "(" + Output.numberFormat.format(backCalls) + " calls)");
	}

}