/*
 * This file is part of the constraint solver ACE. 
 *
 * Copyright (c) 2026. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package utility;

import static dashboard.Output.COMMENT_PREFIX;
import static dashboard.Output.numberFormat;

import java.util.Map;
import java.util.TreeMap;

import constraints.Constraint;
import utility.Kit.Color;

/**
 * This class is about coarse-grained profiling.
 * 
 * @author Christophe Lecoutre
 */
public interface Profiler {

	void before();

	void afterSelectingVariable();

	void afterSelectingValue();

	void afterSelectingInQueue();

	void afterBacktracking();

	void afterObjPropagator();

	void afterFiltering(Constraint c);

	void afterNogoodFiltering();

	void initTime(long time);

	void display(Constraint[] constraints);

	public final class ProfilerFake implements Profiler {

		public void before() {
		}

		public void afterSelectingVariable() {
		}

		public void afterSelectingValue() {
		}

		public void afterSelectingInQueue() {
		}

		public void afterBacktracking() {
		}

		public void afterObjPropagator() {
		}

		public void afterFiltering(Constraint c) {
		}

		public void afterNogoodFiltering() {
		}

		public void initTime(long time) {
		}

		public void display(Constraint[] constraints) {
		}
	}

	public final class ProfilerReal implements Profiler {

		Map<String, Long> wcks = new TreeMap<>();
		Map<String, Long> calls = new TreeMap<>();

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
			String s = c.getClass().getSimpleName();
			if (!wcks.containsKey(s))
				wcks.put(s, 0L);
			wcks.computeIfPresent(s, (k, v) -> v + (System.currentTimeMillis() - start));
			if (!calls.containsKey(s))
				calls.put(s, 0L);
			calls.computeIfPresent(s, (k, v) -> v + 1);
		}

		public void afterNogoodFiltering() {
			nogoTime += System.currentTimeMillis() - start;
			nogoCalls++;
		}

		public void initTime(long time) {
			this.initTime = time;
		}

		private String buildWith(String name, int size) {
			String s = name;
			for (int i = 0; i < size - name.length(); i++)
				s += " ";
			return s;
		}

		public void display(Constraint[] constraints) {
			Map<String, Long> nbs = new TreeMap<>();
			for (Constraint c : constraints) {
				String s = c.getClass().getSimpleName();
				if (!nbs.containsKey(s))
					nbs.put(s, 0L);
				nbs.computeIfPresent(s, (k, v) -> v + 1);
			}
			System.out.println("\n" + COMMENT_PREFIX + Color.BLUE.coloring("Profiler"));
			for (String cl : wcks.keySet()) {
				String byConstraints = wcks.get(cl) + "/" + nbs.get(cl) + " = " + Stopwatch.df1.format(wcks.get(cl) / (double) nbs.get(cl));
				// String byCalls = wcks.get(cl) + "/" + calls.get(cl) + " = "
				// + (calls.get(cl) == 0 ? "NaN" : Stopwatch.df1.format(wcks.get(cl) / (double) calls.get(cl)));
				System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith(cl, 30) + buildWith("wck: " + numberFormat.format(wcks.get(cl)), 30)
				// + buildWith("percall: " + Stopwatch.df1.format(wcks.get(cl) / (double) calls.get(cl)), 30)
						+ "(" + numberFormat.format(calls.get(cl)) + " calls, " + numberFormat.format(nbs.get(cl)) + " ctrs)");
			}
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("NogooddReasoner", 30) + buildWith("wck: " + numberFormat.format(nogoTime), 30) + "("
					+ numberFormat.format(nogoCalls) + " calls)");
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("ObjPropagator", 30) + buildWith("wck: " + numberFormat.format(objpTime), 30) + "("
					+ numberFormat.format(objpCalls) + " calls)");
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("                      Sum: ", 30)
					+ buildWith("wck: " + numberFormat.format(wcks.values().stream().reduce(0L, (a, v) -> a + v) + nogoTime + objpTime), 30));

			System.out.println();
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("init", 30) + buildWith("wck: " + numberFormat.format(initTime), 30));
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("varh", 30) + buildWith("wck: " + numberFormat.format(varhTime), 30) + "("
					+ numberFormat.format(varhCalls) + " calls)");
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("valh", 30) + buildWith("wck: " + numberFormat.format(valhTime), 30) + "("
					+ numberFormat.format(valhCalls) + " calls)");
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("revh", 30) + buildWith("wck: " + numberFormat.format(revhTime), 30) + "("
					+ numberFormat.format(revhCalls) + " calls)");
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("back", 30) + buildWith("wck: " + numberFormat.format(backTime), 30) + "("
					+ numberFormat.format(backCalls) + " calls)");
			System.out.println(COMMENT_PREFIX + COMMENT_PREFIX + buildWith("                      Sum: ", 30)
					+ buildWith("wck: " + numberFormat.format(initTime + varhTime + valhTime + revhTime + backTime), 30));

		}

	}

}