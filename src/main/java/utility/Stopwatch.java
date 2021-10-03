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

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.text.DecimalFormat;
import java.text.DecimalFormatSymbols;
import java.util.Arrays;
import java.util.Locale;

/**
 * A stopwatch is used to measure the time taken by some operations, when solving a problem.
 * 
 * @author Christophe Lecoutre
 */
public class Stopwatch {

	private static DecimalFormat df1 = new DecimalFormat("0.0", new DecimalFormatSymbols(Locale.US));

	private static DecimalFormat df2 = new DecimalFormat("0.00", new DecimalFormatSymbols(Locale.US));

	/**
	 * Returns a string representing a formatted time in seconds for the specified time (in milliseconds)
	 * 
	 * @param time
	 *            a time given in milliseconds
	 * @return a string representing a formatted time in seconds
	 */
	public static String formattedTimeInSeconds(long time) {
		double l = time / 1000.0;
		return l < 10 ? df2.format(l) : df1.format(l);
	}

	/**
	 * This field indicates whether CPU time can be computed
	 */
	private boolean cpuTimeSupported;

	/**
	 * The start wall clock time
	 */
	private long starWckTime;

	/**
	 * Builds a stopwatch and starts it
	 */
	public Stopwatch() {
		cpuTimeSupported = ManagementFactory.getThreadMXBean().isCurrentThreadCpuTimeSupported();
		start();
	}

	private long computeCpuTime() {
		assert cpuTimeSupported;
		ThreadMXBean threads = ManagementFactory.getThreadMXBean();
		return Arrays.stream(threads.getAllThreadIds()).map(id -> threads.getThreadCpuTime(id)).sum();
		// return time; // ManagementFactory.getThreadMXBean().getCurrentThreadCpuTime();
	}

	/**
	 * Starts the stopwatch
	 */
	public void start() {
		starWckTime = System.currentTimeMillis();
	}

	/**
	 * Returns the wall clock time in milliseconds, elapsed since the stopwatch has been started
	 * 
	 * @return the wall clock time in milliseconds
	 */
	public long wckTime() {
		return System.currentTimeMillis() - starWckTime;
	}

	/**
	 * Returns the wall clock time in seconds, elapsed since the stopwatch has been started
	 * 
	 * @return the wall clock time in seconds
	 */
	public String wckTimeInSeconds() {
		return formattedTimeInSeconds(System.currentTimeMillis() - starWckTime);
	}

	/**
	 * Returns the CPU time in milliseconds, or -1 if not supported. This is the CPU (of all involved threads) since the
	 * solver has been launched. Important: avoid calling it too many times as it may be rather expensive.
	 * 
	 * @return the CPU time in milliseconds, or -1 if not supported
	 */
	public long cpuTime() {
		return cpuTimeSupported ? computeCpuTime() / 1000000 : -1;
	}

	/**
	 * Returns the CPU time in seconds, or -1 if not supported. This is the CPU (of all involved threads) since the
	 * solver has been launched. Important: avoid calling it too many times as it may be rather expensive.
	 * 
	 * @return the CPU time in seconds, or -1 if not supported
	 */
	public String cpuTimeInSeconds() {
		return cpuTimeSupported ? cpuTime() / 1000.0 + "" : "-1";
	}
}