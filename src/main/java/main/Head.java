/*
 * This file is part of the constraint solver ACE (AbsCon Essence). 
 *
 * Copyright (c) 2021. All rights reserved.
 * Christophe Lecoutre, CRIL, Univ. Artois and CNRS. 
 * 
 * Licensed under the MIT License.
 * See LICENSE file in the project root for full license information.
 */

package main;

import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.toCollection;
import static org.xcsp.common.Constants.PLUS_INFINITY;
import static utility.Kit.control;
import static utility.Kit.log;

import java.io.File;
import java.io.FileInputStream;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarInputStream;
import java.util.stream.Stream;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.ConstraintExtension;
import constraints.ConstraintIntension.IntensionStructure;
import constraints.extension.structures.Bits;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.MDD;
import dashboard.Control;
import dashboard.Input;
import dashboard.Output;
import heuristics.HeuristicRevisions;
import heuristics.HeuristicValues;
import heuristics.HeuristicVariables;
import interfaces.Observers.ObserverOnConstruction;
import problem.Problem;
import problem.Problem.SymmetryBreaking;
import propagation.Propagation;
import solver.Solver;
import utility.Kit;
import utility.Kit.Color;
import utility.Reflector;
import utility.Stopwatch;

/**
 * This is the class of the main object (head) in charge of solving a problem instance.
 * 
 * @author Christophe Lecoutre
 */
public class Head extends Thread {

	/**********************************************************************************************
	 * Static members
	 *********************************************************************************************/

	/**
	 * The set of objects in charge of solving a problem. Typically, there is only one object. However, in portfolio mode, it contains more than one object.
	 */
	private static Head[] heads;

	/**
	 * Method called in portfolio mode (not the usual case). This mode needs to be entirely revised (and so, should not be used for the moment).
	 * 
	 * @param head
	 *            a main resolution object
	 */
	public synchronized static void saveMultithreadResultsFiles(Head head) {
		String fileName = head.output.save(head.stopwatch.wckTime());
		if (fileName != null) {
			String variantParallelName = Kit.attValueFor(Input.lastArgument(), Input.VARIANT_PARALLEL, Input.NAME);
			String resultsFilename = head.control.general.campaignDir;
			if (resultsFilename.length() != 0)
				resultsFilename += File.separator;
			resultsFilename += Output.RESULTS_DIRECTORY + File.separator + head.output.outputFileNameFrom(head.problem.name(), variantParallelName);
			Kit.copy(fileName, resultsFilename);
			Document document = Kit.load(resultsFilename);
			Kit.modify(document, Output.RESOLUTIONS, Output.CONFIGURATION_FILE_NAME, variantParallelName);
			long totalWCKTime = 0;
			long totalVisitedNodes = 0;
			for (Head h : heads) {
				totalWCKTime += h.instanceStopwatch.wckTime();
				totalVisitedNodes += h.solver.stats.nNodes;
			}
			Element root = document.getDocumentElement();
			Element multiThreadedResults = document.createElement(Output.MULTITHREAD_RESULTS);
			multiThreadedResults.setAttribute(Output.WCK, Double.toString((double) totalWCKTime / 1000));
			multiThreadedResults.setAttribute(Output.N_NODES, Long.toString(totalVisitedNodes));
			root.appendChild(multiThreadedResults);
			Utilities.save(document, resultsFilename);
		}
	}

	private static boolean isAvailableIn() {
		try {
			return System.in.available() > 0;
		} catch (Throwable e) {
			return (Boolean) Kit.exit(e);
		}
	}

	private final static String[] loadVariantNames() {
		if (Input.portfolio) {
			String prefix = Output.SETTINGS_DIRECTORY + File.separator;
			File file = new File(prefix);
			if (!file.exists())
				file.mkdirs();
			else
				control(file.isDirectory());
			return Input.loadSequentialVariants(Input.controlFilename, Input.lastArgument(), prefix);
		}
		return new String[] { Input.controlFilename };
	}

	/**
	 * Starts the main function of the constraint solver ACE (when solving a CSP or COP instance)
	 * 
	 * @param args
	 *            arguments specified by the user
	 */
	public static void main(String[] args) {
		if (args.length == 0 && !isAvailableIn())
			new Head().control.display(); // the usage is displayed
		else {
			Input.loadArguments(args); // always start with that
			// heads (threads) are built and started
			heads = Stream.of(loadVariantNames()).map(v -> new Head(v)).peek(h -> h.start()).toArray(Head[]::new);
		}
	}

	/**********************************************************************************************
	 * Inner classes for available classes and shared structures
	 *********************************************************************************************/

	/**
	 * This class is useful for storing in a map several entries (key, value) where the value is a set of (available) classes that inherit from a root class
	 * (the key).
	 */
	public static class AvailableClasses {

		private static final String DOT_CLASS = ".class";

		/**
		 * The map that associates all available classes (value) that inherit from a class (key)
		 */
		private Map<Class<?>, Set<Class<?>>> map = new LinkedHashMap<>();

		/**
		 * Returns all available classes (value) that inherit from the specified class (seen as a key)
		 * 
		 * @param clazz
		 *            a class
		 * @return all available classes that inherit from the specified class
		 */
		public Set<Class<?>> get(Class<?> clazz) {
			return map.get(clazz);
		}

		private boolean dealWith(Class<?> clazz, Class<?> rootClass) {
			if (rootClass.isAssignableFrom(clazz)) {
				map.computeIfAbsent(rootClass, r -> new LinkedHashSet<>()).add(clazz);
				return true;
			}
			return false;
		}

		private boolean dealWith(Class<?> clazz) {
			if (Modifier.isAbstract(clazz.getModifiers()))
				return false;
			return dealWith(clazz, HeuristicVariables.class) || dealWith(clazz, HeuristicValues.class) || dealWith(clazz, HeuristicRevisions.class)
					|| dealWith(clazz, ConstraintExtension.class) || dealWith(clazz, Propagation.class);
		}

		private void loadRecursively(File directory, String packageName) throws ClassNotFoundException {
			packageName = packageName.startsWith(".") ? packageName.substring(1) : packageName;
			for (File file : directory.listFiles())
				if (file.isDirectory()) {
					control(!file.getName().contains("."));
					loadRecursively(file, packageName + "." + file.getName());
				} else if (file.getName().endsWith(DOT_CLASS) && file.getName().charAt(0) != '/')
					// above, second part of the condition for a class in the default package
					dealWith(Class.forName(packageName + '.' + file.getName().substring(0, file.getName().length() - DOT_CLASS.length())));
		}

		private AvailableClasses() {
			// we load classes
			try {
				// first, we load classes from jar files (this is necessary when ACE is run from a jar)
				for (String token : System.getProperty("java.class.path", ".").split(File.pathSeparator))
					if (token.endsWith(".jar")) {
						try (JarInputStream jarFile = new JarInputStream(new FileInputStream(token))) {
							while (true) {
								JarEntry jarEntry = jarFile.getNextJarEntry();
								if (jarEntry == null)
									break;
								if (jarEntry.getName().endsWith(DOT_CLASS))
									try {
										String s = jarEntry.getName().replaceAll("/", "\\.");
										dealWith(Class.forName(s.substring(0, s.lastIndexOf("."))));
									} catch (Throwable e) {
										Kit.log.fine("Impossible to load" + jarEntry.getName());
									}
							}
						} catch (Exception e) {
							Kit.warning("either a jar is not found or there is a problem with " + token); // e.printStackTrace();
						}
					}
				// next, we load loaded classes
				ClassLoader classLoader = Thread.currentThread().getContextClassLoader();
				// however, if we need to look at unloaded classes, as for example some in a subclass of Propagation, we
				// need to put lines as this one: Class<?> _ = Propagation.class;
				for (Package p : Package.getPackages()) {
					String name = p.getName();
					if (!name.startsWith("constraints") && !name.startsWith("heuristics") && !name.startsWith("propagation"))
						continue;
					for (URL url : Collections.list(classLoader.getResources(p.getName().replace('.', '/'))))
						if (url.getProtocol().equals("file") && new File(url.getFile()).exists())
							loadRecursively(new File(url.getFile()), p.getName());
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		@Override
		public String toString() {
			return map.entrySet().stream().map(e -> e.getKey() + " : " + e.getValue().stream().map(c -> c.getName()).collect(joining(" ")))
					.collect(joining("\n"));
		}
	}

	/**
	 * This class stores information (through maps) about shared data structures, concerning intension, extension and MDD constraints
	 */
	public static class StructureSharing {

		/**
		 * The map that associates an intension structure (tree evaluator) with an intension constraint key
		 */
		public Map<String, IntensionStructure> mapForIntension = new LinkedHashMap<>();

		/**
		 * The map that associates an extension structure with an extension constraint key
		 */
		public Map<String, ExtensionStructure> mapForExtension = new LinkedHashMap<>();

		/**
		 * The map that associates an MDD with an MDD constraint key
		 */
		public Map<String, MDD> mapForMDDs = new LinkedHashMap<>();

		/**
		 * Clears all maps that stores information about the sharing of data structures
		 */
		public void clear() {
			mapForIntension.clear();
			mapForExtension.clear();
			mapForMDDs.clear();
			Bits.map.clear();
		}
	}

	/**********************************************************************************************
	 * Class members
	 *********************************************************************************************/

	/**
	 * The current problem instance to be solved
	 */
	public Problem problem;

	/**
	 * The solver used to solve the current problem instance
	 */
	public Solver solver;

	/**
	 * The object that stores all parameters for piloting the solving process
	 */
	public final Control control;

	/**
	 * The object that handles the output of the solving process (typically, on the standard output)
	 */
	public final Output output;

	/**
	 * The construction observers that are systematically recorded, whatever is the problem instance to be solved
	 */
	private final List<ObserverOnConstruction> permamentObserversConstruction;

	/**
	 * The construction observers that are recorded with respect to the current instance to be solved
	 */
	public List<ObserverOnConstruction> observersConstruction = new ArrayList<>();

	/**
	 * The index of the current problem instance to be solved. of course, when there is only one instance to be solved, this is 0.
	 */
	public int instanceIndex;

	/**
	 * The object that allows us to get (through a map) all available classes that inherit from a class
	 */
	public AvailableClasses availableClasses = new AvailableClasses();

	/**
	 * The object that stores information (through maps) about shared data structures, concerning intension, extension and MDD constraints
	 */
	public StructureSharing structureSharing = new StructureSharing();

	/**
	 * The object that may be used in different steps of resolution: randomization of heuristics, generation of random solutions,...
	 */
	public Random random;

	/**
	 * The main stopwatch
	 */
	public final Stopwatch stopwatch = new Stopwatch();

	/**
	 * The stopwatch used when solving an instance
	 */
	public final Stopwatch instanceStopwatch = new Stopwatch();

	/**
	 * @return true if unary constraints must be preserved (and not be directly taken into account by reducing variable domains)
	 */
	public boolean mustPreserveUnaryConstraints() {
		return control.constraints.preserve1 || this instanceof HeadExtraction || control.problem.symmetryBreaking != SymmetryBreaking.NO
				|| problem.framework == TypeFramework.MAXCSP;
	}

	/**
	 * @return true if time has expired for solving the current problem instance
	 */
	public boolean isTimeExpiredForCurrentInstance() {
		// return control.general.timeout <= instanceStopwatch.wckTime();
		return control.general.timeout != PLUS_INFINITY && control.general.timeout <= instanceStopwatch.wckTime(); // not calling wckTime() when no necessary
	}

	/**
	 * Builds the main resolution object
	 * 
	 * @param controlFileName
	 *            the name of a file with options (possibly, null)
	 */
	public Head(String controlFileName) {
		this.control = new Control(controlFileName);
		this.output = new Output(this, controlFileName);
		this.permamentObserversConstruction = Stream.of(output).map(o -> (ObserverOnConstruction) o).collect(toCollection(ArrayList::new));
		// adding as permanent construction observer GraphViz (when problem built) ? so as to execute
		// Graphviz.saveGraph(problem)
		this.observersConstruction = permamentObserversConstruction.stream().collect(toCollection(ArrayList::new));
		// statement above needed if we run HeadExtraction
	}

	/**
	 * Builds the main resolution object
	 */
	public Head() {
		this(null);
	}

	/**
	 * Builds and returns the ith problem instance to be solved
	 * 
	 * @param i
	 *            the index/number (in a sequence) of the problem instance to be built
	 * @return the ith problem instance to be solved
	 */
	public Problem buildProblem(int i) {
		this.instanceIndex = i;
		random = new Random(control.general.seed + i);
		ProblemAPI api = null;
		try {
			try {
				api = (ProblemAPI) Reflector.buildObject(Input.problemName);
			} catch (Exception e) {
				api = (ProblemAPI) Reflector.buildObject("problems." + Input.problemName);
				// is it still relevant to try that?
			}
		} catch (Exception e) {
			return (Problem) Kit.exit("The class " + Input.problemName + " cannot be found.", e);
		}
		this.problem = new Problem(api, control.problem.variant, control.problem.data, "", false, Input.argsForProblem, this);
		for (ObserverOnConstruction obs : observersConstruction) {
			obs.afterProblemConstruction(this.problem.variables.length);
		}
		problem.display();
		return problem;
	}

	/**
	 * Builds and returns the solver that will be used to solve the specified problem (instance)
	 * 
	 * @param problem
	 *            the problem (instance) to be solved
	 * @return the solver that will be used to solve the specified problem
	 */
	protected final Solver buildSolver(Problem problem) {
		log.config("\n " + Kit.Color.YELLOW.coloring("...Building") + " solver");
		this.solver = Reflector.buildObject(control.solving.clazz, Solver.class, this);
		for (ObserverOnConstruction obs : observersConstruction)
			obs.afterSolverConstruction();
		return solver;
	}

	/**
	 * Solves the ith problem instance (usually, i=0 as there is only one instance to be solved).
	 * 
	 * @param i
	 *            the index/number (in a sequence) of the problem instance to be solved
	 */
	protected void solveInstance(int i) {
		this.observersConstruction = permamentObserversConstruction.stream().collect(toCollection(ArrayList::new));
		structureSharing.clear();
		problem = buildProblem(i);
		structureSharing.clear();
		if (control.solving.enablePrepro || control.solving.enableSearch) {
			solver = buildSolver(problem);
			solver.solve();
			solver.solutions.displayFinalResults();
		}
	}

	@Override
	public void run() {
		log.config("\n" + Color.ORANGE.coloring("ACE v2.5 ") + Kit.dateOf(Head.class) + "\n");
		stopwatch.start();
		boolean[] crashed = new boolean[Input.nInstancesToSolve];
		for (int i = 0; i < Input.nInstancesToSolve; i++) {
			try {
				solveInstance(i);
			} catch (Throwable e) {
				crashed[i] = true;
				Color.RED.println("\n! ERROR (use -ev for more details)");
				if (control.general.exceptionsVisible)
					e.printStackTrace();
			}
		}
		if (Input.portfolio) { // in that case, only one instance to solve (see control in Input)
			if (!crashed[0]) {
				Head.saveMultithreadResultsFiles(this);
				System.exit(0);
			}
		} else
			output.save(stopwatch.wckTime());
	}

}

// private int[] localSearchAtPreprocessing() {
// int[] solution = null;
// if (control.hardCoding.localSearchAtPreprocessing) {
// String solverClassName = control.solving.clazz;
// control.solving.clazz = SolverLocal.class.getSimpleName();
// int nRuns = control.restarts.nRunsLimit;
// control.restarts.nRunsLimit = 10;
// long cutoff = control.restarts.cutoff;
// control.restarts.cutoff = 10000;
// boolean prepro = control.solving.enablePrepro;
// control.solving.enablePrepro = false;
// solver = buildSolver(problem);
// solver.solve();
// solution = solver.solManager.lastSolution;
// control.optimization.ub = ((SolverLocal) solver).nMinViolatedCtrs;
// if (solver.stopping != EStopping.REACHED_GOAL) {
// control.solving.clazz = solverClassName;
// control.restarts.nRunsLimit = nRuns;
// control.restarts.cutoff = cutoff;
// control.solving.enablePrepro = prepro;
// }
// }
// return solution;
// }
