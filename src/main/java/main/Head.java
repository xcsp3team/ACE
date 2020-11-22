package main;

import static utility.Kit.log;

import java.io.File;
import java.io.FileInputStream;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarInputStream;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.extension.Extension;
import constraints.extension.structures.Bits;
import constraints.extension.structures.ExtensionStructure;
import constraints.intension.Intension.SharedTreeEvaluator;
import dashboard.Arguments;
import dashboard.Control;
import dashboard.Control.SettingProblem;
import dashboard.Output;
import heuristics.HeuristicRevisions;
import heuristics.HeuristicValues;
import heuristics.HeuristicVariables;
import interfaces.Observers.ObserverConstruction;
import problem.Problem;
import propagation.Propagation;
import solver.Solver;
import solver.Statistics.StatisticsMultiResolution;
import solver.local.SolverLocal;
import utility.DocumentHandler;
import utility.Enums.EStopping;
import utility.Enums.TypeOutput;
import utility.Graphviz;
import utility.Kit;
import utility.Kit.Stopwatch;
import utility.Reflector;
import xcsp3.XCSP3;

/**
 * This is the class of the head in charge of solving a problem instance
 */
public class Head extends Thread {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	/**
	 * The set of objects in charge of solving a problem. For portfolio mode, contains more than one object.
	 */
	private static Head[] heads;

	public synchronized static void saveMultithreadResultsFiles(Head resolution) {
		String fileName = resolution.output.save(resolution.stopwatch.wckTime());
		if (fileName != null) {
			String variantParallelName = DocumentHandler.attValueFor(Arguments.lastArgument(), ResolutionVariants.VARIANT_PARALLEL, ResolutionVariants.NAME);
			String resultsFileName = resolution.control.settingXml.dirForCampaign;
			if (resultsFileName != "")
				resultsFileName += File.separator;
			resultsFileName += Output.RESULTS_DIRECTORY_NAME + File.separator
					+ resolution.output.outputFileNameFrom(resolution.problem.name(), variantParallelName);
			Kit.copy(fileName, resultsFileName);
			Document document = DocumentHandler.load(resultsFileName);
			DocumentHandler.modify(document, TypeOutput.RESOLUTIONS.toString(), Output.CONFIGURATION_FILE_NAME, variantParallelName);
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
			Utilities.save(document, resultsFileName);
		}
	}

	public static boolean isAvailableIn() {
		try {
			return System.in.available() > 0;
		} catch (Throwable e) {
			return (Boolean) Kit.exit(e);
		}
	}

	public final static String[] loadVariantNames() {
		if (Arguments.multiThreads) {
			String prefix = DocumentHandler.attValueFor(Arguments.userSettingsFilename, "xml", "exportMode");
			if (prefix.equals("NO"))
				prefix = ".";
			if (prefix != "")
				prefix += File.separator;
			prefix += Output.CONFIGURATION_DIRECTORY_NAME + File.separator;
			File file = new File(prefix);
			if (!file.exists())
				file.mkdirs();
			else
				Kit.control(file.isDirectory());
			return ResolutionVariants.loadSequentialVariants(Arguments.userSettingsFilename, Arguments.lastArgument(), prefix);
		} else
			return new String[] { Arguments.userSettingsFilename };
	}

	public static void main(String[] args) {
		if (args.length == 0 && !isAvailableIn())
			new Head().control.settings.display(); // the usage is displayed
		else {
			Arguments.loadArguments(args); // Always start with that
			heads = Stream.of(loadVariantNames()).map(v -> new Head(v)).peek(h -> h.start()).toArray(Head[]::new); // threads built and started
		}
	}

	/**********************************************************************************************
	 * Handling classes
	 *********************************************************************************************/

	public HandlerClasses handlerClasses = new HandlerClasses();

	public static class HandlerClasses {
		private static final String DOT_CLASS = ".class";
		private static final String DOT_JAR = ".jar";

		public Map<Class<?>, Set<Class<?>>> map = new HashMap<>();

		private HandlerClasses() {
			loadClasses();
		}

		private boolean dealWith(Class<?> clazz, Class<?> rootClass) {
			if (rootClass.isAssignableFrom(clazz)) {
				map.computeIfAbsent(rootClass, r -> new HashSet<>()).add(clazz);
				return true;
			}
			return false;
		}

		private boolean dealWith(Class<?> clazz) {
			if (Modifier.isAbstract(clazz.getModifiers()))
				return false;
			return dealWith(clazz, HeuristicVariables.class) || dealWith(clazz, HeuristicValues.class) || dealWith(clazz, HeuristicRevisions.class)
					|| dealWith(clazz, Extension.class) || dealWith(clazz, Propagation.class);
		}

		private void loadRecursively(File directory, String packageName) throws ClassNotFoundException {
			packageName = packageName.startsWith(".") ? packageName.substring(1) : packageName;
			for (File file : directory.listFiles())
				if (file.isDirectory()) {
					Kit.control(!file.getName().contains("."));
					loadRecursively(file, packageName + "." + file.getName());
				} else if (file.getName().endsWith(DOT_CLASS) && file.getName().charAt(0) != '/') // second part for a class in the default package
					dealWith(Class.forName(packageName + '.' + file.getName().substring(0, file.getName().length() - DOT_CLASS.length())));
		}

		private void loadClasses() {
			try {
				// we load classes from jar files, first (it is necessary when AbsCon is run from a jar)
				for (String classPathToken : System.getProperty("java.class.path", ".").split(File.pathSeparator))
					if (classPathToken.endsWith(DOT_JAR))
						try (JarInputStream jarFile = new JarInputStream(new FileInputStream(classPathToken))) {
							// if (classPathToken.endsWith("CyclesAlgorithmsPlugin.jar"))
							// continue;
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
							e.printStackTrace();
						}
				// we load loaded classes, next
				ClassLoader classLoader = Thread.currentThread().getContextClassLoader();
				// however, if we need to look at unloaded classes, as for example some in a subclass of Propagation, we need to put lines
				// as the one below which is commented
				// Class<?> _ = Propagation.class;
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
			String s = "";
			for (Entry<Class<?>, Set<Class<?>>> entry : map.entrySet())
				s += entry.getKey() + " : " + entry.getValue().stream().map(c -> c.getName()).collect(Collectors.joining(" ")) + "\n";
			return s;
		}
	}

	/**********************************************************************************************
	 * Fields
	 *********************************************************************************************/

	public final Stopwatch stopwatch = new Stopwatch(), instanceStopwatch = new Stopwatch();

	/** The current problem instance to be solved. */
	public Problem problem;

	/** The solver used to solve the current problem instance. */
	public Solver solver;

	/**
	 * The object that stores all parameters to pilot resolution.java AbsCon test.TestTreeOptim -trace -varh=Lexico
	 */
	public final Control control;

	public final Output output;

	public final List<ObserverConstruction> observersConstruction = new ArrayList<>();

	/**
	 * The <code> Random </code> object used in resolution (randomization of heuristics, generation of random solutions,...). <br>
	 * However, note that it is not used when generating random lists (see package <code> randomLists </code>).
	 */
	public final Random random = new Random();

	private final StatisticsMultiResolution statisticsMultiresolution;

	/*
	 * UNSTATIFIED FIELDS + METHODS
	 */

	public Map<String, ExtensionStructure> mapOfExtensionStructures = new HashMap<>();

	public Map<String, SharedTreeEvaluator> mapOfEvaluationManagers = new HashMap<>();

	public void clearMapsUsedByConstraints() {
		mapOfExtensionStructures.clear();
		mapOfEvaluationManagers.clear();
		if (Bits.globalMap != null)
			Bits.globalMap.clear();
	}

	/*
	 * END OF UNSTATIFIED METHODS
	 */

	public boolean mustPreserveUnaryConstraints() {
		return control.settingCtrs.preserveUnaryCtrs || this instanceof HeadExtraction || control.settingProblem.isSymmetryBreaking()
				|| control.settingGeneral.framework == TypeFramework.MAXCSP;
	}

	public boolean isTimeExpiredForCurrentInstance() {
		return control.settingGeneral.timeout <= instanceStopwatch.wckTime();
	}

	public Head(String configurationFileName) {
		this.control = Control.buildControlPanelFor(configurationFileName);
		this.output = new Output(this, configurationFileName);
		observersConstruction.add(this.output);
		this.statisticsMultiresolution = StatisticsMultiResolution.buildFor(this);
	}

	public Head() {
		this((String) null);
	}

	public int instanceNumber;

	public Problem buildProblem(int instanceNumber) {
		this.instanceNumber = instanceNumber;
		random.setSeed(control.settingGeneral.seed + instanceNumber);
		ProblemAPI api = null;
		try {
			if (Arguments.problemPackageName.equals(XCSP3.class.getName()))
				api = (ProblemAPI) Reflector.buildObject(Arguments.problemPackageName);
			else {
				if (Arguments.problemPackageName.startsWith(Arguments.DEFAULT_PROBLEMS_PREFIX))
					api = (ProblemAPI) Reflector.buildObject(Arguments.problemPackageName);
				else {
					try {
						api = (ProblemAPI) Reflector.buildObject(Arguments.DEFAULT_PROBLEMS_PREFIX + "." + Arguments.problemPackageName);
					} catch (Exception e) {
						api = (ProblemAPI) Reflector.buildObject(Arguments.problemPackageName);
					}
				}
			}
		} catch (Exception e) {
			return (Problem) Kit.exit("The class " + Arguments.problemPackageName + " cannot be found.", e);
		}
		SettingProblem settings = control.settingProblem;
		problem = new Problem(api, settings.variant, settings.data, settings.dataFormat, settings.dataexport, Arguments.argsForPb, this);
		for (ObserverConstruction obs : observersConstruction)
			obs.afterProblemConstruction();
		problem.display();
		Graphviz.saveGraph(problem, control.settingGeneral.saveNetworkGraph);
		return problem;
	}

	protected final Solver buildSolver(Problem problem) {
		boolean cm = problem.head.control.settingXml.competitionMode;
		Kit.log.config("\n" + Output.COMMENT_PREFIX + "Building solver... " + (cm ? "\n" : ""));
		solver = Reflector.buildObject(control.settingSolving.clazz, Solver.class, this);
		for (ObserverConstruction obs : observersConstruction)
			obs.afterSolverConstruction();
		return solver;
	}

	private int[] localSearchAtPreprocessing() {
		int[] solution = null;
		if (control.settingHardCoding.localSearchAtPreprocessing) {
			String solverClassName = control.settingSolving.clazz;
			control.settingSolving.clazz = SolverLocal.class.getSimpleName();
			int nRuns = control.settingRestarts.nRunsLimit;
			control.settingRestarts.nRunsLimit = 10;
			long cutoff = control.settingRestarts.cutoff;
			control.settingRestarts.cutoff = 10000;
			boolean prepro = control.settingSolving.enablePrepro;
			control.settingSolving.enablePrepro = false;
			solver = buildSolver(problem);
			solver.solve();
			solution = solver.solManager.lastSolution;
			control.settingOptimization.upperBound = ((SolverLocal) solver).nMinViolatedCtrs;
			if (solver.stopping != EStopping.REACHED_GOAL) {
				control.settingSolving.clazz = solverClassName;
				control.settingRestarts.nRunsLimit = nRuns;
				control.settingRestarts.cutoff = cutoff;
				control.settingSolving.enablePrepro = prepro;
			}
		}
		return solution;
	}

	/**
	 * Allows to build all objects which are necessary to solve the current instance
	 */
	protected void solveInstance(int instanceNumber) {
		clearMapsUsedByConstraints();
		observersConstruction.clear();
		observersConstruction.add(output);
		problem = buildProblem(instanceNumber);

		if (control.settingSolving.enablePrepro || control.settingSolving.enableSearch) {
			int[] solution = localSearchAtPreprocessing();
			solver = buildSolver(problem);
			if (solution != null)
				solver.solManager.storeSolution(solution);
			solver.stopping = null;
			solver.solve();
			solver.solManager.displayFinalResults();
		}
	}

	@Override
	public void run() {
		stopwatch.start();
		log.config("\n ACE (AbsCon Essence) v0.9 " + Kit.dateOf(Head.class) + "\n");
		boolean crashed = false;
		for (int i = 0; i < Arguments.nInstancesToSolve; i++) {
			try {
				crashed = false;
				solveInstance(i);
			} catch (Throwable e) {
				crashed = true;
				log.warning("Instance with exception");
				if (control.settingGeneral.makeExceptionsVisible)
					e.printStackTrace();
			}
			statisticsMultiresolution.update(crashed);
		}
		statisticsMultiresolution.outputGlobalStatistics();
		if (Arguments.multiThreads) {
			if (!crashed) {
				Head.saveMultithreadResultsFiles(this);
				System.exit(0);
			}
		} else
			output.save(stopwatch.wckTime());
	}

}
