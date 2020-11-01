package executables;

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

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.hard.CtrExtension;
import constraints.hard.extension.structures.Bits;
import constraints.hard.extension.structures.ExtensionStructure;
import constraints.hard.intension.CtrEvaluationManager;
import dashboard.Arguments;
import dashboard.ControlPanel;
import dashboard.ControlPanel.SettingProblem;
import dashboard.Output;
import heuristics.revisions.HeuristicRevisions;
import heuristics.values.HeuristicValues;
import heuristics.variables.HeuristicVariables;
import interfaces.ObserverConstruction;
import problem.Problem;
import problems.xcsp3.XCSP3;
import search.Solver;
import search.local.SolverLocal;
import search.statistics.StatisticsMultiResolution;
import tools.output.Graphviz;
import utility.Enums.EStopping;
import utility.Enums.TypeOutput;
import utility.Kit;
import utility.Kit.Stopwatch;
import utility.Reflector;
import utility.XMLManager;

/**
 * This is the main class in charge of solving a problem instance
 */
public class Resolution extends Thread {

	/**********************************************************************************************
	 * Static
	 *********************************************************************************************/

	public static final String VERSION = "AbsCon 3";

	public static final int UNDEFINED = -10;

	/**
	 * The set of resolution objects. For portfolio mode, contains more than one object.
	 */
	private static Resolution[] resolutions;

	public synchronized static void saveMultithreadResultsFiles(Resolution resolution) {
		String fileName = resolution.output.save(resolution.stopwatch.getWckTime());
		if (fileName != null) {
			String variantParallelName = XMLManager.getAttValueFor(Arguments.lastArgument(), ResolutionVariants.VARIANT_PARALLEL, ResolutionVariants.NAME);
			String resultsFileName = resolution.cp.settingXml.dirForCampaign;
			if (resultsFileName != "")
				resultsFileName += File.separator;
			resultsFileName += Output.RESULTS_DIRECTORY_NAME + File.separator
					+ resolution.output.outputFileNameFrom(resolution.problem.name(), variantParallelName);
			Kit.copy(fileName, resultsFileName);
			Document document = XMLManager.load(resultsFileName);
			XMLManager.modify(document, TypeOutput.RESOLUTIONS.toString(), Output.CONFIGURATION_FILE_NAME, variantParallelName);
			long totalWCKTime = 0;
			long totalVisitedNodes = 0;
			for (Resolution r : resolutions) {
				totalWCKTime += r.instanceStopwatch.getWckTime();
				totalVisitedNodes += r.solver.stats.nVisitedNodes;
			}
			Element root = document.getDocumentElement();
			Element multiThreadedResults = document.createElement(Output.MULTITHREAD_RESULTS);
			multiThreadedResults.setAttribute(Output.WCK, Double.toString((double) totalWCKTime / 1000));
			multiThreadedResults.setAttribute(Output.N_VISITED_NODES, Long.toString(totalVisitedNodes));
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

	/**
	 * Use directly <code>main</code> in class <code>AbsCon</code> instead.
	 * 
	 * @param args
	 */
	public static void main(String[] args) {
		// Class.forName("AbsCon").getDeclaredMethod("main", String[].class).invoke(null, (Object) args);
		if (args.length == 0 && !isAvailableIn())
			new Resolution().cp.settings.display(); // the usage is displayed
		else {
			Arguments.loadArguments(args); // Always start with that
			String[] variants = ResolutionVariants.loadVariantNames();
			resolutions = new Resolution[variants.length];
			for (int i = 0; i < resolutions.length; i++)
				(resolutions[i] = new Resolution(variants[i])).start();
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
					|| dealWith(clazz, CtrExtension.class);
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
	public final ControlPanel cp;

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

	public Map<String, CtrEvaluationManager> mapOfEvaluationManagers = new HashMap<>();

	public void clearMapsUsedByConstraints() {
		mapOfExtensionStructures.clear();
		if (Bits.globalMap != null)
			Bits.globalMap.clear();
		mapOfEvaluationManagers.clear();
	}

	/*
	 * END OF UNSTATIFIED METHODS
	 */

	public boolean mustPreserveUnaryConstraints() {
		return cp.settingCtrs.preserveUnaryCtrs || this instanceof Extraction || cp.settingProblem.isSymmetryBreaking()
				|| cp.settingGeneral.framework == TypeFramework.MAXCSP;
	}

	public boolean isTimeExpiredForCurrentInstance() {
		return cp.settingGeneral.timeout <= instanceStopwatch.getWckTime();
	}

	public Resolution(String configurationFileName) {
		this.cp = ControlPanel.buildControlPanelFor(configurationFileName);
		this.output = new Output(this, configurationFileName);
		observersConstruction.add(this.output);
		this.statisticsMultiresolution = StatisticsMultiResolution.buildFor(this);
	}

	public Resolution() {
		this((String) null);
	}

	public int instanceNumber;

	public Problem buildProblem(int instanceNumber) {
		this.instanceNumber = instanceNumber;
		random.setSeed(cp.settingGeneral.seed + instanceNumber);
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
		SettingProblem settings = cp.settingProblem;
		problem = new Problem(api, settings.variant, settings.data, settings.dataFormat, settings.dataexport, Arguments.argsForPb, this);
		for (ObserverConstruction obs : observersConstruction)
			obs.onConstructionProblemFinished();
		problem.display();
		Graphviz.saveGraph(problem, cp.settingGeneral.saveNetworkGraph);
		return problem;
	}

	protected final Solver buildSolver(Problem problem) {
		boolean cm = problem.rs.cp.settingXml.competitionMode;
		Kit.log.config("\n" + Output.COMMENT_PREFIX + "Building solver... " + (cm ? "\n" : ""));
		solver = Reflector.buildObject(cp.settingSolving.clazz, Solver.class, this);
		for (ObserverConstruction obs : observersConstruction)
			obs.onConstructionSolverFinished();
		return solver;
	}

	private int[] localSearchAtPreprocessing() {
		int[] solution = null;
		if (cp.settingHardCoding.localSearchAtPreprocessing) {
			String solverClassName = cp.settingSolving.clazz;
			cp.settingSolving.clazz = SolverLocal.class.getSimpleName();
			int nRuns = cp.settingRestarts.nRunsLimit;
			cp.settingRestarts.nRunsLimit = 10;
			long cutoff = cp.settingRestarts.cutoff;
			cp.settingRestarts.cutoff = 10000;
			boolean prepro = cp.settingSolving.enablePrepro;
			cp.settingSolving.enablePrepro = false;
			solver = buildSolver(problem);
			solver.solve();
			solution = solver.solManager.lastSolution;
			cp.settingOptimization.upperBound = ((SolverLocal) solver).nMinViolatedCtrs;
			if (solver.stoppingType != EStopping.REACHED_GOAL) {
				cp.settingSolving.clazz = solverClassName;
				cp.settingRestarts.nRunsLimit = nRuns;
				cp.settingRestarts.cutoff = cutoff;
				cp.settingSolving.enablePrepro = prepro;
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

		if (cp.settingSolving.enablePrepro || cp.settingSolving.enableSearch) {
			int[] solution = localSearchAtPreprocessing();
			solver = buildSolver(problem);
			if (solution != null)
				solver.solManager.storeSolution(solution);
			solver.stoppingType = null;
			solver.solve();
			solver.solManager.displayFinalResults();
		}
	}

	@Override
	public void run() {
		stopwatch.start();
		log.config("\n" + VERSION + " " + Kit.dateOf(Resolution.class) + "\n"); // + " - " + Arguments.configurationFileName
		boolean crashed = false;
		for (int i = 0; i < Arguments.nInstancesToSolve; i++) {
			try {
				crashed = false;
				solveInstance(i);
			} catch (Throwable e) {
				crashed = true;
				log.warning("Instance with exception");
				if (cp.settingGeneral.makeExceptionsVisible)
					e.printStackTrace();
			}
			statisticsMultiresolution.update(crashed);
		}
		statisticsMultiresolution.outputGlobalStatistics();
		if (Arguments.multiThreads) {
			if (!crashed) {
				Resolution.saveMultithreadResultsFiles(this);
				System.exit(0);
			}
		} else
			output.save(stopwatch.getWckTime());
	}

}
