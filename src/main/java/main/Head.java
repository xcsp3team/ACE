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
import org.w3c.dom.NodeList;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Utilities;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.extension.Extension;
import constraints.extension.structures.Bits;
import constraints.extension.structures.ExtensionStructure;
import constraints.extension.structures.MDD;
import constraints.intension.Intension.IntensionStructure;
import dashboard.Control;
import dashboard.Control.SettingProblem;
import dashboard.Input;
import dashboard.Output;
import heuristics.HeuristicRevisions;
import heuristics.HeuristicValues;
import heuristics.HeuristicVariables;
import interfaces.Observers.ObserverConstruction;
import problem.Problem;
import propagation.Propagation;
import solver.Solver;
import utility.Enums.TypeOutput;
import utility.Kit;
import utility.Kit.Stopwatch;
import utility.Reflector;

/**
 * This is the class of the head in charge of solving a problem instance
 */
public class Head extends Thread {

	/**********************************************************************************************
	 * Static members
	 *********************************************************************************************/

	public static final String VARIANT = "variant";
	public static final String VARIANT_PARALLEL = "variantParallel";
	public static final String NAME = "name";
	public static final String MODIFICATION = "modification";
	public static final String PATH = "path";
	public static final String ATTRIBUTE = "attribute";
	public static final String VALUE = "value";
	public static final String MIN = "min";
	public static final String MAX = "max";
	public static final String STEP = "step";
	public static final String SEED = "seed";

	public final static String[] loadSequentialVariants(String configurationFileName, String configurationVariantsFileName, String prefix) {
		List<String> list = new ArrayList<>();
		Document document = Kit.load(configurationVariantsFileName);
		NodeList variants = document.getElementsByTagName(VARIANT);
		for (int i = 0; i < variants.getLength(); i++) {
			Element variant = (Element) variants.item(i);
			Element parent = (Element) variant.getParentNode();
			if (!document.getDocumentElement().getTagName().equals(VARIANT_PARALLEL) && parent.getTagName().equals(VARIANT_PARALLEL))
				continue;
			Document docVariant = Kit.load(configurationFileName);
			String docFilename = prefix + (parent.getTagName().equals(VARIANT_PARALLEL) ? parent.getAttribute(NAME) + "_" : "") + variant.getAttribute(NAME)
					+ ".xml";
			NodeList modifications = variant.getElementsByTagName(MODIFICATION);
			int nModifications = modifications.getLength();
			boolean iteration = nModifications > 0 && !((Element) modifications.item(nModifications - 1)).getAttribute(MIN).equals("");
			int limit = nModifications - (iteration ? 1 : 0);
			for (int j = 0; j < limit; j++) {
				Element modificationElement = (Element) modifications.item(j);
				String path = modificationElement.getAttribute(PATH);
				String attributeName = modificationElement.getAttribute(ATTRIBUTE);
				String attributeValue = modificationElement.getAttribute(VALUE);
				Kit.modify(docVariant, path, attributeName, attributeValue);
			}
			if (iteration) {
				Element modification = (Element) modifications.item(nModifications - 1);
				String path = modification.getAttribute(PATH);
				Kit.control(path.equals(SEED));
				String attributeName = modification.getAttribute(ATTRIBUTE);
				int min = Integer.parseInt(modification.getAttribute(MIN)), max = Integer.parseInt(modification.getAttribute(MAX)),
						step = Integer.parseInt(modification.getAttribute(STEP));
				String basis = docFilename.substring(0, docFilename.lastIndexOf(".xml"));
				for (int cnt = min; cnt <= max; cnt += step) {
					Kit.modify(docVariant, path, attributeName, cnt + "");
					list.add(Utilities.save(docVariant, basis + cnt + ".xml"));
				}
			} else
				list.add(Utilities.save(docVariant, docFilename));
		}
		return list.toArray(new String[list.size()]);
	}

	public final static String[] loadParallelVariants(String configurationVariantsFileName, String prefix) {
		List<String> list = new ArrayList<>();
		Document document = Kit.load(configurationVariantsFileName);
		if (!document.getDocumentElement().getTagName().equals(VARIANT_PARALLEL)) {
			NodeList nodeList = document.getElementsByTagName(VARIANT_PARALLEL);
			for (int i = 0; i < nodeList.getLength(); i++) {
				Document docVariant = Kit.createNewDocument();
				Element element = (Element) docVariant.importNode(nodeList.item(i), true);
				docVariant.appendChild(element);
				list.add(Utilities.save(docVariant, prefix + element.getAttribute(NAME) + ".xml"));
			}
		}
		return list.toArray(new String[list.size()]);
	}

	/**
	 * The set of objects in charge of solving a problem. For portfolio mode, contains more than one object.
	 */
	private static Head[] heads;

	public synchronized static void saveMultithreadResultsFiles(Head resolution) {
		String fileName = resolution.output.save(resolution.stopwatch.wckTime());
		if (fileName != null) {
			String variantParallelName = Kit.attValueFor(Input.lastArgument(), VARIANT_PARALLEL, NAME);
			String resultsFileName = resolution.control.xml.dirForCampaign;
			if (resultsFileName != "")
				resultsFileName += File.separator;
			resultsFileName += Output.RESULTS_DIRECTORY + File.separator + resolution.output.outputFileNameFrom(resolution.problem.name(), variantParallelName);
			Kit.copy(fileName, resultsFileName);
			Document document = Kit.load(resultsFileName);
			Kit.modify(document, TypeOutput.RESOLUTIONS.toString(), Output.CONFIGURATION_FILE_NAME, variantParallelName);
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
		if (Input.multiThreads) {
			String prefix = Kit.attValueFor(Input.userSettingsFilename, "xml", "exportMode");
			if (prefix.equals("NO"))
				prefix = ".";
			if (prefix != "")
				prefix += File.separator;
			prefix += Output.SETTINGS_DIRECTORY + File.separator;
			File file = new File(prefix);
			if (!file.exists())
				file.mkdirs();
			else
				Kit.control(file.isDirectory());
			return loadSequentialVariants(Input.userSettingsFilename, Input.lastArgument(), prefix);
		} else
			return new String[] { Input.userSettingsFilename };
	}

	public static void main(String[] args) {
		if (args.length == 0 && !isAvailableIn())
			new Head().control.settings.display(); // the usage is displayed
		else {
			Input.loadArguments(args); // Always start with that
			heads = Stream.of(loadVariantNames()).map(v -> new Head(v)).peek(h -> h.start()).toArray(Head[]::new); // threads built and started
		}
	}

	/**********************************************************************************************
	 * Handling classes and shared structures
	 *********************************************************************************************/

	public HandlerClasses handlerClasses = new HandlerClasses();

	public static class HandlerClasses {
		private static final String DOT_CLASS = ".class";
		private static final String DOT_JAR = ".jar";

		private Map<Class<?>, Set<Class<?>>> map = new HashMap<>();

		public Set<Class<?>> get(Class<?> clazz) {
			return map.get(clazz);
		}

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
				// we load classes from jar files, first (it is necessary when ACE is run from a jar)
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

	public StructureSharing structureSharing = new StructureSharing();

	public static class StructureSharing {

		// maps used by constraints to share some data structures

		public Map<String, ExtensionStructure> mapOfExtensionStructures = new HashMap<>();

		public Map<String, MDD> mapOfMDDStructures = new HashMap<>();

		public Map<String, IntensionStructure> mapOfTreeEvaluators = new HashMap<>();

		public void clear() {
			mapOfExtensionStructures.clear();
			mapOfMDDStructures.clear();
			mapOfTreeEvaluators.clear();
			Bits.globalMap.clear();
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
	 * The object that stores all parameters to pilot the solving process
	 */
	public final Control control;

	public final Output output;

	public final List<ObserverConstruction> observersConstruction = new ArrayList<>();

	/**
	 * The <code> Random </code> object used in resolution (randomization of heuristics, generation of random solutions,...). <br>
	 * However, note that it is not used when generating random lists (see package <code> randomLists </code>).
	 */
	public final Random random = new Random();

	public boolean mustPreserveUnaryConstraints() {
		return control.constraints.preserveUnaryCtrs || this instanceof HeadExtraction || control.problem.isSymmetryBreaking()
				|| control.general.framework == TypeFramework.MAXCSP;
	}

	public boolean isTimeExpiredForCurrentInstance() {
		return control.general.timeout <= instanceStopwatch.wckTime();
	}

	public Head(String configurationFileName) {
		this.control = Control.buildControlPanelFor(configurationFileName);
		this.output = new Output(this, configurationFileName);
		observersConstruction.add(this.output);
	}

	public Head() {
		this((String) null);
	}

	public int instanceNumber;

	public Problem buildProblem(int instanceNumber) {
		this.instanceNumber = instanceNumber;
		random.setSeed(control.general.seed + instanceNumber);
		ProblemAPI api = null;
		try {
			try {
				api = (ProblemAPI) Reflector.buildObject(Input.problemPackageName);
			} catch (Exception e) {
				api = (ProblemAPI) Reflector.buildObject("problems." + Input.problemPackageName); // is it still relevant to try that?
			}
		} catch (Exception e) {
			return (Problem) Kit.exit("The class " + Input.problemPackageName + " cannot be found.", e);
		}
		SettingProblem settings = control.problem;
		problem = new Problem(api, settings.variant, settings.data, settings.dataFormat, settings.dataexport, Input.argsForPb, this);
		for (ObserverConstruction obs : observersConstruction)
			obs.afterProblemConstruction();
		problem.display();
		// Graphviz.saveGraph(problem, control.general.saveNetworkGraph);
		return problem;
	}

	protected final Solver buildSolver(Problem problem) {
		Kit.log.config("\n" + Output.COMMENT_PREFIX + "Building solver... ");
		solver = Reflector.buildObject(control.solving.clazz, Solver.class, this);
		for (ObserverConstruction obs : observersConstruction)
			obs.afterSolverConstruction();
		return solver;
	}

	protected void solveInstance(int instanceNumber) {
		observersConstruction.clear();
		observersConstruction.add(output);

		structureSharing.clear();
		problem = buildProblem(instanceNumber);
		structureSharing.clear();

		if (control.solving.enablePrepro || control.solving.enableSearch) {
			solver = buildSolver(problem);
			solver.solve();
			solver.solutions.displayFinalResults();
		}
	}

	@Override
	public void run() {
		stopwatch.start();
		log.config("\n" + Kit.preprint("ACE (AbsCon Essence)", Kit.ORANGE) + " v21.05 " + Kit.dateOf(Head.class));
		boolean crashed = false;
		for (int i = 0; i < Input.nInstancesToSolve; i++) {
			try {
				crashed = false;
				solveInstance(i);
			} catch (Throwable e) {
				crashed = true;
				System.out.println(Kit.preprint("\n! ERROR (use -ev for more details)", Kit.RED)); // log.warning("Instance with exception");
				if (control.general.makeExceptionsVisible)
					e.printStackTrace();
			}
		}
		if (Input.multiThreads) {
			if (!crashed) {
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
