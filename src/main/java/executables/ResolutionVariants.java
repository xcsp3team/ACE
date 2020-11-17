package executables;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xcsp.common.Utilities;

import dashboard.Arguments;
import dashboard.Output;
import utility.DocumentHandler;
import utility.Kit;

public final class ResolutionVariants {

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
		Document variantsDocument = DocumentHandler.load(configurationVariantsFileName);

		NodeList nodeList = variantsDocument.getElementsByTagName(VARIANT);
		for (int i = 0; i < nodeList.getLength(); i++) {
			Element variantElement = (Element) nodeList.item(i);
			Element variantParent = (Element) variantElement.getParentNode();
			if (!variantsDocument.getDocumentElement().getTagName().equals(VARIANT_PARALLEL) && variantParent.getTagName().equals(VARIANT_PARALLEL))
				continue;
			Document variantDocument = DocumentHandler.load(configurationFileName);
			String variantFileName = prefix + (variantParent.getTagName().equals(VARIANT_PARALLEL) ? variantParent.getAttribute(NAME) + "_" : "")
					+ variantElement.getAttribute(NAME) + ".xml";
			NodeList modificationList = variantElement.getElementsByTagName(MODIFICATION);
			int nModifications = modificationList.getLength();
			boolean iteration = nModifications > 0 && !((Element) modificationList.item(nModifications - 1)).getAttribute(MIN).equals("");
			int limit = nModifications - (iteration ? 1 : 0);
			for (int j = 0; j < limit; j++) {
				Element modificationElement = (Element) modificationList.item(j);
				String path = modificationElement.getAttribute(PATH);
				String attributeName = modificationElement.getAttribute(ATTRIBUTE);
				String attributeValue = modificationElement.getAttribute(VALUE);
				DocumentHandler.modify(variantDocument, path, attributeName, attributeValue);
			}
			if (iteration) {
				Element modification = (Element) modificationList.item(nModifications - 1);
				String path = modification.getAttribute(PATH);
				Kit.control(path.equals(SEED));
				String attributeName = modification.getAttribute(ATTRIBUTE);
				int min = Integer.parseInt(modification.getAttribute(MIN)), max = Integer.parseInt(modification.getAttribute(MAX)),
						step = Integer.parseInt(modification.getAttribute(STEP));
				String basis = variantFileName.substring(0, variantFileName.lastIndexOf(".xml"));
				for (int cnt = min; cnt <= max; cnt += step) {
					DocumentHandler.modify(variantDocument, path, attributeName, cnt + "");
					list.add(Utilities.save(variantDocument, basis + cnt + ".xml"));
				}
			} else
				list.add(Utilities.save(variantDocument, variantFileName));
		}
		return list.toArray(new String[list.size()]);
	}

	public final static String[] loadParallelVariants(String configurationVariantsFileName, String prefix) {
		List<String> list = new ArrayList<>();
		Document variantsDocument = DocumentHandler.load(configurationVariantsFileName);
		if (!variantsDocument.getDocumentElement().getTagName().equals(VARIANT_PARALLEL)) {
			NodeList nodeList = variantsDocument.getElementsByTagName(VARIANT_PARALLEL);
			for (int i = 0; i < nodeList.getLength(); i++) {
				Document document = DocumentHandler.createNewDocument();
				Element element = (Element) document.importNode(nodeList.item(i), true);
				document.appendChild(element);
				list.add(Utilities.save(document, prefix + element.getAttribute(NAME) + ".xml"));
			}
		}
		return list.toArray(new String[list.size()]);
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
			return loadSequentialVariants(Arguments.userSettingsFilename, Arguments.lastArgument(), prefix);
		} else
			return new String[] { Arguments.userSettingsFilename };
	}
}
