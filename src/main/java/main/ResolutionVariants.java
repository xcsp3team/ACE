package main;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xcsp.common.Utilities;

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
		Document document = DocumentHandler.load(configurationVariantsFileName);
		NodeList variants = document.getElementsByTagName(VARIANT);
		for (int i = 0; i < variants.getLength(); i++) {
			Element variant = (Element) variants.item(i);
			Element parent = (Element) variant.getParentNode();
			if (!document.getDocumentElement().getTagName().equals(VARIANT_PARALLEL) && parent.getTagName().equals(VARIANT_PARALLEL))
				continue;
			Document docVariant = DocumentHandler.load(configurationFileName);
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
				DocumentHandler.modify(docVariant, path, attributeName, attributeValue);
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
					DocumentHandler.modify(docVariant, path, attributeName, cnt + "");
					list.add(Utilities.save(docVariant, basis + cnt + ".xml"));
				}
			} else
				list.add(Utilities.save(docVariant, docFilename));
		}
		return list.toArray(new String[list.size()]);
	}

	public final static String[] loadParallelVariants(String configurationVariantsFileName, String prefix) {
		List<String> list = new ArrayList<>();
		Document document = DocumentHandler.load(configurationVariantsFileName);
		if (!document.getDocumentElement().getTagName().equals(VARIANT_PARALLEL)) {
			NodeList nodeList = document.getElementsByTagName(VARIANT_PARALLEL);
			for (int i = 0; i < nodeList.getLength(); i++) {
				Document docVariant = DocumentHandler.createNewDocument();
				Element element = (Element) docVariant.importNode(nodeList.item(i), true);
				docVariant.appendChild(element);
				list.add(Utilities.save(docVariant, prefix + element.getAttribute(NAME) + ".xml"));
			}
		}
		return list.toArray(new String[list.size()]);
	}

}
