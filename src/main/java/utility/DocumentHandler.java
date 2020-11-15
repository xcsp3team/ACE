/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package utility;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.InputStream;
import java.net.URL;
import java.text.MessageFormat;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.validation.SchemaFactory;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;
import org.xml.sax.helpers.DefaultHandler;

public class DocumentHandler {

	public static final String W3C_XML_SCHEMA = "http://www.w3.org/2001/XMLSchema";

	private static Object handleException(Exception e) {
		if (e instanceof SAXException) { // superclass of SAXParseException
			Kit.log.warning("\n** SAX error " + ((SAXParseException) e).getMessage());
			if (e instanceof SAXParseException)
				Kit.log.warning("  at line " + ((SAXParseException) e).getLineNumber() + ", uri " + ((SAXParseException) e).getSystemId());
			(((SAXException) e).getException() == null ? e : ((SAXException) e).getException()).printStackTrace();
		} else if (e instanceof TransformerException) {
			Kit.log.warning("\n** Transformation error" + e.getMessage());
			(((TransformerException) e).getException() == null ? e : ((TransformerException) e).getException()).printStackTrace();
		}
		return Kit.exit(e);
	}

	public static Document createNewDocument() {
		try {
			return DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
		} catch (ParserConfigurationException e) {
			return (Document) handleException(e);
		}
	}

	private static class ErrorHandler extends DefaultHandler {
		private void print(SAXParseException x) {
			Kit.log.warning(
					new MessageFormat("({0}: {1}, {2}): {3}").format(new Object[] { x.getSystemId(), x.getLineNumber(), x.getColumnNumber(), x.getMessage() }));
		}

		@Override
		public void warning(SAXParseException x) {
			print(x);
		}

		@Override
		public void error(SAXParseException x) {
			print(x);
		}
	}

	/**
	 * Build a DOM object that corresponds to the specified input stream.
	 * 
	 * @param inputStream
	 *            the input stream that denotes the XML document to be loaded.
	 * @param schema
	 *            the schema to be used (<code> null </code> if not used) to validate the document
	 * @return a DOM object
	 */
	private static Document load(InputStream is, URL schema) {
		try {
			DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
			factory.setNamespaceAware(true);
			if (schema != null)
				factory.setSchema(SchemaFactory.newInstance(DocumentHandler.W3C_XML_SCHEMA).newSchema(schema));
			DocumentBuilder builder = factory.newDocumentBuilder();
			builder.setErrorHandler(new ErrorHandler());
			return builder.parse(is);
		} catch (Exception e) {
			return (Document) handleException(e);
		}
	}

	public static Document load(File file) {
		try {
			return load(new FileInputStream(file), null); // no schema
		} catch (FileNotFoundException e) {
			return (Document) Kit.exit("File " + file.getName() + " does not exist", e);
		}
	}

	public static Document load(String fileName) {
		if (fileName.endsWith("xml.bz2") || fileName.endsWith("xml.lzma"))
			try {
				Process p = Runtime.getRuntime().exec((fileName.endsWith("xml.bz2") ? "bunzip2 -c " : "lzma -c -d ") + fileName);
				Document document = load(p.getInputStream(), null);
				p.waitFor();
				p.exitValue();
				p.destroy();
				return document;
			} catch (Exception e) {
				return (Document) Kit.exit("Problem with " + fileName, e);
			}
		return load(new File(fileName));
	}

	public static void modify(Document document, String path, String attName, String attValue) {
		try {
			NodeList result = (NodeList) XPathFactory.newInstance().newXPath().compile("//" + path).evaluate(document, XPathConstants.NODESET);
			Kit.control(result.getLength() == 1, () -> path + " " + result.getLength());
			((Element) result.item(0)).setAttribute(attName, attValue);
		} catch (Exception e) {
			Kit.exit("Pb with " + path, e);
		}
	}

	public static String attValueFor(String fileName, String tagName, String attName) {
		return ((Element) load(fileName).getElementsByTagName(tagName).item(0)).getAttribute(attName);
	}

	public static boolean isXMLFileWithRoot(String fileName, String rootToken) {
		File file = new File(fileName);
		if (!file.isFile())
			return false;
		try (BufferedReader in = new BufferedReader(new FileReader(file))) {
			String line = in.readLine();
			while (line != null && (line.trim().isEmpty() || line.startsWith("<?xml")))
				line = in.readLine();
			return line != null && line.trim().startsWith("<" + rootToken);
		} catch (Exception e) {
			return (Boolean) Kit.exit("Problem with " + fileName, e);
		}
	}

}
