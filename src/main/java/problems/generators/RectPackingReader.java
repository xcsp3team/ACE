/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.generators;

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.stream.Stream;

import javax.json.Json;
import javax.json.JsonArray;
import javax.json.JsonNumber;
import javax.json.JsonObject;
import javax.json.JsonReader;

import org.xcsp.common.Utilities;

import problems.ReaderFile;
import problems.g3_pattern.RectPacking;

/*
 * Reader illustrating how to convert from a JSON format to another one.
 */
public class RectPackingReader extends RectPacking implements ReaderFile {

	void data() {
		String fileName = imp().askString("Enter data filename");
		JsonObject obj = null;
		try (JsonReader jsonReader = Json.createReader(new BufferedReader(new FileReader(fileName)))) {
			obj = jsonReader.readObject();
		} catch (Exception e) {
			e.printStackTrace();
			Utilities.exit("Pb when loading " + e);
		}

		int containerWidth = ((JsonNumber) obj.get("containerWidth")).intValue();
		int containerHeight = ((JsonNumber) obj.get("containerHeight")).intValue();
		Object container = buildInternClassObject("Rectangle", containerWidth, containerHeight);
		Stream<Object> boxes = ((JsonArray) obj.get("boxes")).stream().map(v -> (JsonObject) v)
				.map(v -> buildInternClassObject("Rectangle", ((JsonNumber) v.get("width")).intValue(), ((JsonNumber) v.get("height")).intValue()));
		setDataValues(container, boxes);
	}
}
