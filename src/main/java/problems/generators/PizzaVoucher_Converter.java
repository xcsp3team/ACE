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
import java.util.stream.IntStream;
import java.util.stream.Stream;

import javax.json.Json;
import javax.json.JsonArray;
import javax.json.JsonObject;
import javax.json.JsonReader;

import org.xcsp.common.Utilities;

import problems.ReaderFile;
import problems.g4_world.PizzaVoucher;

/*
 * Reader illustrating how to convert from a JSON format to another one.
 */
public class PizzaVoucher_Converter extends PizzaVoucher implements ReaderFile {

	void data() {
		String fileName = imp().askString("Enter data filename");
		JsonObject obj = null;
		try (JsonReader jsonReader = Json.createReader(new BufferedReader(new FileReader(fileName)))) {
			obj = jsonReader.readObject();
		} catch (Exception e) {
			e.printStackTrace();
			Utilities.exit("Pb when loading " + e);
		}

		JsonArray a1 = (JsonArray) obj.get("pizzaPrices");
		JsonArray a2 = (JsonArray) obj.get("voucherPayPart");
		JsonArray a3 = (JsonArray) obj.get("voucherFreePart");
		Utilities.control(a2.size() == a3.size(), "pb");

		Stream<Object> vouchers = IntStream.range(0, a2.size()).mapToObj(i -> buildInternClassObject("Voucher", a2.getInt(i), a3.getInt(i)));
		setDataValues(range(a1.size()).map(i -> a1.getInt(i)), vouchers);
	}
}
