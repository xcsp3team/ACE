/**
 * AbsCon - Copyright (c) 2017, CRIL-CNRS - lecoutre@cril.fr
 * 
 * All rights reserved.
 * 
 * This program and the accompanying materials are made available under the terms of the CONTRAT DE LICENCE DE LOGICIEL LIBRE CeCILL which accompanies this
 * distribution, and is available at http://www.cecill.info
 */
package problems.todo;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import org.xcsp.common.IVar.Var;
import org.xcsp.modeler.api.ProblemAPI;

import constraints.CtrHard;
import problem.Problem;
import utility.Kit;
import variables.Variable;

/*
 * This problem instance involves determining if there exists a set of " + nWords words of length 8 over the alphabet W={A,C,G,T} with properties defined at
 * http://4c.ucc.ie/~tw/csplib/prob/prob033/
 */
public class WordDesign implements ProblemAPI {

	int n;
	byte[][] words, complementWords;

	byte[] buildComplementOf(byte[] word) {
		byte[] complementWord = new byte[word.length];
		for (int i = 0; i < complementWord.length; i++)
			complementWord[i] = (byte) (word[i] == 'A' ? 'T'
					: word[i] == 'T' ? 'A' : word[i] == 'C' ? 'G' : word[i] == 'G' ? 'C' : (Byte) Kit.exit("Bad letter"));
		return complementWord;
	}

	void data() {
		n = imp().askInt("Order (number of words to be found)", rangeClosed(1, 1000));
		words = new byte[17440][];
		complementWords = new byte[17440][];
		try (BufferedReader in = new BufferedReader(new FileReader("/home/lecoutre/abssol/WordsDNA.dat"))) {
			for (int i = 0; i < words.length; i++) {
				words[i] = in.readLine().getBytes();
				complementWords[i] = buildComplementOf(words[i]);
				// System.out.println((char)words[i][0] + " " + (char)complementWords[i][0]);
			}
			assert in.readLine() == null;
		} catch (IOException e) {
			Kit.exit("Erreur ouverture fichier ", e);
		}
	}

	private boolean checkPair(int i, int j) {
		int cnt1 = 0, cnt2 = 0, cnt3 = 0;
		byte[] word0 = words[i], word1 = words[j], complement0 = complementWords[i], complement1 = complementWords[j];
		for (int k = 0; k < word0.length; k++) {
			if (word0[k] == word1[k]) {
				cnt1++;
				if (cnt1 == 5)
					return false;
			}
			// else if (i - cpt1 == 3)
			// break;
			if (word0[7 - k] == complement1[k]) {
				cnt2++;
				if (cnt2 == 5)
					return false;
			}
			if (word1[7 - k] == complement0[k]) {
				cnt3++;
				if (cnt3 == 5)
					return false;
			}
		}
		return true;

	}

	List<int[]> count() {
		List<int[]> list = new ArrayList<>();
		for (int i = 0; i < words.length; i++)
			for (int j = i + 1; j < words.length; j++)
				if (checkPair(i, j))
					list.add(tuple(i, j));

		return list;
	}

	class DistinctPositions extends CtrHard {
		public DistinctPositions(Problem problem, Variable[] scope) {
			super(problem, scope);
		}

		@Override
		public final boolean checkValues(int[] vals) {
			int cnt1 = 0, cnt2 = 0, cnt3 = 0;
			byte[] word0 = words[vals[0]], word1 = words[vals[1]];
			byte[] complement0 = complementWords[vals[0]], complement1 = complementWords[vals[1]];
			for (int i = 0; i < word0.length; i++) {
				if (word0[i] == word1[i]) {
					cnt1++;
					if (cnt1 == 5)
						return false;
				}
				// else if (i - cpt1 == 3)
				// break;
				if (word0[7 - i] == complement1[i]) {
					cnt2++;
					if (cnt2 == 5)
						return false;
				}
				if (word1[7 - i] == complement0[i]) {
					cnt3++;
					if (cnt3 == 5)
						return false;
				}
			}
			return true;
		}
	}

	@Override
	public void model() {
		// List<int[]> list = count();
		// System.out.println("COUNT =" + list.size());
		// mdd()

		Var[] x = array("x", size(n), dom(range(words.length)), "x[i] is the ith word");
		forall(range(n).range(n), (i, j) -> {
			if (i < j)
				((Problem) imp()).addCtr(new DistinctPositions(((Problem) imp()), (Variable[]) vars(x[i], x[j])));
		});
		strictlyIncreasing(x).tag(SYMMETRY_BREAKING);
	}

	/**********************************************************************************************
	 * Intern class
	 *********************************************************************************************/

	public static class WordsGenerator {
		private char[] word = new char[8], reverseWord = new char[8], watsonCrickWord = new char[8];

		private char giveCorrespondanceFor(int v) {
			return v == 0 ? 'A' : v == 1 ? 'C' : v == 2 ? 'G' : v == 3 ? 'T' : (Character) Kit.exit("Bad letter");
		}

		private char[] decrypt(int v) {
			int cnt = 0;
			for (int i = 0; i < word.length; i++) {
				word[i] = giveCorrespondanceFor(v % 4);
				if (word[i] == 'C' || word[i] == 'G')
					cnt++;
				v = v / 4;
			}
			if (cnt != 4)
				return null;

			for (int i = 0; i < reverseWord.length; i++)
				reverseWord[i] = word[8 - i - 1];
			for (int i = 0; i < watsonCrickWord.length; i++) {
				watsonCrickWord[i] = word[i] == 'A' ? 'T'
						: word[i] == 'T' ? 'A' : word[i] == 'C' ? 'G' : word[i] == 'G' ? 'C' : (Character) Kit.exit("Bad letter");
			}
			int cnt2 = 0;
			for (int i = 0; i < 8; i++)
				if (reverseWord[i] != watsonCrickWord[i])
					cnt2++;
			return cnt2 < 4 ? null : word;
		}
	}

	public static void main(String[] args) {
		try (PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter("WordsDNA.dat")))) {
			WordsGenerator wg = new WordsGenerator();
			int n = (int) Math.pow(4, 8);
			List<char[]> list = new ArrayList<>();
			for (int i = 0; i < n; i++) {
				char[] s = wg.decrypt(i);
				if (s != null) {
					list.add(s);
					out.println(s);
				}
			}
			System.out.println("cnt=" + list.size());
			char[] reversei = new char[8], watsoni = new char[8], reversej = new char[8], watsonj = new char[8];
			int cnt = 0;
			for (int i = 0; i < list.size(); i++) {
				char[] wordi = list.get(i);
				for (int k = 0; k < 8; k++)
					reversei[k] = wordi[8 - k - 1];
				for (int k = 0; k < 8; k++)
					watsoni[k] = wordi[k] == 'A' ? 'T' : wordi[k] == 'T' ? 'A' : wordi[k] == 'C' ? 'G' : 'C';
				for (int j = i + 1; j < list.size(); j++) {
					char[] wordj = list.get(j);
					for (int k = 0; k < 8; k++)
						reversej[k] = wordj[8 - k - 1];
					for (int k = 0; k < 8; k++)
						watsonj[k] = wordj[k] == 'A' ? 'T' : wordj[k] == 'T' ? 'A' : wordj[k] == 'C' ? 'G' : 'C';
					int cnt1 = 0, cnt2 = 0;
					for (int k = 0; k < 8; k++) {
						if (reversei[k] != watsonj[k])
							cnt1++;
						if (reversej[k] != watsoni[k])
							cnt2++;
					}
					if (cnt1 >= 4 && cnt2 >= 4)
						cnt++;
				}
				System.out.println(i + " " + cnt);
			}

		} catch (IOException e) {
			Kit.exit("Not possible to build file ", e);
		}
	}
}