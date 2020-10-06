package problems.generators;

import java.util.StringTokenizer;

import org.xcsp.common.Constants;
import org.xcsp.common.Utilities;

import problems.ReaderFile.ReaderTxt;
import problems.g4_world.Tal;

/**
 * Created on 15 avr. 2013 by remi coletta <br>
 * java abscon.Resolution problems.real.tal.Tal ~/instances/tal/resources/french2 3 15-25-35-25-37-35-25-15-35-25-27 0 -f=cop -varh=Memory
 */
public class TalReader extends Tal implements ReaderTxt {

	void data() {
		scanner(); // for asking the grammar file
		int maxArity = imp().askInt("Max arity");
		String encodedSentence = imp().askString("Encoded sentence");
		int maxHeight = imp().askInt("maximum height");
		int[] sentence = Utilities.splitToInts(encodedSentence, "(\\s|-)+");
		int[][][] grammar = new int[maxArity + 1][][];
		int[] costs = Utilities.splitToInts(nextLine().substring("#Costs:".length()));
		String[] tokens = nextLine().substring("#Tokens: ".length()).split(Constants.REG_WS);
		Utilities.control(tokens[0].length() != 0, "");
		for (int arity = 1; arity <= maxArity; arity++) {
			StringTokenizer st = new StringTokenizer(nextLine(), Constants.WHITE_SPACE + "#");
			int a = Integer.parseInt(st.nextToken()), nb = Integer.parseInt(st.nextToken());
			Utilities.control(a == arity + 1, "");
			grammar[arity] = new int[nb][arity + 3];
			for (int i = 0; i < grammar[arity].length; i++) {
				st = new StringTokenizer(nextLine());
				grammar[arity][i] = new int[st.countTokens()];
				for (int j = 0; j < grammar[arity][i].length; j++) {
					String token = st.nextToken();
					grammar[arity][i][j] = token.equals(STAR_SYMBOL) ? STAR : Integer.parseInt(token);
				}
			}
		}
		setDataValues(maxArity, maxHeight, sentence, grammar, tokens, costs);
	}

}
