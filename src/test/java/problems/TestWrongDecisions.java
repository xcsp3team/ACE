package problems;

import static org.junit.Assert.assertEquals;
import static problems.UtilityForTests.runResolution;

import java.net.URL;
import java.util.Collection;
import java.util.LinkedList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.xcsp.common.Utilities;

import main.Head;

@RunWith(Parameterized.class)
public class TestWrongDecisions {

	static Collection<Object[]> collection = new LinkedList<>();

	static void add(Object instance, int nWrongDecisions, String pars) {
		pars += " -ev";
		URL url = Head.class.getResource(instance + ".xml.lzma");
		Utilities.control(url != null, "not found: " + instance + ".xml.lzma");
		collection.add(new Object[] { url.getPath() + " " + pars, nWrongDecisions });
	}

	static void add(String instance, int nWrongDecisions) {
		add(instance, nWrongDecisions, "");
	}

	@Parameters(name = "{index}: {0} has {1} wrong decisions")
	public static Collection<Object[]> data() {

		add("/csp/Rlfap-scen-11-f06", 11548, "-varh=WdegOnDom");
		add("/csp/Crossword-lex-vg-5-6", 11709, "-varh=WdegOnDom");
		add("/csp/Crossword-lex-vg-5-6", 16388, "-varh=DdegOnDom -positive=str1");
		add("/csp/Crossword-lex-vg-5-6", 16388, "-varh=DdegOnDom -positive=str2");
		add("/csp/Crossword-lex-vg-5-6", 16388, "-varh=DdegOnDom -positive=str3");
		add("/csp/Crossword-lex-vg-5-6", 16388, "-varh=DdegOnDom -positive=mdd");
		return collection;
	}

	@Parameter(0)
	public String args;

	@Parameter(1)
	public int nWrongDecisions;

	@Test
	public void test() throws InterruptedException {
		assertEquals(nWrongDecisions, runResolution(args).solver.stats.nWrongDecisions);
	}
}
