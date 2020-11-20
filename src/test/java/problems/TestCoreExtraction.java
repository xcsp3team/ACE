package problems;

import static org.junit.Assert.assertEquals;
import static problems.UtilityForTests.runExtraction;

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
public class TestCoreExtraction {

	static Collection<Object[]> collection = new LinkedList<>();

	static void add(Object instance, int nWrongDecisions, String pars) {
		pars += " -v=0 -ev";
		URL url = Head.class.getResource(instance + ".xml.lzma");
		Utilities.control(url != null, "not found: " + instance + ".xml.lzma");
		collection.add(new Object[] { url.getPath() + " " + pars, nWrongDecisions });
	}

	static void add(String instance, int nWrongDecisions) {
		add(instance, nWrongDecisions, "");
	}

	@Parameters(name = "{index}: {0} has a first core with {1} constraints")
	public static Collection<Object[]> data() {
		add("/csp/Rlfap-scen-09-w1-f03", 8);
		return collection;
	}

	@Parameter(0)
	public String args;

	@Parameter(1)
	public int nConstraintsOfFirstCore;

	@Test
	public void test() {
		assertEquals(nConstraintsOfFirstCore, runExtraction(args).cores.get(0).size());
	}
}
