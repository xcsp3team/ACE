package problems.todo;

import java.util.ArrayList;
import java.util.List;

import org.xcsp.modeler.api.ProblemAPI;
import org.xcsp.modeler.implementation.NotData;

import utility.Kit;

public class DNA implements ProblemAPI {

	@NotData
	int f;

	private int[] watsonCrickOf(int[] t) {
		int[] tt = new int[8];
		for (int i = 0; i < 8; i++)
			tt[i] = t[i] == 0 ? 3 : t[i] == 1 ? 2 : t[i] == 2 ? 1 : 0;
		return tt;
	}

	private boolean verifyHD(int[] w1, int[] w2) {
		int cnt = 0;
		for (int i = 0; i < 8; i++)
			if (w1[i] != w2[i])
				cnt++;
		return cnt >= 4;
	}

	private boolean verifyRC(int[] w1, int[] w2) {
		int[] w2r = watsonCrickOf(w2);
		int cnt = 0;
		for (int i = 0; i < 8; i++)
			if (w1[8 - i - 1] != w2r[i])
				cnt++;
		return cnt >= 4;
	}

	private int[][] domains() {
		List<int[]> list = new ArrayList<>();
		for (int i1 = 0; i1 < 4; i1++)
			for (int i2 = 0; i2 < 4; i2++)
				for (int i3 = 0; i3 < 4; i3++)
					for (int i4 = 0; i4 < 4; i4++)
						for (int i5 = 0; i5 < 4; i5++)
							for (int i6 = 0; i6 < 4; i6++)
								for (int i7 = 0; i7 < 4; i7++)
									for (int i8 = 0; i8 < 4; i8++) {
										int[] t = { i1, i2, i3, i4, i5, i6, i7, i8 };
										if (Kit.countIn(1, t) + Kit.countIn(2, t) != 4)
											continue;
										if (verifyRC(t, t))
											list.add(t);

										// int[] tt = watsonCrickOf(t); // IntStream.of(t).map(v -> v == 0 ? 3 : v == 1 ? 2 : v == 2 ? 1 :
										// // 0).toArray();
										// int d = (int) IntStream.range(0, 7).filter(i -> t[8 - i - 1] != tt[i]).count();
										// if (d >= 4)
										// list.add(t);
									}
		System.out.println("Nb" + list.size());
		return Kit.intArray2D(list);

	}

	@Override
	public void model() {
		int[][] m = domains();
		int cnt = 0;
		for (int i = 0; i < m.length; i++)
			for (int j = i + 1; j < m.length; j++) {
				if (verifyHD(m[i], m[j]) && verifyRC(m[i], m[j]) && verifyRC(m[j], m[i]))
					// int ii = i, jj = j, d = (int) IntStream.range(0, 7).filter(k -> m[ii][k] != m[jj][k]).count();
					// if (d < 4)
					// continue;

					cnt++;
				// int[] tti = watsonCrickOf(m[i]);

			}
		System.out.println("cnt" + cnt);

	}

}
