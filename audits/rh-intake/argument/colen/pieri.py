# Pieri model of the coarse block count behind t0G4 / blockOrd (ObjSeg.lean:282-284, 439-442):
# Sym^A (x) Sym^B = sum_{o=0}^{min(A,B)} V_(A+B-o, o)  for GL_n, n = m+1.
# Cost of the piece with o contractions in the coarse model = P*o (P = p^(G-d)), so the dimension-weighted
# distribution of o says how much of Sym^A (x) Sym^B needs cost close to P*min(A,B) = min(b, a/p^d).
# Prints, for each n, the fraction of dim with o <= (1-delta)*min(A,B), and the mean deficiency.
import sys
from math import comb, log

def dim2(n, l1, l2):  # hook-content formula for the two-row partition (l1, l2) in GL_n
    num = den = 1
    for j in range(l1):           # row 0, content j
        num *= n + j
        h = (l1 - j - 1) + (1 if j < l2 else 0) + 1
        den *= h
    for j in range(l2):           # row 1, content j-1
        num *= n + j - 1
        den *= (l2 - j - 1) + 1
    assert num % den == 0
    return num // den

def run(n, A, B):
    M = min(A, B)
    ds = [dim2(n, A + B - o, o) for o in range(M + 1)]
    tot = sum(ds)
    assert tot == comb(A + n - 1, n - 1) * comb(B + n - 1, n - 1)
    def frac_le(o_max): return sum(ds[: o_max + 1]) / tot
    mean_def = sum((M - o) * d for o, d in enumerate(ds)) / tot / M
    return frac_le, mean_def, M

if __name__ == '__main__':
    A = int(sys.argv[1]); B = int(sys.argv[2])
    print("A=%d B=%d : fraction of dim(Sym^A x Sym^B) with o <= (1-delta)min(A,B); mean (min-o)/min" % (A, B))
    print(" n=m+1 | delta=0.5   0.25    0.1    0.05 | mean deficiency | log(A)/n")
    for n in [2, 3, 5, 10, 20, 50, 100, 200]:
        f, md, M = run(n, A, B)
        row = [f(int((1 - d) * M)) for d in (0.5, 0.25, 0.1, 0.05)]
        print(" %4d  | %s | %.4f | %.4f" % (n, "  ".join("%.2e" % x for x in row), md, log(A) / n))
