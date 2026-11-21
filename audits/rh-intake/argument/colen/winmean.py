# Toy test of WindowFullAP / WindowMeanAP (MahlerMeasure/QuotientUpperBoundsOfPowerBounds.lean:22-56):
# for a matrix M(t) whose entries are Z_p-combinations of binom(t,k), k<=del0,
# mean over t in a progression of length Y0 of #{Smith entries with v_p >= E}
#   <= n*(del0/Y0 + (La0 + del0*h/Y0)/E),  with  -log_p|lead| + #roots/(p-1) <= n*La0, Y0<=p^h, del0<=p^h.
import sys, random
from fractions import Fraction
from math import comb

def vp(x, p):
    if x == 0: return 10**9
    x = abs(x); v = 0
    while x % p == 0: x //= p; v += 1
    return v

def vpF(q, p):
    if q == 0: return 10**9
    return vp(q.numerator, p) - vp(q.denominator, p)

def smith_vals(M, p):
    # p-adic Smith valuations of an integer matrix (over Z_(p))
    A = [[Fraction(x) for x in row] for row in M]
    n = len(A); vals = []
    rows = list(range(n)); cols = list(range(n))
    while rows:
        best = None
        for i in rows:
            for j in cols:
                v = vpF(A[i][j], p)
                if best is None or v < best[0]: best = (v, i, j)
        v, i, j = best
        if v >= 10**9:
            vals += [10**9] * len(rows); break
        vals.append(v)
        piv = A[i][j]
        for i2 in rows:
            if i2 != i and A[i2][j] != 0:
                f = A[i2][j] / piv
                for j2 in cols: A[i2][j2] -= f * A[i][j2]
        rows.remove(i); cols.remove(j)
    return vals

def det(M):
    A = [[Fraction(x) for x in r] for r in M]; n = len(A); d = Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None: return Fraction(0)
        if piv != c: A[c], A[piv] = A[piv], A[c]; d = -d
        d *= A[c][c]
        for r in range(c+1, n):
            f = A[r][c] / A[c][c]
            for k in range(c, n): A[r][k] -= f * A[c][k]
    return d

def lead_coeff(Mt, D):
    # det(M(t)) polynomial of degree <= D: leading coefficient via finite differences
    vals = [det(Mt(t)) for t in range(D + 1)]
    for _ in range(D):
        vals = [vals[i+1] - vals[i] for i in range(len(vals) - 1)]
    # D-th difference = D! * coeff_D
    c = vals[0]; f = 1
    for i in range(2, D + 1): f *= i
    return c / f

def run(name, Mt, n, del0, p, t0, Y0, E):
    D = n * del0
    lc = lead_coeff(Mt, D); dg = D
    while lc == 0 and dg > 0:
        dg -= 1; lc = lead_coeff(Mt, dg)
    h = 0
    while p**h < max(Y0, del0): h += 1
    lam = -vpF(lc, p) * -1  # -log_p|lead| = v_p(lead)
    lam = vpF(lc, p)
    La0 = (lam + dg / (p - 1)) / n
    tot = 0
    for j in range(Y0):
        sv = smith_vals(Mt(t0 + j), p)
        tot += sum(1 for v in sv if v >= E)
    mean = tot / Y0
    bound = n * (del0 / Y0 + (La0 + del0 * h / Y0) / E)
    print(f"{name:10s} p={p} n={n} del0={del0} Y0={Y0} E={E} v(lead)={lam} degdet={dg} "
          f"mean#bad={mean:.4f} share={mean/n:.4f} bound={bound:.4f} boundshare={bound/n:.4f}")
    return mean, bound

if __name__ == "__main__":
    random.seed(1)
    out = []
    for p in (5, 7):
        for n in (3, 5):
            # (A) Hankel of binomials: M_ij(t) = C(t, i+j)
            Mt = lambda t, n=n: [[comb(t, i + j) for j in range(n)] for i in range(n)]
            for E in (2, 4, 8):
                out.append(run("hankel", Mt, n, 2*n-2, p, 3*p**3 + 1, 200, E))
            # (B) random integer combos of binomials, deg <= 3
            C = [[[random.randint(-3, 3) for k in range(4)] for j in range(n)] for i in range(n)]
            Mt2 = lambda t, C=C, n=n: [[sum(C[i][j][k]*comb(t, k) for k in range(4)) for j in range(n)] for i in range(n)]
            for E in (2, 4, 8):
                out.append(run("randbin", Mt2, n, 3, p, 1000, 200, E))
    viol = [o for o in out if o[0] > o[1] + 1e-12]
    print("violations:", len(viol))
