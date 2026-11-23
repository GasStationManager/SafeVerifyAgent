"""E5: the DIV Young-diagram remainder eE over m lifts, with the Lean's own weight formulas
(Numbers.lean: srcPar, nu (NUM:224-225), sigPar, aPlus (NUM:178-184), apRows/logHook (NUM:239-245);
NumbersLink.lean: eEN (NL:35-36)).  Question: is sum_j eE_j <= m * C * w * La with C independent of m,
i.e. is the per-lift remainder stationary in the lift index j, or does it accumulate faster?
Also: the binomial loss that WOULD occur if the m lifts reused one top variable (accumulated degree).
Usage: python3 -I composite6_young.py
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import composite6_lib as L
from fractions import Fraction as F


def shapes(k, m, t, a, w1, ex, top=True, bbig=True):
    """Return per-lift (nu rows (real), a+ rows (floored), eE, w_j)."""
    r = k + m - 1; nV = r + t
    N = lambda j: k + j * (t + 1)
    w = {j: F(w1) + (j - 1) * (t + 1 + ex) for j in range(1, m + 1)}
    u = [F(a) + F(k - 1, 2) if top else F(k - 1, 2)] + [F(k - 1, 2) - i for i in range(1, k)]
    v = [F(k - 2, 2) - i for i in range(k - 1)]
    b = [F(10 ** 9) if bbig else F(0)] * m
    assert all(u[i + 1] < v[i] < u[i] for i in range(k - 1)), "interlacing"
    def uW(i):
        return v[i - 1] - F(1, 2) if 1 <= i and i + 1 < k else u[i]
    def srcPar(i):
        if i < k:
            return uW(i)
        l = (i - k) // (t + 1)
        if l < m:
            return -w[l + 1] + F(t + 2 - 2 * (((i - k) % (t + 1)) + 1), 2)
        return F(0)
    def sigPar(i):
        if i < k - 1:
            return v[i]
        if i - (k - 1) < m:
            return -b[i - (k - 1)]
        return F(0)
    out = []
    for j in range(1, m + 1):
        nu = [srcPar(i) + w[j] - F(N(j - 1) + N(j) - 1 - 2 * i, 2) for i in range(N(j - 1))]
        ap = [sigPar(i) + w[j] - F(nV - 1 - 2 * i, 2) - F((k + j - 1) - (m - j), 2) for i in range(k + j - 1)]
        apN = [max(0, math.floor(x)) for x in ap]
        assert all(x >= 0 for x in nu), ("nu0 violated", j, nu)
        e = sum(L.ph(float(x)) for x in nu) - L.log_hook(apN) - (L.ph(a) if top else 0.0)
        out.append((nu, apN, e, float(w[j])))
    return out


print("=== eE_j along the lifts, top place (rows: nu = (a+w', w'^(k-1), blk), a+ = (w'+sh)^(k-1) floored) ===")
print("k | t | ex | a | w1 | m | eE_1 .. eE_m | sum eE | sum/(m * w_mean * La) | max_j eE_j/(w_j La) | blk sum at j=m | eE_m - eE_1")
for k in (2, 3, 4):
    for t in (0, 1):
        for ex in (0, 1):
            for a in (50, 200, 2000):
                for w1 in (5, 10, 20, 40):
                    if w1 >= a:
                        continue
                    for m in (1, 2, 3, 4, 6, 8):
                        if (a, w1) not in ((50, 5), (200, 10), (2000, 40), (200, 40)) and m != 8:
                            continue
                        sh = shapes(k, m, t, a, w1, ex)
                        La = math.log(a + 2 * w1)
                        es = [x[2] for x in sh]
                        wm = sum(x[3] for x in sh) / m
                        blk = float(sum(x for x in sh[-1][0][k:]))
                        rat = max(x[2] / (x[3] * La) for x in sh)
                        if m in (1, 3, 8):
                            print(f"{k} | {t} | {ex} | {a} | {w1} | {m} | " + " ".join(f"{e:.1f}" for e in es)
                                  + f" | {sum(es):.1f} | {sum(es)/(m*wm*La):.3f} | {rat:.3f} | {blk:.0f} | {es[-1]-es[0]:.1f}")

print("\n=== off-top places (u_0 = (k-1)/2): eE_j along the lifts ===")
print("k | t | ex | w1 | m | eE_1 .. eE_m | max_j eE_j/(w_j log(w_j))")
for k in (2, 3, 4):
    for t in (0, 1):
        for ex in (0, 1):
            for w1 in (10, 40):
                m = 6
                sh = shapes(k, m, t, 0, w1, ex, top=False)
                es = [x[2] for x in sh]
                print(f"{k} | {t} | {ex} | {w1} | {m} | " + " ".join(f"{e:.1f}" for e in es)
                      + f" | {max(x[2]/(x[3]*math.log(x[3])) for x in sh):.3f}")

print("\n=== The binomial that a REUSED top variable would produce (not the Lean's structure; control) ===")
print("If lift j multiplied the same variable by z^a, the composite would carry (m a)! while the step bounds carry m*ph(a):")
print("a | m | log((m a)!) - m*ph(a) | m*a*log m | (for comparison: one-lift allowance 2 w La, w = a/50)")
for a in (50, 200, 2000):
    for m in (2, 3, 8):
        x = L.lfact(m * a) - m * L.ph(a)
        print(f"{a} | {m} | {x:.1f} | {m*a*math.log(m):.1f} | {2*(a/50)*math.log(a):.1f}")
