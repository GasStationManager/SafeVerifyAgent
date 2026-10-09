"""Exact LP certificates for the 9/4 growth-lemma LP at every a0, by the absorbing-Markov-chain
argument of the ReadingGroup review (brainstorms/mm94-primal-review-and-general-certificates.md).

States (a,b), 2 <= a <= a0, a <= b <= 4a-4.  From (a,b) with b < 4a-4: to (a,b+1) with probability
q*(a,b), to sorted(a,b-1) with probability 1-q*(a,b).  From (a,4a-4): to (a-1,a).  (1,2) absorbs.
The dual weight of row E_{a,b,q*} (resp. F_{a,a-1}) is the expected number of visits to (a,b)
(resp. (a,4a-4)) starting from (a0,a0).  All inflow into row a enters at (a,a+1), so each row is a
tridiagonal system and the whole thing is O(a0^2) exact rational operations.

Usage: python3 chain_certificate.py A0 [--print]   (prints weights for small A0; summary otherwise)
"""
import sys, math
from fractions import Fraction as Fr
from math import lcm

def c(a):
    r = Fr(1)
    for m in range(1, a): r *= 1 + Fr(1, 3*m)
    return r
def Dstar(a): return Fr(3*a - 1, 2) * c(a)
def qstar(a, b): return Fr(3*a + 1, 6*a - 2) if a == b else Fr(a + 2*b + 1, 2*(a + 2*b - 1))
def H(q): q = float(q); return -q*math.log(q) - (1-q)*math.log(1-q)

def weights(a0):
    """Exact expected visit counts w[(a,b)], row by row from a0 down to 2."""
    w = {}
    inflow = Fr(0)                       # inflow into row a at state (a,a+1)
    for a in range(a0, 1, -1):
        B = 4*a - 4
        bs = list(range(a, B + 1)); n = len(bs)
        # unknowns x_b; equations x_b = src_b + q_{b-1} x_{b-1} + (1-q_{b+1}) x_{b+1}
        src = {b: Fr(0) for b in bs}
        if a == a0: src[a] += 1
        if a + 1 <= B: src[a + 1] += inflow
        q = {b: qstar(a, b) for b in bs}
        # tridiagonal: -q_{b-1} x_{b-1} + x_b - (1-q_{b+1}) x_{b+1} = src_b ; x_B has no (1-q) inflow from B+1
        # coefficients: sub[b] = -q_{b-1} (b>a), diag = 1, sup[b] = -(1-q_{b+1}) (b<B)
        sub = {b: -q[b-1] for b in bs if b > a}
        sup = {b: -(1 - q[b+1]) for b in bs if b < B - 1}   # (a,B) never moves back
        # Thomas algorithm (exact)
        cp = {}; dp = {}
        for i, b in enumerate(bs):
            if i == 0:
                cp[b] = sup[b] if b < B - 1 else Fr(0); dp[b] = src[b]
            else:
                m = 1 - sub[b] * cp[bs[i-1]]
                cp[b] = (sup[b] / m) if b < B - 1 else Fr(0)
                dp[b] = (src[b] - sub[b] * dp[bs[i-1]]) / m
        x = {}
        for i in range(n - 1, -1, -1):
            b = bs[i]
            x[b] = dp[b] - (cp[b] * x[bs[i+1]] if i < n - 1 else 0)
        for b in bs: w[(a, b)] = x[b]
        inflow = (1 - q[a]) * x[a] + x[B]       # to (a-1,a): from (a,a) with prob 1-q, from (a,B) surely
    return w

def certificate_value(a0, w):
    """w^T r with r the constant terms: E rows 6H(q*)-6log2 (+ boundary), F rows 6log3 (+ boundary)."""
    val = 0.0
    for (a, b), wt in w.items():
        if b < 4*a - 4:
            q = qstar(a, b); r = 6*H(q) - 6*math.log(2)
            if a == 2 and b == 2: r += float(1 - q) * 6*math.log(2)      # (2,1) sorts to (1,2)
        else:
            r = 6*math.log(3)
            if a == 2: r += 6*math.log(2)                                  # (1,2)
        val += float(wt) * r
    return val

if __name__ == "__main__":
    a0 = int(sys.argv[1]); w = weights(a0)
    assert all(v >= 0 for v in w.values())
    den = 1
    for v in w.values(): den = lcm(den, v.denominator)
    val = certificate_value(a0, w); target = 6*math.log(float(Dstar(a0)))
    omega = 3*math.log(2*a0 - 1) / math.log(float(Dstar(a0)))
    print(f"a0={a0}: {len(w)} rows, all weights nonnegative, w^T r = {val:.9f}, 6 log D* = {target:.9f}, "
          f"diff = {val-target:.1e}; lcm of denominators has {len(str(den))} digits; omega(a0) = {omega:.6f}")
    if "--print" in sys.argv:
        for s in sorted(w): print(f"  {s}: {w[s]}  (x lcm = {w[s]*den})")
