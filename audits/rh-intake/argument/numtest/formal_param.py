"""Robustness: redo the valuation test in the integral formal-group parameter t = -2x/y
(= -x/Y for the integral model Y^2 = x^3 - (g2/4)x - g3/4) instead of z, for curve A
(g2=4, g3=0). Prints v_p(a! [t^a] sigma(z(t))) and the same z-statistics side by side,
and also v_p of the coefficients of z(t) = log_F(t) and of t(z) = exp_F(z)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import factorial
from sigma_lib import sigma_derivs_stream, vp_fact
M = int(sys.argv[1]) if len(sys.argv) > 1 else 241

def vpq(x, p):
    if x == 0: return None
    n, d, v = x.numerator, x.denominator, 0
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v

def mul(A, B, n):
    C = [F(0)] * n
    for i, x in enumerate(A[:n]):
        if x:
            for j in range(n - i):
                if B[j]: C[i + j] += x * B[j]
    return C

def inv(A, n):  # A[0] != 0
    R = [F(0)] * n; R[0] = 1 / A[0]
    for k in range(1, n):
        R[k] = -sum((A[j] * R[k - j] for j in range(1, k + 1) if j < len(A) and A[j]), F(0)) / A[0]
    return R

g2, g3 = F(4), F(0)
n = M + 4
# wp = z^-2 (1 + sum_{k>=2} c_k z^{2k}); wp' = z^-3 (-2 + sum (2k-2) c_k z^{2k})
K = n // 2 + 2
c = [F(0)] * (K + 1); c[2] = g2 / 20; c[3] = g3 / 28
for k in range(4, K + 1):
    c[k] = F(3, (2 * k + 1) * (k - 3)) * sum((c[m] * c[k - m] for m in range(2, k - 1)), F(0))
P = [F(0)] * n; Q = [F(0)] * n; P[0] = F(1); Q[0] = F(-2)
for k in range(2, K + 1):
    if 2 * k < n: P[2 * k] = c[k]; Q[2 * k] = (2 * k - 2) * c[k]
# t = -2 wp/wp' = z * (-2 P / Q)
T = [F(0)] + [-2 * x for x in mul(P, inv(Q, n), n - 1)]   # t(z) coefficients, T[1] = 1
# invert t(z) -> z(t) by Lagrange-free iteration: z = t - sum_{k>=2} T_k z^k
Z = [F(0), F(1)] + [F(0)] * (n - 2)
pw = [None, Z[:]]
for it in range(n):
    # recompute powers of Z
    pw = [[F(1)] + [F(0)] * (n - 1), Z[:]]
    for k in range(2, n): pw.append(mul(pw[-1], Z, n))
    newZ = [F(0), F(1)] + [F(0)] * (n - 2)
    for k in range(2, n):
        if T[k]:
            for j in range(n): newZ[j] -= T[k] * pw[k][j]
    if newZ == Z: break
    Z = newZ
D = sigma_derivs_stream(n, {'A': (2, 0)})['A']
sig = [F(D[k], factorial(k)) for k in range(n)]
# sigma(z(t)) = sum sig_k Z^k
S = [F(0)] * n
for k in range(1, n):
    if sig[k]:
        for j in range(n): S[j] += sig[k] * pw[k][j]
for p in (7, 11, 5, 13):
    print(f"p={p} ({'inert' if p % 4 == 3 else 'split'}):  a : v_p(a![t^a]sigma) | v_p(D^a_z sigma) | v_p(a!)-a/(p^2-1) [claim] | sum floor(a/p^2k)")
    for a in range(1, M + 1, 4):
        if a % 40 == 1 or a == M:
            w = 0; q = p * p
            while q <= a: w += a // q; q *= p * p
            print(f"   {a:4d}: {vpq(S[a] * factorial(a), p)!s:>5} | {vpq(sig[a]*factorial(a), p)!s:>5} | "
                  f"{float(vp_fact(a, p) - F(a, p*p-1)):7.2f} | {w}")
    vz = [vpq(Z[k], p) for k in range(1, n) if Z[k]]
    vt = [vpq(T[k], p) for k in range(1, n) if T[k]]
    print(f"   log_F(t) coefficients: min v_p = {min(vz)};  exp_F(z) coefficients: v_p(T_k)+k/(p^2-1) min over k<{n} = "
          f"{min(float(vpq(T[k],p) + F(k-1, p*p-1)) for k in range(1, n) if T[k]):.3f}")
