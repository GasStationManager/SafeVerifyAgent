"""Independent high-order check (different algorithm): sigma from the wp-coefficient recursion
c_k = 3/((2k+1)(k-3)) sum_{m=2}^{k-2} c_m c_{k-m}, log(sigma/z) = -sum c_k z^{2k}/((2k)(2k-1)),
sigma/z = exp(.) by E' = L'E, all in exact Fractions; compare a! [z^a] with the integer
D^a sigma(0) from Weierstrass's recursion, for curves A (g2=4,g3=0), B (g2=0,g3=4), C (g2=-10,g3=7/2)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import factorial
from sigma_lib import sigma_derivs_stream
M = int(sys.argv[1]) if len(sys.argv) > 1 else 260

def sigma_via_wp(g2, g3, M):
    K = M // 2 + 1
    c = [F(0)] * (K + 1)
    c[2] = g2 / 20; c[3] = g3 / 28
    for k in range(4, K + 1):
        c[k] = F(3, (2 * k + 1) * (k - 3)) * sum(c[m] * c[k - m] for m in range(2, k - 1))
    L = [F(0)] * (M + 1)            # L(z) = log(sigma/z)
    for k in range(2, K + 1):
        if 2 * k <= M: L[2 * k] = -c[k] / ((2 * k) * (2 * k - 1))
    E = [F(0)] * (M + 1); E[0] = F(1)   # E = exp(L): n E_n = sum_j j L_j E_{n-j}
    for n in range(1, M + 1):
        E[n] = sum((j * L[j] * E[n - j] for j in range(1, n + 1) if L[j]), F(0)) / n
    return [F(0)] + E[:M]            # sigma coefficients: [z^{k}] = E[k-1]

curves = {'A': ((2, 0), F(4), F(0)), 'B': ((0, 8), F(0), F(4)), 'C': ((-5, 7), F(-10), F(7, 2))}
Ds = sigma_derivs_stream(M, {k: v[0] for k, v in curves.items()})
for name, (_, g2, g3) in curves.items():
    s = sigma_via_wp(g2, g3, M)
    bad = [k for k in range(1, M + 1) if s[k] * factorial(k) != Ds[name][k]]
    print(f"curve {name}: D^a sigma(0) agree for all a <= {M}: {not bad}  (mismatches: {bad[:5]})")
    assert not bad
