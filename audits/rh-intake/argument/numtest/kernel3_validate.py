"""Validation of kernel3_lib (second, independent methods).
1. th0 jets: check th0(z)^2 == sigma(z)^2 (wp(z) - e) as exact power series (sigma from sigma_lib's Weierstrass
   recursion, wp from the Laurent recursion), i.e. th0 is the co-sigma function sigma*(z+t)e^{..}/sigma*(t).
2. Functional check: |th0(x)| e^{-pi x^2/(2A)} is periodic-bounded on the real line (Gaussian growth, H = 1/A).
3. J(a,w): recompute from a brute-force bivariate expansion of th0(z0+z1) th0(c(z0-z1)) in Z_{p^2}/p^K, a+w <= 40.
4. Perturbation control: T_20 += 1 changes the valuations.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import math, random
from fractions import Fraction
from math import comb, factorial
from sigma_lib import sigma_derivs_stream
from kronecker_lib import wp_coeffs
from kernel3_lib import th0_jets, Zp2, jets_grid

M = 44
curves = {'Zi': (4, 0, [0, 1, -1]), 'Zw': (0, 4, [1])}
print('== 1. th0^2 = sigma^2 (wp - e), exact, through z^%d' % M)
for name, (g2, g3, es) in curves.items():
    D = sigma_derivs_stream(M + 3, {name: (g2 // 2, 2 * g3)})[name]
    sig = [Fraction(D[k], factorial(k)) for k in range(M + 3)]
    c = wp_coeffs(g2, g3, M)
    for e in es:
        T = th0_jets(g2, g3, e, M)
        th = [Fraction(T[k], factorial(k)) for k in range(M + 1)]
        # wp - e as Laurent: z^-2 + (-e) + sum_{n>=2} c_n z^{2n-2};  sigma^2 (wp-e) power series
        s2 = [sum(sig[i] * sig[k - i] for i in range(k + 1)) for k in range(M + 3)]
        W = {-2: Fraction(1), 0: Fraction(-e)}
        for n in range(2, M // 2 + 2): W[2 * n - 2] = c[n] if n < len(c) else 0
        rhs = [sum(s2[k - j] * W.get(j, 0) for j in range(-2, k + 1) if 0 <= k - j < len(s2)) for k in range(M + 1)]
        lhs = [sum(th[i] * th[k - i] for i in range(k + 1)) for k in range(M + 1)]
        ok = all(lhs[k] == rhs[k] for k in range(M + 1))
        print(f'  {name} e={e:2d}: identity holds to z^{M}: {ok};  T_0..T_10 = {T[:11]}')

print('\n== 2. Gaussian growth of th0 on the real axis (Z[i], e=1):  log|th0(x)| - pi x^2/(2A)')
g2, g3, e = 4, 0, 1
def agm(a, b):
    for _ in range(60): a, b = (a + b) / 2, math.sqrt(a * b)
    return a
w1 = math.pi / agm(math.sqrt(2), 1.0)   # real period of y^2 = 4x^3 - 4x (roots 1, 0, -1); lattice = w1*Z[i]
A = w1 * w1
T = th0_jets(g2, g3, e, 400)
def th0(x):  # Taylor sum with floats via logs to avoid overflow
    s = 0.0
    for k in range(0, 400, 2):
        if T[k]:
            s += (1 if T[k] > 0 else -1) * math.exp(math.log(abs(T[k])) - math.lgamma(k + 1) + k * math.log(abs(x))) if x else (1.0 if k == 0 else 0.0)
    return s
print(f'  period w1 = {w1:.6f}, area A = {A:.6f}')
for x in [0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0]:
    v = th0(x)
    print(f'  x={x:3.1f}  th0={v: .5e}  log|th0| - pi x^2/(2A) = {math.log(abs(v)) - math.pi*x*x/(2*A) if v else float("nan"): .4f}')

print('\n== 3. J(a,w) vs brute-force bivariate expansion (Z_{p^2} mod p^K), a+w <= 40')
for (g2, g3, e, p) in [(4, 0, 1, 7), (4, 0, 0, 11), (0, 4, 1, 5), (0, 4, 1, 11)]:
    K = 30
    R = Zp2(p, K)
    c = R.elt_of_norm(-1, 1) or R.elt_of_norm(-1, 2)
    assert R.norm(c) == R.q - 1
    T = th0_jets(g2, g3, e, 60)
    G = jets_grid(T, R, c, [0, 1, 2, 3, 5], 35)
    # brute: Theta = sum_{i,j} T_i T_j c^j (z0+z1)^i (z0-z1)^j / (i! j!), coefficient of z0^a z1^w times a! w!
    q = R.q
    cp = [(1, 0)]
    for k in range(80): cp.append(R.mul(cp[-1], c))
    bad = 0; tot = 0
    for (a, w), val in G.items():
        if a + w > 40: continue
        n = a + w
        acc = (0, 0)
        for i in range(n + 1):
            j = n - i
            # [z0^a z1^w] (z0+z1)^i (z0-z1)^j  = sum_r C(i,r) C(j, a-r) (-1)^{j-(a-r)}
            co = sum(comb(i, r) * comb(j, a - r) * (-1) ** (j - (a - r)) for r in range(max(0, a - j), min(i, a) + 1))
            co = Fraction(co * T[i] * T[j] * factorial(a) * factorial(w), factorial(i) * factorial(j))
            assert co.denominator % p != 0
            cm = co.numerator * pow(co.denominator, -1, q) % q
            acc = R.add(acc, R.smul(cm, cp[j]))
        tot += 1
        if acc != val: bad += 1
    print(f'  g2={g2} g3={g3} e={e} p={p}: {tot} entries, mismatches = {bad}')

print('\n== 4. perturbation control: T_20 += 1 (Z[i], e=1, p=7, w=0,2)')
p, K = 7, 120
R = Zp2(p, K); c = R.elt_of_norm(-1, 1)
T = th0_jets(4, 0, 1, 420)
G0 = jets_grid(T, R, c, [0, 2], 400)
T2 = list(T); T2[20] += 1
G1 = jets_grid(T2, R, c, [0, 2], 400)
ch = sum(1 for k in G0 if R.v(G0[k]) != R.v(G1[k]))
print(f'  valuations changed at {ch} of {len(G0)} (a,w) points;  e.g. a=400,w=0: {R.v(G0[(400,0)])} -> {R.v(G1[(400,0)])}')
