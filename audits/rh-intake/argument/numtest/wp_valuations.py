"""Follow-up to NODE-NUMTEST: the same experiment for the Weierstrass p-function, which
(unlike sigma) is integral in the formal-group parameter.  wp(z) = z^-2 + sum_{n>=2} c_n z^(2n-2),
c_2 = g2/20, c_3 = g3/28, c_n = 3/((2n+1)(n-3)) * sum_{m=2}^{n-2} c_m c_{n-m}.
Tests v_p( (2n-2)! * c_n ) against gamma_p*(2n-2), gamma_p = p/(p^2-1), at inert and split p."""
import sys
from fractions import Fraction
from math import factorial
def coeffs(g2, g3, N):
    c = [Fraction(0)] * (N + 1)
    c[2], c[3] = Fraction(g2, 20), Fraction(g3, 28)
    for n in range(4, N + 1):
        c[n] = Fraction(3, (2*n + 1) * (n - 3)) * sum(c[m] * c[n - m] for m in range(2, n - 1))
    return c
def vp(x, p):
    if x == 0: return None
    v, a, b = 0, x.numerator, x.denominator
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v
def check_ode(c, g2, g3, order=14):          # wp'^2 = 4 wp^3 - g2 wp - g3 as Laurent series, low order
    from collections import defaultdict
    P = defaultdict(Fraction); P[-2] = Fraction(1)
    for n in range(2, order): P[2*n - 2] = c[n]
    D = defaultdict(Fraction)
    for k, v in P.items(): D[k - 1] += k * v
    def mul(A, B, cut=12):               # keep enough intermediate terms; only degrees <= 4 are compared
        R = defaultdict(Fraction)
        for i, a in A.items():
            for j, b in B.items():
                if i + j <= cut: R[i + j] += a * b
        return R
    L = mul(D, D); P3 = mul(mul(P, P), P)
    return all(L[k] - 4*P3[k] + g2*P[k] + (g3 if k == 0 else 0) == 0 for k in range(-6, 5))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 900
for name, g2, g3, inert in [('Z[i]  g2=4,g3=0', 4, 0, lambda p: p % 4 == 3), ('Z[w]  g2=0,g3=4', 0, 4, lambda p: p % 3 == 2),
                            ('non-CM g2=4,g3=4', 4, 4, None)]:
    c = coeffs(g2, g3, N)
    print(f'\n== {name}   ODE check: {check_ode(c, g2, g3)}')
    print(' p   type    slope v/a (last)   gamma_p   1/(p^2-1)   min_a[v - gamma_p*a]   min_a[v]')
    for p in [5, 7, 11, 13, 17, 19, 23]:
        rows = [(2*n - 2, vp(factorial(2*n - 2) * c[n], p)) for n in range(4, N + 1) if c[n] != 0]
        a, v = rows[-1]
        g = p / (p*p - 1)
        typ = '?' if inert is None else ('inert' if inert(p) else 'split')
        print(f'{p:3d}  {typ:6s}  {v/a:10.4f}        {g:8.4f}  {1/(p*p-1):8.4f}   {min(v - g*a for a, v in rows):10.1f}        {min(v for a, v in rows)}')
