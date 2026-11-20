"""Validation of kronecker_lib against an independent brute-force computation.

(1) Brute force: sigma Taylor coefficients from Weierstrass's recursion (sigma_lib, a different algorithm from the
    wp recursion), Theta*z*w = sigma(z+w) / (stilde(z) stilde(w)) as a truncated two-variable Fraction series,
    total degree <= D.  Compare every C_{a,b} (a+b <= D-2) with the p-adic engine's N_{a,b} mod p^K.
(2) Symmetry G(z,w) = G(w,z):  Np[i][k] = Np[k][i] for i,k <= 14 (the engine only builds rows in i).
(3) b = 1 slice: C_{a,1} = [w^a](zeta(w) - 1/w) = -c_n/(2n-1), a = 2n-1.
(4) Perturbation control: changing one Phi_m makes (1)-(3) fail.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
from math import factorial, comb
from kronecker_lib import phi_numbers, rows_padic, wp_coeffs, to_mod, vpF
from sigma_lib import sigma_coeffs, derivs

D = 40
curves = {'Z[i] g2=4,g3=0': (4, 0), 'Z[w] g2=0,g3=4': (0, 4), 'C g2=-10,g3=7/2': (-10, Fraction(7, 2))}


def brute(g2, g3, D):
    a = sigma_coeffs(D + 2)
    h2, h3 = Fraction(g2) / 2, 2 * Fraction(g3)
    Dk = derivs(a, D + 2, h2, h3)
    s = [Fraction(x) / factorial(k) for k, x in enumerate(Dk)]      # sigma = sum s_k u^k
    st = s[1:]                                                       # stilde = sigma/u
    inv = [Fraction(0)] * (D + 1); inv[0] = 1 / st[0]
    for n in range(1, D + 1):
        inv[n] = -sum(st[j] * inv[n - j] for j in range(1, n + 1)) / st[0]
    # sigma(z+w) coefficient of z^i w^k = s_{i+k} C(i+k,i)
    Sz = {(i, k): s[i + k] * comb(i + k, i) for i in range(D + 2) for k in range(D + 2) if i + k <= D + 1}
    # multiply by inv(z) inv(w)
    T = {}
    for (i, k), x in Sz.items():
        if x == 0: continue
        for j in range(0, D + 2 - i - k):
            if inv[j] == 0: continue
            for l in range(0, D + 2 - i - k - j):
                if inv[l] == 0: continue
                key = (i + j, k + l)
                T[key] = T.get(key, 0) + x * inv[j] * inv[l]
    # z w Theta = T ; C_{a,b} = coeff of z^{b-1} w^a in Theta = T[(b, a+1)]
    return T


def run(perturb=None):
    ok_all = True
    for name, (g2, g3) in curves.items():
        T = brute(g2, g3, D)
        Phi = phi_numbers(g2, g3, D + 22)
        if perturb: Phi[perturb] += 1
        for p in (5, 7, 13):
            K = 60
            rows, h = rows_padic(Phi, p, K, [D + 2] * 16)
            q = p ** K
            bad = 0; n = 0
            for b in range(1, 15):
                for a in range(0, D - b):
                    C = T.get((b, a + 1), Fraction(0))
                    N = factorial(a) * factorial(b - 1) * C
                    X = (a + 1) * rows[b][a] + b * p ** h * rows[b - 1][a + 1]   # = p^{hb} (a+1) b N
                    exp_ = to_mod(N * (a + 1) * b * Fraction(p) ** (h * b), p, K)
                    n += 1
                    if X % q != exp_: bad += 1
            # symmetry
            sym = sum(1 for i in range(15) for k in range(15)
                      if (rows[i][k] * p ** (h * k) - rows[k][i] * p ** (h * i)) % q != 0)
            print(f'{name:18s} p={p:2d} h={h}: brute-force mismatches {bad}/{n}; symmetry mismatches {sym}/225')
            ok_all &= (bad == 0 and sym == 0)
        c = wp_coeffs(g2, g3, D)
        b1 = sum(1 for n_ in range(2, D // 2) if T.get((1, 2 * n_), 0) != -c[n_] / (2 * n_ - 1))
        b1 += sum(1 for a in range(0, D - 2, 2) if T.get((1, a + 1), 0) != 0)
        print(f'{name:18s} b=1 slice vs zeta(w)-1/w from wp recursion: mismatches {b1}')
        ok_all &= b1 == 0
    return ok_all


if __name__ == '__main__':
    print('== unperturbed'); print('ALL OK' if run() else 'FAILURES')
    print('\n== perturbation control: Phi_12 += 1 in the engine only')
    print('ALL OK (control FAILED to detect)' if run(perturb=12) else 'failures detected, as they must be')
