"""Normalisation check for NODE-NORMS (auditors' own script; uses only sigma_lib.py from this folder).

Question: is ph(a) - a*logOmega, with the Lean's logOmega = gamma + log(2 pi/sqrt d) - L'/L(1, chi_{-d})
(lattice normalised to g2^3 - 27 g3^2 = 1, Omega = area/pi), the right archimedean size of
|D^a sigma(0)|^2 for a CM curve?  Prediction (Cauchy/Fock, sharp up to O(log a)):
    2 log|D^a sigma_L(0)| = log a! - a*log(area(L)/pi) + O(log a),
and area(L) = area(L_1) * |Delta(L)|^(-1/6) where L_1 is the Delta = 1 rescaling.
Curves: A: g2 = 4, g3 = 0 (CM Z[i], d = 4, tau = i); B: g2 = 0, g3 = 4 (CM Z[w], d = 3, tau = w).
For these, s2 = 0 by symmetry, so sigma = sigma* (the reduced sigma whose growth is exp(pi|z|^2/(2 area))).
Usage: python3 -I normcheck_cs.py [N]
"""
import sys, os, math, cmath
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sigma_lib import sigma_derivs_stream

N = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
GAMMA = 0.5772156649015329

def eta(tau, terms=200):
    q = cmath.exp(2j * math.pi * tau)
    p = 1
    for n in range(1, terms):
        p *= (1 - q ** n)
    return cmath.exp(2j * math.pi * tau / 24) * p

def area_from(tau, Delta):
    # Delta(L) = (2 pi/w1)^12 eta(tau)^24, area = |w1|^2 Im tau  =>  area = (2pi)^2 |eta|^4 Im tau / |Delta|^(1/6)
    return (2 * math.pi) ** 2 * abs(eta(tau)) ** 4 * tau.imag / abs(Delta) ** (1 / 6)

def chi(d, n):
    if d == 4:
        return 0 if n % 2 == 0 else (1 if n % 4 == 1 else -1)
    if d == 3:
        r = n % 3
        return 0 if r == 0 else (1 if r == 1 else -1)
    raise ValueError

def L_and_Lprime(d, K=400000):
    # L(1,chi) = sum chi(n)/n, L'(1,chi) = -sum chi(n) log n / n, summed in full periods of length d (+ tail estimate)
    L = Lp = 0.0
    for k in range(K):
        for r in range(1, d + 1):
            n = k * d + r
            c = chi(d, n)
            if c:
                L += c / n
                Lp -= c * math.log(n) / n
    # tail: sum_{k>=K} sum_r chi(r) g(kd + r) ~ sum_r chi(r) r * sum_k g'(kd), g = 1/x resp. log x / x
    m1 = sum(chi(d, r) * r for r in range(1, d + 1))
    X = K * d
    L += m1 * (-1 / X) / d                   # int_X^inf -1/x^2 dx / d
    Lp -= m1 * (-math.log(X) / X) / d  # int_X^inf (1 - log x)/x^2 dx = -(log X)/X
    return L, Lp

CURVES = {
    'A (d=4, Z[i])': dict(h=(2, 0), g=(4, 0), tau=1j, d=4),
    'B (d=3, Z[w])': dict(h=(0, 8), g=(0, 4), tau=complex(-0.5, math.sqrt(3) / 2), d=3),
}
D = sigma_derivs_stream(N, {k: v['h'] for k, v in CURVES.items()})
for name, c in CURVES.items():
    g2, g3 = c['g']
    Delta = g2 ** 3 - 27 * g3 ** 2
    d = c['d']
    A = area_from(c['tau'], Delta)
    A1 = area_from(c['tau'], 1)
    L, Lp = L_and_Lprime(d)
    logOm_lean = GAMMA + math.log(2 * math.pi / math.sqrt(d)) - Lp / L
    print(f"\n## curve {name}: g2={g2}, g3={g3}, Delta=g2^3-27g3^2={Delta}")
    print(f"   area(L) = {A:.12f};  area(L_1), Delta=1 rescaling = {A1:.12f}")
    print(f"   L(1,chi) = {L:.10f} (2 pi h/(w sqrt d) = {2 * math.pi / ((4 if d == 4 else 6) * math.sqrt(d)):.10f});  L'/L(1,chi) = {Lp / L:.8f}")
    if d == 4:
        ref = GAMMA + 2 * math.log(2) + 3 * math.log(math.pi) - 4 * math.lgamma(0.25)
        print(f"   closed form L'/L(1,chi_-4) = gamma + 2log2 + 3log pi - 4 log Gamma(1/4) = {ref:.8f}")
    print(f"   Lean logOmega = gamma + log(2pi/sqrt d) - L'/L   = {logOm_lean:.8f}")
    print(f"   log(area(L_1)/pi)                              = {math.log(A1 / math.pi):.8f}   (Chowla-Selberg: should agree)")
    print(f"   predicted slope -(1/2)log(area(L)/pi)          = {-0.5 * math.log(A / math.pi):.6f}")
    print("      a | 2log|D^a| | log a! - a*log(area/pi) | remainder R(a) | R(a)/log a | (2log|D^a| - log a!)/a | -log(area/pi)")
    nz = [k for k in range(1, N + 1) if D[name][k]]
    for a in [nz[int(len(nz) * f)] for f in (0.05, 0.1, 0.25, 0.5, 0.75)] + [nz[-1]]:
        two = 2 * math.log(abs(D[name][a]))
        main = math.lgamma(a + 1) - a * math.log(A / math.pi)
        R = two - main
        print(f"   {a:5d} | {two:10.2f} | {main:10.2f} | {R:9.3f} | {R / math.log(a):7.3f} | "
              f"{(two - math.lgamma(a + 1)) / a:.6f} | {-math.log(A / math.pi):.6f}")
    # in the Lean's normalisation: log(area(L)/pi) = logOmega_Lean - (1/6)log|Delta|
    a = nz[-1]
    two = 2 * math.log(abs(D[name][a]))
    ph = a * math.log(a) - a
    print(f"   at a={a}: 2log|D^a| - [ph(a) - a*logOm_Lean + (a/6)log|Delta|] = "
          f"{two - (ph - a * logOm_lean + a / 6 * math.log(abs(Delta))):.3f}  (log a = {math.log(a):.2f})")
    # control: a wrong constant c per unit weight (e.g. Omega -> 2 Omega, i.e. area/(2pi) normalisation)
    print(f"   control: same with logOm + log 2 (area/(2 pi) convention): "
          f"{two - (ph - a * (logOm_lean + math.log(2)) + a / 6 * math.log(abs(Delta))):.1f}")
