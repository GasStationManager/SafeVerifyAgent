"""NODE-NUMTEST3, both sides for the same numbers: one global instance.

Host E = Q(i, beta), beta^2 = -13; K = Q(i), F = Q(sqrt 13), Tau = Gal(E/K) = {1, g}.
AA0 = O_K a_1 + O_K a_2,  a_1 = (1+i)/2,  a_2 = gamma*beta,  gamma = (1+5i)/26:  tr_{E/K}(a_k abar_l) = delta_kl.
M = (tau(a_k)) is unitary; u = M^* z gives   Theta(z0,z1) = th0(abar_1 (z0+z1)) * th0(-gammabar beta (z0-z1)).
Served primes (Frob_p = c*g): p = 3 mod 4 and (13/p) = -1  [p = 7, 11, 19, 31, ...].
Non-served inert (Frob_p = c): p = 3 mod 4, (13/p) = +1  [p = 23, 43, ...].  Split in K: p = 1 mod 4.

J(a,w) = d_{z0}^a d_{z1}^w Theta(0) = A^n * Jt,  A = abar_1,  Jt = sum_k S(a,w,k) T_k T_{n-k} (c^2)^{(n-k)/2},
c = C/A = -(3-2i) beta/13,  c^2 = (2+3i)/(2-3i) in K.   So J in K, and
  Jstar := 13^{n/2} Jt = sum_k S_k T_k T_{n-k} (2+3i)^{n-k} 13^{k/2}  is a Gaussian integer (exact).
Archimedean: log|J| = log|Jstar| - (n/2) log 13 - (n/2) log 2.   Fock-type bound (NODE-HEIGHT):
  log|J|^2  <=  log(a! w!) + n log(pi/Area) + O(log n)     (H = |z|^2/Area, M unitary).
Product formula: log N_{K/Q}(Jstar) = sum_p v_p(N Jstar) log p, split by prime type.
usage: python3 -I kernel3_global.py [amax]   -> out_kernel3_global.txt
"""
import sys, os, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import comb, lgamma, log
from kernel3_lib import th0_jets, vp_fact, gam, lt_pred
from sigma_lib import vp, primes_upto

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400
WS = [0, 1, 2, 3]
t0 = time.time()
T = th0_jets(4, 0, 1, AMAX + 10)

def gmul(x, y): return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])

NMAX = AMAX + max(WS) + 1
pw = [(1, 0)]
for k in range(NMAX + 1): pw.append(gmul(pw[-1], (2, 3)))
p13 = [13 ** (k // 2) for k in range(NMAX + 1)]

def Jstar(a, w):
    n = a + w
    # S(a,w,k) = [x^k y^{n-k}] (x+y)^a (x-y)^w
    S = [0] * (n + 1)
    for j in range(w + 1):
        cj = comb(w, j) * (-1) ** (w - j)          # (x-y)^w term x^j y^{w-j}
        for i in range(a + 1):
            S[i + j] += comb(a, i) * cj
    re = im = 0
    for k in range(0, n + 1, 2):
        if S[k] == 0 or T[k] == 0 or T[n - k] == 0: continue
        f = S[k] * T[k] * T[n - k] * p13[k]
        z = pw[n - k]
        re += f * z[0]; im += f * z[1]
    return (re, im)

def area_Zi():
    a, b = math.sqrt(2), 1.0
    for _ in range(60): a, b = (a + b) / 2, math.sqrt(a * b)
    return (math.pi / a) ** 2

AREA = area_Zi()
PR = primes_upto(NMAX + 50)
def ptype(p):
    if p == 2: return 'two'
    if p == 13: return 'ram13'
    if p % 4 == 1: return 'split'
    return 'served' if pow(13, (p - 1) // 2, p) == p - 1 else 'aniso'

out = []; P = out.append
P(f'NODE-NUMTEST3 global instance E = Q(i, sqrt-13), Z[i] curve (g2=4, g3=0), e_t = 1, Area = {AREA:.6f}')
P('served p: ' + ' '.join(str(p) for p in PR if ptype(p) == 'served' and p < 120) + ' ...;  aniso inert p: '
  + ' '.join(str(p) for p in PR if ptype(p) == 'aniso' and p < 120) + ' ...')
P('\n(1) archimedean: Fock gap  D := [log(a!w!) + n log(pi/Area)] - log|J|^2   (bound requires D >= -O(log n))')
P('    and p-adic valuations at served p (v_p(J) = v_p(Jstar), p != 13) vs LT = v_p(a!)+v_p(w!)-(n-1)/(p^2-1)')
P('   a   w   log|J|^2   Fock     D      D/n  | v7/LT7      v11/LT11    v19/LT19    | v23 (aniso) | v5 v13(split)')
rows = []
for a in list(range(20, AMAX + 1, 20)):
    for w in WS:
        aa = a if (a + w) % 2 == 0 else a + 1
        if aa > AMAX + 1: continue
        n = aa + w
        J = Jstar(aa, w)
        N = J[0] * J[0] + J[1] * J[1]
        logJ2 = log(N) - n * log(13) - n * log(2)
        fock = lgamma(aa + 1) + lgamma(w + 1) + n * log(math.pi / AREA)
        D = fock - logJ2
        vs = {p: vp(N, p) // 2 for p in (7, 11, 19, 23)}   # inert in K: v(N) = 2 v(J)
        v5, v13 = vp(N, 5), vp(N, 13)
        rows.append((aa, w, N))
        if w in (0, 2) and aa % 100 == 0 or (aa % 100 == 0 and w == 1):
            P(f' {aa:4d} {w:3d} {logJ2:10.1f} {fock:9.1f} {D:7.1f} {D/n:6.3f} |'
              f' {vs[7]:4d}/{lt_pred(aa, w, 7):6.1f} {vs[11]:4d}/{lt_pred(aa, w, 11):6.1f} {vs[19]:4d}/{lt_pred(aa, w, 19):6.1f} |'
              f' {vs[23]:4d} ({(n)/(23*23-1):4.1f}) | {v5:3d} {v13:3d}')
# worst Fock gap
Dmin = min(lgamma(a + 1) + lgamma(w + 1) + (a + w) * log(math.pi / AREA) - (log(N) - (a + w) * (log(13) + log(2))) for a, w, N in rows)
P(f'  min over all computed (a,w) of D: {Dmin:.2f}')
P('\n(2) product formula for Jstar in Z[i]:  log N(Jstar) = sum_p v_p(N) log p   (natural logs)')
P('    columns: log N | served p: actual, LT-law prediction 2*sum LT_p log p | aniso inert | split | 2 | 13 | cofactor (p > n+50)')
for (a, w, N) in rows:
    if w != 0 or a % 100 != 0: continue
    n = a + w
    tot = log(N); parts = {'served': 0.0, 'aniso': 0.0, 'split': 0.0, 'two': 0.0, 'ram13': 0.0}
    pred = 0.0; M = N
    for p in PR:
        v = vp(M, p)
        if v:
            parts[ptype(p)] += v * log(p); M //= p ** v
        if ptype(p) == 'served' and p <= n:
            pred += 2 * max(0.0, lt_pred(a, w, p)) * log(p)
    cof = log(M) if M > 1 else 0.0
    P(f'  a={a:4d}: logN={tot:9.1f} | served {parts["served"]:8.1f} (pred {pred:8.1f}) | aniso {parts["aniso"]:6.1f} |'
      f' split {parts["split"]:6.1f} | two {parts["two"]:6.1f} | 13: {parts["ram13"]:7.1f} | cofactor {cof:9.1f}'
      f' | served share {parts["served"]/tot:.3f}; (1/4)a log a / (a log a) ref')
P(f'\nelapsed {time.time() - t0:.1f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kernel3_global.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
