"""NODE-NUMTEST4 main runs: v_p of J(a; n1, n2, n3) = d_{z0}^a d_{z1}^{n1} d_{z2}^{n2} d_{z3}^{n3} Theta(0) for the n'=4 instance
(kernel4_lib docstring), one (curve, p) per invocation.

usage: python3 -I kernel4_run.py CURVE P AMAX TAG      CURVE in {Zw, Zi}   -> out_kernel4_run_TAG.txt
Columns:  v            = v_p(J)   (in Z_p[eta]; = Z_{p^4} for p inert in F; min over places otherwise)
          LT           = v_p(a!) + sum_s v_p(n_s!) - (a+|n|-1)/(p^2-1)          (Gaussian-free law)
          G            = gam_p (a + |n|)
          L_lean       = sum_{e odd} min(a/p^e, n_{e mod 4})  (the Lean's charge; positions 1,3 at odd distance, 2 never)
          L_shared     = min(a/p, n1 + n3)                     (one shared budget for both odd positions)
"""
import sys, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kernel3_lib import th0_jets
from kernel4_lib import (coeffs, positions, Ring, pair_tables, pair_jets, final_jet, down_closure, vp_fact, gam,
                         lean4_loss)

CURVES = {'Zw': (0, 4, 1), 'Zi': (4, 0, 1)}
cv, p, AMAX, TAG = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
WMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 12
g2, g3, e = CURVES[cv]
g = gam(p)
t0 = time.time()

axis1 = [(i, 0, 0) for i in range(WMAX + 1)]
axis3 = [(0, 0, j) for j in range(WMAX + 1)]
axis2 = [(0, l, 0) for l in range(0, min(WMAX, 8) + 1)]
mixed = [(i, 0, j) for i in (2, 4, 8) for j in (2, 4, 8)] + [(2, 2, 2), (4, 4, 4), (3, 0, 9), (9, 0, 3)]
mixed = [n for n in mixed if sum(n) <= WMAX]
grid = list(dict.fromkeys(axis1 + axis3 + axis2 + mixed))
nlist = down_closure(grid)
asamp = sorted(set(list(range(AMAX // 2, AMAX + 1, AMAX // 10)) + [AMAX]))

T = th0_jets(g2, g3, e, AMAX + WMAX + 4)
K = int(g * (AMAX + WMAX)) + max(40, int(0.12 * AMAX))
if g * AMAX < 15: K = int(AMAX / (p * p - 1)) + 40 + WMAX   # non-served controls: valuations are small
R = Ring(p, K)
m = coeffs(p)
taus, lab = positions(p)
P12 = pair_tables(R, T, m[0][0], m[1][0], AMAX, WMAX)
P34 = pair_tables(R, T, m[2][0], m[3][0], AMAX, WMAX)
t1 = time.time()
Q12 = pair_jets(R, P12, m[0], m[1], AMAX, nlist)
Q34 = pair_jets(R, P34, m[2], m[3], AMAX, nlist)
t2 = time.time()
V = {}
for n in grid:
    for a0 in asamp:
        a = a0 if (a0 + sum(n)) % 2 == 0 else a0 + 1
        if a > AMAX: a -= 2
        V[(a, n)] = R.v(final_jet(R, Q12, Q34, a, n))
t3 = time.time()

out = []
P = out.append
P(f'NODE-NUMTEST4 run {TAG}: curve {cv} (g2={g2},g3={g3},e_t={e}), p={p}, p mod 16={p % 16}, taus(k mod 16)={taus}; {lab}')
P(f'  gamma_p={g:.4f}  1/(p^2-1)={1 / (p * p - 1):.4f}  precision p^{K}  AMAX={AMAX}  WMAX={WMAX}')
P(f'  time: pair tables {t1 - t0:.0f}s, pair jets {t2 - t1:.0f}s, final {t3 - t2:.0f}s')
P('  (v = K means the jet is 0 mod p^K; jets with a+|n| odd vanish identically and are never sampled)')


def lt(a, n): return vp_fact(a, p) + sum(vp_fact(x, p) for x in n) - (a + sum(n) - 1) / (p * p - 1)


def row(n):
    pts = sorted((a, v) for (a, nn), v in V.items() if nn == n)
    return pts


def lsq(xs, ys):
    k = len(xs); mx = sum(xs) / k; my = sum(ys) / k
    sxx = sum((x - mx) ** 2 for x in xs); sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    return sxy / sxx


P('\n  slope dv/da at fixed n over the sampled a in [AMAX/2, AMAX]:')
for n in [(0, 0, 0), (4, 0, 0), (0, 0, 4), (8, 0, 0), (0, 0, 8), (0, 4, 0), (4, 0, 4)]:
    if n in grid:
        pts = [(a, v) for a, v in row(n) if v < K]
        P(f'    n={n}: {lsq([a for a, _ in pts], [v for _, v in pts]):.4f}')

P('\n  v - LT at n = 0 (Gaussian-free law, w = 0):  ' + '  '.join(f'a={a}:{v - lt(a, (0, 0, 0)):+.2f}' for a, v in row((0, 0, 0))))

for name, axis in [('n1 (position 1, e=1 partner)', axis1), ('n3 (position 3, e=3 partner)', axis3), ('n2 (position 2, even distance)', axis2)]:
    P(f'\n  AXIS {name}:  entries  v / [v - v(n=0 at nearest a)] / L_lean / L_shared ;  rows a, columns weight')
    ws = [n for n in axis]
    P('    a\\w  ' + ''.join(f'{sum(n):>24d}' for n in ws))
    for a0 in asamp:
        line = f'  {a0:5d} '
        for n in ws:
            a = [aa for (aa, nn) in V if nn == n and abs(aa - a0) <= 1][0]
            a_ref = [aa for (aa, nn) in V if nn == (0, 0, 0) and abs(aa - a0) <= 1][0]
            v = V[(a, n)]; dv = v - V[(a_ref, (0, 0, 0))]
            line += f'{v:>7d}/{dv:+4d}/{lean4_loss(a, n, p):5.2f}/{min(a / p, n[0] + n[2]):5.1f}'
        P(line)

P('\n  DECISIVE: drop D(n) = [G(a,n) - v(a,n)] - [G(a,0) - v(a,0)]  (loss relative to the gamma-law, n=0 removed),')
P('            against L_lean and L_shared.  If a weight costs nothing beyond gamma, D = 0; if each unit costs 1, D = |n|.')
for n in grid:
    if n == (0, 0, 0): continue
    ds = []
    for a, v in row(n):
        a_ref = [aa for (aa, nn) in V if nn == (0, 0, 0) and abs(aa - a) <= 1][0]
        D = (g * (a + sum(n)) - v) - (g * a_ref - V[(a_ref, (0, 0, 0))])
        ds.append((a, D, lean4_loss(a, n, p), min(a / p, n[0] + n[2])))
    P(f'    n={str(n):12s} ' + ' '.join(f'a={a}:D={D:5.2f}|Ll={Ll:4.2f}|Ls={Ls:4.1f}' for a, D, Ll, Ls in ds[::2]))

viol = [(a, n, v, g * a - lean4_loss(a, n, p)) for (a, n), v in V.items() if v < g * a - lean4_loss(a, n, p) - 3]
P(f'\n  points with v < gam*a - L_lean - 3 : {len(viol)} / {len(V)}   ' + str(viol[:8]))
mins = min(v - (g * a - lean4_loss(a, n, p)) for (a, n), v in V.items())
P(f'  min over grid of v - (gam*a - L_lean) = {mins:.2f};   min of v - (sum_e (a/p^e - cap)_+) is the same up to the e-truncation')
viols = [(a, n, v) for (a, n), v in V.items() if v < g * (a + sum(n)) - min(a / p, n[0] + n[2]) - 3]
P(f'  points with v < gam*(a+|n|) - L_shared - 3 : {len(viols)}')
fn = os.path.join(os.path.dirname(os.path.abspath(__file__)), f'out_kernel4_run_{TAG}.txt')
open(fn, 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
print(f'total {time.time() - t0:.0f}s')
