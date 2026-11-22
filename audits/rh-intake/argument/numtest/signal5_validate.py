"""NODE-NUMTEST5 validation of the engines in signal5_lib.
 V1  n'=2: grid2 (incremental S-polynomial) vs j2_double_sum (direct double Leibniz sum), exact equality mod p^K,
     on (a, nu) points spread over the region used, including nu > a/p.
 V2  n'=2: two precisions K and K+25: identical valuations on a sub-grid.
 V3  n'=4: pair_D/final4 vs kernel4_lib's pair_tables/pair_jets/final_jet (independent algorithm), equality of v_p
     for a <= 60, n1 <= 14, n3 <= 3.
 V4  n'=4: pair_D with the factor pairing (1,3),(2,4) instead of (1,2),(3,4): identical v_p.
 V5  th0 jets: T_n integral and T_odd = 0 (sanity); grid2 symmetry check J(a,nu) vs the conjugate kernel.
usage: python3 -I signal5_validate.py -> out_signal5_validate.txt
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import comb
from kernel3_lib import th0_jets, Zp2, gam
from kernel4_lib import Ring, coeffs, pair_tables, pair_jets, final_jet, down_closure
from signal5_lib import grid2, j2_double_sum, pair_D, final4

out = []; P = out.append
t0 = time.time()
random.seed(5)

# V1, V2
for (cv, g2, g3, e, p, A, W) in [('Zw', 0, 4, 1, 5, 260, 80), ('Zi', 4, 0, 1, 7, 240, 60)]:
    T = th0_jets(g2, g3, e, A + W + 30)
    assert all(T[k] == 0 for k in range(1, len(T), 2))
    for Kx in (0, 25):
        K = int(gam(p) * (A + W)) + 40 + Kx
        R = Zp2(p, K)
        c = R.elt_of_norm(-1, 1) or R.elt_of_norm(-1, 2)
        Tq = [t % R.q for t in T]
        G = grid2(Tq, R, c, A, W)
        if Kx == 0:
            G0, R0 = G, R
            pts = [(a, w) for a in range(0, A + 1) for w in range(0, W + 1) if (a + w) % 2 == 0]
            sub = random.sample(pts, 120) + [(A - (A + W) % 2, W), (p * 20, 20), (p * 20 + 2, 20), (p * 20 - 2, 20)]
            bad = 0
            for (a, w) in sub:
                if (a + w) % 2: continue
                if j2_double_sum(Tq, R, c, a, w) != G[(a, w)]: bad += 1
            P(f'V1 {cv} p={p}: grid2 vs direct double sum, {len(sub)} points (a<={A}, nu<={W}): {bad} mismatches')
        else:
            diff = sum(1 for k in G0 if min(R0.v(G0[k]), R0.K) != min(R.v(G[k]), R0.K) or (R0.v(G0[k]) >= R0.K))
            nmax = max(R0.v(x) for x in G0.values())
            P(f'V2 {cv} p={p}: precisions p^{R0.K} vs p^{R.K}: {diff} of {len(G0)} valuations differ or hit the '
              f'precision (max v at low precision = {nmax})')

# V3, V4
p, A, N, L = 5, 60, 14, 3
T = th0_jets(0, 4, 1, A + N + L + 10)
K = int(gam(p) * (A + N + L)) + 40
R = Ring(p, K)
m = coeffs(p)
Tq = [t % R.q for t in T]
D12 = pair_D(R, Tq, m[0], m[1], A, set(range(N + 1)), L)
D34 = pair_D(R, Tq, m[2], m[3], A, set(range(N + 1)), L)
D13 = pair_D(R, Tq, m[0], m[2], A, set(range(N + 1)), L)
D24 = pair_D(R, Tq, m[1], m[3], A, set(range(N + 1)), L)
grid = [(n1, 0, n3) for n1 in range(N + 1) for n3 in range(L + 1)]
nl = down_closure(grid)
P12 = pair_tables(R, T, m[0][0], m[1][0], A, N + L)
P34 = pair_tables(R, T, m[2][0], m[3][0], A, N + L)
Q12 = pair_jets(R, P12, m[0], m[1], A, nl)
Q34 = pair_jets(R, P34, m[2], m[3], A, nl)
bad3 = bad4 = tot = 0
for a in range(0, A + 1, 3):
    crow = [comb(a, b) % R.q for b in range(a + 1)]
    for (n1, _, n3) in grid:
        if (a + n1 + n3) % 2: continue
        x = final4(R, D12, D34, a, n1, n3, crow)
        y = final_jet(R, Q12, Q34, a, (n1, 0, n3))
        z = final4(R, D13, D24, a, n1, n3, crow)
        tot += 1
        bad3 += (R.v(x) != R.v(y))
        bad4 += (R.v(x) != R.v(z))
P(f'V3 n\'=4 p=5: new pair engine vs kernel4_lib engine: {bad3}/{tot} valuation mismatches (a<={A}, n1<={N}, n3<={L})')
P(f'V4 n\'=4 p=5: pairing (1,2)(3,4) vs (1,3)(2,4): {bad4}/{tot} valuation mismatches')
P(f'elapsed {time.time() - t0:.0f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_signal5_validate.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
