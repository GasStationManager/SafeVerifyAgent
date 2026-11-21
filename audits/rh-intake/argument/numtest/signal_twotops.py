"""Signal-place check: n'=4 orbit with TWO tops at even positions 0 and 2 (the configuration only signal places have:
all tops at even positions of the z-orbit, odd positions = thick/thin places at the conjugate place w-bar).
J(a; n1, n2, n3), top weights a (pos 0) and n2 (pos 2), caps n1 (pos 1), n3 (pos 3)."""
import sys, time
sys.path.insert(0, sys.argv[1])
from kernel3_lib import th0_jets
from kernel4_lib import coeffs, Ring, pair_tables, pair_jets, final_jet, down_closure, gam
p = int(sys.argv[2]); AMAX = int(sys.argv[3])
g2, g3, e = (0, 4, 1)          # Z[omega]
g = gam(p)
grid = [(0, n2, 0) for n2 in (0, 8, 16, 24, 32)] + [(n1, n2, n3) for n2 in (16, 32) for (n1, n3) in ((4, 0), (0, 4), (8, 0), (0, 8), (4, 4))]
grid += [(n1, 0, n3) for (n1, n3) in ((4, 0), (0, 4), (8, 0), (0, 8))]
WMAX = max(sum(n) for n in grid)
nlist = down_closure(grid)
T = th0_jets(g2, g3, e, AMAX + WMAX + 4)
K = int(g * (AMAX + WMAX)) + 40
R = Ring(p, K); m = coeffs(p)
t0 = time.time()
P12 = pair_tables(R, T, m[0][0], m[1][0], AMAX, WMAX); P34 = pair_tables(R, T, m[2][0], m[3][0], AMAX, WMAX)
Q12 = pair_jets(R, P12, m[0], m[1], AMAX, nlist); Q34 = pair_jets(R, P34, m[2], m[3], AMAX, nlist)
def loss(A, caps):   # caps: dict odd distance mod 4 -> cap weight
    s, ee = 0.0, 1
    while p ** ee <= A:
        s += min(A / p ** ee, caps[ee % 4]); ee += 2
    return s
print(f'p={p} gamma={g:.4f} AMAX={AMAX} K={K} prep {time.time()-t0:.0f}s')
print('  a   (n1,n2,n3)     v     gam(a+n2)-L2    v-pred   [L2 = loss(top0) + loss(top2)]')
worst = 99
for a0 in (AMAX // 2, 3 * AMAX // 4, AMAX):
    for n in grid:
        a = a0 if (a0 + sum(n)) % 2 == 0 else a0 - 1
        v = R.v(final_jet(R, Q12, Q34, a, n))
        if v >= K: continue
        L2 = loss(a, {1: n[0], 3: n[2]}) + loss(n[1], {1: n[2], 3: n[0]})
        pred = g * (a + n[1]) - L2
        worst = min(worst, v - pred)
        print(f'{a:4d} {str(n):14s} {v:5d} {pred:10.2f} {v - pred:+8.2f}')
print(f'min v - pred = {worst:.2f}   total {time.time()-t0:.0f}s')
