"""NODE-NUMTEST3: shape of the law in the conjugate (odd-position) order w, served configurations only.
Compares v = v_p(J(a,w)) with
  LEAN(a,w) = sum_{e odd}(a/p^e - w)_+            (the Lean's capped gain, cap = w)
  EMP(a,w)  = max(gamma(a+w) - w, (a+w)/(p^2-1)) (NUMTEST2's empirical Kronecker law)
and fits v = alpha a + beta w + c on the region w <= a/(2p), a >= 100.
usage: python3 -I kernel3_shape.py [amax]  -> out_kernel3_shape.txt
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kernel3_lib import th0_jets, Zp2, jets_grid, gam, lean_pred

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 800
WS = list(range(0, 13)) + [16, 20, 25, 30, 40]
t0 = time.time()
out = []; P = out.append
P(f'shape in w, served configurations (N(c) = -1), a <= {AMAX}, w in {WS}')
P(' curve  p   min(v-LEAN)  #(v<LEAN)  [min,max](v-EMP)  mean(v-EMP)   alpha   gamma   beta   gamma-1   (fit region w<=a/2p, a>=100)')
for (cv, g2, g3, e, p) in [('Zi', 4, 0, 1, 7), ('Zi', 4, 0, 1, 11), ('Zi', 4, 0, 1, 19), ('Zw', 0, 4, 1, 5), ('Zw', 0, 4, 1, 11), ('Zw', 0, 4, 1, 17)]:
    T = th0_jets(g2, g3, e, AMAX + max(WS) + 2)
    g = gam(p); K = int(g * (AMAX + max(WS))) + 60
    R = Zp2(p, K); c = R.elt_of_norm(-1, 1) or R.elt_of_norm(-1, 2)
    G = jets_grid(T, R, c, WS, AMAX)
    pts = [(a, w, R.v(x)) for (a, w), x in G.items() if (a + w) % 2 == 0 and a + w > 0 and x != (0, 0)]
    dl = [v - lean_pred(a, w, p) for a, w, v in pts]
    de = [v - max(g * (a + w) - w, (a + w) / (p * p - 1)) for a, w, v in pts if a >= 50]
    fit = [(a, w, v) for a, w, v in pts if a >= 100 and w <= a / (2 * p)]
    # least squares for v = al*a + be*w + c
    n = len(fit); Sa = sum(a for a, _, _ in fit); Sw = sum(w for _, w, _ in fit); Sv = sum(v for _, _, v in fit)
    Saa = sum(a * a for a, _, _ in fit); Sww = sum(w * w for _, w, _ in fit); Saw = sum(a * w for a, w, _ in fit)
    Sav = sum(a * v for a, _, v in fit); Swv = sum(w * v for _, w, v in fit)
    import itertools
    Mx = [[Saa, Saw, Sa], [Saw, Sww, Sw], [Sa, Sw, n]]; bb = [Sav, Swv, Sv]
    # solve 3x3
    def det3(m): return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1]) - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0]) + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
    D0 = det3(Mx); sol = []
    for i in range(3):
        Mi = [row[:] for row in Mx]
        for r in range(3): Mi[r][i] = bb[r]
        sol.append(det3(Mi) / D0)
    P(f' {cv:4s} {p:3d}   {min(dl):9.2f}  {sum(1 for x in dl if x < 0):6d}/{len(dl):<6d} [{min(de):6.2f},{max(de):6.2f}]  {sum(de)/len(de):8.2f}    {sol[0]:.4f}  {g:.4f}  {sol[1]:.4f}  {g-1:.4f}')
P(f'elapsed {time.time() - t0:.1f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kernel3_shape.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
