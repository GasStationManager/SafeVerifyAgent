"""NODE-NUMTEST3 main grid: v_p of the Lean kernel's jet entries J(a,w) = d_{z0}^a d_{z1}^w Theta(0),
Theta = th0(z0+z1) th0(c(z0-z1)), in the smallest instance (see kernel3_lib docstring).

  config 'served'  : c c^sigma = -1  (Frob_p = c*g: the positions tau_0, tau_1 are a hyperbolic pair at p)
  config 'aniso'   : c c^sigma = +1  (Frob_p = c: p inert in K but split in F; tau_0 direction anisotropic)
  config 'split'   : p split in K (no supersingular reduction), c of norm -1 in the unramified Z_{p^2}

usage: python3 -I kernel3_run.py [amax]      -> out_kernel3_run.txt
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kernel3_lib import th0_jets, Zp2, jets_grid, vp_fact, gam, lean_pred, lt_pred, sigma_like

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
WS = [0, 1, 2, 3, 5, 8, 12, 16, 20, 30]
SAMPLE_A = [100, 200, 300, 500, 700, 1000]

cases = [  # (curve, g2, g3, e, p, type)
    ('Zi', 4, 0, 1, 7, 'inert'), ('Zi', 4, 0, 0, 7, 'inert'), ('Zi', 4, 0, 1, 11, 'inert'), ('Zi', 4, 0, 1, 19, 'inert'),
    ('Zw', 0, 4, 1, 5, 'inert'), ('Zw', 0, 4, 1, 11, 'inert'), ('Zw', 0, 4, 1, 17, 'inert'),
    ('Zi', 4, 0, 1, 5, 'split'), ('Zi', 4, 0, 1, 13, 'split'), ('Zw', 0, 4, 1, 7, 'split'), ('Zw', 0, 4, 1, 13, 'split'),
]

def lsq(xs, ys):
    n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs); sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    return sxy / sxx

t0 = time.time()
Tcache = {}
out = []
P = out.append
P(f'NODE-NUMTEST3 main grid, a <= {AMAX}, w in {WS}')
P('columns: v = v_p(J(a,w)) [valuation in Z_{p^2}];  LT = v_p(a!)+v_p(w!)-(a+w-1)/(p^2-1) [Gaussian-free law];')
P('         LEAN = sum_{e odd}(a/p^e - w)_+ [the Lean capped gain, cap = w];  SIG = (a+w)/(p^2-1) [single-variable sigma-type];')
P('         gam*a = p/(p^2-1)*a.')
summary = []
for (cv, g2, g3, e, p, typ) in cases:
    key = (g2, g3, e)
    if key not in Tcache:
        Tcache[key] = th0_jets(g2, g3, e, AMAX + max(WS) + 2)
    T = Tcache[key]
    g = gam(p)
    K = int(g * (AMAX + max(WS))) + 60
    R = Zp2(p, K)
    confs = []
    if typ == 'inert':
        for b in (1, 2, 3):
            cN = R.elt_of_norm(-1, b)
            if cN: confs.append((f'served(c=({cN[0] % 1000}..,{b}))', cN));
            if len(confs) == 2: break
        cA = R.elt_of_norm(1, 1) or R.elt_of_norm(1, 2)
        confs.append(('aniso (N(c)=+1)', cA))
    else:
        cN = R.elt_of_norm(-1, 1) or R.elt_of_norm(-1, 2)
        confs.append(('split-p, N(c)=-1', cN))
    for (cname, c) in confs:
        G = jets_grid(T, R, c, WS, AMAX)
        P(f'\n=== {cv} (g2={g2},g3={g3}) e_t={e}  p={p} [{typ}]  config {cname}   gamma_p={g:.4f}  1/(p^2-1)={1/(p*p-1):.4f}')
        # slopes at fixed w, over even-n points with a in (AMAX/2, AMAX]
        line = '  slope dv/da at fixed w (a in (AMAX/2,AMAX]): '
        slopes = {}
        for w in WS:
            pts = [(a, R.v(G[(a, w)])) for a in range(AMAX // 2, AMAX + 1) if (a + w) % 2 == 0 and G[(a, w)] != (0, 0)]
            pts = [(a, v) for a, v in pts if v < K]
            slopes[w] = lsq([x for x, _ in pts], [y for _, y in pts]) if len(pts) > 3 else float('nan')
            line += f'w={w}:{slopes[w]:.4f} '
        P(line)
        # global deviations
        nz = lambda a, w: G[(a, w)] != (0, 0)   # exact zeros (identities for special c, e.g. c = 1+sqrt2) excluded
        nzero = sum(1 for (a, w) in G if (a + w) % 2 == 0 and a + w > 0 and not nz(a, w))
        d_lt = min(R.v(G[(a, 0)]) - lt_pred(a, 0, p) for a in range(2, AMAX + 1, 2) if nz(a, 0))
        d_lt_max = max(R.v(G[(a, 0)]) - lt_pred(a, 0, p) for a in range(2, AMAX + 1, 2) if nz(a, 0))
        viol_lean = sum(1 for (a, w) in G if (a + w) % 2 == 0 and a + w > 0 and nz(a, w) and R.v(G[(a, w)]) < lean_pred(a, w, p) - 2)
        tot = sum(1 for (a, w) in G if (a + w) % 2 == 0 and a + w > 0 and nz(a, w))
        dev2 = [R.v(G[(a, w)]) - (lt_pred(a, w, p) - w) for (a, w) in G if (a + w) % 2 == 0 and a >= 50 and nz(a, w)]
        P(f'  w=0: min_a [v - LT] = {d_lt:.3f}, max = {d_lt_max:.3f}   (a even, 2..{AMAX})')
        P(f'  exact zeros: {nzero};  points with v < LEAN - 2: {viol_lean} / {tot};   v - (LT - w) over a>=50, all w: [{min(dev2):.2f}, {max(dev2):.2f}]')
        P('  grid  v / LT / LEAN / SIG   (rows a, columns w)')
        P('    a\\w ' + ''.join(f'{w:>22d}' for w in WS))
        for a0 in SAMPLE_A:
            if a0 > AMAX: continue
            row = f'  {a0:5d} '
            for w in WS:
                a = a0 if (a0 + w) % 2 == 0 else a0 + 1
                if a > AMAX: a -= 2
                v = R.v(G[(a, w)]) if G[(a, w)] != (0, 0) else 'zero'
                row += f'{v:>6}/{lt_pred(a, w, p):6.1f}/{lean_pred(a, w, p):5.1f}/{sigma_like(a, w, p):4.1f}'.rjust(22)
            P(row)
        summary.append((cv, e, p, typ, cname, slopes[0], slopes[5], slopes[20], d_lt, g))
P('\n=== SUMMARY: slope of v_p(J(a,w)) in a at w = 0, 5, 20, against gamma_p and 1/(p^2-1)')
P(' curve e  p   type   config                         s(w=0)  s(w=5)  s(w=20)  gamma_p  1/(p^2-1)  min_a[v-LT](w=0)')
for (cv, e, p, typ, cname, s0, s5, s20, d, g) in summary:
    P(f' {cv:4s} {e:2d} {p:3d}  {typ:6s} {cname:30s} {s0:7.4f} {s5:7.4f} {s20:7.4f}  {g:7.4f}  {1/(p*p-1):8.4f}   {d:8.2f}')
P(f'\nelapsed {time.time() - t0:.1f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kernel3_run.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
