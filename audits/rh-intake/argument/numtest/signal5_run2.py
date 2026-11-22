"""NODE-NUMTEST5 main run, n'=2 signal place (h = 0), rank one and 2x2 block, cap ~ a/p regime.
For each served case: full grid J2(a, nu), a <= AMAX, nu <= NUMAX (a + nu even), exact mod p^K.
Columns used below:
  v      = v_p(J2(a,nu))  (valuation in Z_{p^2})
  P1     = sum_{e odd} (a/p^e - nu)_+          the ENGINE2 / ledger capped law (cap nu at every odd e: n'=2)
  LS     = P1 - gamma*Wc - 2(log_p a + 1)      the Lean's stated per-top bound with its backward charge (Wc = nu) and
                                                 Lemma RA's digit-sum loss for 2 coordinates
  LP     = lp_opt(a, [(nu,1)], p, 2)           best dual-radius bound (forward AND backward constraint), no digit loss
  LPf    = gamma(a+nu) - min(nu, a/p)          forward constraint only (what one would get if backward Gaussians were free)
  sig    = (a+nu)/(p^2-1)
usage: python3 -I signal5_run2.py -> out_signal5_run2.txt
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import log
from kernel3_lib import th0_jets, Zp2, gam
from signal5_lib import CURVES, grid2, block_jet, P1, lean_charge, lp_opt, sigma_floor, logloss

CASES = [('Zw', 5, 625, 200), ('Zi', 7, 1029, 220), ('Zw', 11, 726, 100), ('Zi', 11, 726, 100)]


def run_case(case):
    cv, p, AMAX, NUMAX = case
    g2, g3, e = CURVES[cv]
    g = gam(p)
    t0 = time.time()
    T = th0_jets(g2, g3, e, AMAX + NUMAX + 4)
    K = int(g * (AMAX + NUMAX)) + 40
    R = Zp2(p, K)
    c = R.elt_of_norm(-1, 1) or R.elt_of_norm(-1, 2)
    Tq = [t % R.q for t in T]
    G = grid2(Tq, R, c, AMAX, NUMAX)
    V = {k: R.v(x) for k, x in G.items()}
    t1 = time.time()
    # block jets (cap = number of minors nu, partner degree 2 nu), a <= ABLK
    ABLK = min(AMAX, 30 * p if p > 5 else 250)
    xis = {'e1': ((1, 0), (0, 0)), 'e2': ((0, 0), (1, 0)), 'gen1': ((1, 0), (2, 1)), 'gen2': ((3, 1), (1, 2))}
    Bv = {}
    nus_blk = sorted(set([0, 2, 4] + list(range(6, min(NUMAX, ABLK // p + 24) + 1, 2))))
    nus_blk = [n for n in nus_blk if 2 * n <= NUMAX]
    for a in sorted(set([ABLK // 2 - (ABLK // 2) % 2, ABLK - ABLK % 2])):
        for nu in nus_blk:
            vs = {}
            for name, xi in xis.items():
                x = block_jet(R, G, a, nu, xi)
                vs[name] = R.v(x)
            Bv[(a, nu)] = vs
    t2 = time.time()
    return dict(cv=cv, p=p, AMAX=AMAX, NUMAX=NUMAX, K=K, V=V, Bv=Bv, ABLK=ABLK, times=(t1 - t0, t2 - t1))


def main():
    import multiprocessing as mp
    with mp.get_context('fork').Pool(4) as pool:
        res = pool.map(run_case, CASES)
    out = []; P = out.append
    P('NODE-NUMTEST5 run2: n\'=2 signal place, Theta = th0(z0+z1) th0(c(z0-z1)), c c^sigma = -1; J2(a,nu) = d_z0^a d_z1^nu Theta(0)')
    P('  v = v_p(J2);  P1 = sum_{e odd}(a/p^e - nu)_+ [claim];  LS = P1 - gamma*nu - 2(log_p a + 1) [Lean stated, with backward');
    P('  charge and digit loss];  LP = best dual-radius bound (fwd + bwd constraints);  LPf = gamma(a+nu) - min(nu, a/p) [fwd only];')
    P('  sig = (a+nu)/(p^2-1).   Only a + nu even (odd total order vanishes identically).')
    for r in res:
        cv, p, AMAX, NUMAX, K, V = r['cv'], r['p'], r['AMAX'], r['NUMAX'], r['K'], r['V']
        g = gam(p)
        P(f'\n==================== {cv}  p={p}  gamma={g:.4f}  1/(p^2-1)={1/(p*p-1):.4f}  a<={AMAX} (= {AMAX/p**3:.2f} p^3, {AMAX/p**2:.1f} p^2)'
          f'  nu<={NUMAX}  precision p^{K}  time grid {r["times"][0]:.0f}s, blocks {r["times"][1]:.0f}s')
        pts0 = [(a, n) for (a, n) in V if a + n > 0]
        hit = sum(1 for k in pts0 if V[k] >= K)
        pts = [k for k in pts0 if V[k] < K]   # exact zeros (Z[i] selection rule) excluded
        cap = lambda n: (lambda e: n)
        # global statistics by region
        regs = {'nu < a/p - 2': lambda a, n: n < a / p - 2, '|nu - a/p| <= 2 (kink)': lambda a, n: abs(n - a / p) <= 2,
                'nu > a/p + 2': lambda a, n: n > a / p + 2}
        P(f'  points {len(pts0)}, jets = 0 mod p^K (excluded below): {hit}')
        P('  region                      #pts   min(v-P1)  at (a,nu)      min(v-LS)  min(v-LP)  max(v-LP)  mean(v-LP)  min(v-LPf) max(v-LPf)  min(v-P1-g*nu) #(v<P1+g*nu-3)')
        for name, f in regs.items():
            sel = [(a, n) for (a, n) in pts if f(a, n) and a >= p]
            if not sel: continue
            d1 = [(V[k] - P1(k[0], cap(k[1]), p), k) for k in sel]
            dls = [V[k] - (P1(k[0], cap(k[1]), p) - g * k[1] - logloss(k[0], 2, p)) for k in sel]
            dlp = [V[k] - lp_opt(k[0], [(k[1], 1)], p, 2) for k in sel]
            dlf = [V[k] - (g * (k[0] + k[1]) - min(k[1], k[0] / p)) for k in sel]
            dnb = [V[k] - P1(k[0], cap(k[1]), p) - g * k[1] for k in sel]
            mn = min(d1)
            P(f'  {name:26s} {len(sel):6d}   {mn[0]:8.2f}  {str(mn[1]):12s}   {min(dls):8.2f}  {min(dlp):8.2f}  {max(dlp):8.2f}  '
              f'{sum(dlp)/len(dlp):8.2f}   {min(dlf):8.2f}  {max(dlf):8.2f}   {min(dnb):8.2f}  {sum(1 for x in dnb if x < -3):6d}')
        # slice A: fixed nu, a across the kink a = p nu
        P('\n  SLICE A (fixed nu, a across the kink a = p*nu):  a: v / P1 / LP / LPf / sig')
        for nu in [x for x in (8, 16, 24, 40, 60, 90, 120) if x <= NUMAX and p * x * 1.6 <= AMAX]:
            offs = sorted(set(int(p * nu * f) for f in (0.5, 0.7, 0.85, 0.95, 1.0, 1.05, 1.15, 1.3, 1.6)))
            row = []
            for a in offs:
                a += (a + nu) % 2
                if a > AMAX: continue
                row.append(f'{a}: {V[(a, nu)]}/{P1(a, cap(nu), p):.1f}/{lp_opt(a, [(nu, 1)], p, 2):.1f}/'
                           f'{g * (a + nu) - min(nu, a / p):.1f}/{sigma_floor(a, nu, p):.1f}')
            P(f'   nu={nu:3d} (kink a={p*nu}):  ' + '   '.join(row))
        # slice B: fixed a, nu from 0 to 1.6 a/p
        P('\n  SLICE B (fixed a, nu across the kink nu = a/p):  nu: v / P1 / LP / LPf')
        for a0 in sorted(set([p ** 2 * 4, p ** 3, 2 * p ** 3, 4 * p ** 3, AMAX])):
            if a0 > AMAX: continue
            kk = a0 / p
            nus = sorted(set(int(kk * f) for f in (0, 0.25, 0.5, 0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 2.0)))
            row = []
            for nu in nus:
                a = a0 - ((a0 + nu) % 2)
                if nu > NUMAX: continue
                row.append(f'{nu}: {V[(a, nu)]}/{P1(a, cap(nu), p):.1f}/{lp_opt(a, [(nu, 1)], p, 2):.1f}/'
                           f'{g * (a + nu) - min(nu, a / p):.1f}')
            P(f'   a={a0:4d} (a/p={kk:.1f}, a/p^3={a0/p**3:.2f}):  ' + '   '.join(row))
        # slice C: along the kink line nu = round(a/p) + delta
        P('\n  SLICE C (on the kink: nu = a/p + delta):  rows delta, columns a;  entries v - P1 (v - LP)')
        alist = [a for a in (p ** 2, 2 * p ** 2, 4 * p ** 2, p ** 3, 2 * p ** 3, 3 * p ** 3, 4 * p ** 3) if a <= AMAX and a / p + 10 <= NUMAX]
        P('     delta ' + ''.join(f'{a:>16d}' for a in alist))
        for dlt in (-6, -3, -1, 0, 1, 3, 6):
            row = f'     {dlt:+4d}  '
            for a0 in alist:
                nu = int(round(a0 / p)) + dlt
                a = a0 - ((a0 + nu) % 2)
                if nu < 0 or nu > NUMAX: row += ' ' * 16; continue
                row += f'{V[(a, nu)] - P1(a, cap(nu), p):+7.2f} ({V[(a, nu)] - lp_opt(a, [(nu, 1)], p, 2):+5.2f})'.rjust(16)
            P(row)
        # slack fit: region nu <= a/p, a >= 4p
        sel = [(a, n) for (a, n) in pts if n <= a / p and a >= 4 * p]
        X = [(a, n, V[(a, n)] - P1(a, cap(n), p)) for a, n in sel]
        import itertools
        # least squares slack = alpha a + beta nu + c0
        def lsq3(rows):
            S = [[0.0] * 3 for _ in range(3)]; b = [0.0] * 3
            for a, n, y in rows:
                x = (a, n, 1.0)
                for i in range(3):
                    b[i] += x[i] * y
                    for j in range(3): S[i][j] += x[i] * x[j]
            # solve 3x3
            M = [S[i] + [b[i]] for i in range(3)]
            for i in range(3):
                piv = max(range(i, 3), key=lambda r_: abs(M[r_][i])); M[i], M[piv] = M[piv], M[i]
                for r_ in range(3):
                    if r_ != i:
                        f = M[r_][i] / M[i][i]
                        M[r_] = [u - f * w for u, w in zip(M[r_], M[i])]
            return [M[i][3] / M[i][i] for i in range(3)]
        al, be, c0 = lsq3(X)
        P(f'\n  slack fit, region nu <= a/p, a >= 4p ({len(X)} pts): v - P1 = {al:.4f} a + {be:.4f} nu + {c0:.2f}')
        P(f'    prediction of LP - P1 in this region: gamma*nu + (gamma - 1/p - [e>=3 terms]) a ; gamma = {g:.4f},'
          f' gamma - 1/p = {g - 1/p:.4f}')
        sel = [(a, n) for (a, n) in pts if n >= a / p and a >= 4 * p]
        X = [(a, n, V[(a, n)]) for a, n in sel]
        al, be, c0 = lsq3(X)
        P(f'  fit of v itself, region nu >= a/p, a >= 4p ({len(X)} pts): v = {al:.4f} a + {be:.4f} nu + {c0:.2f}   '
          f'[LP (backward constraint) predicts {1/(p*p-1):.4f} a + {1/(p*p-1):.4f} nu;  LPf (no backward) {g - 1/p:.4f} a + {g:.4f} nu]')
        # residual of v - LP in each region, by a-bands (growth of the loss?)
        P('  v - LP by a-band (min / mean / max) and region:')
        bands = [(lo, lo * 2) for lo in (4 * p, 8 * p, 16 * p, 32 * p, 64 * p) if lo <= AMAX]
        for lo, hi in bands:
            line = f'    a in [{lo},{hi}): '
            for name, f in regs.items():
                ds = [V[k] - lp_opt(k[0], [(k[1], 1)], p, 2) for k in pts if lo <= k[0] < hi and f(*k)]
                if ds: line += f'{name}: {min(ds):+.2f}/{sum(ds)/len(ds):+.2f}/{max(ds):+.2f}   '
            P(line)
        # blocks
        Bv = r['Bv']
        P(f'\n  2x2 BLOCK (xi X11 + xi2 X21)^a det(Y)^nu at the partner: cap = nu minors, partner degree 2nu.')
        P('   a   nu  | v for xi = e1 / e2 / gen1 / gen2 | min v | P1(cap=nu) | P1(cap=2nu) | blockLP = gam(a+2nu)-min(nu,a/p)'
          ' | min v - P1(nu)')
        worstB = 99
        for (a, nu), vs in sorted(Bv.items()):
            mv = min(vs.values())
            p1 = P1(a, cap(nu), p)
            worstB = min(worstB, mv - p1) if mv < K else worstB
            P(f'  {a:4d} {nu:4d} | ' + ' / '.join(f'{vs[k]:3d}' for k in ('e1', 'e2', 'gen1', 'gen2')) +
              f' | {mv:4d} | {p1:8.2f} | {P1(a, cap(2 * nu), p):8.2f} | {g * (a + 2 * nu) - min(nu, a / p):8.2f} | {mv - p1:+7.2f}')
        P(f'  block: min over all (a,nu,xi) of v - P1(cap = nu) = {worstB:+.2f}')
    P('')
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_signal5_run2.txt'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))


if __name__ == '__main__':
    t0 = time.time()
    main()
    print(f'total {time.time() - t0:.0f}s')
