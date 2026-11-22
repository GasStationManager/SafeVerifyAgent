"""NODE-NUMTEST5 run on the n'=4 orbit (kernel4_lib instance, curve Z[w], p = 5): e = 1 lands on position 1, e = 3 on
position 3, e = 5 on position 1.  J4(a, n1, n3) = d_z0^a d_z1^n1 d_z3^n3 Theta(0), exact mod p^K.
Part 1: full grid n3 = 0, a <= AMAX, n1 <= N1MAX  (e = 1 kink nu1 = a/p).
Part 2: n3 in 0..L at a in ASET, n1 on a set around a/p (e = 3 cap ~ a/p^3 together with e = 1 cap ~ a/p).
Columns:  P1 = sum_{e odd}(a/p^e - cap_e)_+ with cap_e = n1 (e = 1 mod 4), n3 (e = 3 mod 4)   [the claim]
          LS = P1 - gamma*Wc - 3(log_p a + 1), Wc = max(n1, n3)                        [Lean stated, with backward charge]
          LP = lp_opt(a, [(n1,1),(n3,3)], p, 4)                                         [best dual radii, fwd + bwd]
          LPf = gamma(a+n1+n3) - min(n1, a/p) - min(n3, a/p^3)                         [forward constraints only]
usage: python3 -I signal5_run4.py [AMAX N1MAX]  -> out_signal5_run4.txt
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import comb
from kernel3_lib import th0_jets, gam
from kernel4_lib import Ring, coeffs, positions
from signal5_lib import pair_D_parallel, final4, P1, lp_opt, sigma_floor, logloss

AMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 320
N1MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 100
p = 5
L = 4
ASET = [a for a in (250, 320) if a <= AMAX] or [AMAX - AMAX % 2]
g = gam(p)
K = int(g * (AMAX + N1MAX + L)) + 40
G = {}


def caps(n1, n3): return lambda e: n1 if e % 4 == 1 else n3


def work(args):
    a, items = args
    R = Ring(p, K)
    crow = [comb(a, b) % R.q for b in range(a + 1)]
    res = []
    for (n1, n3) in items:
        res.append(((a, n1, n3), R.v(final4(R, G['D12'], G['D34'], a, n1, n3, crow))))
    return res


def main():
    import multiprocessing as mp
    t0 = time.time()
    T = th0_jets(0, 4, 1, AMAX + N1MAX + L + 6)
    m = coeffs(p)
    taus, lab = positions(p)
    R = Ring(p, K)
    Tq = [t % R.q for t in T]
    G['D12'] = pair_D_parallel(p, K, Tq, m[0], m[1], AMAX, N1MAX, L)
    G['D34'] = pair_D_parallel(p, K, Tq, m[2], m[3], AMAX, N1MAX, L)
    t1 = time.time()
    jobs = []
    for a in range(0, AMAX + 1):
        items = [(n1, 0) for n1 in range(N1MAX + 1) if (a + n1) % 2 == 0]
        if a in ASET or a + 1 in ASET:
            kk = (a + (a + 1 in ASET)) // p
            n1s = sorted(set([0, kk // 4, kk // 2, kk - 8, kk - 4, kk - 2, kk, kk + 2, kk + 4, kk + 8, kk + 16]))
            items += [(n1, n3) for n1 in n1s for n3 in range(1, L + 1) if (a + n1 + n3) % 2 == 0 and n1 <= N1MAX]
        jobs.append((a, items))
    jobs.sort(key=lambda j: -j[0])
    with mp.get_context('fork').Pool(4) as pool:
        parts = pool.map(work, jobs, chunksize=1)
    V = {}
    for pt in parts:
        for k, v in pt: V[k] = v
    t2 = time.time()
    out = []; P = out.append
    P(f'NODE-NUMTEST5 run4: n\'=4 orbit, curve Z[w], p={p}, taus={taus} ({lab}); gamma={g:.4f}; a<={AMAX} '
      f'(= {AMAX/p**3:.2f} p^3), n1<={N1MAX}; precision p^{K}; time pair tables {t1-t0:.0f}s, jets {t2-t1:.0f}s')
    P('  v = v_p(J4(a,n1,n3)); P1 claim; LS Lean stated (backward charge gamma*max(n1,n3) + digit loss); LP best dual radii;'
      ' LPf forward-only.')
    pts = [k for k in V if k[2] == 0 and k[0] + k[1] > 0]
    hit = sum(1 for k in V if V[k] >= K)
    P(f'  points (n3 = 0): {len(pts)};  all points: {len(V)};  jets = 0 mod p^K: {hit} at {sorted(k for k in V if V[k] >= K)} (excluded)')
    pts = [k for k in pts if V[k] < K]
    LPv = lambda a, n1, n3: lp_opt(a, [(n1, 1), (n3, 3)], p, 4)
    LPf = lambda a, n1, n3: g * (a + n1 + n3) - min(n1, a / p) - min(n3, a / p ** 3)
    LS = lambda a, n1, n3: P1(a, caps(n1, n3), p) - g * max(n1, n3) - 3 * logloss(a, 1, p)
    regs = {'n1 < a/p - 2': lambda a, n: n < a / p - 2, '|n1 - a/p| <= 2 (kink)': lambda a, n: abs(n - a / p) <= 2,
            'n1 > a/p + 2': lambda a, n: n > a / p + 2}
    P('  region (n3 = 0, a >= p)     #pts   min(v-P1)  at (a,n1)     min(v-LS)  min(v-LP)  max(v-LP)  mean(v-LP)  min(v-LPf) max(v-LPf)  min(v-P1-g*n1) #(v<P1+g*n1-3)')
    for name, f in regs.items():
        sel = [k for k in pts if f(k[0], k[1]) and k[0] >= p]
        d1 = [(V[k] - P1(k[0], caps(k[1], 0), p), k[:2]) for k in sel]
        dls = [V[k] - LS(*k) for k in sel]
        dlp = [V[k] - LPv(*k) for k in sel]
        dlf = [V[k] - LPf(*k) for k in sel]
        dnb = [V[k] - P1(k[0], caps(k[1], 0), p) - g * k[1] for k in sel]
        mn = min(d1)
        P(f'  {name:26s} {len(sel):6d}   {mn[0]:8.2f}  {str(mn[1]):12s}   {min(dls):8.2f}  {min(dlp):8.2f}  {max(dlp):8.2f}  '
          f'{sum(dlp)/len(dlp):8.2f}   {min(dlf):8.2f}  {max(dlf):8.2f}   {min(dnb):8.2f}  {sum(1 for x in dnb if x < -3):6d}')
    P('\n  SLICE A (fixed n1, a across the kink a = p*n1):  a: v / P1 / LP / LPf')
    for nu in (8, 16, 24, 32, 40, 60):
        row = []
        for f in (0.5, 0.7, 0.85, 0.95, 1.0, 1.05, 1.15, 1.3, 1.6):
            a = int(p * nu * f); a += (a + nu) % 2
            if a > AMAX: continue
            row.append(f'{a}: {V[(a, nu, 0)]}/{P1(a, caps(nu, 0), p):.1f}/{LPv(a, nu, 0):.1f}/{LPf(a, nu, 0):.1f}')
        P(f'   n1={nu:3d} (kink a={p*nu}):  ' + '   '.join(row))
    P('\n  SLICE B (fixed a, n1 across the kink n1 = a/p):  n1: v / P1 / LP / LPf')
    for a0 in (100, 125, 160, 250, 320):
        if a0 > AMAX: continue
        kk = a0 / p
        row = []
        for f in (0, 0.25, 0.5, 0.75, 0.9, 1.0, 1.1, 1.25, 1.5, 2.0, 2.5):
            nu = int(kk * f)
            if nu > N1MAX: continue
            a = a0 - ((a0 + nu) % 2)
            row.append(f'{nu}: {V[(a, nu, 0)]}/{P1(a, caps(nu, 0), p):.1f}/{LPv(a, nu, 0):.1f}/{LPf(a, nu, 0):.1f}')
        P(f'   a={a0:4d} (a/p={kk:.0f}):  ' + '   '.join(row))
    P('\n  SLICE B, full resolution at a = 320 / 319 (n1 = 0..N1MAX): v - P1, then v - LP')
    for lab_, fn in (('v-P1', lambda a, n: V[(a, n, 0)] - P1(a, caps(n, 0), p)), ('v-LP', lambda a, n: V[(a, n, 0)] - LPv(a, n, 0))):
        a0 = AMAX
        s = []
        for nu in range(0, N1MAX + 1):
            a = a0 - ((a0 + nu) % 2)
            s.append(f'{fn(a, nu):+.1f}')
        for i in range(0, len(s), 20):
            P(f'   {lab_} n1={i:3d}..: ' + ' '.join(s[i:i + 20]))
    # fits
    def lsq3(rows):
        S = [[0.0] * 3 for _ in range(3)]; b = [0.0] * 3
        for a, n, y in rows:
            x = (a, n, 1.0)
            for i in range(3):
                b[i] += x[i] * y
                for j in range(3): S[i][j] += x[i] * x[j]
        M = [S[i] + [b[i]] for i in range(3)]
        for i in range(3):
            piv = max(range(i, 3), key=lambda r_: abs(M[r_][i])); M[i], M[piv] = M[piv], M[i]
            for r_ in range(3):
                if r_ != i:
                    f = M[r_][i] / M[i][i]
                    M[r_] = [u - f * w for u, w in zip(M[r_], M[i])]
        return [M[i][3] / M[i][i] for i in range(3)]
    X = [(k[0], k[1], V[k]) for k in pts if k[1] <= k[0] / p and k[0] >= 4 * p]
    al, be, c0 = lsq3(X)
    P(f'\n  fit of v, region n1 <= a/p, a >= 4p ({len(X)} pts): v = {al:.4f} a + {be:.4f} n1 + {c0:.2f}   [gamma = {g:.4f}, gamma-1 = {g-1:.4f}]')
    X = [(k[0], k[1], V[k]) for k in pts if k[1] >= k[0] / p and k[0] >= 4 * p]
    al, be, c0 = lsq3(X)
    den = p ** 4 - 1
    P(f'  fit of v, region n1 >= a/p, a >= 4p ({len(X)} pts): v = {al:.4f} a + {be:.4f} n1 + {c0:.2f}   '
      f'[LP predicts {g - (p**3-1)/den:.4f} a + {g - (p-1)/den:.4f} n1;  LPf {g - 1/p:.4f} a + {g:.4f} n1;  sigma-type {1/(p*p-1):.4f}(a+n1)]')
    P('  v - LP by a-band (min / mean / max), n3 = 0:')
    for lo, hi in ((20, 40), (40, 80), (80, 160), (160, 321)):
        line = f'    a in [{lo},{hi}): '
        for name, f in regs.items():
            ds = [V[k] - LPv(*k) for k in pts if lo <= k[0] < hi and f(k[0], k[1])]
            if ds: line += f'{name}: {min(ds):+.2f}/{sum(ds)/len(ds):+.2f}/{max(ds):+.2f}   '
        P(line)
    P('\n  PART 2 (both caps): a, n1, n3: v / P1 / LS / LP   [a/p^3 = 2.0 at a=250, 2.56 at a=320]')
    worst2 = 99
    for a0 in ASET:
        for n3 in range(0, L + 1):
            kk = a0 // p
            row = []
            for n1 in sorted(set([0, kk // 4, kk // 2, kk - 8, kk - 4, kk - 2, kk, kk + 2, kk + 4, kk + 8, kk + 16])):
                a = a0 - ((a0 + n1 + n3) % 2)
                if (a, n1, n3) not in V: continue
                v = V[(a, n1, n3)]
                if v >= K: row.append(f'{n1}: ZERO'); continue
                p1 = P1(a, caps(n1, n3), p)
                worst2 = min(worst2, v - p1)
                row.append(f'{n1}: {v}/{p1:.1f}/{LS(a, n1, n3):.1f}/{LPv(a, n1, n3):.1f}')
            P(f'   a~{a0} n3={n3}:  ' + '   '.join(row))
    P(f'  PART 2: min(v - P1) = {worst2:+.2f}')
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_signal5_run4.txt'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))
    print(f'total {time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
