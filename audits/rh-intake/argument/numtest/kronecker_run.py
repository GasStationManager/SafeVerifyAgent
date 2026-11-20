"""v_p(N_{a,b}) for the Kronecker theta function, N_{a,b} = a!(b-1)! [z^{b-1} w^a] sigma(z+w)/(sigma(z)sigma(w)).

usage: python3 -I kronecker_run.py CURVE p L m      (CURVE in Zi, Zw, C;  a < L, 1 <= b <= m)
writes out_kron_CURVE_p<p>.txt.

Candidate laws compared (gamma = p/(p^2-1), rho = 1/(p^2-1), vf = v_p(n!)):
  LEAN(a,b) = sum_{e odd} max(0, a/p^e - b)                 -- the capped gain the proof uses (cap w = b)
  EMP(a,b)  = max(gamma(a+b) - b, rho(a+b))                 -- empirical law found here
  LB(a,b)   = vf(a) + vf(b-1) - rho(a+b) - min(b, (a+b)/(p+1)) -- Lean-style form with #factors = min(b,(a+b)/(p+1))
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kronecker_lib import phi_numbers, rows_padic, N_val, vp_fact, pred_cap
from fractions import Fraction

CURVES = {'Zi': (4, 0, 4, lambda p: 'inert' if p % 4 == 3 else 'split'),
          'Zw': (0, 4, 6, lambda p: 'inert' if p % 3 == 2 else 'split'),
          'C': (-10, Fraction(7, 2), 2, lambda p: 'supersingular' if p in (5, 7, 13) else 'ordinary')}


def lsq(xs, ys):
    n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx


def lsq2(rows):          # y = al*a + be*b + c
    import itertools
    n = len(rows)
    S = [[0.0] * 3 for _ in range(3)]; T = [0.0] * 3
    for a, b, y in rows:
        x = (a, b, 1.0)
        for i in range(3):
            T[i] += x[i] * y
            for j in range(3): S[i][j] += x[i] * x[j]
    # solve 3x3
    M = [S[i] + [T[i]] for i in range(3)]
    for c in range(3):
        piv = max(range(c, 3), key=lambda r: abs(M[r][c])); M[c], M[piv] = M[piv], M[c]
        for r in range(3):
            if r != c:
                f = M[r][c] / M[c][c]
                M[r] = [M[r][k] - f * M[c][k] for k in range(4)]
    return [M[i][3] / M[i][i] for i in range(3)]


def main():
    cname, p, L, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    g2, g3, dd, typ = CURVES[cname]; typ = typ(p)
    t0 = time.time()
    Phi = phi_numbers(g2, g3, L + m + 6)
    K = int(L / (p - 1)) + 80
    rows, h = rows_padic(Phi, p, K, [L + 2] * (m + 2))
    gam, rho = p / (p * p - 1), 1 / (p * p - 1)
    LEAN = lambda a, b: pred_cap(a, b, p)
    EMP = lambda a, b: max(gam * (a + b) - b, rho * (a + b))
    LB = lambda a, b: vp_fact(a, p) + vp_fact(b - 1, p) - rho * (a + b) - min(b, (a + b) / (p + 1))
    V = {}
    for b in range(1, m + 1):
        for a in range(0, L):
            if (a + b) % dd or a + b <= 2: continue      # weight-2 part is identically 0 (phi starts at u^4)
            v, ok = N_val(rows, h, a, b, p, K)
            if not ok: raise SystemExit(f'precision exhausted at {(a, b)}')
            V[(a, b)] = v
    out = [f'curve {cname} (g2={g2}, g3={g3}), p = {p} ({typ}), a < {L}, 1 <= b <= {m}; K = {K}, h = {h}; '
           f'{len(V)} nonzero N_ab; gamma_p = {gam:.4f}, 1/(p^2-1) = {rho:.4f}; time {time.time() - t0:.0f}s', '']
    big = [(a, b) for (a, b) in V if a >= 50]
    dl = [V[k] - LEAN(*k) for k in big]; de = [V[k] - EMP(*k) for k in big]; db = [V[k] - LB(*k) for k in big]
    worst = min(big, key=lambda k: V[k] - LEAN(*k))
    out.append(f'over a >= 50: min(v - LEAN) = {min(dl):.2f} at {worst}; #(v < LEAN - 3) = {sum(1 for x in dl if x < -3)}')
    out.append(f'               v - EMP in [{min(de):.2f}, {max(de):.2f}], mean {sum(de) / len(de):.2f}')
    out.append(f'               v - LB  in [{min(db):.2f}, {max(db):.2f}], mean {sum(db) / len(db):.2f}  (#negative: {sum(1 for x in db if x < 0)})')
    # slopes at fixed b
    out.append('\nslope dv/da (LSQ over a in [L/2, L)) at fixed b:')
    for b in [1, 2, 3, 5, 8, 12, 16, 24, 32, 40]:
        if b > m: continue
        pts = [(a, V[(a, b)]) for a in range(L // 2, L) if (a, b) in V]
        if len(pts) > 5: out.append(f'  b={b:3d}: {lsq([x for x, _ in pts], [y for _, y in pts]):.4f}')
    # fit in the regime b <= a/(2p)
    reg = [(a, b, V[(a, b)]) for (a, b) in V if a >= 100 and b <= a / (2 * p)]
    if len(reg) > 20:
        al, be, c = lsq2(reg)
        out.append(f'\nLSQ fit v = al*a + be*b + c over b <= a/(2p), a >= 100 ({len(reg)} points): '
                   f'al = {al:.4f} (gamma {gam:.4f}), be = {be:.4f} (gamma-1 = {gam - 1:.4f}; LEAN slope -#{{e odd: p^e<=a/b}} = -1,-2,..), c = {c:.2f}')
    # plateau regime b >= a/p
    pl = [(a, b) for (a, b) in V if b >= a / p + 2 and a + b >= 20]
    if pl:
        d = [V[k] - rho * (k[0] + k[1]) for k in pl]
        out.append(f'regime b >= a/p + 2 ({len(pl)} points): v - (a+b)/(p^2-1) in [{min(d):.2f}, {max(d):.2f}], mean {sum(d) / len(d):.2f}')
    bal = [(a, b) for (a, b) in V if abs(a - b) <= 2 and b >= 8]
    if bal:
        out.append('balanced a~b: ' + ', '.join(f'(a={a},b={b}: v={V[(a, b)]}, (a+b)/(p^2-1)={rho * (a + b):.1f})' for a, b in sorted(bal)[-6:]))
    # grid table
    As = [x for x in [100, 200, 300, 600, 1000, 1500, 2000] if x < L]
    Bs = [b for b in [1, 2, 3, 5, 8, 12, 16, 20, 30, 40] if b <= m]
    out.append('\ngrid: entry = v / LEAN / EMP  (a = largest a <= row label with N_ab != 0)')
    out.append('a\\b   ' + ''.join(f'{b:>17d}' for b in Bs))
    for A in As:
        line = f'{A:5d} '
        for b in Bs:
            a = max([a for a in range(A - 12, A + 1) if (a, b) in V], default=None)
            line += f'{V[(a, b)]:>6d}/{LEAN(a, b):5.1f}/{EMP(a, b):5.1f}' if a is not None else ' ' * 17
        out.append(line)
    if typ in ('split', 'ordinary'):
        vs = list(V.values())
        out.append(f'\n{typ}: v over all (a,b): min {min(vs)}, max {max(vs)}, mean {sum(vs) / len(vs):.3f}')
    txt = '\n'.join(out)
    print(txt)
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'out_kron_{cname}_p{p}.txt'), 'w').write(txt + '\n')


if __name__ == '__main__':
    main()
