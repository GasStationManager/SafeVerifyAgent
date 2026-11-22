"""NODE-NUMTEST5: the backward charge at distance 1 on the n'=4 orbit (curve Z[w], p = 5).
Position 3 is the e = 3 FORWARD partner of the top z0 and its distance-1 BACKWARD partner (3 = 0 - 1 mod 4).
J4(a, n1, n3) for n3 = 0..N3MAX (well beyond the e = 3 cap a/p^3), n1 in {0, 8}.
Predictions:  P1   = sum_{e odd}(a/p^e - cap_e)_+                      (claim; never needs a partner credit)
              LPf  = gamma(a+n1+n3) - min(n1, a/p) - min(n3, a/p^3)     (forward constraints only: partner rows keep gamma)
              LP   = lp_opt with forward AND backward constraints        (position 3: r3 >= (1 - eps)/p)
              LGc  = gamma(a+n1+n3) - [Lean forward charge] - gamma*Wc,  Wc = max(n1, n3)
                     (the Lean's accounting with the partner rows credited gamma per unit and the backward charge gamma*Wc)
usage: python3 -I signal5_back4.py [N3MAX] -> out_signal5_back4.txt
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import comb
from kernel3_lib import th0_jets, gam
from kernel4_lib import Ring, coeffs
from signal5_lib import pair_D, final4, P1, lean_charge, lp_opt

N3MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 64
p, AMAX = 5, 320
JS = (0, 4)
g = gam(p)
K = int(g * (AMAX + N3MAX + 8)) + 40


def pairjob(args):
    rA, rB = args
    R = Ring(p, K)
    T = th0_jets(0, 4, 1, AMAX + N3MAX + 16)
    Tq = [t % R.q for t in T]
    return pair_D(R, Tq, rA, rB, AMAX, set(range(max(JS) + 1)), N3MAX)


def main():
    import multiprocessing as mp
    t0 = time.time()
    m = coeffs(p)
    with mp.get_context('fork').Pool(2) as pool:
        D12, D34 = pool.map(pairjob, [(m[0], m[1]), (m[2], m[3])])
    t1 = time.time()
    R = Ring(p, K)
    out = []; P = out.append
    P(f'NODE-NUMTEST5 back4: n\'=4 orbit, Z[w], p={p}; position 3 = e=3 forward partner AND distance-1 backward partner of z0.')
    P(f'  precision p^{K}; pair tables {t1 - t0:.0f}s')
    P('  entries n3: v / P1 / LPf / LP / LGc ;  ZERO = jet vanishes mod p^K')
    stats = {'P1': [], 'LPf': [], 'LP': [], 'LGc': []}
    VV = {}
    for a0 in (125, 200, 320):
        for n1 in JS:
            crow = {}
            row = []
            for n3 in range(0, N3MAX + 1):
                a = a0 - ((a0 + n1 + n3) % 2)
                if a not in crow: crow[a] = [comb(a, b) % R.q for b in range(a + 1)]
                v = R.v(final4(R, D12, D34, a, n1, n3, crow[a]))
                caps = lambda e: n1 if e % 4 == 1 else n3
                pr = {'P1': P1(a, caps, p),
                      'LPf': g * (a + n1 + n3) - min(n1, a / p) - min(n3, a / p ** 3),
                      'LP': lp_opt(a, [(n1, 1), (n3, 3)], p, 4),
                      'LGc': g * (a + n1 + n3) - lean_charge(a, caps, p) - g * max(n1, n3)}
                if v >= K:
                    row.append(f'{n3}:ZERO'); continue
                VV[(a, n1, n3)] = v
                for k in stats: stats[k].append((v - pr[k], (a, n1, n3)))
                if n3 % 4 == 0 or n3 < 6:
                    row.append(f'{n3}: {v}/{pr["P1"]:.1f}/{pr["LPf"]:.1f}/{pr["LP"]:.1f}/{pr["LGc"]:.1f}')
            P(f'\n  a~{a0} (a/p^3 = {a0/p**3:.2f}), n1 = {n1}:')
            for i in range(0, len(row), 6): P('     ' + '   '.join(row[i:i + 6]))
    P('\n  min / max of v - prediction over all points (and where the min is attained):')
    for k, s in stats.items():
        P(f'    {k:4s}: min {min(s)[0]:+7.2f} at {min(s)[1]}   max {max(s)[0]:+7.2f}   #(v < pred - 3) = {sum(1 for x, _ in s if x < -3)}/{len(s)}')
    P('\n  least-squares slope dv/dn3 on n3 >= 2 a/p^3 + 4 (the region past the e = 3 kink):')
    for a0 in (125, 200, 320):
        for n1 in JS:
            pts = [(k[2], VV[k]) for k in VV if abs(k[0] - a0) <= 1 and k[1] == n1 and k[2] >= 2 * a0 / p ** 3 + 4]
            n = len(pts); mx = sum(x for x, _ in pts) / n; my = sum(y for _, y in pts) / n
            sl = sum((x - mx) * (y - my) for x, y in pts) / sum((x - mx) ** 2 for x, _ in pts)
            P(f'    a~{a0} n1={n1}: slope {sl:+.4f}   [LPf: gamma = {g:+.4f};  LP: gamma - (1-eps*)/p = '
              f'{g - (1 - (p - 1) / (p ** 4 - 1)) / p:+.4f};  LGc: 0]')
    P(f'\n  total {time.time() - t0:.0f}s')
    open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_signal5_back4.txt'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))


if __name__ == '__main__':
    main()
