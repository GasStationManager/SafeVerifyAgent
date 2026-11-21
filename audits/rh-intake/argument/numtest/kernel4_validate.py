"""NODE-NUMTEST4 validation.
 (1) exact global checks of the instance: Gram = I_4, Frobenius orders, isotropy sum_k f_k sigma^j(f_k) = delta_{j0}/lam;
 (2) th0 jets: reuse kernel3_lib (validated there against sigma^2(wp - e) to z^44);
 (3) engine vs brute force: J(a; n) by the direct 4-factor multinomial expansion in exact Z[eta] (no modulus),
     reduced mod p^K, against the pair-product engine, for all a <= 14 and all n with |n| <= 4;
 (4) engine with the other pairing of factors ((1,3),(2,4)) vs the default ((1,2),(3,4)) at large a.
usage: python3 -I kernel4_validate.py  -> out_kernel4_validate.txt
"""
import sys, os, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import comb, factorial
from kernel3_lib import th0_jets
from kernel4_lib import (F_BASIS, LAM_NUM, zmul, zpow, ztr, check_global, coeffs, frob_order, Ring,
                         pair_tables, pair_jets, final_jet, down_closure)

out = []
P = out.append
t0 = time.time()
P('NODE-NUMTEST4 validation')
for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
    ok, iso = check_global(p)
    P(f'  p={p:2d}  p mod 16={p % 16:2d}  ord(Frob_p|F)={frob_order(p)}  Gram==I4: {ok}   8*lam*sum_k f_k sigma^j f_k (j=0..3) -> '
      + ' '.join(str(zmul(LAM_NUM, s)) for s in iso))


def multinom(parts):
    n = sum(parts); r = factorial(n)
    for x in parts: r //= factorial(x)
    return r


from functools import lru_cache
zpow = lru_cache(maxsize=None)(zpow)

def brute(T, m, a, n):
    """exact element of Z[eta]."""
    tot = (0, 0, 0, 0)
    for ak in itertools.product(range(a + 1), repeat=4):
        if sum(ak) != a: continue
        # distribute each n_s among the 4 factors
        splits = []
        for s in range(3):
            splits.append([c for c in itertools.product(range(n[s] + 1), repeat=4) if sum(c) == n[s]])
        for sp in itertools.product(*splits):
            cf = multinom(ak)
            for s in range(3): cf *= multinom(sp[s])
            el = (cf, 0, 0, 0)
            for k in range(4):
                deg = ak[k] + sum(sp[s][k] for s in range(3))
                el = zmul(el, zpow(m[k][0], ak[k]))
                for s in range(3): el = zmul(el, zpow(m[k][s + 1], sp[s][k]))
                el = tuple(T[deg] * x for x in el)
            tot = tuple(u + v for u, v in zip(tot, el))
    return tot


for (cv, g2, g3, e, p) in [('Zw', 0, 4, 1, 5), ('Zi', 4, 0, 1, 11)]:
    T = th0_jets(g2, g3, e, 40)
    m = coeffs(p)
    R = Ring(p, 30)
    A = 14
    nlist = [n for n in itertools.product(range(5), repeat=3) if sum(n) <= 4]
    Pt12 = pair_tables(R, T, m[0][0], m[1][0], A, 4)
    Pt34 = pair_tables(R, T, m[2][0], m[3][0], A, 4)
    Q12 = pair_jets(R, Pt12, m[0], m[1], A, nlist)
    Q34 = pair_jets(R, Pt34, m[2], m[3], A, nlist)
    bad = tot = 0
    for a in range(A + 1):
        for n in nlist:
            if a > 9 and sum(n) > 2: continue
            ex = brute(T, m, a, n)
            en = R.unpack(final_jet(R, Q12, Q34, a, n))
            tot += 1
            if any((x - y) % R.q for x, y in zip(ex, en)): bad += 1
    P(f'  brute force vs engine, {cv} p={p}: {bad} mismatches / {tot} jets (a<=14, |n|<=4; a>9 only |n|<=2)')

# (4) other pairing at large a
for (cv, g2, g3, e, p, A, K) in [('Zw', 0, 4, 1, 5, 300, 90)]:
    T = th0_jets(g2, g3, e, A + 10)
    m = coeffs(p)
    R = Ring(p, K)
    nlist = [(0, 0, 0), (3, 0, 0), (0, 0, 3), (2, 0, 2), (0, 2, 0)]
    res = {}
    for name, (i1, i2, i3, i4) in [('(12)(34)', (0, 1, 2, 3)), ('(13)(24)', (0, 2, 1, 3))]:
        Pa = pair_tables(R, T, m[i1][0], m[i2][0], A, 4)
        Pb = pair_tables(R, T, m[i3][0], m[i4][0], A, 4)
        Qa = pair_jets(R, Pa, m[i1], m[i2], A, down_closure(nlist))
        Qb = pair_jets(R, Pb, m[i3], m[i4], A, down_closure(nlist))
        res[name] = {(a, n): final_jet(R, Qa, Qb, a, n) for a in (100, 199, 250, 300) for n in nlist}
    same = sum(1 for k in res['(12)(34)'] if res['(12)(34)'][k] == res['(13)(24)'][k])
    P(f'  pairing (12)(34) vs (13)(24), {cv} p={p}, a in (100,199,250,300), 5 n: identical {same}/{len(res["(12)(34)"])}')
    P('    v_p: ' + ' '.join(f'{a},{n}:{R.v(res["(12)(34)"][(a, n)])}' for (a, n) in sorted(res['(12)(34)'])))
P(f'time {time.time() - t0:.1f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kernel4_validate.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
