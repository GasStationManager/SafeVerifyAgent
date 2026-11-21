"""NODE-NUMTEST3 controls.  w = 0 slice J(a,0) = d^a [th(z) th(c z)](0) unless stated; p-adic, exact mod p^K.
 C1  c with N(c) = -1 + p^k only (k = 1, 2, 3): how much of the gain needs exact isotropy?
 C2  wrong second Eisenstein value: th0 * exp(-s2 z^2/2) with s2 = 1, 1/7-free unit, and s2 = p.
 C3  scrambled jets: T_n -> p^{v(T_n)} * random unit (keeps every one-variable valuation).
 C4  sigma instead of the 2-torsion translate: Theta = sigma(z0+z1) sigma(c(z0-z1)) (NormRel for sigma* itself).
 C5  independent recomputation: global exact Gaussian-integer entries (kernel3_global) vs local engine with the
     global c = -(3-2i) beta/13 embedded in Z_{49}, Z_{121}.
usage: python3 -I kernel3_controls.py   -> out_kernel3_controls.txt
"""
import sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import comb
from kernel3_lib import th0_jets, Zp2, jets_grid, lt_pred, gam
from sigma_lib import sigma_derivs_stream, vp

t0 = time.time()
out = []; P = out.append
A = 600
def slice0(T, R, c, amax=A, step=1):
    """J(a,0) for all a <= amax, any parity of T (generic convolution)."""
    q = R.q
    cp = [(1, 0)]
    for k in range(amax + 1): cp.append(R.mul(cp[-1], c))
    res = {}
    for a in range(1, amax + 1, step):
        acc0 = acc1 = 0
        for k in range(a + 1):
            if T[k] == 0 or T[a - k] == 0: continue
            f = comb(a, k) * T[k] * T[a - k]
            g = cp[a - k]
            acc0 += f * g[0]; acc1 += f * g[1]
        res[a] = (acc0 % q, acc1 % q)
    return res

def report(tag, R, res, p, ref=lambda a: lt_pred(a, 0, p)):
    pts = [(a, R.v(x)) for a, x in res.items() if x != (0, 0) and a >= A // 2]
    n = len(pts); mx = sum(a for a, _ in pts) / n; my = sum(v for _, v in pts) / n
    sl = sum((a - mx) * (v - my) for a, v in pts) / sum((a - mx) ** 2 for a, _ in pts)
    d = min(R.v(x) - ref(a) for a, x in res.items() if x != (0, 0))
    alast = max(a for a, x in res.items() if x != (0, 0))   # identically-zero entries (symmetry) are skipped
    P(f'  {tag:52s} slope {sl:.4f} (gamma {gam(p):.4f}, 1/(p^2-1) {1/(p*p-1):.4f});  min_a[v - LT] = {d:8.2f};  v(J({alast},0)) = {R.v(res[alast])}, LT = {ref(alast):.1f}')

T = th0_jets(4, 0, 1, A + 5)
for p in (7, 11):
    K = int(gam(p) * A) + 40
    R = Zp2(p, K)
    P(f'\n== Z[i], e_t = 1, p = {p} (served configuration unless stated)')
    c = R.elt_of_norm(-1, 1)
    report('reference: N(c) = -1 exactly', R, slice0(T, R, c), p)
    # C1
    for k in (1, 2, 3):
        ck = R.elt_of_norm(-1 + p ** k, 1)
        if ck is None: ck = R.elt_of_norm(-1 + 2 * p ** k, 1)
        nk = (R.norm(ck) + 1) % R.q
        report(f'C1: N(c) = -1 + p^{vp(nk, p)}*unit', R, slice0(T, R, ck), p)
    # C2
    for s2 in (1, 3, p):
        Ts = th0_jets(4, 0, 1, A + 5, s2=s2)
        report(f'C2: wrong s2 = {s2}', R, slice0(Ts, R, c), p)
    # C3
    random.seed(1)
    for trial in range(2):
        Tr = [0] * len(T)
        for k, t in enumerate(T):
            if t == 0: continue
            vv = vp(t, p)
            u = random.randrange(1, p ** 6)
            while u % p == 0: u = random.randrange(1, p ** 6)
            Tr[k] = p ** vv * u * (1 if t > 0 else -1)
        report(f'C3: scrambled T_n (same v_p), trial {trial}', R, slice0(Tr, R, c), p)
# C4: sigma itself (odd), Theta = sigma(z) sigma(cz):  J(a,0) for even a
P('\n== C4: sigma(z) sigma(c z) (no 2-torsion translate); compare LT shifted by the z^2 zero: v_p(a!) - (a-3)/(p^2-1) - v_p(a(a-1))')
for (g2, g3, p) in [(4, 0, 7), (0, 4, 5), (0, 4, 11)]:
    D = sigma_derivs_stream(A + 3, {'c': (g2 // 2, 2 * g3)})['c']
    K = int(gam(p) * A) + 40
    R = Zp2(p, K)
    c = R.elt_of_norm(-1, 1)
    res = slice0(D, R, c)
    report(f'C4 g2={g2} g3={g3}: sigma(z)sigma(cz), N(c)=-1', R, res, p,
           ref=lambda a: lt_pred(a, 0, p) - vp(a * (a - 1), p) if a > 1 else 0)
    ca = R.elt_of_norm(1, 1) or R.elt_of_norm(1, 2) or (1, 0)
    res = slice0(D, R, ca)
    report(f'C4 g2={g2} g3={g3}: sigma(z)sigma(cz), N(c)=+1', R, res, p,
           ref=lambda a: lt_pred(a, 0, p) - vp(a * (a - 1), p) if a > 1 else 0)
    # sigma alone (NUMTEST): J = D^a sigma(0)
    sl = [(a, vp(D[a], p)) for a in range(A // 2, A + 1) if D[a]]
    n = len(sl); mx = sum(a for a, _ in sl) / n; my = sum(v for _, v in sl) / n
    s = sum((a - mx) * (v - my) for a, v in sl) / sum((a - mx) ** 2 for a, _ in sl)
    P(f'  {"   (NUMTEST reference) sigma alone":52s} slope {s:.4f}')
# C5: independent recomputation against kernel3_global's exact Gaussian integers
P('\n== C5: exact global entries (Gaussian integers, kernel3_global.Jstar) vs local p-adic engine with c = -(3-2i)beta/13')
import kernel3_global as KG  # runs its own (fast) table on import; we only use Jstar
for p in (7, 11, 19):
    K = 80
    R = Zp2(p, K, n0=p ** K - 1)     # theta^2 = -1, i.e. Z_{p^2} = Z_p[i] (p = 3 mod 4)
    b = R.sqrt_mod(-13)              # beta in Z_p (p served: (-13/p) = 1)
    inv13 = pow(13, -1, R.q)
    cg = R.smul(inv13, R.mul((-3 % R.q, 2), (b, 0)))   # -(3-2i) beta / 13
    assert R.norm(cg) == R.q - 1
    G = jets_grid(KG.T, R, cg, [0, 1, 2], 400)
    agree = tot = 0
    for a in range(20, 401, 20):
        for w in (0, 1, 2):
            aa = a if (a + w) % 2 == 0 else a + 1
            if aa > 400: continue
            Js = KG.Jstar(aa, w)
            vg = min(vp(Js[0], p) if Js[0] else 10 ** 9, vp(Js[1], p) if Js[1] else 10 ** 9)
            vl = R.v(G[(aa, w)])
            tot += 1; agree += (vg == vl)
    P(f'  p = {p}: {agree}/{tot} entries have identical v_p (global exact vs local engine)')
P(f'\nelapsed {time.time() - t0:.1f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kernel3_controls.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
