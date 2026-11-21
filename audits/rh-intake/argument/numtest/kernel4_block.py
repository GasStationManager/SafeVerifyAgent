"""NODE-NUMTEST4 (T2): a 2x2 block of matrix entries with column-minor operators, n'=4 instance, p = 5 (curve Z[w]).

The Lean's kernel for an N' x N matrix variable is thZero = tensPow(thMM) = prod_{i,j} thMM(z_{.,i,j})
(LateralTheory.lean:34-35), so for the standard lattice the block kernel is Theta_blk(Z) = prod_{i,j in {1,2}} Theta(Z_{.,i,j}),
Theta the one-entry n'=4 kernel of kernel4_lib.  X = Z_{pos 0} (the top), Y = Z_{pos s} (s = 1 or 3, the partner).
Operators (applyD, FGS:256 -> jet of each monomial; the jet of a product of independent entries factorises):
  (a)  P = (xi1 X11 + xi2 X21)^a * det(Y)^m                    m minors of height 2 (weight 2m) at a non-top
  (b)  P = X21^a * Y11^(nu1-nu2) * det(Y)^nu2                   overhang in row 1, top direction row 2
  (c)  P = X11^a * Y11^(nu1-nu2) * det(Y)^nu2                   overhang in the same row as the top direction
  (d)  P = (xi1 X11 + xi2 X21)^a * Y11^w                         single-entry control (cap = derivative order)
Predictions: Lean cap at a non-top = number of minors coupled (HitsCapPos / MinorHits, SAB:42,58; cap FGS:36):
  loss <= sum_e min(a/p^e, cap); 'derivative order' alternative cap = total Y-degree in the coupled column(s).
usage: python3 -I kernel4_block.py [A]  -> out_kernel4_block.txt
"""
import sys, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import comb
from kernel3_lib import th0_jets
from kernel4_lib import coeffs, Ring, pair_tables, pair_jets, final_jet, down_closure, gam, vp_fact

A = int(sys.argv[1]) if len(sys.argv) > 1 else 320
p, M = 5, 6
g = gam(p)
t0 = time.time()
T = th0_jets(0, 4, 1, A + 2 * M + 6)
K = int(g * (A + 4 * M)) + 60
R = Ring(p, K)
m = coeffs(p)
idx = {1: lambda n: (n, 0, 0), 3: lambda n: (0, 0, n)}
nl = down_closure([idx[1](2 * M), idx[3](2 * M)])
P12 = pair_tables(R, T, m[0][0], m[1][0], A, 2 * M)
P34 = pair_tables(R, T, m[2][0], m[3][0], A, 2 * M)
Q12 = pair_jets(R, P12, m[0], m[1], A, nl)
Q34 = pair_jets(R, P34, m[2], m[3], A, nl)
# single-entry jets: J[s][(r, n)] for r <= A (r + n even), n <= 2M, s in {1,3}
J = {1: {}, 3: {}}
for s in (1, 3):
    for n in range(2 * M + 1):
        for r in range(A + 1):
            if (r + n) % 2 == 0:
                J[s][(r, n)] = final_jet(R, Q12, Q34, r, idx[s](n))
            else:
                J[s][(r, n)] = 0
t1 = time.time()
ONE = R.pack((1, 0, 0, 0))


def scal(c): return R.pack((c % R.q, 0, 0, 0))


def detpow_terms(nu1, nu2):
    """Y11^(nu1-nu2) det(Y)^nu2 as {(y11,y12,y21,y22): coeff}."""
    out = {}
    for k in range(nu2 + 1):
        c = comb(nu2, k) * (-1) ** (nu2 - k)
        key = (nu1 - nu2 + k, nu2 - k, nu2 - k, k)
        out[key] = out.get(key, 0) + c
    return out


def block_jet(s, a, xi, ymono):
    """sum over r and Y-monomials; entries: 11 (X:r, Y:y11), 21 (X:a-r, Y:y21), 12 (0, y12), 22 (0, y22)."""
    xi1, xi2 = xi
    p1 = [ONE]; p2 = [ONE]
    for _ in range(a): p1.append(R.mul(p1[-1], xi1)); p2.append(R.mul(p2[-1], xi2))
    tot = 0
    Js = J[s]
    for (y11, y12, y21, y22), c in ymono.items():
        if not isinstance(c, tuple) and c == 0: continue
        rest = R.mul(Js[(0, y12)], Js[(0, y22)])
        if rest == 0: continue
        sub = 0
        for r in range(a + 1):
            j1, j2 = Js[(r, y11)], Js[(a - r, y21)]
            if j1 == 0 or j2 == 0: continue
            w = R.mul(R.mul(p1[r], p2[a - r]), R.mul(j1, j2))
            sub += (comb(a, r) % R.q) * w
        cp = c[1] if isinstance(c, tuple) else scal(c)
        tot += R.mul(cp, R.mul(R.reduce4(sub), rest))
    return R.reduce4(tot)


def overhang_generic(zeta, o, nu2):
    """(zeta1 Y11 + zeta2 Y21)^o det(Y)^nu2 with ring coefficients ('r', packed)."""
    out = {}
    z1 = [ONE]; z2 = [ONE]
    for _ in range(o): z1.append(R.mul(z1[-1], zeta[0])); z2.append(R.mul(z2[-1], zeta[1]))
    for i in range(o + 1):
        ci = R.mul(scal(comb(o, i)), R.mul(z1[i], z2[o - i]))
        for k in range(nu2 + 1):
            c = R.mul(ci, scal(comb(nu2, k) * (-1) ** (nu2 - k)))
            key = (i + k, nu2 - k, o - i + nu2 - k, k)
            prev = out.get(key, ('r', 0))[1]
            out[key] = ('r', R.reduce4(prev + c))
    return out


xiG = (R.pack((1, 1, 0, 0)), R.pack((2, 0, 1, 0)))        # generic row direction (units of Z_{p^4})
xiE1 = (ONE, 0); xiE2 = (0, ONE)


def loss_lean(a, s, cap):
    e, L = 1, 0.0
    while p ** e <= a:
        if e % 4 == s: L += min(a / p ** e, cap)
        e += 2
    return L


out = []
P = out.append
P(f'NODE-NUMTEST4 (T2) 2x2 block, n\'=4 instance, Z[w], p={p}, A={A}, precision p^{K}; time {t1 - t0:.0f}s for single-entry tables')
P('Each line: v = v_p(block jet); v0 = v at the same a with the Y-operator removed (Y-degree 0); drop = v0 + gam*degY - v')
P('  [loss beyond the gamma-law];  Lc = Lean loss sum_e min(a/p^e, cap) with cap = number of minors (nu2 for the')
P('  (b),(c) shapes = the Lean cap at a top);  Lw = same with cap = the Y-weight |nu| (the rank-one reading, cap = w).')
for s in (1, 3):
    for a0 in (A // 2, A):
        P(f'\n position s={s} (e={s} partner), a ~ {a0}, a/p^{s}={a0 / p ** s:.2f}')
        zeta = (R.pack((3, 0, 1, 1)), R.pack((1, 2, 0, 0)))   # a second generic direction, for (e)
        cases = (
                [(f'(a) generic xi, det^{mm}', xiG, detpow_terms(mm, mm), mm, 2 * mm) for mm in (2, 4, 6)] +
                [(f'(d) generic xi, Y11^{w}', xiG, {(w, 0, 0, 0): 1}, w, w) for w in (2, 4, 6)] +
                [(f'(b) xi=e2, Y11^{n1 - n2} det^{n2} (nu=({n1},{n2}))', xiE2, detpow_terms(n1, n2), n2, n1 + n2)
                 for (n1, n2) in ((4, 2), (6, 2), (6, 4), (8, 4))] +
                [(f'(c) xi=e1, Y11^{n1 - n2} det^{n2} (nu=({n1},{n2}))', xiE1, detpow_terms(n1, n2), n2, n1 + n2)
                 for (n1, n2) in ((4, 2), (6, 2), (6, 4), (8, 4))] +
                [(f'(e) generic xi, generic zeta overhang, nu=({n1},{n2})', xiG, overhang_generic(zeta, n1 - n2, n2), n2, n1 + n2)
                 for (n1, n2) in ((4, 2), (6, 2), (6, 4))])
        for name, xi, mk, capC, degY in cases:
            a = a0 if (a0 + degY) % 2 == 0 else a0 - 1
            # reference: Y-degree 0, same xi, same parity class -> use a' = a (degY even) or a-1+1
            aref = a if (a % 2 == 0) else a - 1
            v = R.v(block_jet(s, a, xi, mk))
            vref = R.v(block_jet(s, aref, xi, {(0, 0, 0, 0): 1}))
            drop = vref + g * (a - aref) + g * degY - v
            zero = ' EXACT ZERO' if v >= K else ''
            P(f'   {name:46s} a={a}: v={v:4d}  v0={vref:4d}  drop={drop:6.2f}  Lc={loss_lean(a, s, capC):5.2f}  '
              f'Lw={loss_lean(a, s, degY):5.2f}   v-(gam*a-Lc)={v - (g * a - loss_lean(a, s, capC)):+.2f}  '
              f'v-(gam*a-Lw)={v - (g * a - loss_lean(a, s, degY)):+.2f}{zero}')

# (f) two copies: at one place of the Lean host E_L = Q(sqrt-d, sqrt-q, eta), z = ((1,1),h) fixes sqrt-q, so (inferred)
#     Theta_v(z) = Psi(c1 z) Psi(c2 z) with Psi the one-entry kernel above and c_k = iota_p(abar_k) in Z_{p^2}; we take
#     c1 = 1, c2 = eta^2 (a unit of Z_{p^2} = Z_p[eta^2] at p = 5) as a stand-in.
P('\n(f) two-copy product Psi(z) Psi(c z), c = eta^2 (structure of one place of the Lean host with sqrt(-q); inferred):')
c = R.pack((0, 0, 1, 0))
cp = [ONE]
for _ in range(A + 2 * M): cp.append(R.mul(cp[-1], c))
for s in (1, 3):
    for a in (A // 2, A):
        vs = []
        for n in range(0, 2 * M + 1, 2):
            tot = 0
            for b in range(a + 1):
                for n1 in range(n + 1):
                    j1, j2 = J[s][(b, n1)], J[s][(a - b, n - n1)]
                    if j1 == 0 or j2 == 0: continue
                    tot += (comb(a, b) * comb(n, n1) % R.q) * R.mul(cp[a - b + n - n1], R.mul(j1, j2))
            vs.append((n, R.v(R.reduce4(tot)), R.v(J[s][(a, n)])))
        P(f'  s={s} a={a}: (n: v_two-copy / v_one-copy / Lean loss) ' + '  '.join(
            f'{n}:{v2}/{v1}/{loss_lean(a, s, n):.2f}' for n, v2, v1 in vs))
P(f'\ntotal time {time.time() - t0:.0f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kernel4_block.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
