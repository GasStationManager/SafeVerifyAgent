"""NODE-NUMTEST5 negative controls, n'=2 engine (signal5_lib.grid2), same grid shape as the main run.
Each control replaces one ingredient of the served signal-place kernel th0(z0+z1) th0(c(z0-z1)), N(c) = -1, p inert:
 C1 split prime (p split in K; the formal group is ordinary)                        expected: no gain at all
 C2 inert prime, anisotropic direction N(c) = +1 (Frob_p = c: inert, not a signal/served place)  expected: sigma-level only
 C3 wrong Gaussian: th0 * exp(-s2 z^2/2) with s2 = 1 (wrong Eisenstein correction)  expected: gain destroyed
 C4 non-CM curve (j not a CM j-invariant), same construction, at an ordinary and at a supersingular prime
 C5 scrambled jets T_n -> p^{v(T_n)} * random unit                                     expected: gain destroyed
Reported per control: #(v < P1 - 1) out of all points with a >= 2p; min(v - P1); v on the kink slice; slope dv/da at nu = 0.
usage: python3 -I signal5_controls.py -> out_signal5_controls.txt
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kernel3_lib import th0_jets, Zp2, gam
from signal5_lib import grid2, P1, lp_opt

A, W = 300, 90
out = []; P = out.append
t0 = time.time()


def vint(x, p):
    if x == 0: return 10 ** 9
    k = 0
    while x % p == 0: x //= p; k += 1
    return k


def ap(g2, g3, p):
    """a_p of y^2 = 4x^3 - g2 x - g3 (p odd, good reduction)."""
    n = 1
    for x in range(p):
        r = (4 * x ** 3 - g2 * x - g3) % p
        n += 1 + (0 if r == 0 else (1 if pow(r, (p - 1) // 2, p) == 1 else -1))
    return p + 1 - n


def jinv(g2, g3):
    from fractions import Fraction
    return Fraction(1728 * g2 ** 3, g2 ** 3 - 27 * g3 ** 2)


def lsq(xs, ys):
    n = len(xs); mx = sum(xs) / n; my = sum(ys) / n
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)


def run(tag, T, p, cnorm, scramble=False):
    g = gam(p)
    K = int(g * (A + W)) + 40
    R = Zp2(p, K)
    c = R.elt_of_norm(cnorm, 1) or R.elt_of_norm(cnorm, 2) or R.elt_of_norm(cnorm, 3)
    Tq = [t % R.q for t in T]
    if scramble:
        random.seed(11)
        Tq = []
        for t in T:
            if t == 0: Tq.append(0); continue
            u = random.randrange(1, p ** 6)
            while u % p == 0: u = random.randrange(1, p ** 6)
            Tq.append(p ** vint(abs(t), p) * u % R.q)
    G = grid2(Tq, R, c, A, W)
    V = {k: R.v(x) for k, x in G.items()}
    cap = lambda n: (lambda e: n)
    pts = [k for k in V if k[0] >= 2 * p and V[k] < K]
    viol = [k for k in pts if V[k] < P1(k[0], cap(k[1]), p) - 1]
    worst = min((V[k] - P1(k[0], cap(k[1]), p), k) for k in pts)
    xs = [a for a in range(A // 2, A + 1, 2) if V[(a, 0)] < K]
    sl = lsq(xs, [V[(a, 0)] for a in xs])
    a0 = 250 if p == 5 else (7 * 35 if p == 7 else A)
    a0 -= a0 % 2
    kk = a0 // p
    sl_b = ' '.join(f'{nu}:{V[(a0 - (a0 + nu) % 2, nu)]}/{P1(a0 - (a0 + nu) % 2, cap(nu), p):.0f}'
                    for nu in sorted(set([0, kk // 4, kk // 2, 3 * kk // 4, kk, 5 * kk // 4, 3 * kk // 2])) if nu <= W)
    P(f'  {tag:58s} p={p:2d}  #(v<P1-1) = {len(viol):5d}/{len(pts)}  min(v-P1) = {worst[0]:+8.2f} at {worst[1]}  '
      f'slope(nu=0) = {sl:.4f} [gamma {g:.4f}, 1/(p^2-1) {1/(p*p-1):.4f}]')
    P(f'  {"":58s}       slice a={a0} (nu: v/P1): {sl_b}')
    return len(viol)


P(f'NODE-NUMTEST5 controls (n\'=2 engine, a <= {A}, nu <= {W}).  Reference rows first (served signal kernel).')
Tw = th0_jets(0, 4, 1, A + W + 4)
Ti = th0_jets(4, 0, 1, A + W + 4)
P('\n REFERENCE (served: p inert in K, N(c) = -1)')
run('Z[w] served', Tw, 5, -1)
run('Z[i] served', Ti, 7, -1)
P('\n C1 split primes (N(c) = -1 in the unramified Z_{p^2})')
run('Z[w], p = 7 split', Tw, 7, -1)
run('Z[w], p = 13 split', Tw, 13, -1)
run('Z[i], p = 5 split', Ti, 5, -1)
P('\n C2 inert prime, anisotropic N(c) = +1 (not a signal place)')
run('Z[w], p = 5, N(c) = +1', Tw, 5, 1)
run('Z[i], p = 7, N(c) = +1', Ti, 7, 1)
P('\n C3 wrong Gaussian s2 = 1 (and s2 = p: p-adically small, should NOT matter)')
run('Z[w], p = 5, s2 = 1', th0_jets(0, 4, 1, A + W + 4, s2=1), 5, -1)
run('Z[i], p = 7, s2 = 1', th0_jets(4, 0, 1, A + W + 4, s2=1), 7, -1)
run('Z[w], p = 5, s2 = 5 (p-adically small perturbation)', th0_jets(0, 4, 1, A + W + 4, s2=5), 5, -1)
P('\n C4 non-CM curves y^2 = 4x^3 - g2 x - g3 with 2-torsion e = 1 (4 - g2 - g3 = 0), s2 = 0, served-type c')
found = {}
for g2 in range(-40, 42, 2):
    g3 = 4 - g2
    if g2 ** 3 - 27 * g3 ** 2 == 0: continue
    j = jinv(g2, g3)
    if j in (0, 1728, -3375, 8000, -32768, 54000, 287496, -884736, -12288000, 16581375, -884736000,
             -147197952000, -262537412640768000): continue
    disc = g2 ** 3 - 27 * g3 ** 2
    for p in (5, 7):
        if disc % p == 0: continue
        a = ap(g2, g3, p)
        kind = 'supersingular' if a % p == 0 else 'ordinary'
        if (p, kind) not in found: found[(p, kind)] = (g2, g3, j, a)
for (p, kind), (g2, g3, j, a) in sorted(found.items()):
    T = th0_jets(g2, g3, 1, A + W + 4)
    run(f'non-CM g2={g2},g3={g3} (j={j}), a_p={a}, {kind}', T, p, -1)
P('\n C5 scrambled jets')
run('Z[w], p = 5, scrambled T_n', Tw, 5, -1, scramble=True)
run('Z[i], p = 7, scrambled T_n', Ti, 7, -1, scramble=True)
P(f'\nelapsed {time.time() - t0:.0f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_signal5_controls.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
