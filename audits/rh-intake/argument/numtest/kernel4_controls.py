"""NODE-NUMTEST4 controls, n'=4 instance, curve Z[w], p = 5, a <= 400.
 C1 scrambled jets: T_n -> p^{v(T_n)} * (random unit), coefficients unchanged.
 C2 broken isotropy: basis (f1 + f2, f2, f3, f4) (not orthonormal; sum_k f_k sigma(f_k) != 0 mod p).
 C3 isotropic only mod p: f1 -> f1 + p*(1,0,0,0)  (orthonormality and isotropy hold mod p, fail mod p^2).
 C4 precision: the true instance at two precisions (identical valuations required).
Per configuration: slope dv/da at n = 0 and the drops v(a,0) - v(a,n) on the three axes at a ~ 400.
usage: python3 -I kernel4_controls.py -> out_kernel4_controls.txt
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kernel3_lib import th0_jets
from kernel4_lib import (coeffs, Ring, pair_tables, pair_jets, final_jet, down_closure, gam, zmul, zsub, galois_elt,
                         positions, vp_fact)

p, A, W = 5, 400, 6
g = gam(p)
T0 = th0_jets(0, 4, 1, A + W + 4)
grid = [(0, 0, 0)] + [(i, 0, 0) for i in (2, 4, 6)] + [(0, 0, j) for j in (2, 4, 6)] + [(0, l, 0) for l in (2, 4, 6)]
nl = down_closure(grid)
asamp = list(range(200, A + 1, 40))


def vp(x):
    if x == 0: return 10 ** 9
    k = 0
    while x % p == 0: x //= p; k += 1
    return k


def run(T, m, K):
    R = Ring(p, K)
    P12 = pair_tables(R, T, m[0][0], m[1][0], A, W)
    P34 = pair_tables(R, T, m[2][0], m[3][0], A, W)
    Q12 = pair_jets(R, P12, m[0], m[1], A, nl)
    Q34 = pair_jets(R, P34, m[2], m[3], A, nl)
    V = {}
    for n in grid:
        for a in asamp:
            V[(a, n)] = R.v(final_jet(R, Q12, Q34, a, n))   # a, |n| even
    return V, K


def lsq(xs, ys):
    k = len(xs); mx = sum(xs) / k; my = sum(ys) / k
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)


out = []
P = out.append
P(f'NODE-NUMTEST4 controls: curve Z[w], p={p}, a in {asamp}; gamma_p={g:.4f}, 1/(p^2-1)={1 / (p * p - 1):.4f}')


def report(name, V, K):
    xs = [a for a in asamp if V[(a, (0, 0, 0))] < K]
    s = lsq(xs, [V[(a, (0, 0, 0))] for a in xs]) if len(xs) > 2 else float('nan')
    a = asamp[-1]
    v0 = V[(a, (0, 0, 0))]
    d = lambda n: v0 - V[(a, n)]
    P(f'  {name:44s} slope(n=0)={s:.4f}  v(400,0)={v0:3d}   drop at a=400 for n1=2,4,6: {d((2,0,0))},{d((4,0,0))},{d((6,0,0))}'
      f' | n3=2,4,6: {d((0,0,2))},{d((0,0,4))},{d((0,0,6))} | n2=2,4,6: {d((0,2,0))},{d((0,4,0))},{d((0,6,0))}')


t0 = time.time()
m = coeffs(p)
V, K = run(T0, m, int(g * A) + 50); report('true instance (K=p^%d)' % K, V, K)
V2, K2 = run(T0, m, int(g * A) + 90)
same = sum(1 for k in V if V[k] == V2[k])
P(f'  C4 precision p^{K} vs p^{K2}: identical valuations {same}/{len(V)}')

random.seed(1)
Ts = [0 if t == 0 else (p ** vp(t)) * random.choice([u for u in range(1, p ** 3) if u % p]) * random.choice([1, -1]) for t in T0]
V, K = run(Ts, m, int(g * A) + 50); report('C1 scrambled jets (p^v(T_n) * random unit)', V, K)

# C2: broken isotropy
mb = [[tuple(x + y for x, y in zip(m[0][s], m[1][s])) for s in range(4)]] + m[1:]
iso = [0, 0, 0, 0]
for k in range(4): iso = [u + v for u, v in zip(iso, zmul(mb[k][0], mb[k][1]))]
V, K = run(T0, mb, int(g * A) + 50); report(f'C2 basis (f1+f2,f2,f3,f4), sum f sigma f={tuple(iso)}', V, K)

# C3: f1 + p (orthonormal and isotropic mod p only) ; apply the Galois conjugates consistently
taus, _ = positions(p)
f1 = tuple(x + (p if i == 0 else 0) for i, x in enumerate(m[0][0]))
mc = [[zsub(f1, galois_elt(t)) for t in taus]] + m[1:]
iso = [0, 0, 0, 0]
for k in range(4): iso = [u + v for u, v in zip(iso, zmul(mc[k][0], mc[k][1]))]
V, K = run(T0, mc, int(g * A) + 50); report(f'C3 f1 -> f1 + p, sum f sigma f={tuple(iso)}', V, K)
P(f'time {time.time() - t0:.0f}s')
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out_kernel4_controls.txt'), 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
