# GL2 over Q_{q}, q=p^2 (unramified, n'=2), V = Sym^{k0}(std) (x) Sym^{k1}(std^sigma)  [vector parts only,
# same model as pair.py], H0 = monomial lattice.  W(L) = sum over the q+1 index-q sublattice neighbours L' of
# p^{k0+k1} HL(L'), inside HL(L).  Prints the p-adic elementary divisors of W(L) in HL(L).
# Same mathematics as pair.py, but exact arithmetic in Z_q / p^N (N > k0+k1 >= every ED) instead of Fractions.
# Usage: python3 -I pairfast.py p k0 k1 [k0 k1 ...]
import sys
from math import comb
from collections import Counter

def find_poly(p):
    for s in range(p):
        for r in range(p):
            if all((x*x - s*x - r) % p for x in range(p)): return s, r

def run(p, k0, k1):
    S, R = find_poly(p)
    N = k0 + k1 + 2; M = p**N
    def mul(a, b):
        x, y = a; u, v = b
        return ((x*u + R*y*v) % M, (x*v + y*u + S*y*v) % M)
    def add(a, b): return ((a[0]+b[0]) % M, (a[1]+b[1]) % M)
    def sig(a):  # Frobenius on Z_q: t -> S - t (the other root)
        x, y = a; return ((x + y*S) % M, (-y) % M)
    def pw(a, n):
        r = (1, 0)
        for _ in range(n): r = mul(r, a)
        return r
    def vl(a):
        x, y = a
        if x == 0 and y == 0: return N
        v = 0
        while x % p == 0 and y % p == 0: x //= p; y //= p; v += 1
        return v
    def inv(a):
        x, y = a; nn = (x*x + x*y*S - y*y*R) % M; ni = pow(nn, -1, M)
        return (((x + y*S)*ni) % M, (-y*ni) % M)
    def transform(k, i, ia, ib, ic, id_):
        co = [(0, 0)]*(k+1)
        Ap = [mul((comb(i, s) % M, 0), mul(pw(ia, s), pw(ib, i-s))) for s in range(i+1)]
        Bp = [mul((comb(k-i, s) % M, 0), mul(pw(ic, s), pw(id_, k-i-s))) for s in range(k-i+1)]
        for s1, u in enumerate(Ap):
            for s2, v in enumerate(Bp): co[s1+s2] = add(co[s1+s2], mul(u, v))
        return co
    cs = [(a, b) for a in range(p) for b in range(p)]
    # neighbour L' = g L, g = (p c; 0 1) or (1 0; 0 p).  p*g^{-1} = adj(g) is integral; p^{k0+k1} g^{-1} on
    # Sym^{k0} (x) Sym^{k1} = Sym^{k0}(adj g) (x) Sym^{k1}(adj g^sigma)  (degrees add up to k0+k1).
    nb = [((1, 0), ((-c[0]) % M, (-c[1]) % M), (0, 0), (p, 0)) for c in cs] + [((p, 0), (0, 0), (0, 0), (1, 0))]
    n = (k0+1)*(k1+1)
    rows = []
    for g in nb:
        gs = tuple(sig(x) for x in g)
        T0 = [transform(k0, i, *g) for i in range(k0+1)]
        T1 = [transform(k1, j, *gs) for j in range(k1+1)]
        for i in range(k0+1):
            for j in range(k1+1):
                r = [mul(T0[i][a], T1[j][b]) for a in range(k0+1) for b in range(k1+1)]
                rows.append(([x for x, _ in r], [y for _, y in r]))
    out = []; cols = set(range(n))
    while cols:
        best = None
        for ri, (X, Y) in enumerate(rows):
            for cj in cols:
                if X[cj] or Y[cj]:
                    v = vl((X[cj], Y[cj]))
                    if best is None or v < best[0]: best = (v, ri, cj)
                    if v == 0: break
            if best and best[0] == 0: break
        if best is None:  # remaining columns are >= N: record N as "large"
            out += [N]*len(cols); break
        v, ri, cj = best; out.append(v)
        PX, PY = rows.pop(ri)
        pv = (PX[cj], PY[cj])
        # pv = p^v * unit ; f = entry / pv computed as (entry/p^v) * unit^{-1}
        u = (pv[0]//p**v, pv[1]//p**v); ui = inv(u)
        new = []
        for X, Y in rows:
            e = (X[cj], Y[cj])
            if e[0] or e[1]:
                f = mul((e[0]//p**v, e[1]//p**v), ui)
                f0, f1 = f
                X = [(x - f0*a - R*f1*b) % M for x, a, b in zip(X, PX, PY)]
                Y = [(y - f0*b - f1*a - S*f1*b) % M for y, a, b in zip(Y, PX, PY)]
                if not (any(X) or any(Y)): continue
            new.append((X, Y))
        rows = new; cols.discard(cj)
    return sorted(out)

if __name__ == '__main__':
    p = int(sys.argv[1]); ks = [int(x) for x in sys.argv[2:]]
    q = p*p
    for k0, k1 in zip(ks[::2], ks[1::2]):
        ed = run(p, k0, k1); n = len(ed)
        mn = min(k1, k0/p)
        def frac_above(t): return sum(1 for e in ed if e > t)/n
        print("p=%d k0=%d k1=%d dim=%d mean=%.2f max=%d | min(k1,k0/p)=%.2f k0/p^2=%.2f (k0+p*k1)/(q+1)=%.2f"
              " | frac(ED>min)=%.3f frac(ED>min/2)=%.3f frac(ED>k0/p^2)=%.3f"
              % (p, k0, k1, n, sum(ed)/n, max(ed), mn, k0/q, (k0+p*k1)/(q+1),
                 frac_above(mn), frac_above(mn/2), frac_above(k0/q)))
        print("   ", sorted(Counter(ed).items()))
