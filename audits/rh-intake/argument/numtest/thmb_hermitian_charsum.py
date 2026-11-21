"""NODE-THMB Part 2 hand check.
Lean leaf `term_integral_near_one_bound` (FM/TermIntegralNearOneBoundStatement.lean):
 for U = Lambda ∩ perp(Ysp J) (an O_E-lattice), InZ(u) <=> h(u,u) in varpi^a O_F,
  (i)  | vol{u in U: InZ u} * q^a - 1 |                       <= 8/7 q^{-(k-2r-4)}
  (iii)| ∫_{u in U, InZ u} psi0(h(y,u)) du | * q^a            <= 8/7 q^{-(k-2r-4)}
        whenever u -> psi0(h(y,u)) is nontrivial on U.
Model: E/F unramified, U = O_E^n with the standard (unimodular) hermitian form
h(x,y)=sum x_i conj(y_i), computed modulo varpi^a (a=1,2), psi0 = psi_F o Tr, conductor O.
We compute exactly by brute force for small n and compare with q^{-(n-1)}.
"""
import itertools, cmath, sys

def ring(q, a, d):
    # O_E / q^a = (Z/q^a)[sqrt d], elements (x0,x1) meaning x0 + x1 sqrt d
    M = q**a
    els = [(x, y) for x in range(M) for y in range(M)]
    return M, els

def run(q, a, d, n, ys):
    M, els = ring(q, a, d)
    def conj(z): return (z[0], (-z[1]) % M)
    def mul(z, w): return ((z[0]*w[0] + d*z[1]*w[1]) % M, (z[0]*w[1] + z[1]*w[0]) % M)
    def add(z, w): return ((z[0]+w[0]) % M, (z[1]+w[1]) % M)
    def tr(z): return (2*z[0]) % M
    total = 0; inZ = 0
    sums = {tuple(y): 0j for y in ys}
    for u in itertools.product(els, repeat=n):
        total += 1
        nrm = (0, 0)
        for ui in u: nrm = add(nrm, mul(ui, conj(ui)))
        if nrm[0] % M != 0:  # h(u,u) is in F; condition h(u,u) in q^a O
            continue
        inZ += 1
        for y in ys:
            s = (0, 0)
            for yi, ui in zip(y, u): s = add(s, mul(yi, conj(ui)))
            sums[tuple(y)] += cmath.exp(2j*cmath.pi*tr(s)/M)
    A = inZ / total * q**a - 1
    out = []
    for y in ys:
        out.append((y, abs(sums[tuple(y)]) / total * q**a))
    return A, out

cases = [ (3,1,-1,n) for n in (1,2,3,4,5) ] + [ (5,1,2,n) for n in (1,2,3,4) ] + [ (3,2,-1,n) for n in (1,2,3) ]
print("q a n | rel.count err A | max rel char sum C | q^-(n-1)")
for q,a,d,n in cases:
    M = q**a
    ys = []
    ys.append([(1,0)] + [(0,0)]*(n-1))            # primitive y
    if n >= 2: ys.append([(1,0),(0,1)] + [(0,0)]*(n-2))
    if a == 2: ys.append([(q,0)] + [(0,0)]*(n-1))  # y in varpi O, still nontrivial
    A, out = run(q,a,d,n,ys)
    C = max(c for _,c in out)
    print(f"{q} {a} {n} | {A:+.6f} | {C:.6f} | {q**-(n-1):.6f}  " + "  ".join(f"{c:.6f}" for _,c in out))
