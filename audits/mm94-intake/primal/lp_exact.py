"""Exact-type version: constraints E only at the least profile's word types
   q*(a,a)   = (3a+1)/(6a-2),           q*(a,b) = (a+2b+1)/(2(a+2b-1))  for a<b<=4a-2,
plus F at all h, M. Prints optimum vs 6 log D*, the certificate, and the omega bound.
usage: python3 -I lp_exact.py a0 [a0 ...]"""
import sys, math, json
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
from lp_cert import Dstar, H, LOG2, LOG3

def qstar(a, b):
    return Fr(3*a+1, 6*a-2) if b == a else Fr(a+2*b+1, 2*(a+2*b-1))

def build(a0):
    idx = {}
    for a in range(2, a0+1):
        for b in range(a, 4*a): idx[(a, b)] = len(idx)
    class OutOfRange(Exception): pass
    def ref(a, b):
        if a > b: a, b = b, a
        if a == 1: return None, 6*math.log(b)
        if (a, b) not in idx: raise OutOfRange
        return idx[(a, b)], 0.0
    rows, rhs, tags, qs = [], [], [], []
    def add(terms, c, tag, q=None):
        row = {}; cc = c
        try:
            for (a, b), coef in terms:
                v, k = ref(a, b)
                if v is None: cc -= coef*k
                else: row[v] = row.get(v, 0.0) + coef
        except OutOfRange:
            return
        rows.append(row); rhs.append(cc); tags.append(tag); qs.append(q)
    for a in range(2, a0+1):
        for b in range(a, 4*a-1):
            q = qstar(a, b); qp = float(q)
            add([((a, b), 1.0), ((a, b+1), -qp), ((a, b-1), -(1-qp))], 6*H(qp) - 6*LOG2, ('E', a, b), q)
        for h in range(1, a+1):
            add([((a, 3*h+a-1), 1.0), ((a, h), -1.0)], 6*LOG3, ('F', a, h))
        for b in range(a, 4*a-1):
            add([((a, b+1), 1.0), ((a, b), -1.0)], 0.0, ('M', a, b))
    n, m = len(idx), len(rows)
    A = lil_matrix((m, n))
    for i, row in enumerate(rows):
        for v, coef in row.items(): A[i, v] = -coef
    c = np.zeros(n); c[idx[(a0, a0)]] = 1.0
    return idx, A.tocsr(), -np.array(rhs), c, tags, qs, rhs, rows

def omega_bound(a0):
    return 3*math.log(2*a0-1)/math.log(Dstar(a0))

if __name__ == '__main__':
    for a0 in map(int, sys.argv[1:]):
        idx, A, bub, c, tags, qs, rhs, rows = build(a0)
        res = linprog(c, A_ub=A, b_ub=bub, bounds=[(0, None)]*len(c), method='highs')
        assert res.status == 0, res.message
        target = 6*math.log(Dstar(a0))
        w = -res.ineqlin.marginals
        used = [i for i in range(len(w)) if w[i] > 1e-9]
        coef = np.zeros(len(idx))
        for i in used:
            for v, cf in rows[i].items(): coef[v] += w[i]*cf
        e = np.zeros(len(idx)); e[idx[(a0, a0)]] = 1
        kinds = {}
        for i in used: kinds[tags[i][0]] = kinds.get(tags[i][0], 0) + 1
        print(f"a0={a0:4d} vars={len(idx):7d} cons={len(tags):7d}  LP={res.fun:.6f}  6logD*={target:.6f}  diff={res.fun-target:+.2e}  "
              f"cert: {len(used)} constraints {kinds}  identity err={np.abs(coef-e).max():.1e}  "
              f"omega<= {omega_bound(a0):.5f}")
        json.dump({'a0': a0, 'opt': res.fun, 'target': target,
                   'cert': [(tags[i], (str(qs[i]) if qs[i] is not None else None), float(w[i])) for i in used]},
                  open(f'/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/mm94/certx_{a0}.json', 'w'))
