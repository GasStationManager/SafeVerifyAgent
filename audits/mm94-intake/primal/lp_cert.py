"""LP form of the paper's growth lemma (mm94 §5), and its dual certificate.

Variables L(a,b) = log lambda(S(a,b)), S(a,b) = tensor_{pi in S3} C(a,b)^pi, with the
character-dependent normalisation t set to 1 (all constraints are homogeneous in (L,t)).
Each constraint is a PRIMAL degeneration of the paper, read with a character:
  (E_{a,b,q})  L(a,b) + 6 log 2 >= 6 H(q) + q+ L(a,b+1) + q- L(a,b-1)
               [Lemma 4.1 degeneration + Cor 3.2 at a FIXED word type q, all six legs]
  (F_{a,h})    L(a,3h+a-1) >= 6 log 3 + L(a,h)          [Lemma 4.2 + Cor 3.2, uniform type]
  (B)          L(1,b) = L(b,1) = 6 log b                 [C(1,b) = B_X(b); S(1,b) = T_b^{(x)2}]
  (M)          L(a,b) <= L(a,b+1)                        [C(a,b) <= C(a,b+1), restriction]
  symmetry     L(a,b) = L(b,a)                            [S(a,b) = S(b,a) as tensors]
Goal: minimise L(a0,a0); the paper's Lemma 5.1 says >= 8 log a0, the least profile gives
6 log D*(a0), D*(a) = (3a-1)/2 * prod_{m<a} (1 + 1/(3m)).
The dual multipliers of an optimal solution are a nonnegative combination of primal
degenerations whose net effect is  S(a0,a0) (x) T_A (x) Cat  >~  T_B (x) Cat  with
log(B/A) = (1/3) * optimum. Usage: python3 -I lp_cert.py a0 [K]  (K = q-grid size, 0 = q* only)
"""
import sys, math, json
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

LOG2, LOG3 = math.log(2), math.log(3)
def H(qp): return -(qp*math.log(qp) + (1-qp)*math.log(1-qp)) if 0 < qp < 1 else 0.0

def Dstar(a):
    p = Fr(1)
    for m in range(1, a): p *= 1 + Fr(1, 3*m)
    return Fr(3*a-1, 2) * p

def build(a0, qsets):
    """qsets[(a,b)] = list of q+ values to include for constraint E at (a,b)."""
    idx = {}
    for a in range(2, a0+1):
        for b in range(a, 4*a):
            idx[(a, b)] = len(idx)
    n = len(idx)
    const = {}  # boundary values
    def ref(a, b):
        """return (var index or None, constant) for L(a,b)"""
        if a > b: a, b = b, a
        if a == 1: return None, 6*math.log(b)
        return idx[(a, b)], 0.0
    rows, rhs, tags = [], [], []
    def add(terms, c, tag):
        """constraint  sum coef*L >= c  ; terms list of ((a,b),coef)"""
        row = {}; cc = c
        for (a, b), coef in terms:
            v, k = ref(a, b)
            if v is None: cc -= coef*k
            else: row[v] = row.get(v, 0.0) + coef
        rows.append(row); rhs.append(cc); tags.append(tag)
    for a in range(2, a0+1):
        for b in range(a, 4*a-1):          # b in [a, 4a-2]
            for qp in qsets.get((a, b), []):
                add([((a, b), 1.0), ((a, b+1), -qp), ((a, b-1), -(1-qp))], 6*H(qp) - 6*LOG2, ('E', a, b, qp))
        for h in range(1, a+1):            # 3h+a-1 <= 4a-1
            add([((a, 3*h+a-1), 1.0), ((a, h), -1.0)], 6*LOG3, ('F', a, h))
        for b in range(a, 4*a-1):
            add([((a, b+1), 1.0), ((a, b), -1.0)], 0.0, ('M', a, b))
    m = len(rows)
    A = lil_matrix((m, n))
    for i, row in enumerate(rows):
        for v, coef in row.items(): A[i, v] = -coef     # -A x <= -rhs
    bub = -np.array(rhs)
    c = np.zeros(n); c[idx[(a0, a0)]] = 1.0
    return idx, A.tocsr(), bub, c, tags, rhs, rows

def solve(a0, qsets):
    idx, A, bub, c, tags, rhs, rows = build(a0, qsets)
    res = linprog(c, A_ub=A, b_ub=bub, bounds=[(0, None)]*len(c), method='highs')
    assert res.status == 0, res.message
    return res, idx, tags, rhs, rows

def grid_qsets(a0, K):
    qs = [k/K for k in range(1, K)]
    return {(a, b): qs for a in range(2, a0+1) for b in range(a, 4*a-1)}

def qstar_from_L(a0, L, idx):
    """q*(a,b) = (P(a,b+1), P(a,b-1)) / sum, P = exp(L/6)."""
    def P(a, b):
        if a > b: a, b = b, a
        if a == 1: return float(b)
        return math.exp(L[idx[(a, b)]]/6)
    return {(a, b): [P(a, b+1)/(P(a, b+1)+P(a, b-1))] for a in range(2, a0+1) for b in range(a, 4*a-1)}

if __name__ == '__main__':
    a0 = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 32
    target = 6*math.log(Dstar(a0)); goal84 = 8*math.log(a0)
    if K > 0:
        res, idx, tags, rhs, rows = solve(a0, grid_qsets(a0, K))
        print(f"a0={a0} grid K={K}: LP min L(a0,a0) = {res.fun:.6f}   6 log D* = {target:.6f}   8 log a0 = {goal84:.6f}   vars={len(idx)} cons={len(tags)}")
        qs = qstar_from_L(a0, res.x, idx)
    else:
        # exact least profile q*: from the rational least table (paper's chain is tight on it)
        qs = None
    # second pass with q* only (from the grid solution's optimal L, rounded to the rational q* of the least profile)
    if qs is not None:
        res2, idx2, tags2, rhs2, rows2 = solve(a0, qs)
        print(f"a0={a0} q* only  : LP min L(a0,a0) = {res2.fun:.6f}   (vars={len(idx2)} cons={len(tags2)})")
        w = -res2.ineqlin.marginals
        used = [(tags2[i], w[i]) for i in range(len(w)) if w[i] > 1e-9]
        print("certificate support:", len(used), "constraints; sum of weights", sum(x for _, x in used))
        # verify the identity: sum_i w_i row_i == e_{a0,a0}, sum_i w_i rhs_i == optimum
        coef = np.zeros(len(idx2))
        for i in range(len(w)):
            for v, cf in rows2[i].items(): coef[v] += w[i]*cf
        e = np.zeros(len(idx2)); e[idx2[(a0, a0)]] = 1
        print("max |sum w_i row_i - e_(a0,a0)| =", float(np.abs(coef-e).max()), "   sum w_i rhs_i =", float(sum(w[i]*rhs2[i] for i in range(len(w)))))
        for tag, x in sorted(used, key=lambda t: (t[0][0], t[0][1], t[0][2])):
            print("  ", tag, round(x, 6))
        json.dump({'a0': a0, 'opt': res2.fun, 'target': target, 'cert': [(list(map(float, t[1:])) if t[0]=='E' else list(t[1:]), t[0], float(x)) for t, x in used]},
                  open(f'/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/mm94/cert_{a0}.json', 'w'))
