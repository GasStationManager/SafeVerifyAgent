"""Exact rational certificate for small a0: take the LP support, solve the linear identity
sum_i w_i row_i = e_{(a0,a0)} in Fractions, and print the resulting primal statement.
usage: python3 exact_cert.py a0"""
import sys, json, math
from fractions import Fraction as Fr
from lp_exact import qstar
from lp_cert import Dstar
a0 = int(sys.argv[1])
cert = json.load(open(f'/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/mm94/certx_{a0}.json'))['cert']
# variables: all (a,b) with 2<=a<=a0, a<=b<=4a-1 ; boundary (1,b)
def key(a, b):
    if a > b: a, b = b, a
    return (a, b)
rows = []   # list of (dict var->Fraction coef, tag, q)
for tag, q, w in cert:
    kind, a, b = tag[0], tag[1], tag[2]
    if kind == 'E':
        q = Fr(q)
        rows.append(({key(a, b): Fr(1), key(a, b+1): -q, key(a, b-1): -(1-q)}, tag, q, w))
    else:  # F a h
        h = b
        rows.append(({key(a, 3*h+a-1): Fr(1), key(a, h): Fr(-1)}, tag, None, w))
# unknown weights x_i (Fractions). Equations: for each non-boundary variable v: sum_i x_i row_i[v] = [v==(a0,a0)]
vars_ = sorted({v for r, *_ in rows for v in r if v[0] >= 2})
import sympy
X = sympy.symbols(f'x0:{len(rows)}')
eqs = []
for v in vars_:
    eqs.append(sum(sympy.Rational(r[v].numerator, r[v].denominator)*X[i] for i, (r, *_) in enumerate(rows) if v in r) - (1 if v == (a0, a0) else 0))
sol = sympy.linsolve(eqs, X)
sol = list(sol)[0]
free = [s for s in sol if s.free_symbols]
if free:
    # pick the LP solution's values for the free symbols (round to rationals)
    subs = {}
    for i, s in enumerate(sol):
        if s.free_symbols and s in X:
            subs[s] = sympy.nsimplify(rows[i][3], rational=True, tolerance=1e-6)
    sol = [s.subs(subs) for s in sol]
w = [Fr(int(s.p), int(s.q)) for s in sol]
assert all(x >= 0 for x in w), w
# constant term: sum w_i * (boundary contributions and entropy terms) -> log of the T-ratio
# Each E: L(a,b) + 6log2 >= 6H(q) + q L(a,b+1) + (1-q) L(a,b-1); each F: L(a,B) >= 6 log3 + L(a,h)
# Collect: T-cost on LHS: 6 log 2 per E weight; T-gain on RHS: 6H(q) per E, 6 log 3 per F; boundary L(1,b)=6 log b moves to the side it is on.
lhs_log = 0.0; rhs_log = 0.0; S_left = {}; S_right = {}
def addS(d, v, c):
    d[v] = d.get(v, Fr(0)) + c
for (r, tag, q, _), x in zip(rows, w):
    if x == 0: continue
    if tag[0] == 'E':
        a, b = tag[1], tag[2]
        lhs_log += float(x)*6*math.log(2); rhs_log += float(x)*6*(-(float(q)*math.log(float(q)) + (1-float(q))*math.log(1-float(q))))
        for v, c in r.items():
            if v[0] == 1:   # boundary: value 6 log b
                if c > 0: lhs_log += float(x*c)*6*math.log(v[1])
                else: rhs_log += float(-x*c)*6*math.log(v[1])
            else:
                if c > 0: addS(S_left, v, x*c)
                else: addS(S_right, v, -x*c)
    else:
        a, h = tag[1], tag[2]
        rhs_log += float(x)*6*math.log(3)
        for v, c in r.items():
            if v[0] == 1:
                if c > 0: lhs_log += float(x*c)*6*math.log(v[1])
                else: rhs_log += float(-x*c)*6*math.log(v[1])
            else:
                if c > 0: addS(S_left, v, x*c)
                else: addS(S_right, v, -x*c)
den = 1
for x in w: den = den*x.denominator//math.gcd(den, x.denominator)
print(f"a0={a0}: exact weights (x denominator {den}):")
for (r, tag, q, _), x in zip(rows, w):
    if x: print("  ", tag, "q=" + str(q) if q is not None else "", "weight", x, "=", x*den, "/", den)
print("S-factors LHS:", {k: str(v) for k, v in S_left.items()})
print("S-factors RHS:", {k: str(v) for k, v in S_right.items()})
net = {k: S_left.get(k, 0) - S_right.get(k, 0) for k in set(S_left) | set(S_right)}
print("net S exponents (should be e_(a0,a0)):", {k: str(v) for k, v in net.items() if v != 0})
print(f"T-bookkeeping (per unit): log(size) cost on LHS = {lhs_log:.6f}, gain on RHS = {rhs_log:.6f}, net = {rhs_log-lhs_log:.6f} = 2*log(D*) = {2*math.log(Dstar(a0)):.6f}")
