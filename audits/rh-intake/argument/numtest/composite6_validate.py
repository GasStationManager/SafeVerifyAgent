"""Validation of composite6_lib against brute-force exact polynomial arithmetic (auditors' code).
V1  Fischer norm^2 of the extremal vector prod Delta_s^{c_s} equals the hook product H(nu).
V2  Sym^A step matrices (1->2, 2->2, 2->3, 3->4) equal the brute-force jet map
    P |-> sum_m coeff_{xi^m}[P(xi^T Y)] * prod d_{m}  with exact rational stand-in moments.
V3  the det^w square surrogate, same check.
V4  hook formula: cell product vs Frobenius form.
V5  theta moments: stability under enlarging the lattice window; one-variable sharpness.
Usage: python3 -I composite6_validate.py
"""
import sys, os, math, itertools, random
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import composite6_lib as L

random.seed(1)

# ---------------- tiny exact polynomial algebra: dict {exponent tuple: Fraction}
def pmul(P, Q):
    R = {}
    for e1, c1 in P.items():
        for e2, c2 in Q.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            R[e] = R.get(e, 0) + c1 * c2
    return {e: c for e, c in R.items() if c != 0}

def padd(P, Q, s=1):
    R = dict(P)
    for e, c in Q.items():
        R[e] = R.get(e, 0) + s * c
    return {e: c for e, c in R.items() if c != 0}

def ppow(P, n, nv):
    R = {(0,) * nv: Fraction(1)}
    for _ in range(n):
        R = pmul(R, P)
    return R

def var(i, nv):
    e = [0] * nv; e[i] = 1
    return {tuple(e): Fraction(1)}

def det_poly(M, nv):
    n = len(M)
    if n == 1:
        return M[0][0]
    R = {}
    for j in range(n):
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        R = padd(R, pmul(M[0][j], det_poly(minor, nv)), 1 if j % 2 == 0 else -1)
    return R

def fischer(P):
    return sum(c * c * math.prod(math.factorial(x) for x in e) for e, c in P.items())

print("V1: Fischer norm of extremal vectors = hook product")
ok1 = True
for n in (2, 3):
    nv = n * n
    X = [[var(i * n + j, nv) for j in range(n)] for i in range(n)]
    minors = [det_poly([row[:s] for row in X[:s]], nv) for s in range(1, n + 1)]
    for nu in itertools.product(range(0, 5), repeat=n):
        if list(nu) != sorted(nu, reverse=True) or sum(nu) == 0 or sum(nu) > 7:
            continue
        P = {(0,) * nv: Fraction(1)}
        for s in range(n):
            c = nu[s] - (nu[s + 1] if s + 1 < n else 0)
            for _ in range(c):
                P = pmul(P, minors[s])
        f = fischer(P)
        h = math.exp(L.log_hook(nu))
        good = abs(f - h) < 1e-6 * h
        ok1 &= good
        print(f"  n={n} nu={nu}: Fischer={f}  hook={h:.6g}  {'OK' if good else 'MISMATCH'}")
print("V1", "PASS" if ok1 else "FAIL")

# ---------------- V2: Sym^A steps vs brute force
def brute_step(d, A, Nin, Nout, r):
    """raw output coefficients (dict S->Fraction) of E[prod_a (sum_b xi_{b a} y_b)^{r_a}]."""
    # variables: xi_{b a} (Nout*Nin) then y_b (Nout)
    nx = Nout * Nin; nv = nx + Nout
    P = {(0,) * nv: Fraction(1)}
    for a in range(Nin):
        lin = {}
        for b in range(Nout):
            e = [0] * nv; e[b * Nin + a] = 1; e[nx + b] = 1
            lin[tuple(e)] = Fraction(1)
        P = pmul(P, ppow(lin, r[a], nv))
    out = {}
    for e, c in P.items():
        val = c
        for k in range(nx):
            val *= d[e[k]]
        S = e[nx:]
        out[S] = out.get(S, 0) + val
    return out

def check_general(A, Nin, Nout, d):
    dt = np.array([float(d[p]) / math.sqrt(math.factorial(p)) for p in range(len(d))], dtype=complex)
    if Nin == 1:
        Kt = L.step_1to2(dt, A)[:, None]; ins = [(A,)]; outs = [(s, A - s) for s in range(A, -1, -1)]
        # step_1to2 indexes by s = exponent of y0 ascending
        outs = [(s, A - s) for s in range(A + 1)]
    elif Nin == 2 and Nout == 2:
        Kt = L.step_square2(dt, A)
        ins = [(r0, A - r0) for r0 in range(A + 1)]; outs = [(s, A - s) for s in range(A + 1)]
    else:
        Kt, ins, outs = L.step_general(dt, A, Nin, Nout)
    err = 0.0; scale = 0.0
    for c, r in enumerate(ins):
        raw = brute_step(d, A, Nin, Nout, r)
        for i, S in enumerate(outs):
            val = float(raw.get(S, 0)) * math.sqrt(math.prod(math.factorial(x) for x in S) /
                                                    math.prod(math.factorial(x) for x in r)) / math.sqrt(math.factorial(A))
            err = max(err, abs(Kt[i, c] - val)); scale = max(scale, abs(val))
    return err, scale

print("\nV2: Sym^A steps vs brute force (random integer stand-in moments)")
ok2 = True
d = [Fraction(random.randint(-5, 5)) for _ in range(20)]
for (A, Nin, Nout) in [(5, 1, 2), (6, 2, 2), (5, 2, 3), (4, 3, 4), (4, 2, 4)]:
    err, scale = check_general(A, Nin, Nout, d)
    good = err <= 1e-9 * max(scale, 1)
    ok2 &= good
    print(f"  A={A} {Nin}->{Nout}: max|lib - brute| = {err:.2e} (max entry {scale:.3g}) {'OK' if good else 'FAIL'}")
print("V2", "PASS" if ok2 else "FAIL")

# ---------------- V3: det^w surrogate
def brute_detw(d, A, w, r):
    # variables xi00, xi01, xi10, xi11 (xi_{b a}: index b*2+a), y0, y1
    nv = 6
    xi = lambda b, a: var(b * 2 + a, nv)
    y = [var(4, nv), var(5, nv)]
    x0 = padd(pmul(xi(0, 0), y[0]), pmul(xi(1, 0), y[1]))
    x1 = padd(pmul(xi(0, 1), y[0]), pmul(xi(1, 1), y[1]))
    detxi = padd(pmul(xi(0, 0), xi(1, 1)), pmul(xi(0, 1), xi(1, 0)), -1)
    P = pmul(pmul(ppow(x0, r[0], nv), ppow(x1, r[1], nv)), ppow(detxi, w, nv))
    out = {}
    for e, c in P.items():
        val = c * d[e[0]] * d[e[1]] * d[e[2]] * d[e[3]]
        out[(e[4], e[5])] = out.get((e[4], e[5]), 0) + val
    return out

print("\nV3: det^w square surrogate vs brute force")
ok3 = True
for (A, w) in [(4, 1), (5, 2), (6, 3)]:
    dt = np.array([float(d[p]) / math.sqrt(math.factorial(p)) for p in range(len(d))], dtype=complex)
    Kt = L.step_square2_detw(dt, A, w)
    err = 0.0; scale = 0.0
    for r0 in range(A + 1):
        r = (r0, A - r0)
        raw = brute_detw(d, A, w, r)
        for s in range(A + 1):
            val = float(raw.get((s, A - s), 0)) * math.sqrt(math.factorial(s) * math.factorial(A - s) /
                                                          (math.factorial(r0) * math.factorial(A - r0)))
            val /= math.sqrt(math.factorial(A + w) * math.factorial(w))
            err = max(err, abs(Kt[s, r0] - val)); scale = max(scale, abs(val))
    good = err <= 1e-9 * max(scale, 1)
    ok3 &= good
    print(f"  A={A} w={w}: max err {err:.2e} (max entry {scale:.3g}) {'OK' if good else 'FAIL'}")
print("V3", "PASS" if ok3 else "FAIL")

print("\nV4: hook product, cells vs Frobenius form")
ok4 = True
for rows in [(5,), (3, 3), (7, 2, 2), (40, 10, 10, 3), (100, 30, 29, 0)]:
    a, b = L.log_hook(rows), L.log_hook_frob([r for r in rows])
    good = abs(a - b) < 1e-8 * max(1, abs(a))
    ok4 &= good
    print(f"  {rows}: {a:.10f} {b:.10f} {'OK' if good else 'FAIL'}")
print("V4", "PASS" if ok4 else "FAIL")

print("\nV5: theta moments (principal lattices, area pi); window stability and 1-variable sharpness")
for name, shift in [('Zi', 0.0), ('Zi', 0.5), ('Zw', 0.0), ('O7', 0.0), ('O7', 0.5)]:
    dt1 = L.moments(name, 400, shift)
    dt2 = L.moments(name, 600, shift)
    diff = np.max(np.abs(dt1 - dt2[:401]))
    S1 = L.sup_growth(name, shift)
    nz = [p for p in range(1, 401) if abs(dt1[p]) > 1e-8]
    # 1-variable: log|d_p|^2 - log p! = 2 log|d~_p|; Lean 1x1 bound: log tmax - log p! = 2logS1+1+2log(2p+2)+ph(p)-log p!
    rows = []
    for p in (40, 100, 200, 400):
        q = max(x for x in nz if x <= p)
        rows.append(f"p={q}: 2log|d~|={2*math.log(abs(dt1[q])):+.2f}")
    print(f"  {name} shift={shift}: window diff {diff:.1e}; S1={S1:.4f}; nonzero p mod {math.gcd(*nz) if len(nz)>1 else 0} ; " + "; ".join(rows))
