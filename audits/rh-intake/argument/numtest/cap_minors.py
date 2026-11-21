#!/usr/bin/env python3
"""NODE-HIGHERRANK hand check of the cap lemma (HitsCapPos / MinorHits, UTS/StatementE.lean:15,
UTS/StatementAB.lean:58).  Stdlib only, exact integer arithmetic.

Polynomials in X[a][b] (r0 x r1 matrix at ONE position) are dicts {exponent tuple: int}.
A product of column minors  prod_c det((T_c X)[:, I_c])  is built with random integer frames T_c.
D(xi, b) = sum_a xi_a d/dX[a][b]  (directional derivative in row-direction xi, column b).
Ordinary derivatives are nonzero iff Hasse derivatives are (char 0).

Claims tested:
 (1) with ONE direction xi (any columns), more than C = #minors derivatives always kill P;
     exactly C derivatives generically do not.
 (2) with DIFFERENT directions the bound fails (so the cap is per direction, as HitsCapPos says).
"""
import itertools, random

random.seed(1)
R0, R1 = 3, 3
NV = R0 * R1
def vid(a, b): return a * R1 + b

def mul(P, Q):
    out = {}
    for m1, c1 in P.items():
        for m2, c2 in Q.items():
            m = tuple(x + y for x, y in zip(m1, m2))
            out[m] = out.get(m, 0) + c1 * c2
    return {m: c for m, c in out.items() if c}

def add(P, Q, s=1):
    out = dict(P)
    for m, c in Q.items():
        out[m] = out.get(m, 0) + s * c
    return {m: c for m, c in out.items() if c}

def lin(coeffs):  # coeffs: {var: int}
    P = {}
    for v, c in coeffs.items():
        m = [0] * NV; m[v] = 1
        if c: P[tuple(m)] = c
    return P

def det(M):
    n = len(M)
    if n == 1: return M[0][0]
    out = {}
    for j in range(n):
        minor = [row[:j] + row[j+1:] for row in M[1:]]
        out = add(out, mul(M[0][j], det(minor)), 1 if j % 2 == 0 else -1)
    return out

def minor(T, I):  # T: list of row vectors (len R0), I: list of columns
    M = [[lin({vid(a, b): T[i][a] for a in range(R0)}) for b in I] for i in range(len(T))]
    return det(M)

def D(P, xi, b):
    out = {}
    for m, c in P.items():
        for a in range(R0):
            v = vid(a, b)
            if m[v] and xi[a]:
                mm = list(m); mm[v] -= 1
                out[tuple(mm)] = out.get(tuple(mm), 0) + c * m[v] * xi[a]
    return {m: c for m, c in out.items() if c}

def rvec(): return [random.randint(-5, 5) for _ in range(R0)]

def build(shape):  # shape: list of column heights; returns product of minors
    P = {tuple([0] * NV): 1}
    for h in shape:
        T = [rvec() for _ in range(h)]
        I = random.sample(range(R1), h)
        P = mul(P, minor(T, I))
    return P

def max_order_one_dir(P, xi, kmax):
    best = 0
    for k in range(1, kmax + 1):
        alive = False
        for cols in itertools.product(range(R1), repeat=k):
            Q = P
            for b in cols:
                Q = D(Q, xi, b)
                if not Q: break
            if Q: alive = True; break
        if alive: best = k
        else: break
    return best

def mixed_exceeds(P, C):
    # try C+1 derivatives with random distinct directions, all columns
    for _ in range(200):
        dirs = [rvec() for _ in range(C + 1)]
        for cols in itertools.product(range(R1), repeat=C + 1):
            Q = P
            for xi, b in zip(dirs, cols):
                Q = D(Q, xi, b)
                if not Q: break
            if Q: return True
    return False

cases = {
    "weight (2,1): columns 2,1": [2, 1],
    "weight (2,2): columns 2,2": [2, 2],
    "weight (3,2,1): columns 3,2,1": [3, 2, 1],
    "weight (1,1,1): column 3": [3],
}
for name, shape in cases.items():
    P = build(shape)
    C = len(shape)
    worst = min(max_order_one_dir(P, rvec(), C + 2) for _ in range(5))
    best = max(max_order_one_dir(P, rvec(), C + 2) for _ in range(5))
    print(f"{name:32s} C=#minors={C}  max order in one generic direction: {worst}..{best}  "
          f"(never > C: {best <= C})  mixed directions exceed C: {mixed_exceeds(P, C)}")

# the textbook example by hand: P = det[[x11,x12],[x21,x22]] * x11, frame rows e1, e2
e1, e2 = [1, 0, 0], [0, 1, 0]
P = mul(minor([e1, e2], [0, 1]), minor([e1], [0]))
print("P = (x11 x22 - x12 x21) x11 :")
print("  d_x11 d_x12 P   nonzero:", bool(D(D(P, e1, 0), e1, 1)))
print("  d_x11^2 d_x12 P nonzero:", bool(D(D(D(P, e1, 0), e1, 0), e1, 1)))
print("  d_x11^3 P       nonzero:", bool(D(D(D(P, e1, 0), e1, 0), e1, 0)))
print("  d_x11^2 d_x22 P (mixed dirs) nonzero:", bool(D(D(D(P, e1, 0), e1, 0), e2, 1)))
print("  max order in direction e2:", max_order_one_dir(P, e2, 4))
