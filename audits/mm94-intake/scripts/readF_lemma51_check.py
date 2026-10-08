# Independent numerical check of Lemma 5.1 (diagonal growth), paper mm94 section 5.
from fractions import Fraction as F
import math, sys, functools
print = functools.partial(print, flush=True)

print("== (i) elementary inequality and product bound (exact rationals)")
bad = 0
for m in range(1, 10**6 + 1):
    # (1+1/(3m))^3 >= 1+1/m  <=>  (3m+1)^3 >= 27 m^2 (m+1)  (integers, exact)
    if (3*m + 1)**3 < 27*m*m*(m + 1):
        bad += 1
print("m=1..10^6 violations of (1+1/(3m))^3 >= 1+1/m:", bad)
# exact slack: (3m+1)^3 - 27m^3 - 27m^2 = 9m + 1 > 0
print("identity (3m+1)^3 - 27m^2(m+1) == 9m+1 for m<=1000:",
      all((3*m+1)**3 - 27*m*m*(m+1) == 9*m+1 for m in range(1, 1001)))
H = F(1); badH = 0; minslack = None
for a in range(1, 2001):
    if a >= 2:
        H *= (1 + F(1, 3*(a-1)))
    if H**3 < a:
        badH += 1
print("a=1..2000 violations of (prod_{m<a}(1+1/(3m)))^3 >= a:", badH,
      "; H_2000^3/2000 =", float(H**3 / 2000))
# also D_a >= a*H_a >= a^{4/3} with D_a = (3a-1)/2 H_a
print("(3a-1)/2 >= a for all a>=1: trivially 3a-1>=2a <=> a>=1")

print("\n== (ii) profiles on [1..N]^2, N=60")
N = 60
def check(P, N, name):
    tol = 1e-9
    pos = all(P(a, b) > 0 for a in range(1, N+1) for b in range(1, N+1))
    sym = all(abs(P(a, b) - P(b, a)) <= tol*max(1, abs(P(a, b)))
              for a in range(1, N+1) for b in range(1, N+1))
    bnd = all(abs(P(1, b) - b) <= tol*b for b in range(1, N+1))
    conc = all(P(a, b-1) + P(a, b+1) <= 2*P(a, b) + tol*max(1, P(a, b))
               for a in range(1, N+1) for b in range(2, N))
    trip_viol = [(a, h) for a in range(1, N+1) for h in range(1, N+1)
                 if 3*h + a - 1 <= N and 3*P(a, h) > P(a, 3*h + a - 1) + tol*P(a, 3*h+a-1)]
    trip = not trip_viol
    ratios = [(P(a, a) / a**(4/3), a) for a in range(1, N+1)]
    r_all = min(ratios); r_ge2 = min(r for r in ratios if r[1] >= 2)
    # Run the paper's argument on the table where in range (4a-1 <= N)
    arg_ok = True; msgs = []
    Hs = {}
    for a in range(1, N+1):
        if 4*a - 1 > N: break
        D = P(a, a); Ha = 2*D/(3*a - 1); Hs[a] = Ha
        Daa = P(a, a+1) - P(a, a)
        tel = P(a, 4*a - 1) - D             # sum_{h=a}^{4a-2} Delta_{a,h}: 3a-1 terms
        nterms = (4*a - 2) - a + 1
        assert nterms == 3*a - 1
        if hyps_ok := (pos and sym and bnd and conc and trip):
            if not (2*D <= tel + 1e-9 and tel <= nterms*Daa + 1e-9 and Daa >= Ha - 1e-9):
                arg_ok = False; msgs.append(("tripling/telescope", a))
            if a >= 2:
                if not (D - P(a-1, a-1) >= Hs[a-1] + Ha - 1e-9):
                    arg_ok = False; msgs.append(("5.1", a))
                if not (Ha >= (1 + 1/(3*(a-1))) * Hs[a-1] - 1e-9):
                    arg_ok = False; msgs.append(("recurrence", a))
    print(f"{name}: positive={pos} symmetric={sym} P(1,b)=b={bnd} concave(4.6)={conc} "
          f"tripling(4.9)={trip}" + ("" if trip else f" [first violations {trip_viol[:3]}, total {len(trip_viol)}]"))
    print(f"   min_a P(a,a)/a^(4/3) over a=1..{N}: {r_all[0]:.6f} at a={r_all[1]};"
          f" over a>=2: {r_ge2[0]:.6f} at a={r_ge2[1]};"
          f" paper-argument steps hold where hyps hold: {arg_ok if (pos and sym and bnd and conc and trip) else 'n/a (hyps fail)'} {msgs[:3]}")
check(lambda a, b: math.sqrt(a*b*(a+b-1)), N, "sqrt(ab(a+b-1))")
check(lambda a, b: a*b, N, "a*b")
check(lambda a, b: a+b-1+(a-1)*(b-1)/3, N, "a+b-1+(a-1)(b-1)/3")
check(lambda a, b: a+b-1, N, "a+b-1")

print("\n== (iii) minimum possible P(a,a) under the hypotheses (truncated tables)")
# All constraints are P(x) >= nonneg. combination of other P's, plus fixed P(1,b)=P(b,1)=b and
# symmetry. Such a feasible set is closed under pointwise min, so its pointwise least element
# (= simultaneous LP minimum of every P(a,a)) is the least fixed point of the monotone map
#   P(x) <- max(P(x), all lower bounds at x), started from 0 off the boundary.
# Truncating to a finite table drops constraints, so the result is a LOWER bound on the true min.
def concave_envelope(xs, ys):
    # least concave majorant on integer grid of points (xs[i], ys[i]) (upper hull, linear interp)
    hull = []
    for p in zip(xs, ys):
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # remove middle point if it lies on or below segment (x1,y1)-(p)
            if (y2 - y1) * (p[0] - x1) <= (p[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(p)
    out = []
    j = 0
    for x in xs:
        while j + 1 < len(hull) and hull[j + 1][0] < x:
            j += 1
        if j + 1 < len(hull):
            (x1, y1), (x2, y2) = hull[j], hull[j + 1]
            out.append(y1 + (y2 - y1) * (x - x1) / (x2 - x1) if x2 != x1 else max(y1, y2))
        else:
            out.append(hull[j][1])
    return out
def least(N, iters=100000, tol=1e-12):
    # P[a][b], 1-indexed, rows/cols 1..N. Each operation below maps a point that is <= every
    # feasible table to another such point, so the monotone limit is the least feasible table.
    P = [[0.0] * (N + 1) for _ in range(N + 1)]
    for b in range(1, N + 1):
        P[1][b] = float(b); P[b][1] = float(b)
    xs = list(range(1, N + 1))
    for it in range(iters):
        old = [row[:] for row in P]
        for a in range(2, N + 1):                       # concavity (4.6) in each row, b>=2 interior
            env = concave_envelope(xs, [P[a][b] for b in xs])
            for b in xs: P[a][b] = max(P[a][b], env[b - 1])
        for a in range(1, N + 1):                       # tripling (4.9)
            for h in range(1, N + 1):
                t = 3 * h + a - 1
                if t <= N and 3 * P[a][h] > P[a][t]: P[a][t] = 3 * P[a][h]
        for a in range(1, N + 1):                       # symmetry
            for b in range(a + 1, N + 1):
                m = max(P[a][b], P[b][a]); P[a][b] = m; P[b][a] = m
        ch = max(abs(P[a][b] - old[a][b]) for a in range(1, N + 1) for b in range(1, N + 1))
        if ch < tol: break
    return P, it
for N in (12, 48, 120):
    P, it = least(N)
    # verify feasibility of the computed least point
    feas = all(P[a][b-1] + P[a][b+1] <= 2*P[a][b] + 1e-9 for a in range(1, N+1) for b in range(2, N)) and \
           all(3*P[a][h] <= P[a][3*h+a-1] + 1e-9 for a in range(1, N+1) for h in range(1, N+1) if 3*h+a-1 <= N)
    print(f"N={N} (converged after {it} sweeps, least point feasible={feas}):")
    rows = []
    Hprod = 1.0
    for a in range(1, 13):
        if a >= 2: Hprod *= 1 + 1/(3*(a-1))
        proof_bound = (3*a - 1)/2 * Hprod
        rows.append(f"  a={a:2d} minP(a,a)={P[a][a]:9.4f}  a^(4/3)={a**(4/3):8.4f}  "
                    f"ratio={P[a][a]/a**(4/3):6.4f}  proof bound (3a-1)/2*prod={proof_bound:8.4f}  "
                    f"a^2={a*a}")
    print("\n".join(rows))
