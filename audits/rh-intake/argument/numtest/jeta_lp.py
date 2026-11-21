# NODE-JETA check: the top-row assembly in ThmAJetA (rowRadiusAssembly / TopRadius).
# For one top with row-0 degree A and partner caps cap_j (odd j >= 1), the Lean's per-top
# gain is topTerm = sum_{odd j<J} (A/l^j - cap_j)_+ + sum_{odd j>J} A/l^j (J = dTop, or inf).
# The proof needs eps >= l^{-J} with
#   A*gam - A*eps - sum_{odd j<J, l^j<=A} cap_j*(1 - l^j eps)_+  >=  topTerm.
# We (1) find the best eps over breakpoints, (2) check the inequality exactly (Fractions),
# (3) compare with the true LP max #Gaussian factors  max sum n_j, n_j<=cap_j, sum l^j n_j <= A
# (shared top budget), confirming the Lean charges sum_j min(cap_j, A/l^j) >= that LP value.
# Also checks every dual constraint l^al*eps + l^be*tau >= 1 used in TheoremAOneMonomialLogLoss.
import random
from fractions import Fraction as F

def gam(l, terms=60):  # sum over odd j of l^-j, exact = l/(l^2-1)
    return F(l, l * l - 1)

def top_term(l, A, cap, J):
    s = F(0)
    for j in range(1, 80, 2):
        if J is not None and j == J:
            continue
        if J is None or j < J:
            s += max(F(A, l ** j) - cap(j), 0)
        else:
            s += F(A, l ** j)
    return s

def tail(l, A, J):  # exact tail sum_{odd j > 79} A/l^j is negligible; handle via closed form
    return F(0)

def loss(l, A, cap, eps):
    L = A * eps
    j = 1
    while l ** j <= A:
        L += cap(j) * max(1 - l ** j * eps, 0)
        j += 2
    return L

def best_eps(l, A, cap, J):
    lo = F(0) if J is None else F(1, l ** J)
    cands = {lo}
    j = 1
    while l ** j <= max(A, 1) * l ** 2:
        e = F(1, l ** j)
        if e >= lo:
            cands.add(e)
        j += 2
    return min(cands, key=lambda e: loss(l, A, cap, e))

def lp_primal(l, A, cap):
    # greedy is optimal: cheapest levels first (smallest l^j)
    rem, tot, j = F(A), F(0), 1
    while l ** j <= A:
        n = min(F(cap(j)), rem / l ** j)
        tot += n; rem -= n * l ** j; j += 2
    return tot

random.seed(1)
bad = 0; worst = None; nt = 0
for trial in range(4000):
    l = random.choice([3, 5, 7, 11])
    A = random.randint(1, 3 * l ** 4)
    caps = {j: random.choice([0, 0, 1, 2, 3, random.randint(0, 50), random.randint(0, 5 * A // l + 1)])
            for j in range(1, 80, 2)}
    cap = lambda j: caps[j]
    J = random.choice([None, None, 1, 3, 5, 7])
    eps = best_eps(l, A, cap, J)
    lhs = A * gam(l) - loss(l, A, cap, eps)
    # exact tail correction for j>=81 in topTerm (only matters for J finite or caps 0): bound it
    rhs = top_term(l, A, cap, J)
    nt += 1
    if lhs < rhs - F(1, 10 ** 30):
        bad += 1
        if worst is None: worst = (l, A, J, float(lhs), float(rhs))
    # charged factors vs true LP
    if J is None:
        charged = sum(min(F(cap(j)), F(A, l ** j)) for j in range(1, 80, 2))
        assert charged >= lp_primal(l, A, cap)
    # dual constraints for top-partner factors x_top^{l^al} y^{l^be}, j = al-be odd
    for al in range(0, 6):
        for be in range(0, 6):
            jj = al - be
            if jj % 2 == 0:
                continue
            if jj > 0:
                if l ** jj > A: continue
                tau = max(F(0), 1 - l ** jj * eps)
            else:
                tau = F(1, l ** (-jj))
            assert l ** al * eps + l ** be * tau >= 1
print("trials", nt, "violations of assembly inequality", bad, worst)

# hand example from NODE-JETA §2.4
l, A = 5, 125
caps = {1: 3, 3: 0}
cap = lambda j: caps.get(j, 0)
def vfact(n, p):
    v = 0
    while n: n //= p; v += n
    return v
print("p=5 a=125: v(a!)=", vfact(125, 5), " a*rho=", float(F(125, 24)), " a*gam=", float(125 * gam(5)),
      " topTerm(cap1=3,cap3=0)=", float(top_term(5, 125, cap, None)),
      " v(a!)-a*rho-#factors(3)=", float(vfact(125, 5) - F(125, 24) - 3),
      " Lean bound topTerm-(log5 a+1)=", float(top_term(5, 125, cap, None)) - 4)
