"""Independent check: build sigma from the recursion for generic rational g2,g3,
compute wp = -(log sigma)'' as a Laurent series and check wp'^2 = 4wp^3 - g2 wp - g3,
plus the known initial coefficients. Also show the brief's variant of the recursion fails."""
from fractions import Fraction as F
from math import factorial
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sigma_lib import sigma_coeffs

ORD = 40
def series(a, g2, g3, N):
    c = [F(0)] * (N + 1)
    for (m, n), x in a.items():
        k = 4 * m + 6 * n + 1
        if k <= N:
            c[k] += x * (g2 / 2) ** m * (2 * g3) ** n / factorial(k)
    return c

def mul(A, B, N):
    C = [F(0)] * (N + 1)
    for i, x in enumerate(A):
        if x:
            for j in range(0, N + 1 - i):
                if B[j]: C[i + j] += x * B[j]
    return C

def check(middle, g2, g3):
    N = ORD + 2
    a = sigma_coeffs(N + 1, middle)
    c = series(a, g2, g3, N + 1)
    # sigma = z*S(z), S(0)=1. log sigma = log z + log S. wp = 1/z^2 - (log S)''.
    S = c[1:]  # S[k] = coeff of z^k
    # log S via L' = S'/S
    inv = [F(0)] * (N + 1); inv[0] = F(1)
    for k in range(1, N + 1):
        inv[k] = -sum(S[j] * inv[k - j] for j in range(1, k + 1) if j < len(S))
    dS = [(k + 1) * S[k + 1] for k in range(N)]
    Lp = mul(dS, inv, N - 1)  # (log S)'
    Lpp = [(k + 1) * Lp[k + 1] for k in range(N - 2)]
    # wp = z^-2 + w(z), w = -Lpp ; represent wp*z^2 = 1 + z^2 w  as power series P
    M = N - 2
    P = [F(0)] * M; P[0] = F(1)
    for k in range(M - 2): P[k + 2] = -Lpp[k]
    # wp' * z^3 = z P' - 2P
    Q = [k * P[k] - 2 * P[k] for k in range(M)]
    lhs = mul(Q, Q, M - 1)                       # wp'^2 z^6
    P3 = mul(mul(P, P, M - 1), P, M - 1)
    rhs = [4 * P3[k] for k in range(M)]
    for k in range(M):
        if k >= 4: rhs[k] -= g2 * P[k - 4]
        if k >= 6: rhs[k] -= g3 * (1 if k == 6 else 0)
    bad = [k for k in range(M - 1) if lhs[k] != rhs[k]]
    return bad, c

g2, g3 = F(7, 3), F(-5, 11)
bad, c = check('m-2', g2, g3)
print("recursion a_{m-2,n+1}: wp'^2=4wp^3-g2wp-g3 fails at z-orders", bad, "(checked to order z^%d of wp'^2)" % (ORD - 6))
assert not bad
assert c[5] == -g2 / 240 and c[7] == -g3 / 840 and c[9] == -g2 ** 2 / 161280
print("initial coefficients z - g2 z^5/240 - g3 z^7/840 - g2^2 z^9/161280: OK")
try:
    bad2, _ = check('m-1', g2, g3)
    print("brief's variant a_{m-1,n+1}: mismatches at orders", bad2[:5])
except AssertionError as e:
    print("brief's variant a_{m-1,n+1}: produces non-integer a_{m,n}:", e)

# control: perturb a_{2,1} by +1 and confirm the ODE check detects it
import sigma_lib
orig = sigma_lib.sigma_coeffs
def perturbed(N, middle='m-2'):
    a = orig(N, middle); a[(2, 1)] += 1; return a
sigma_coeffs = perturbed
badp, _ = check('m-2', g2, g3)
print("control (a_{2,1} += 1): ODE check fails at orders", badp[:6])
assert badp
