"""Kronecker theta function Theta(z,w) = sigma(z+w)/(sigma(z)sigma(w)) -- exact p-adic engine.

Write sigma(u) = u*exp(phi(u)), phi(u) = log(sigma(u)/u) = -sum_{n>=2} c_n u^{2n}/((2n)(2n-1)),
where wp(u) = u^-2 + sum_{n>=2} c_n u^{2n-2}.  Then

    Theta(z,w) = (1/z + 1/w) * G(z,w),   G = exp(phi(z+w) - phi(z) - phi(w))   (a power series, G = 1 + O(zw)).

Write G = sum_{i,k} Np[i][k] z^i w^k /(i! k!)  (double exponential generating function) and Phi_m = m! [u^m] phi
(so Phi_{2n} = -(2n-2)! c_n, the Hurwitz-type numbers of wp, up to sign).  Then
log G = sum_{i>=1,m>=1} Phi_{i+m} z^i w^m/(i! m!), and d/dz G = (d/dz log G) G gives the integral recursion

    Np[0][k] = delta_{k0},
    Np[i+1][k] = sum_{r=0}^{i} C(i,r) sum_{s=1}^{k} C(k,s) Phi_{r+1+s} Np[i-r][k-s].

Theta = 1/z + 1/w + sum_{a>=0,b>=1} C_{a,b} z^{b-1} w^a with C_{a,b} = g_{b,a} + g_{b-1,a+1}, g_{i,k} = Np[i][k]/(i!k!), so

    N_{a,b} := a!(b-1)! C_{a,b} = Np[b][a]/b + Np[b-1][a+1]/(a+1).

p-adic engine: all arithmetic in Z/p^K (exact ring operations; denominators prime to p inverted).  If
min_m v_p(Phi_m) = -h < 0 we use Phit_m = p^h Phi_m (and extra scalings below), so the
computed row i is p^{h i} Np[i] (a factor Phi_{r+1+s} entering at z-index r+1 is scaled by p^{h(r+1)}, since the
recursion is graded, not homogeneous, in Phi).  Any computed valuation < K is exact.
"""
from fractions import Fraction
from math import comb, factorial
from operator import mul


def wp_coeffs(g2, g3, N):
    """c_n, n <= N, for wp = u^-2 + sum c_n u^{2n-2} (same recursion as wp_valuations.py)."""
    g2, g3 = Fraction(g2), Fraction(g3)
    c = [Fraction(0)] * (N + 1)
    if N >= 2: c[2] = g2 / 20
    if N >= 3: c[3] = g3 / 28
    for n in range(4, N + 1):
        c[n] = Fraction(3, (2 * n + 1) * (n - 3)) * sum(c[m] * c[n - m] for m in range(2, n - 1))
    return c


def phi_numbers(g2, g3, M):
    """Phi_m for m <= M (Fractions)."""
    c = wp_coeffs(g2, g3, M // 2 + 1)
    Phi = [Fraction(0)] * (M + 1)
    for n in range(2, M // 2 + 1):
        Phi[2 * n] = -factorial(2 * n - 2) * c[n]
    return Phi


def vpF(x, p):
    if x == 0: return None
    v, a, b = 0, x.numerator, x.denominator
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v


def vpi(x, p, K):
    """valuation of an integer mod p^K; returns K if x == 0 mod p^K (meaning '>= K')."""
    x %= p ** K
    if x == 0: return K
    v = 0
    while x % p == 0: x //= p; v += 1
    return v


def to_mod(x, p, K):
    """Fraction with p-integral value -> residue mod p^K."""
    q = p ** K
    return x.numerator % q * pow(x.denominator % q, -1, q) % q


def rows_padic(Phi, p, K, lengths, perturb=None):
    """lengths[i] = number of k-entries of row i wanted (nonincreasing in i, i = 0..I).
    Returns (rows, h): rows[i][k] = p^{h i} Np[i][k] mod p^K."""
    q = p ** K
    vals = [vpF(x, p) for x in Phi if x != 0]
    h = max(0, -min(vals))
    Pt = [to_mod(x * Fraction(p) ** h, p, K) for x in Phi]
    if perturb is not None:
        m, d = perturb; Pt[m] = (Pt[m] + d) % q
    from math import gcd
    d = 0
    for m, x in enumerate(Phi):
        if x != 0: d = gcd(d, m)       # Phi supported on multiples of d (d = 4 for Z[i], 6 for Z[w], 2 generic)
    I = len(lengths) - 1
    rows = [[0] * lengths[i] for i in range(I + 1)]
    rows[0][0] = 1
    Kmax = lengths[0]
    binI = [[comb(i, r) for r in range(i + 1)] for i in range(I + 1)]
    bk = [1]
    for k in range(1, Kmax):
        bk = [1] + [(bk[s] + bk[s - 1]) % q for s in range(1, k)] + [1]   # Pascal: C(k, s) mod p^K
        # u[r][s] = C(k,s) Phi_{r+1+s}, s = 1..k (index s)
        need = [i for i in range(1, I + 1) if lengths[i] > k]
        if not need: break
        rmax = max(need) - 1
        u = []
        for r in range(rmax + 1):
            sc = p ** (h * r)      # factor with z-index r+1 carries p^{h(r+1)}: row i is then exactly p^{h i} Np[i]
            ur = [0] * (k + 1)
            for s in range(1 + (-(r + 2)) % d, k + 1, d):
                x = Pt[r + 1 + s]
                if x: ur[s] = bk[s] * x * sc % q
            u.append(ur)
        for i1 in need:            # computing row i1 = i+1
            i = i1 - 1
            tot = 0
            for r in range(i + 1):
                row = rows[i - r]
                ur = u[r]
                lo = max(1, k - len(row) + 1)
                lo += (-(r + 1 + lo)) % d          # only s with Phi_{r+1+s} != 0, i.e. r+1+s = 0 mod d
                acc = sum(map(mul, ur[lo:k + 1:d], row[k - lo::-d])) if k - lo >= 0 else 0
                tot += binI[i][r] * acc
            rows[i1][k] = tot % q
    return rows, h


def N_val(rows, h, a, b, p, K):
    """v_p(N_{a,b}) from the p-adic rows; returns (v, exact_flag)."""
    X = (a + 1) * rows[b][a] + b * p ** h * rows[b - 1][a + 1]
    off = h * b + vpi(a + 1, p, 50) + vpi(b, p, 50)
    vx = vpi(X, p, K)
    return vx - off, vx < K


def vp_fact(n, p):
    s, q = 0, p
    while q <= n: s += n // q; q *= p
    return s


def pred_cap(a, b, p, c=1.0, shift=0):
    """sum_{e odd} max(0, a/p^e - c*b)  (shift moves e -> e+shift in the cap position: a/p^(e+shift))."""
    s, e = 0.0, 1
    while p ** e <= 10 * a + 10:
        s += max(0.0, a / p ** (e + shift) - c * b)
        e += 2
    return s
