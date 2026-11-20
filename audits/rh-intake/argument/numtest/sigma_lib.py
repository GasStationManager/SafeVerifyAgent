"""Exact Weierstrass sigma coefficients via Weierstrass's recursion.
sigma(z) = sum a_{m,n} (g2/2)^m (2 g3)^n z^{4m+6n+1}/(4m+6n+1)!
a_{m,n} = 3(m+1) a_{m+1,n-1} + (16/3)(n+1) a_{m-2,n+1} - (1/3)(2m+3n-1)(4m+6n-1) a_{m-1,n}
NOTE: the task brief wrote a_{m-1,n+1} in the middle term; that index is inconsistent with
homogeneity (degree 4m+6n-2 needed) and is wrong; a_{m-2,n+1} is Weierstrass's form and is
verified in verify_recursion.py.
D^a sigma(0) = sum_{4m+6n+1=a} a_{m,n} (g2/2)^m (2g3)^n  -- an integer when g2/2, 2g3 are integers.
"""
from fractions import Fraction

def sigma_coeffs(N, middle='m-2'):
    """Return dict a[(m,n)] (integers) for 4m+6n+1 <= N."""
    a = {(0, 0): 1}
    smax = (N - 1) // 4
    for s in range(1, smax + 1):
        for n in range(0, s + 1):
            m = s - n
            if 4 * m + 6 * n + 1 > N:
                continue
            v = 0  # 3*a_{m,n}
            if n >= 1:
                v += 9 * (m + 1) * a.get((m + 1, n - 1), 0)
            if middle == 'm-2':
                if m >= 2:
                    v += 16 * (n + 1) * a.get((m - 2, n + 1), 0)
            else:  # the brief's version
                if m >= 1:
                    v += 16 * (n + 1) * a.get((m - 1, n + 1), 0)
            if m >= 1:
                v -= (2 * m + 3 * n - 1) * (4 * m + 6 * n - 1) * a.get((m - 1, n), 0)
            q, r = divmod(v, 3)
            assert r == 0, ((m, n), Fraction(v, 3))
            a[(m, n)] = q
    return a

def derivs(a, N, h2, h3):
    """D^k sigma(0) for k<=N with g2/2 = h2, 2 g3 = h3 (integers or Fractions)."""
    D = [0] * (N + 1)
    for (m, n), x in a.items():
        k = 4 * m + 6 * n + 1
        if k <= N:
            D[k] += x * h2 ** m * h3 ** n
    return D

def vp(x, p):
    """p-adic valuation of a nonzero integer, fast for large valuations."""
    if x == 0:
        return None
    x = abs(x)
    pw = [p]
    while pw[-1] * pw[-1] <= x:
        pw.append(pw[-1] * pw[-1])
    v = 0
    for j in range(len(pw) - 1, -1, -1):
        q, r = divmod(x, pw[j])
        while r == 0:
            x = q; v += 1 << j
            q, r = divmod(x, pw[j])
    return v

def vp_fact(n, p):
    s, q = 0, p
    while q <= n:
        s += n // q; q *= p
    return s

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]

def sigma_derivs_stream(N, curves, perturb=None):
    """Streaming version: returns {name: [D^k sigma(0) for k<=N]} for curves {name:(h2,h3)},
    h2 = g2/2, h3 = 2 g3 integers. Keeps only two recursion levels in memory.
    perturb=(m,n): add 3^(N//3) to a_{m,n} right after computing it (code control)."""
    D = {c: [0] * (N + 1) for c in curves}
    prev = {(0, 0): 1}
    for c in curves: D[c][1] = 1
    if perturb == (0, 0): raise ValueError
    smax = (N - 1) // 4
    P2 = {c: [h2 ** i for i in range(smax + 2)] for c, (h2, h3) in curves.items()}
    P3 = {c: [h3 ** i for i in range(N // 6 + 2)] for c, (h2, h3) in curves.items()}
    for s in range(1, smax + 1):
        # increasing n within level s=m+n: a_{m,n} uses a_{m+1,n-1} (same level), others level s-1
        cur = {}
        for n in range(0, s + 1):
            m = s - n
            k = 4 * m + 6 * n + 1
            if k > N: break
            v = 0
            if n >= 1: v += 9 * (m + 1) * cur.get((m + 1, n - 1), 0)
            if m >= 2: v += 16 * (n + 1) * prev.get((m - 2, n + 1), 0)
            if m >= 1: v -= (2 * m + 3 * n - 1) * (4 * m + 6 * n - 1) * prev.get((m - 1, n), 0)
            q, r = divmod(v, 3); assert r == 0
            if perturb == (m, n): q += 3 ** (N // 3)  # a large power of 3 keeps the later divisions by 3 exact
            cur[(m, n)] = q
            for c, (h2, h3) in curves.items():
                if (h2 == 0 and m) or (h3 == 0 and n): continue
                D[c][k] += q * P2[c][m] * P3[c][n]
        prev = cur
    return D
