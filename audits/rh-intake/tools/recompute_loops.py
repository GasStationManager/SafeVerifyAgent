"""Python ports of the Bool-valued programs the artifact closes with `decide +kernel`.
Each port is written from the Lean definition; Lean's Nat semantics (truncated
subtraction, x / 0 = 0) are kept. Usage: recompute_loops.py <src-root>"""
import sys, re, ast, math
root = sys.argv[1]
div = lambda a, b: 0 if b == 0 else a // b
fact = math.factorial
# --- Formalism/.../ChebyshevPrimeBounds/SmallLoop.lean  (PI.PC.loop)
def tst(n, c): return n**256 < 2**div(3225600000000*n - 1 if n > 0 else 0, c*6931471808)
def pc_loop(B, k, n, c, Q):
    while k > 0:
        if math.gcd(n, Q) == 1:
            if not tst(n, c+1): return False
            n, c, Q = n+1, c+1, (Q*n if n <= B else Q)
        else:
            if not tst(n, c): return False
            n = n+1
        k -= 1
    return True
print('PI.PC.loop_run                 ', pc_loop(362, 131070, 2, 0, 1))
# --- Formalism/.../DyadicPrimeIntervals/SmallLoop.lean (PI.PrimesDyadicRS.K.run)
def tstR(h, d): return 0 < d and 2**(div(7680000000000*(h+1), 10*d*6931471803) + 257) <= h**256
def pr(Q, m):
    if m <= 362: return 1 if math.gcd(m, fact(m-1) if m >= 1 else 1) == 1 else 0
    return 1 if math.gcd(m, Q) == 1 else 0
def nxt(Q, h, d):
    return max(0, d + pr(Q, h+1) - (pr(Q, (h+1)//2) if (h+1) % 2 == 0 else 0))
def run(hT, dT, k, h, d):
    Q = fact(362)
    while k > 0:
        if not (h < 41 or tstR(h, d)): return False
        h, d = h+1, nxt(Q, h, d); k -= 1
    return h == hT and d == dT
for i, a in enumerate([(32768,1612,32766,2,1),(65536,3030,32768,32768,1612),(98304,4388,32768,65536,3030),(131072,5709,32768,98304,4388)], 1):
    print(f'PI.PrimesDyadicRS.K.run{i}         ', run(*a))
# --- Formalism/PadicSubsetSums/StableGradedCounts/IRRPrimeRecipSum.lean (ladder)
def test(F, r, a, b, p): return p+3 <= a and b < 2*p and r < p and p < (r+1)*(r+1) and math.gcd(p, F) == 1
def term(M, F, r, a, b, p): return M // p if test(F, r, a, b, p) else 0
def bsum(t, k, lo): return sum(t(p) for p in range(lo, lo + 2**k))   # = the recursive bsum, by bsum_eq
def chk(M, F, r, a, b): return M <= 20 * bsum(lambda p: term(M, F, r, a, b, p), a.bit_length()-1, b//2)
def ladder(M, F, r, T, f, a):
    while True:
        if f == 0: return T <= a
        if T <= a: return True
        if not chk(M, F, r, a, a + a//10): return False
        f, a = f-1, a + a//10 + 1
for r, T, a in [(13,196,100),(31,1024,196),(141,20000,1024)]:
    print(f'ladder r={r:<3} T={T:<6}            ', ladder(10**9, fact(r), r, T, 60, a))
# --- Development/.../InvFiveLogLeSumInvPrimes.lean (okAll table)
src = open(root + '/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvFiveLogLeSumInvPrimes.lean', encoding='utf-8').read()
tab = ast.literal_eval(re.search(r'def table : .*? := (\[.*?\n\])', src, re.S)[1].replace('\n', ' ')) if re.search(r'def table : .*? := (\[.*?\n\])', src, re.S) else ast.literal_eval(re.search(r'def table : [^\n]*:= (\[.*?\])\n\ntheorem table_ok', src, re.S)[1])
def noSmallDiv(p, D): return all(p < d*d or d < 2 or p % d != 0 for d in range(1, D+1))
def okIv(a, b, j, c, L):
    return all(2 <= p < 17161 and noSmallDiv(p, 130) and b <= 2*p and p+3 <= a and p <= c for p in L) and \
        all(x < y for x, y in zip(L, L[1:])) and 2**j <= a and 0 < c and c * 10**10 <= 5*len(L)*j*6931471803
def okAll(lo, T, hi):
    for (a, b, j, c, L) in T:
        if not (a <= lo and okIv(a, b, j, c, L)): return False
        lo = b
    return hi <= lo
print(f'table_ok ({len(tab)} rows, {sum(len(r[4]) for r in tab)} primes)   ', okAll(100, tab, 16900))
# --- lcmUpto bounds
def lcmUpto(n):
    l = 1
    for i in range(1, n+1): l = l*i // math.gcd(l, i)
    return l
print('lcmUpto n <= 3^n, n < 30       ', all(lcmUpto(n) <= 3**n for n in range(30)))
print('lcmUpto n <= 4^n, n <= 100     ', all(lcmUpto(n) <= 4**n for n in range(101)))
