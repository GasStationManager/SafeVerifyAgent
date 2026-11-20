"""Code controls: (1) vp() against naive repeated division; (2) perturbing one recursion
coefficient a_{3,0} (by 3^(N//3), to keep the exact divisions by 3 valid) changes the
p-adic statistics; (3) the brief's variant recursion (a_{m-1,n+1}) is not even integral."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sigma_lib import sigma_derivs_stream, vp, sigma_coeffs
random.seed(1)
for _ in range(2000):
    p = random.choice([5, 7, 11, 13]); x = random.randrange(1, 10 ** 50) * p ** random.randrange(0, 300)
    n, y = 0, x
    while y % p == 0: y //= p; n += 1
    assert vp(x, p) == n
print("vp() agrees with naive division on 2000 random cases")
N = 1500
cur = {'A': (2, 0), 'C': (-5, 7)}
D0 = sigma_derivs_stream(N, cur); D1 = sigma_derivs_stream(N, cur, perturb=(3, 0))
for c in cur:
    for p in (7, 11, 13):
        ch = sum(1 for a in range(1, N + 1) if D0[c][a] and vp(D0[c][a], p) != vp(D1[c][a], p))
        below = 0
        for a in range(1, N + 1):
            if D1[c][a]:
                w = 0; q = p * p
                while q <= a: w += a // q; q *= p * p
                below += vp(D1[c][a], p) < w
        print(f"curve {c} p={p}: #a whose v_p changed after perturbing a_(3,0): {ch}; "
              f"#a violating v >= sum floor(a/p^2k) after perturbation: {below}")
try:
    sigma_coeffs(40, middle='m-1'); print("brief's recursion: integral (unexpected)")
except AssertionError as e:
    print("brief's recursion variant a_{m-1,n+1}: non-integral at", e)
