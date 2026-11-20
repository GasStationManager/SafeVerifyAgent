"""Part 3: how much of log|D^a sigma(0)| is accounted for by inert primes.
Usage: python3 -I product_formula.py [N]"""
import sys, os, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sigma_lib import sigma_derivs_stream, vp, primes_upto

N = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
CURVES = {'A (Z[i])': ((2, 0), lambda p: p % 4 == 3, 4), 'B (Z[w])': ((0, 8), lambda p: p % 3 == 2, 6)}
D = sigma_derivs_stream(N, {k: v[0] for k, v in CURVES.items()})
P = primes_upto(N)
lf = lambda n: math.lgamma(n + 1)
for name, (_, inert, step) in CURVES.items():
    print(f"\n## curve {name}  (all logs natural)")
    print("   a | log|D^a| | (1/2)log a! | inert: actual sum v_p log p | claimed sum_{e odd} a/p^e log p | "
          "sum_{e even} floor(a/p^e) log p | split primes | p=2,3 | unfactored cofactor (log) | (log|D^a|-(1/2)log a!)/a")
    nz = [k for k in range(1, N + 1) if D[name][k]]
    picks = [nz[i] for i in (len(nz) // 8, len(nz) // 4, len(nz) // 2, 3 * len(nz) // 4, len(nz) - 1)]
    for a in picks:
        x = abs(D[name][a]); L = math.log(x)
        inert_act = split_act = small = 0.0; claim = even = 0.0; rest = x
        for p in P:
            if p > a: break
            v = vp(rest, p)
            if v: rest //= p ** v
            if p in (2, 3): small += v * math.log(p); continue
            if inert(p):
                inert_act += v * math.log(p)
                e, q = 1, p
                while q <= a:
                    if e % 2: claim += math.log(p) * a / q
                    else: even += math.log(p) * (a // q)
                    e += 1; q *= p
            else:
                split_act += v * math.log(p)
        cof = math.log(rest) if rest > 1 else 0.0
        print(f"{a:5d} | {L:9.1f} | {lf(a)/2:9.1f} | {inert_act:8.1f} | {claim:8.1f} | {even:7.1f} | "
              f"{split_act:6.1f} | {small:6.1f} | {cof:9.1f} | {(L - lf(a)/2)/a:.4f}")
    # growth constant: (log|D^a| - (1/2) log a!)/a along all nonzero a
    vals = [((math.log(abs(D[name][a])) - lf(a) / 2) / a) for a in nz if a > 50]
    print(f"   (log|D^a| - (1/2)log a!)/a : first {vals[0]:.4f}, a~N/2 {vals[len(vals)//2]:.4f}, last {vals[-1]:.4f}")
