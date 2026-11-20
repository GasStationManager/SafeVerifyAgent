"""Parts 2 and 4: p-adic valuations of D^a sigma(0) for CM and non-CM curves.
Usage: python3 -I run_valuations.py [N] [--perturb m n]
Curves are given by (h2, h3) = (g2/2, 2 g3); D^a sigma(0) = sum a_{m,n} h2^m h3^n is an integer."""
import sys, os, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sigma_lib import sigma_derivs_stream, vp, vp_fact
from fractions import Fraction as F

args = sys.argv[1:]
N = int(args[0]) if args and args[0].isdigit() else 6000
perturb = None
if '--perturb' in args:
    i = args.index('--perturb'); perturb = (int(args[i + 1]), int(args[i + 2]))
PR = [5, 7, 11, 13, 17, 19, 23, 29, 31]
CURVES = {  # name: (h2, h3, description)
    'A  y^2=4x^3-4x  (CM Z[i])': (2, 0),
    'B  y^2=4x^3-4   (CM Z[w])': (0, 8),
    'C  g2=-10,g3=7/2 (non-CM)': (-5, 7),
    'C2 g2=-4,g3=7/2  (non-CM)': (-2, 7),
}

def a_p(h2, h3, p):
    g2 = 2 * h2 % p; g3 = h3 * pow(2, -1, p) % p
    sq = [0] * p
    for y in range(p): sq[y * y % p] += 1
    return p + 1 - (1 + sum(sq[(4 * x ** 3 - g2 * x - g3) % p] for x in range(p)))

def disc(h2, h3):
    g2 = F(2 * h2); g3 = F(h3, 2); return g2 ** 3 - 27 * g3 ** 2

t0 = time.time()
D = sigma_derivs_stream(N, {k: v for k, v in CURVES.items()}, perturb=perturb)
print(f"# N = {N}, perturb = {perturb}, recursion time {time.time()-t0:.1f}s")
THR = [t for t in (100, 250, 500, 1000, 2000, 3000, 4000, 6000, 8000) if t <= N]
if N not in THR: THR.append(N)

for name, (h2, h3) in CURVES.items():
    Dl = disc(h2, h3)
    print(f"\n## Curve {name}: Delta = {Dl}")
    nz = [k for k in range(1, N + 1) if D[name][k] != 0]
    print(f"nonzero D^a sigma(0): a in {{{', '.join(map(str, nz[:6]))}, ...}}, count {len(nz)}")
    for p in PR:
        if Dl.numerator % p == 0:
            print(f"p={p}: bad reduction, skipped"); continue
        ap = a_p(h2, h3, p)
        ss = (ap % p == 0)
        typ = 'SUPERSINGULAR' if ss else 'ordinary'
        g = F(p, p * p - 1)
        rows = []
        for a in nz:
            v = vp(D[name][a], p)
            vf = vp_fact(a, p)
            weven = 0; q = p * p
            while q <= a: weven += a // q; q *= p * p
            rows.append(dict(a=a, v=v, dg=v - g * a, dlean=v - (vf - F(a, p * p - 1)),
                             d1=v - F(a, p * p - 1), dev=v - weven, vf=vf))
        hdr = f"p={p:2d} a_p={ap:+3d} {typ:13s} gamma_p={float(g):.5f} 1/(p^2-1)={1/(p*p-1):.5f}"
        out = [hdr]
        for T in THR:
            sub = [r for r in rows if r['a'] <= T]
            mg = min(sub, key=lambda r: r['dg']); m1 = min(sub, key=lambda r: r['d1'])
            out.append(f"   a<={T:5d}: min[v-gamma_p a]={float(mg['dg']):9.2f}   "
                       f"min[v-a/(p^2-1)]={float(m1['d1']):6.2f} (a={m1['a']})   "
                       f"min[v-sum_k floor(a/p^2k)]={min(r['dev'] for r in sub):3d}   "
                       f"max[v-sum_k floor(a/p^2k)]={max(r['dev'] for r in sub):3d}   "
                       f"log_p A={math.log(T, p):5.2f}   max v={max(r['v'] for r in sub)}")
        tail = [r for r in rows if r['a'] > N // 2]
        li = min(F(r['v'], r['a']) for r in tail)
        xs = [r['a'] for r in tail]; ys = [r['v'] for r in tail]
        mx = sum(xs) / len(xs); my = sum(ys) / len(ys)
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        zero = sum(1 for r in rows if r['v'] == 0)
        out.append(f"   tail a in ({N//2},{N}]: min v/a={float(li):.5f}, LSQ slope dv/da={slope:.5f}; "
                   f"#(v=0) {zero}/{len(rows)}; v_p(c_a)=v-v_p(a!): min over all a = {min(r['v']-r['vf'] for r in rows)}")
        pick = {nz[len(nz) // 4], nz[len(nz) // 2], nz[-1]}
        out.append("   rows (a: v_p(D^a sigma(0)) | claimed gamma_p a | a/(p^2-1) | v_p(a!)): " + "; ".join(
            f"({r['a']}: {r['v']} | {float(g*r['a']):.1f} | {r['a']/(p*p-1):.1f} | {r['vf']})"
            for r in rows if r['a'] in pick))
        print("\n".join(out))
print(f"\n# total time {time.time()-t0:.1f}s")
