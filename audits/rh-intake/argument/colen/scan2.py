# Scan of pairfast.run: quantiles of the elementary divisors of W(L) for V = Sym^k0 (x) Sym^k1∘sigma (GL2, q=p^2)
# against the Lean main term min(k1, k0/p) (t0G4, ObjSeg.lean:439-442, segment G=2, d=1).
import sys, time
sys.path.insert(0, '.')
from pairfast import run
def q(ed, f):  # smallest t with #{ED > t} <= f*dim
    n = len(ed); s = sorted(ed)
    return s[min(n-1, max(0, int((1-f)*n + 0.999999) - 1))]
p = int(sys.argv[1]); pairs = [tuple(map(int, x.split(','))) for x in sys.argv[2:]]
print("p k0 k1 dim | mean q90 q95 max | base_max(k1=0) | min(k1,k0/p) k0/p^2 k1/p | max-base")
base = {}
for k0, k1 in pairs:
    if k0 not in base: base[k0] = max(run(p, k0, 0))
    t = time.time(); ed = run(p, k0, k1); n = len(ed)
    print("%d %d %d %d | %.2f %d %d %d | %d | %.2f %.2f %.2f | %d   (%.0fs)" % (p, k0, k1, n, sum(ed)/n, q(ed, .10), q(ed, .05), max(ed),
          base[k0], min(k1, k0/p), k0/p**2, k1/p, max(ed)-base[k0], time.time()-t), flush=True)
