import cmath, itertools, random
from collections import defaultdict

def run(M, dX, dY, dZ, L=None, seed=0, verbose=False):
    rnd = random.Random(seed)
    L = L or 5*M
    zeta = cmath.exp(2j*cmath.pi/L)
    # blocks A_h in X (x) Y_h (x) Z_h, h = 1..M, random complex
    A = {h: {(a,b,c): complex(rnd.randint(-3,3), rnd.randint(-3,3)) or 1
             for a in range(dX) for b in range(dY) for c in range(dZ)} for h in range(1,M+1)}
    # source: L copies of sum_h A_h with variables x^(r)_a, y^(r)_{h,b}, z^(r)_{h,c}
    # substitution: x^(r)_a -> sum_g zeta^{2rg} eps^{g^2} X_{a,g}
    #               y^(r)_{h,b} -> sum_u zeta^{r(u-h)} eps^{hu-h^2} Y_{h,b,u}
    #               z^(r)_{h,c} -> (1/L) sum_v zeta^{r(-v-h)} eps^{-hv} Z_{h,c,v}
    # target coefficient of X_{a,g} Y_{h,b,u} Z_{h2,c,v}: poly in eps (dict exp->coef)
    T = defaultdict(lambda: defaultdict(complex))
    R = range(1,M+1)
    for r in range(L):
        for h in R:
            for (a,b,c),coef in A[h].items():
                for g in R:
                    for u in R:
                        for v in R:
                            ph = zeta**(2*r*g) * zeta**(r*(u-h)) * zeta**(r*(-v-h)) / L
                            w = g*g + (h*u-h*h) + (-h*v)
                            T[(a,g,h,b,u,h,c,v)][w] += coef*ph
    # cross-sector terms (h != h2 on Y,Z) never arise since A has no such terms.
    tol = 1e-9
    minw = None; surv_ok = True; neg_ok = True
    for key, poly in T.items():
        a,g,h,b,u,h2,c,v = key
        nz = {w:val for w,val in poly.items() if abs(val) > tol}
        assert len(poly) == 1
        w = next(iter(poly))
        phase = u - v + 2*(g-h)
        survives = bool(nz)
        if survives != (phase == 0 and abs(A[h][(a,b,c)])>0): surv_ok = False
        if survives:
            if w != (g-h)**2: surv_ok = False
            if w < 0: neg_ok = False
            minw = w if minw is None else min(minw, w)
            if w == 0 and not (g == h and u == v): surv_ok = False
            if w == 0 and abs(nz[0]-A[h][(a,b,c)])>1e-9: surv_ok=False
    # weight-zero tensor vs direct sum (+)_h A_h (x) B_X(M):
    # target index X:(a,g) Y:(h,b,u) Z:(h2,c,v); expected coef = [g=h=h2][u=v] A_h[a,b,c]
    D_ok = True
    for a in range(dX):
      for g in R:
        for h in R:
          for b in range(dY):
            for u in R:
              for h2 in R:
                for c in range(dZ):
                  for v in R:
                    got = T.get((a,g,h,b,u,h2,c,v), {}).get(0, 0) if h==h2 else 0
                    exp = A[h][(a,b,c)] if (g==h==h2 and u==v) else 0
                    if abs(got-exp) > 1e-9: D_ok = False
    # max |phase| and wrap
    maxph = max(abs(u-v+2*(g-h)) for g,h,u,v in itertools.product(R,R,R,R))
    return dict(M=M, L=L, surv_ok=surv_ok, nonneg_surviving=neg_ok, minw=minw,
                weight0_is_directsum=D_ok, max_phase=maxph, bound=3*(M-1))

print(run(2,1,1,1,L=10))
for M in range(1,6):
    print(run(M,2,2,1,seed=M))
# negative control: too few copies -> wrap-around should break exactness
for M,L in [(3,6),(3,7),(4,9),(3,3*(3-1))]:
    print('control', run(M,1,1,1,L=L,seed=7))
