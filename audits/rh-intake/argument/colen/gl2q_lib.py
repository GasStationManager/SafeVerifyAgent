
from fractions import Fraction as Fr
S=R=0; p=0
def setp(pp):
    global p,S,R
    p=pp
    for s in range(p):
        for r in range(p):
            if all((x*x - s*x - r)%p for x in range(p)):
                S,R=s,r; return
class E:
    __slots__=('a','b')
    def __init__(s,a,b=0): s.a=Fr(a); s.b=Fr(b)
    def __add__(s,o): return E(s.a+o.a,s.b+o.b)
    def __sub__(s,o): return E(s.a-o.a,s.b-o.b)
    def __mul__(s,o):
        a,b,c,d=s.a,s.b,o.a,o.b
        return E(a*c+b*d*R, a*d+b*c+b*d*S)
    def iszero(s): return s.a==0 and s.b==0
    def inv(s):
        a,b=s.a,s.b; N=a*a+a*b*S-b*b*R; return E((a+b*S)/N, -b/N)
def sig(e): return E(e.a+e.b*S, -e.b)
def vfr(x):
    if x==0: return 10**9
    n,d=x.numerator,x.denominator; v=0
    while n%p==0: n//=p; v+=1
    while d%p==0: d//=p; v-=1
    return v
def val(e): return min(vfr(e.a),vfr(e.b))
def powE(e,n):
    r=E(1)
    for _ in range(n): r=r*e
    return r
def elim(gens,n):
    M=[g[:] for g in gens]; out=[]; cols=list(range(n))
    while cols:
        best=None
        for ri,r in enumerate(M):
            for cj in cols:
                if not r[cj].iszero():
                    v=val(r[cj])
                    if best is None or v<best[0]: best=(v,ri,cj)
                    if v==0: break
            if best and best[0]==0: break
        v,ri,cj=best; out.append(v); piv=M.pop(ri); pinv=piv[cj].inv()
        newM=[]
        for r in M:
            if not r[cj].iszero():
                fct=r[cj]*pinv
                r=[r[t]-fct*piv[t] for t in range(n)]
            if any(not x.iszero() for x in r): newM.append(r)
        M=newM; cols.remove(cj)
    return sorted(out)
