# GL2 over Q_{p^f} (f=1,2): V = Sym^k via embedding 0, lattice HL(L)=monomials (H0/Sym lattice).
# W(L) = sum over the q+1 index-q neighbours L' (pL < L' < L) of p^k * HL(L'), inside HL(L).
# Output: p-adic elementary divisors of W(L) in HL(L)  (colength = their sum).
from fractions import Fraction as Fr
from math import comb
import itertools, sys
p=int(sys.argv[1]); f=int(sys.argv[2]); ks=[int(x) for x in sys.argv[3:]]
# ring Q_p(t), t^2 = s*t + r irreducible mod p (f=2); f=1: plain
def find_poly(p):
    for s in range(p):
        for r in range(p):
            if all((x*x - s*x - r)%p for x in range(p)): return s,r
S,R=find_poly(p) if f==2 else (0,0)
class E:
    __slots__=('a','b')
    def __init__(s,a,b=0): s.a=Fr(a); s.b=Fr(b)
    def __add__(s,o): return E(s.a+o.a,s.b+o.b)
    def __sub__(s,o): return E(s.a-o.a,s.b-o.b)
    def __mul__(s,o):
        # (a+bt)(c+dt) = ac + (ad+bc)t + bd t^2, t^2 = S t + R
        a,b,c,d=s.a,s.b,o.a,o.b
        return E(a*c+b*d*R, a*d+b*c+b*d*S)
    def iszero(s): return s.a==0 and s.b==0
    def inv(s):
        # conj: t -> S - t ; (a+bt)(a+b(S-t)) = a^2+abS - b^2(t^2 - S t)= a^2+abS - b^2 R  (norm)
        a,b=s.a,s.b; N=a*a+a*b*S-b*b*R; return E((a+b*S)/N, -b/N)
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
def run(k):
    cs=[E(a,b) for a in range(p) for b in (range(p) if f==2 else [0])]
    q=p**f
    gens=[]
    # neighbours: columns (p,0),(c,1) for c in F_q ; and (1,0),(0,p)
    nb=[(E(p),c,E(0),E(1)) for c in cs]+[(E(1),E(0),E(0),E(p))]
    pk=powE(E(p),k)
    for (A,B,C,D) in nb:
        det=A*D-B*C; di=det.inv()
        ia,ib,ic,id_=D*di, E(0)-B*di, E(0)-C*di, A*di   # g^{-1}
        for i in range(k+1):
            # x^i y^(k-i) at (ia x + ib y, ic x + id y)
            co=[E(0) for _ in range(k+1)]
            Apow=[E(comb(i,s))*powE(ia,s)*powE(ib,i-s) for s in range(i+1)]
            Bpow=[E(comb(k-i,s))*powE(ic,s)*powE(id_,k-i-s) for s in range(k-i+1)]
            for s1,u in enumerate(Apow):
                for s2,v in enumerate(Bpow): co[s1+s2]=co[s1+s2]+u*v
            gens.append([x*pk for x in co])
    for g in gens: assert all(val(x)>=0 for x in g)
    n=k+1; M=[g[:] for g in gens]; out=[]; cols=list(range(n))
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
for k in ks:
    ed=run(k); q=p**f
    print("p=%d f=%d q=%d k=%d  ED=%s  colen/dim=%.2f  k/(q+1)=%.2f k/4=%.2f"%(p,f,q,k,ed,sum(ed)/(k+1),k/(q+1),k/4))
