# GL2 over Q_{p^2}: V = Sym^{k0}(std) (x) Sym^{k1}(std^sigma). Elementary divisors of
# W(L) = sum_{q+1 neighbours} p^{k0+k1} HL(L') inside HL(L) (monomial = H0 lattices).
import sys
from fractions import Fraction as Fr
from math import comb
exec(open('gl2q_lib.py').read())
p=int(sys.argv[1]); k0=int(sys.argv[2]); k1=int(sys.argv[3])
setp(p)
def transform(k,i,ia,ib,ic,id_):
    co=[E(0) for _ in range(k+1)]
    Ap=[E(comb(i,s))*powE(ia,s)*powE(ib,i-s) for s in range(i+1)]
    Bp=[E(comb(k-i,s))*powE(ic,s)*powE(id_,k-i-s) for s in range(k-i+1)]
    for s1,u in enumerate(Ap):
        for s2,v in enumerate(Bp): co[s1+s2]=co[s1+s2]+u*v
    return co
cs=[E(a,b) for a in range(p) for b in range(p)]
nb=[(E(p),c,E(0),E(1)) for c in cs]+[(E(1),E(0),E(0),E(p))]
pk=powE(E(p),k0+k1)
gens=[]
for (A,B,C,D) in nb:
    det=A*D-B*C; di=det.inv()
    g=(D*di, E(0)-B*di, E(0)-C*di, A*di); gs=tuple(sig(x) for x in g)
    T0=[transform(k0,i,*g) for i in range(k0+1)]
    T1=[transform(k1,j,*gs) for j in range(k1+1)]
    for i in range(k0+1):
        for j in range(k1+1):
            gens.append([T0[i][a]*T1[j][b]*pk for a in range(k0+1) for b in range(k1+1)])
for g in gens: assert all(val(x)>=0 for x in g)
ed=elim(gens,(k0+1)*(k1+1))
n=len(ed); q=p*p
print("p=%d k0=%d k1=%d dim=%d colen/dim=%.3f max=%d | k0/(q+1)=%.2f k1/(q+1)=%.2f (k0+p*k1)/(q+1)=%.2f min(k1,k0/p)=%.2f"%(p,k0,k1,n,sum(ed)/n,max(ed),k0/(q+1),k1/(q+1),(k0+p*k1)/(q+1),min(k1,k0/p)))
from collections import Counter; print(sorted(Counter(ed).items()))
