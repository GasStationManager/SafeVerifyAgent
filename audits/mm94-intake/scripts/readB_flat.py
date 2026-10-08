from fractions import Fraction
from itertools import product
def rank(M):
    M=[[Fraction(v) for v in row] for row in M]
    r=0; rows=len(M); cols=len(M[0]) if M else 0
    for c in range(cols):
        p=next((i for i in range(r,rows) if M[i][c]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        for i in range(rows):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]
                M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        r+=1
    return r
# tensor as dict over (X,Y,Z) index lists
def tensor(X,Y,Z,f): return (X,Y,Z,{(x,y,z):f(x,y,z) for x in X for y in Y for z in Z})
def flat(T,leg):
    X,Y,Z,d=T; legs=[X,Y,Z]; others=[l for i,l in enumerate(legs) if i!=leg]
    M=[]
    for a in legs[leg]:
        row=[]
        for b in others[0]:
            for c in others[1]:
                idx=[None]*3; idx[leg]=a
                o=[i for i in range(3) if i!=leg]; idx[o[0]]=b; idx[o[1]]=c
                row.append(d[tuple(idx)])
        M.append(row)
    return rank(M)
def Tn(a,b,c):  # matrixMultiplication a b c : x=(i,j), y=(j',k), z=(k',i'), 1 iff j=j',k=k',i'=i
    X=list(product(range(a),range(b)));Y=list(product(range(b),range(c)));Z=list(product(range(c),range(a)))
    return tensor(X,Y,Z,lambda x,y,z: int(x[1]==y[0] and y[1]==z[0] and z[1]==x[0]))
def dot(m): # Lean dotPairing: Tensor U U Unit = B_Z
    return tensor(list(range(m)),list(range(m)),[()],lambda x,y,z:int(x==y))
def cyc(T): # cyclic T : Y Z X, (cyclic T) y z x = T x y z
    X,Y,Z,d=T; return (Y,Z,X,{(y,z,x):d[(x,y,z)] for x in X for y in Y for z in Z})
def prod_(T,S):
    X,Y,Z,d=T;U,V,W,e=S
    return tensor(list(product(X,U)),list(product(Y,V)),list(product(Z,W)),lambda x,y,z:d[(x[0],y[0],z[0])]*e[(x[1],y[1],z[1])])
def dsum(T,S):
    X,Y,Z,d=T;U,V,W,e=S
    XX=[(0,x) for x in X]+[(1,u) for u in U];YY=[(0,y) for y in Y]+[(1,v) for v in V];ZZ=[(0,z) for z in Z]+[(1,w) for w in W]
    def f(x,y,z):
        if x[0]==y[0]==z[0]==0: return d[(x[1],y[1],z[1])]
        if x[0]==y[0]==z[0]==1: return e[(x[1],y[1],z[1])]
        return 0
    return tensor(XX,YY,ZZ,f)
print("n: flattening ranks (X,Y,Z) of T_n")
for n in range(1,6): print(n,[flat(Tn(n,n,n),l) for l in range(3)], "n^2=",n*n)
print("m: B_Z=dot(m), B_Y=cyc(dot), B_X=cyc(cyc(dot)) X/Y/Z-flattening ranks")
for m in range(1,6):
    BZ=dot(m);BY=cyc(BZ);BX=cyc(BY)
    print(m,"BX",[flat(BX,l) for l in range(3)],"BY",[flat(BY,l) for l in range(3)],"BZ",[flat(BZ,l) for l in range(3)])
# check B_X(m)⊗B_Y(m)⊗B_Z(m) flattening equals T_m flattening, and multiplicativity/additivity
for m in range(1,4):
    BZ=dot(m);BY=cyc(BZ);BX=cyc(BY)
    P=prod_(prod_(BX,BY),BZ)
    print("m",m,"prod BX BY BZ flats",[flat(P,l) for l in range(3)],"T_m",[flat(Tn(m,m,m),l) for l in range(3)])
A=Tn(2,2,2);B=Tn(1,2,3)
print("mult",[flat(prod_(A,B),l) for l in range(3)],[flat(A,l)*flat(B,l) for l in range(3)])
print("add ",[flat(dsum(A,B),l) for l in range(3)],[flat(A,l)+flat(B,l) for l in range(3)])
# value_matrixCoefficients: chi(T(a,b,c)) = b^pZ a^pY c^pX ; X-flattening (pX,pY,pZ)=(0,1,1): a*b
for (a,b,c) in [(1,2,3),(2,3,4),(3,1,2)]:
    T=Tn(a,b,c); print((a,b,c),"X-flat",flat(T,0),"pred b^1 a^1 c^0=",a*b,"Y-flat",flat(T,1),"pred b*c=",b*c,"Z-flat",flat(T,2),"pred c*a=",c*a)
