from fractions import Fraction as F
# forms of bidegree (e,1) in u,v ; s,w : represent as dict {(i, c): coeff} meaning u^{e-i} v^i * (s if c==0 else w)
def solve(basis, vec, n):
    # basis: list of vectors (lists length n); solve sum c_k basis_k = vec, exact
    m=len(basis)
    A=[[F(basis[k][r]) for k in range(m)]+[F(vec[r])] for r in range(n)]
    piv=[];r=0
    for c in range(m):
        p=next((i for i in range(r,n) if A[i][c]!=0),None)
        if p is None: raise Exception("singular")
        A[r],A[p]=A[p],A[r]
        A[r]=[x/A[r][c] for x in A[r]]
        for i in range(n):
            if i!=r and A[i][c]!=0:
                f=A[i][c]; A[i]=[x-f*y for x,y in zip(A[i],A[r])]
        piv.append(c); r+=1
    assert all(all(x==0 for x in A[i]) for i in range(r,n))
    return [A[i][m] for i in range(m)]

def vec_index(e):  # coordinates: (i,c) for i in 0..e, c in {s,w}
    return [(i,c) for c in (0,1) for i in range(e+1)]

def adapted_basis(e):
    idx=vec_index(e); pos={k:n for n,k in enumerate(idx)}
    B=[]
    names=[]
    for i in range(e+1):  # u^{e-i} v^i s
        v=[0]*len(idx); v[pos[(i,0)]]=1; B.append(v); names.append(('q',i))
    v=[0]*len(idx); v[pos[(e,1)]]=1; B.append(v); names.append(('q',e+1))  # v^e w
    for j in range(e):   # D u^{e-1-j} v^j, D = u w - v s
        v=[0]*len(idx); v[pos[(j,1)]]+=1; v[pos[(j+1,0)]]-=1; B.append(v); names.append(('k',j))
    return B,names

def mult(i, e, vec):  # multiply by u^{d-i} v^i (degree shift in v index by i)
    idx=vec_index(e); out={}
    for n,(j,c) in enumerate(idx):
        if vec[n]: out[(j+i,c)]=out.get((j+i,c),0)+vec[n]
    return out

def check(a,b,verbose=False):
    d,e=a-1,b-1
    Bin,nin=adapted_basis(e); Bout,nout=adapted_basis(d+e)
    oidx=vec_index(d+e); opos={k:n for n,k in enumerate(oidx)}
    T={}
    for i in range(a):
        for jn,bv in enumerate(Bin):
            prod=mult(i,e,bv); pv=[0]*len(oidx)
            for k,v in prod.items(): pv[opos[k]]+=v
            coeffs=solve(Bout,pv,len(oidx))
            for kn,cf in enumerate(coeffs):
                if cf!=0: T[(i,nin[jn],nout[kn])]=cf
    # weights (paper): second leg kernel -1, output-dual kernel +1
    w2=lambda n: -1 if n[0]=='k' else 0
    w3=lambda n: 1 if n[0]=='k' else 0
    neg=[k for k in T if w2(k[1])+w3(k[2])<0]
    upper_right=[k for k in T if k[1][0]=='k' and k[2][0]=='q']
    star=[k for k in T if k[1][0]=='q' and k[2][0]=='k']
    zero={k:v for k,v in T.items() if w2(k[1])+w3(k[2])==0}
    Cplus={(i,j,i+j) for i in range(a) for j in range(b+1)}
    Cminus={(i,j,i+j) for i in range(a) for j in range(b-1)}
    qq={(i,j[1],k[1]) for (i,j,k),v in zero.items() if j[0]=='q' and k[0]=='q'}
    kk={(i,j[1],k[1]) for (i,j,k),v in zero.items() if j[0]=='k' and k[0]=='k'}
    allone=all(v==1 for v in zero.values())
    # Lean adaptedTensor formula
    lean={}
    for i in range(a):
        for j in range(e+2):
            for k in range(d+e+2):
                if i+j==k: lean[(i,('q',j),('q',k))]=1
            for k in range(d+e):
                if j==e+1 and i<d and e+i==k: lean[(i,('q',j),('k',k))]=1
        for j in range(e):
            for k in range(d+e):
                if i+j==k: lean[(i,('k',j),('k',k))]=1
    res=dict(neg=len(neg),upper_right=len(upper_right),star=sorted(star),
             qq_is_C_a_bplus1=(qq==Cplus),kk_is_C_a_bminus1=(kk==Cminus),allone=allone,
             lean_formula_matches=(lean=={k:int(v) for k,v in T.items()} and all(v in (1,) for v in T.values())))
    if verbose:
        for k in sorted(T): print(k,T[k])
    return res
print("a=b=2:"); print(check(2,2,verbose=True))
allok=True
for a in range(1,6):
    for b in range(2,7):
        r=check(a,b)
        if not(r['neg']==0 and r['upper_right']==0 and r['qq_is_C_a_bplus1'] and r['kk_is_C_a_bminus1'] and r['allone'] and r['lean_formula_matches']):
            allok=False; print("FAIL",a,b,r)
print("all a<=5, 2<=b<=6 ok:",allok)
