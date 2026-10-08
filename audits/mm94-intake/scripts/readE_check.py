from fractions import Fraction as F
import itertools, math

def rank(M):
    M=[[F(x) for x in r] for r in M]; r=0
    rows=len(M); cols=len(M[0]) if M else 0
    for c in range(cols):
        p=None
        for i in range(r,rows):
            if M[i][c]!=0: p=i;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        for i in range(rows):
            if i!=r and M[i][c]!=0:
                f=M[i][c]/M[r][c]
                M[i]=[a-f*b for a,b in zip(M[i],M[r])]
        r+=1
    return r

def C(a,b):
    return {(i,j,i+j):1 for i in range(a) for j in range(b)}, (a,b,a+b-1)

def flat(T,dims,leg):
    d=dims; others=[l for l in range(3) if l!=leg]
    idx=list(itertools.product(range(d[others[0]]),range(d[others[1]])))
    M=[]
    for x in range(d[leg]):
        row=[]
        for (u,v) in idx:
            key=[0,0,0]; key[leg]=x; key[others[0]]=u; key[others[1]]=v
            row.append(T.get(tuple(key),0))
        M.append(row)
    return rank(M)

# (i) flattening ranks
ok=True
for a in range(1,7):
    for b in range(1,7):
        T,d=C(a,b)
        r=(flat(T,d,0),flat(T,d,1),flat(T,d,2))
        if r!=(a,b,a+b-1): ok=False; print("bad",a,b,r)
print("(i) flattening ranks (a,b,a+b-1) for a,b<=6:",ok)

# (ii) X-flattening character: lambda(T)=rank of X-flattening; p_X = exponent on B_X(n) (singleton X leg) -> rank 1 -> pX=0; pY: B_Y(n): X dim n -> rank n -> 1; pZ=1.
# six permuted values on C(a,b): flattening ranks of leg pi(0): each leg appears twice -> product (a b (a+b-1))^2, t=2/3, P=(prod)^(1/(6t)) = (a b (a+b-1))^(1/2)
def P(a,b): return (a*b*(a+b-1))**0.5
t=2/3
ok=True
for a in range(1,13):
    for b in range(1,13):
        if abs(P(a,b)-P(b,a))>1e-9: ok=False
        if P(a,b)<=0: ok=False
        if P(a,b) > (a+b-1)**(1/t)+1e-9: ok=False; print("rank",a,b)
    if abs(P(1,a)-a)>1e-9: ok=False; print("bdry",a)
for a in range(1,13):
    for b in range(2,13):
        if 2*P(a,b) < P(a,b+1)+P(a,b-1)-1e-9: ok=False; print("conc",a,b)
for a in range(1,13):
    for h in range(1,13):
        if P(a,3*h+a-1) < 3*P(a,h)-1e-9: ok=False; print("trip",a,h,P(a,3*h+a-1),3*P(a,h))
print("(ii) (4.5), Lemma 4.1, Lemma 4.2 for X-flattening profile, a,b,h<=12:",ok)
# also check the per-character pre-symmetrization forms for each of the 6 permuted flattening characters
# lambda_pi = flattening rank of one leg; pX^(pi) = 1 if that leg is not X ... compute directly
def lam(leg,a,b): return [a,b,a+b-1][leg]
def pXpi(leg): return 0 if leg==0 else 1   # B_X(n) has X-dim 1, flattening of Y or Z leg has rank n
ok=True
for leg in range(3):
  p=pXpi(leg)
  for a in range(1,10):
    for b in range(2,10):
      for q in [0,0.1,0.3,0.5,0.77,1]:
        H=0 if q in (0,1) else -q*math.log(q)-(1-q)*math.log(1-q)
        lhs=math.exp(p*H)*lam(leg,a,b+1)**q*lam(leg,a,b-1)**(1-q)
        if lhs> 2**p*lam(leg,a,b)+1e-9: ok=False; print("conc tag",leg,a,b,q)
    for h in range(1,10):
      Cs=[a,a+h-1,h][leg]  # C^sigma legs: (a, a+h-1, h)
      lhs=3**p*lam(leg,a,h)**(2/3)*Cs**(1/3)
      if lhs> lam(leg,a,3*h+a-1)+1e-9: ok=False; print("trip tag",leg,a,h)
print("(ii') per-character tag inequalities for the three flattening ranks:",ok)
