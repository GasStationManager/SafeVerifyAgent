def run(a,h,verbose):
    B=3*h+a-1; rs=2*h+a-1
    midY=lambda y: h<=y<rs
    midZ=lambda z: h+a-1<=z<rs
    terms=[(x,y,x+y) for x in range(a) for y in range(B)]
    W={t:(1 if midY(t[1]) else 0)+(-1 if midZ(t[2]) else 0) for t in terms}
    assert min(W.values())>=0
    zero=[t for t in terms if W[t]==0]
    L={(x,y,z) for (x,y,z) in zero if y<h}
    M={(x,y,z) for (x,y,z) in zero if midY(y)}
    R={(x,y,z) for (x,y,z) in zero if y>=rs}
    C={(i,j,i+j) for i in range(a) for j in range(h)}
    # outer: translation
    Lok = {(x,y,z) for (x,y,z) in L}==C and all(z<h+a-1 for (_,_,z) in L)
    Rok = {(x,y-rs,z-rs) for (x,y,z) in R}==C
    # middle: x -> a-1-x (reverse), Y offset y-h is C's output, Z offset z-(h+a-1) is C's second input
    Mok = {(a-1-x, z-(h+a-1), y-h) for (x,y,z) in M}==C
    # Lean parametrization
    leanM={(a-1-u,h+u+r,h+a-1+r) for u in range(a) for r in range(h)}
    erased=[t for t in terms if W[t]==1]
    erased_ok=all(midY(y) and not midZ(z) for (_,y,z) in erased)
    if verbose:
        for t in terms: print(t,"w=",W[t], "L" if t in L else "M" if t in M else "R" if t in R else "-")
    return dict(nterms=len(terms),zero=len(zero),L=Lok,M=Mok,R=Rok,leanM=(leanM==M),erased=len(erased),erased_ok=erased_ok)
print("a=2,h=1:",run(2,1,True))
print("a=3,h=2:",run(3,2,True))
ok=all(all(v for k,v in run(a,h,False).items() if k in('L','M','R','leanM','erased_ok')) for a in range(1,9) for h in range(1,9))
print("all a,h<=8:",ok)
