import math
# Lean recurrence (Growth.lean:142-144, RecursiveBlockPrograms.lean:350):
# S(0)=1, S(k+1) = R*S(k) + K*(u^k)^2 with K = 6*R*u^2, N = u^k
def S(u,R,kmax):
    K=6*R*u*u; s=1; out=[(1,s)]
    for k in range(kmax):
        s=R*s+K*(u**k)**2; out.append((u**(k+1),s))
    return out
for (u,R) in [(2,4),(3,9),(2,7),(3,23),(4,49)]:
    rows=S(u,R,30)
    print(f"u={u} R={R} (u^2={u*u})")
    for N,s in rows[10::5]:
        k=round(math.log(N,u))
        if R==u*u: print(f"  k={k:3d} S/(N^2 log_u N)={s/(N*N*k):.4f}")
        else:
            e=math.log(R,u); print(f"  k={k:3d} S/N^log_u R={s/N**e:.4f}  (exp {e:.4f})")
# also check the Lean geometric bound: x_k <= C q^k with C = x0 + b/(q-a) + 1, a=R,b=K,d=u^2,q=u^(tau+eps)
for (u,R,eps) in [(2,4,0.01),(2,7,0.001)]:
    tau=max(2,math.log(R,u)); q=u**(tau+eps); K=6*R*u*u; C=1+K/(q-R)+1
    ok=all(s<=C*q**k*(1+1e-12) for k,(N,s) in enumerate(S(u,R,200)))
    print(f"geom bound u={u} R={R} eps={eps}: C={C:.3e} holds for k<=200: {ok}")
