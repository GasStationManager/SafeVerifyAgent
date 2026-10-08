import math
d,k,m,RD,nu,delta,u,Rs = 2,4,1,10,2.3,0.01,2,5
tau = nu+delta
print("d^nu =", d**nu, "> k =", k)
# limit form after j->inf: n*k + R(D) >= d^nu * n^(nu/tau)
for e in range(0,7):
    n = 10**e
    lhs = n*k+RD; rhs = d**nu * n**(nu/tau)
    print(f"n=1e{e}: nk+R(D)={lhs:.4g}  d^nu n^(nu/tau)={rhs:.4g}  holds={lhs>=rhs}")
# delta->0 form: n*k+R(D) >= n d^nu fails once n > R(D)/(d^nu-k)
print("delta->0 bound fails for n >", RD/(d**nu-k))
# finite-j form (no limits): (d^j g_j)^nu <= u^0*R(s)*K^j with g_j=u^floor(j log_u n/tau)
n = 10**4; K = n*k+RD
for j in (1,10,100,1000,10000):
    l = math.floor(j*math.log(n,u)/tau)
    lhs = nu*(j*math.log(d)+l*math.log(u)); rhs = math.log(Rs)+j*math.log(K)
    print(f"n=1e4 j={j}: log(d^j g_j)^nu={lhs:.1f} log R(s)K^j={rhs:.1f} rank-bound-consistent={lhs<=rhs}")
# order of limits: at FIXED delta the j-limit inequality is satisfied again for huge n
for e in (20,21,22,30):
    n=10**e; print(f"fixed delta n=1e{e}: holds={n*k+RD >= d**nu * n**(nu/tau)}")
