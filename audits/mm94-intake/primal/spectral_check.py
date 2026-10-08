"""Sanity check of the primal claim  S(a,a) (x) T_A  >~  T_{A D*(a)^2}  against known spectral points.
For any character, lambda(S(a,a)) >= lambda(T_{D*^2}) = D*^{2(pX+pY+pZ)}.  Known characters have pX+pY+pZ = 2:
  flattening:  lambda(C(a,b)) = (a, b, a+b-1) ranks -> lambda(S(a,a)) = a^4 (2a-1)^2
  quantum functional F^theta (= support functional, C(a,a) is tight): F^theta(C) = max_P 2^{sum theta_i H(P_i)},
  and prod over the six leg permutations is prod_pi F^{pi theta}(C).  We use the uniform P on the support as a
  LOWER bound on F (max over P), so a pass here is a genuine pass.
Need: value >= D*(a)^4."""
import math
from lp_cert import Dstar
def Hbits(p): return -sum(x*math.log2(x) for x in p if x > 0)
print(" a   D*^4        flattening   QF(uniform-P, theta=(1/3,1/3,1/3)) ratio_flat ratio_QF")
for a in range(2, 31):
    D4 = float(Dstar(a))**4
    flat = a**4 * (2*a-1)**2
    # uniform P on support {(i,j,i+j)}: H(i)=H(j)=log2 a, H(i+j) = entropy of the triangular distribution
    conv = [0]*(2*a-1)
    for i in range(a):
        for j in range(a): conv[i+j] += 1/(a*a)
    hsum = 2*math.log2(a) + Hbits(conv)          # H1+H2+H3 in bits
    # F^theta(C^pi) for theta uniform = 2^{(H1+H2+H3)/3}; six-fold product = 2^{2(H1+H2+H3)}
    qf = 2**(2*hsum)
    print(f"{a:2d} {D4:12.1f} {flat:12.1f} {qf:12.1f}   {flat/D4:7.3f}  {qf/D4:7.3f}")
