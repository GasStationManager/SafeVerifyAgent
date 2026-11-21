"""NODE-NUMTEST3 engine: the Lean theta kernel in its smallest instance (see NODE-NUMTEST3.md, Sec. A).

Smallest instance (host E = Q(sqrt-d, sqrt-q) biquadratic, |Tau| = 2, one place v over p with n'_v = 2,
Frob_p = c*g where Gal(E/K) = {1, g}; positions s = 0, 1 <-> tau_0 = 1, tau_1 = g):

  one matrix entry of thZero = tensPow(thMM) is   thMM(z_0, z_1) = th0(u_1) th0(u_2),   u = M^* z,

with M = (tau(a_k))_{tau,k} unitary (a_1, a_2 an orthonormal O_K-basis of AA0 for tr_{E/K}(x xbar)), and
th0 = opU(omega_0/2)(sigma*) / opU(omega_0/2)(sigma*)(0) (SemiChar.lean:34), i.e. the co-sigma function

  th0(z) = sigma*(z+t) exp(-pi z tbar/A) / sigma*(t),    t = omega_0/2 a 2-torsion point,
  log th0 '' = -wp(z+t) - s2,  log th0(0) = log th0'(0) = 0.

For Z[i] and Z[w], s2 = 0.  All jets T_n = th0^(n)(0) are INTEGERS (computed below from wp^(m)(t)).

After the unit rescaling z -> z/abar_1 the kernel becomes, at a served inert p,

  Theta(z0, z1) = th0(z0 + z1) * th0(c (z0 - z1)),   c in Z_{p^2},  c * c^sigma = -1      (served, isotropic)

and the Lean jet entry (one entry, unrescaled) is J(a,w) = d_{z0}^a d_{z1}^w Theta(0):
  J(a,w) = sum_k S(a,w,k) T_k T_{n-k} c^{n-k},  n = a+w,  S(a,w,k) = [x^k y^{n-k}] (x+y)^a (x-y)^w.
Control (non-served inert p, Frob_p = c): same formula with c c^sigma = +1 (anisotropic directions).
"""
from math import comb, log


# ---------------------------------------------------------------- th0 jets (exact integers)
def wp_at_t_derivs(g2, g3, e, N):
    """Q_m = wp^(m)(t), m <= N, at a 2-torsion point t with wp(t) = e (4e^3 - g2 e - g3 = 0).
    wp'' = 6 wp^2 - g2/2, wp'(t) = 0.  Needs g2 even (g2/2 integer)."""
    assert 4 * e ** 3 - g2 * e - g3 == 0 and g2 % 2 == 0
    Q = [0] * (N + 1)
    Q[0] = e
    for m in range(0, N - 1):
        s = 6 * sum(comb(m, k) * Q[k] * Q[m - k] for k in range(m + 1))
        if m == 0: s -= g2 // 2
        Q[m + 2] = s
    return Q


def th0_jets(g2, g3, e, N, s2=0):
    """T_n = th0^(n)(0), n <= N (integers). L = log th0, L_k = L^(k)(0): L_2 = -e - s2, L_k = -Q_{k-2}.
    th0' = L' th0  =>  T_{n+1} = sum_k C(n,k) L_{k+1} T_{n-k}."""
    Q = wp_at_t_derivs(g2, g3, e, N)
    L = [0] * (N + 2)
    for k in range(2, N + 2):
        L[k] = -Q[k - 2]
    L[2] -= s2
    T = [0] * (N + 1)
    T[0] = 1
    for n in range(0, N):
        T[n + 1] = sum(comb(n, k) * L[k + 1] * T[n - k] for k in range(n + 1))
    return T


# ---------------------------------------------------------------- Z_{p^2} = Z_p[th]/(th^2 - n0) mod p^K
class Zp2:
    def __init__(self, p, K, n0=None):
        self.p, self.K, self.q = p, K, p ** K
        if n0 is None:
            n0 = next(x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1)
        self.n0 = n0

    def mul(self, x, y):
        q = self.q
        return ((x[0] * y[0] + self.n0 * x[1] * y[1]) % q, (x[0] * y[1] + x[1] * y[0]) % q)

    def add(self, x, y):
        return ((x[0] + y[0]) % self.q, (x[1] + y[1]) % self.q)

    def smul(self, s, x):
        return (s * x[0] % self.q, s * x[1] % self.q)

    def sig(self, x):
        return (x[0], -x[1] % self.q)

    def norm(self, x):  # x * sigma(x) in Z_p
        return (x[0] * x[0] - self.n0 * x[1] * x[1]) % self.q

    def v(self, x):
        def vi(t):
            t %= self.q
            if t == 0: return self.K
            k = 0
            while t % self.p == 0: t //= self.p; k += 1
            return k
        return min(vi(x[0]), vi(x[1]))

    def sqrt_mod(self, a):
        """square root of a p-adic unit a in Z_p (mod p^K), Hensel."""
        p, q = self.p, self.q
        a %= q
        r = next(x for x in range(1, p) if (x * x - a) % p == 0)
        k = 1
        while k < self.K:
            k = min(2 * k, self.K)
            m = p ** k
            r = (r - (r * r - a) * pow(2 * r, -1, m)) % m
        return r % q

    def elt_of_norm(self, target, b=1):
        """x = (a, b) with a^2 - n0 b^2 = target (mod p^K); b fixed, a by Hensel (needs target + n0 b^2 a square unit)."""
        t = (target + self.n0 * b * b) % self.q
        if pow(t % self.p, (self.p - 1) // 2, self.p) != 1:
            return None
        return (self.sqrt_mod(t), b % self.q)


# ---------------------------------------------------------------- the jet entries
def jets_grid(T, R, c, ws, amax):
    """J(a,w) for w in ws, a <= amax, in ring R (Zp2), Theta = th0(z0+z1) th0(c(z0-z1)).
    Returns dict (a,w) -> ring element.  Uses S(a+1,w,k) = S(a,w,k) + S(a,w,k-1)."""
    q = R.q
    N = amax + max(ws) + 1
    cp = [(1, 0)]
    for k in range(N):
        cp.append(R.mul(cp[-1], c))
    g = [R.smul(T[k], cp[k]) for k in range(N)]  # c^k T_k
    out = {}
    for w in ws:
        # S(0,w,k) = [x^k y^{w-k}] (x - y)^w = C(w,k) (-1)^{w-k}
        S = [comb(w, k) * (-1) ** (w - k) % q for k in range(w + 1)]
        for a in range(0, amax + 1):
            n = a + w
            if n % 2 == 0:
                acc0 = acc1 = 0
                for k in range(0, n + 1, 2):
                    s = S[k]
                    if s == 0: continue
                    f = T[k] * s
                    gg = g[n - k]
                    acc0 += f * gg[0]; acc1 += f * gg[1]
                out[(a, w)] = (acc0 % q, acc1 % q)
            else:
                out[(a, w)] = (0, 0)
            # multiply by (x + y): S'[k] = S[k] + S[k-1]
            S = [(S[k] if k < len(S) else 0) + (S[k - 1] if k >= 1 else 0) for k in range(len(S) + 1)]
            S = [s % q for s in S]
    return out


# ---------------------------------------------------------------- predictions
def vp_fact(n, p):
    s, t = 0, p
    while t <= n:
        s += n // t; t *= p
    return s


def gam(p): return p / (p * p - 1)


def lean_pred(a, w, p):
    """Lean's capped gain, rank one, cap w at the single partner position: sum_{e odd} (a/p^e - w)_+."""
    s, e = 0.0, 1
    while p ** e <= a:
        s += max(0.0, a / p ** e - w); e += 2
    return s


def lt_pred(a, w, p):
    """Gaussian-free LT law for w = 0 (exp_LT denominators): v_p(a!) - (a-1)/(p^2-1)."""
    return vp_fact(a, p) + vp_fact(w, p) - max(a + w - 1, 0) / (p * p - 1)


def sigma_like(a, w, p):
    return (a + w) / (p * p - 1)
