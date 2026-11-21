"""NODE-NUMTEST4 engine: the Lean theta kernel in an instance with residue degree n' = 4 (see NODE-NUMTEST4.md, Sec. A).

Host  E = K . F,  K = Q(sqrt-3) (curve C/Z[w]) or Q(i) (curve C/Z[i]),  F = Q(zeta_16)^+ = Q(eta), eta = 2cos(pi/8),
      eta^4 - 4 eta^2 + 2 = 0, O_F = Z[eta], Gal(F/Q) = (Z/16)^x/{+-1} = HGrp 2 (cyclic of order 4).
Gal(E/K) = Gal(F/Q) = Tau (CM type lifted from K).  z = Frob_p . c acts on F as Frob_p, so n' = ord(Frob_p | F):
      p = +-3, +-5 mod 16 -> n' = 4 (one place);  p = +-7 mod 16 -> n' = 2 (two places);  p = +-1 -> n' = 1 (not served).
Lattice: O_E = O_K (x) O_F with hermitian form tr_{E/K}(lam x ybar), lam = eps / eta^11 totally positive (lam O_F = D_F^-1),
      which has the orthonormal O_K-basis f_1..f_4 in O_F (found by enumeration; Gram = I_4 exactly).
One matrix entry of thZero:  Theta(z_0..z_3) = prod_k th0(u_k),  u_k = sum_s sigma^s(lam f_k) z_s   (z_s <-> tau = z^s).
The unit rescaling z_s -> z_s / sigma^s(lam) does not change any v_p, so we use m_{k,s} = sigma^s(f_k) in Z_p[eta] = Z_{p^4}
(p inert in F) or Z_p[eta]/(g) a product of fields (p not inert; then v is the min over the factors, see vring).

Jets J(a; n1, n2, n3) = d_{z0}^a d_{z1}^{n1} d_{z2}^{n2} d_{z3}^{n3} Theta(0), exact mod p^K.
Algorithm: pair products of factors (1,2) and (3,4) by binomial convolution, then one final convolution at sampled a.
"""
import itertools
from math import comb

# ---------------------------------------------------------------- F = Q(eta), exact integer arithmetic in Z[eta]
F_BASIS = [(-1, -1, 1, 1), (-1, 0, 1, -1), (-1, 0, 2, 0), (-1, 1, 2, -1)]   # orthonormal for tr(lam x y)
LAM_NUM = (82, -99, -24, 29)   # lam = LAM_NUM / 8 = (41/4, -99/8, -3, 29/8)


def zmul(x, y):
    c = [0] * 7
    for i in range(4):
        xi = x[i]
        if xi:
            for j in range(4):
                c[i + j] += xi * y[j]
    for d in (6, 5, 4):
        t = c[d]; c[d] = 0; c[d - 2] += 4 * t; c[d - 4] -= 2 * t
    return tuple(c[:4])


def zpow(x, n):
    r = (1, 0, 0, 0)
    for _ in range(n): r = zmul(r, x)
    return r


def ztr(x): return 4 * x[0] + 8 * x[2]


def cheb(k):
    """C_k(eta) = 2 cos(k pi/8) as an element of Z[eta]."""
    a, b = (2, 0, 0, 0), (0, 1, 0, 0)   # C_0, C_1
    if k == 0: return a
    for _ in range(k - 1):
        a, b = b, tuple(u - v for u, v in zip(zmul((0, 1, 0, 0), b), a))
    return b


def zsub(x, img):
    """x(eta) with eta -> img."""
    r = (0, 0, 0, 0); pw = (1, 0, 0, 0)
    for i in range(4):
        r = tuple(u + x[i] * v for u, v in zip(r, pw)); pw = zmul(pw, img)
    return r


def frob_img(p): return cheb(p % 16)


def frob_order(p):
    img = frob_img(p); x = (0, 1, 0, 0); n = 0
    while True:
        x = zsub(x, img); n += 1
        if x == (0, 1, 0, 0): return n


def galois_elt(k):
    """the element eta -> 2cos(k pi/8) of Gal(F/Q), k odd mod 16."""
    return cheb(k % 16)


def positions(p):
    """the four CM-type embeddings tau_0..tau_3 (as k mod 16, tau: eta -> 2cos(k pi/8)) in the order used for the
    variables z_0..z_3, and a label.  z = Frob_p c acts on F as Frob_p (k = p mod 16).
      n' = 4: tau_s = Frob^s  (one place; positions s = 0..3 of the Lean, posG = orbRep . z^s)
      n' = 2: (1, Frob | 3, 3 Frob)  (z_0, z_1 = the two positions of place v; z_2, z_3 = the other place)
      n' = 1: (1, 3, 5, 7)  (four places, no Frobenius partner)"""
    k = p % 16
    o = frob_order(p)
    if o == 4:
        return [pow(k, s, 16) for s in range(4)], "n'=4: z_s at position s (tau = Frob^s)"
    if o == 2:
        return [1, k, 3, (3 * k) % 16], "n'=2: z0,z1 = positions 0,1 of place v; z2,z3 = place v'"
    return [1, 3, 5, 7], "n'=1 (not served): four places"


def coeffs(p, nprime=None):
    """m[k][s] = tau_s(f_k)."""
    taus, _ = positions(p)
    return [[zsub(tuple(f), galois_elt(t)) for t in taus] for f in F_BASIS]


def check_global(p):
    """exact global checks: tr(lam f_k f_l) = delta; sum_k f_k sigma^j f_k = delta_j0 / lam (x8)."""
    lam8 = LAM_NUM
    G = [[ztr(zmul(lam8, zmul(F_BASIS[k], F_BASIS[l]))) for l in range(4)] for k in range(4)]
    ok1 = all(G[k][l] == (8 if k == l else 0) for k in range(4) for l in range(4))
    m = coeffs(p)
    out = []
    for j in range(4):
        s = (0, 0, 0, 0)
        for k in range(4):
            s = tuple(u + v for u, v in zip(s, zmul(m[k][0], m[k][j])))
        out.append(s)
    return ok1, out


# ---------------------------------------------------------------- ring Z[eta]/(p^K), packed into one Python int
class Ring:
    def __init__(self, p, K, slot_bits=None):
        self.p, self.K, self.q = p, K, p ** K
        qb = self.q.bit_length()
        self.S = slot_bits or (3 * qb + 40)
        self.M = (1 << self.S) - 1

    def pack(self, x):
        q, S = self.q, self.S
        return (x[0] % q) | ((x[1] % q) << S) | ((x[2] % q) << 2 * S) | ((x[3] % q) << 3 * S)

    def unpack(self, X, n=4):
        S, M = self.S, self.M
        return [(X >> (i * S)) & M for i in range(n)]

    def reduce7(self, X):
        """X = packed product (7 slots, nonneg, unreduced) -> packed reduced element."""
        c = self.unpack(X, 7)
        for d in (6, 5, 4):
            t = c[d]; c[d] = 0; c[d - 2] += 4 * t; c[d - 4] -= 2 * t
        return self.pack(c[:4])

    def reduce4(self, X):
        return self.pack(self.unpack(X, 4))

    def mul(self, X, Y): return self.reduce7(X * Y)

    def v(self, X):
        """p-adic valuation of a packed element (min over coordinates in the basis 1,eta,eta^2,eta^3; this is the
        valuation in Z_p[eta] = Z_{p^4} when p is inert in F, and the min over the factor fields otherwise since
        p is unramified in F and Z_p[eta] is the maximal order)."""
        p, K = self.p, self.K
        best = K
        for t in self.unpack(X, 4):
            t %= self.q
            if t == 0: continue
            k = 0
            while t % p == 0: t //= p; k += 1
            best = min(best, k)
        return best


# ---------------------------------------------------------------- jets
def pair_tables(R, T, fA, fB, A, rmax):
    """P[(r1,r2)][c] = d^c/dz^c [th0^(r1)(fA z) th0^(r2)(fB z)] at 0, c <= A, r1 + r2 <= rmax. Packed ring elements."""
    q = R.q
    pa = [R.pack((1, 0, 0, 0))]; pb = [R.pack((1, 0, 0, 0))]
    for _ in range(A):
        pa.append(R.mul(pa[-1], R.pack(fA))); pb.append(R.mul(pb[-1], R.pack(fB)))
    # CR[c][b] = C(c,b) fA^b fB^{c-b}
    CR = []
    for c in range(A + 1):
        CR.append([R.reduce4((comb(c, b) % q) * R.reduce7(pa[b] * pb[c - b])) for b in range(c + 1)])
    Tm = [t % q for t in T]
    P = {}
    for r1 in range(rmax + 1):
        for r2 in range(rmax + 1 - r1):
            tab = []
            for c in range(A + 1):
                row = CR[c]
                acc = 0
                for b in range(c + 1):
                    acc += (Tm[b + r1] * Tm[c - b + r2] % q) * row[b]
                tab.append(R.reduce4(acc))
            P[(r1, r2)] = tab
    return P


def down_closure(ns):
    out = set()
    for n in ns:
        for m in itertools.product(*[range(x + 1) for x in n]): out.add(m)
    return sorted(out)


def multi_indices(nmax_tuple):
    return list(itertools.product(*[range(n + 1) for n in nmax_tuple]))


def pair_jets(R, P, mA, mB, A, nlist):
    """Q[n][c] = d_{z0}^c d_{z1}^{n1} d_{z2}^{n2} d_{z3}^{n3} [th0(uA) th0(uB)] at 0 for n in nlist.
    mA, mB: coefficient rows (m_{k,0..3}) as Z[eta] tuples."""
    q = R.q
    # powers of low coefficients
    def pows(f, n):
        out = [R.pack((1, 0, 0, 0))]
        for _ in range(n): out.append(R.mul(out[-1], R.pack(f)))
        return out
    nm = [max(n[i] for n in nlist) for i in range(3)]
    PA = [pows(mA[s + 1], nm[s]) for s in range(3)]
    PB = [pows(mB[s + 1], nm[s]) for s in range(3)]
    Q = {}
    for n in nlist:
        tab = [0] * (A + 1)
        for nA in itertools.product(*[range(x + 1) for x in n]):
            nB = tuple(x - y for x, y in zip(n, nA))
            cf = 1
            for x, y in zip(n, nA): cf *= comb(x, y)
            w = R.pack((cf % q, 0, 0, 0))
            for s in range(3):
                w = R.mul(w, R.mul(PA[s][nA[s]], PB[s][nB[s]]))
            src = P[(sum(nA), sum(nB))]
            for c in range(A + 1):
                tab[c] += w * src[c]       # unreduced 7-slot product, accumulate
        Q[n] = [R.reduce7(x) for x in tab]
    return Q


def final_jet(R, Q12, Q34, a, n):
    """J(a; n) = sum_b sum_{n'} C(a,b) C(n,n') Q12[n'][b] Q34[n-n'][a-b]."""
    q = R.q
    acc = 0
    for n1 in itertools.product(*[range(x + 1) for x in n]):
        n2 = tuple(x - y for x, y in zip(n, n1))
        cf = 1
        for x, y in zip(n, n1): cf *= comb(x, y)
        A1, A2 = Q12[n1], Q34[n2]
        sub = 0
        for b in range(a + 1):
            sub += (comb(a, b) % q) * (A1[b] * A2[a - b])     # unreduced 7-slot accumulation
        acc += (cf % q) * R.reduce7(sub)
    return R.reduce4(acc)


# ---------------------------------------------------------------- predictions
def vp_fact(n, p):
    s, t = 0, p
    while t <= n:
        s += n // t; t *= p
    return s


def gam(p): return p / (p * p - 1)


def lean4(a, n, p, nprime=4):
    """Lean capped gain, one top at position 0 with weight a, low weights n = (n1,n2,n3) at positions 1,2,3:
    sum over odd e of (a/p^e - cap(t+e))_+, cap = weight at position e mod n'."""
    s, e = 0.0, 1
    w = {1: n[0], 2: n[1], 3: n[2], 0: 0}
    while p ** e <= a:
        s += max(0.0, a / p ** e - w[e % nprime]); e += 2
    return s


def lean4_loss(a, n, p, nprime=4):
    """the Lean's charged loss sum_{e odd} min(a/p^e, cap(t+e))."""
    s, e = 0.0, 1
    w = {1: n[0], 2: n[1], 3: n[2], 0: 0}
    while p ** e <= a:
        s += min(a / p ** e, w[e % nprime]); e += 2
    return s
