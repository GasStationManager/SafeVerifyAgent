"""NODE-LEAVES, exact check of the one-letter laws in the Weierstrass formal parameter T = -x/y
(standard library only; python3 -I leaves_normrel.py [M]).

Curve y^2 = x^3 + a4 x + a6 with x = wp, y = wp'/2 (the Lean's shortW g2 g3: a4 = -g2/4, a6 = -g3/4).
z = log_W(T) is the formal logarithm (z = int omega), so T(z) = -2 wp(z)/wp'(z).
sigma* = sigma(z) exp(-s2 z^2/2).  ph(T) = -log(sigma*(z(T))/T)  (the Lean's phCurve / phO).

Tests (all coefficients exact in Q(sqrt(-d)); p inert, so v_p(a + b sqrt(-d)) = min(v_p a, v_p b)):
  NR(alpha):  exp(ph([alpha]T) - N(alpha) ph(T)) = T(alpha z) sigma*(z)^N / (T(z)^N sigma*(alpha z))
              -- the Lean's NormRel (Simeq) in the Weierstrass parameter (curveNorm, SecondLogDerivativeUnique.lean:218);
  PH:         exp(-ph) = sigma*(z(T))/T  (expected NOT integral);
  KR(e):      T * K_t(z(T)), K_t = co-sigma at the 2-torsion point with x = e; K_t^2 = wp - e was verified in
              leaves_float.py for the Lean's opU/th0 normalisation; here its p-integrality in T.
Everything is even in z / T, so series are kept in u = z^2 and S = T^2; M = number of S-coefficients (T-degree 2M).
"""
import sys, time
from fractions import Fraction as Fr

M = int(sys.argv[1]) if len(sys.argv) > 1 else 40


class QF:
    """a + b r, r^2 = -d.  Stored as Fractions."""
    __slots__ = ("a", "b")
    d = 1

    def __init__(self, a, b=0):
        self.a = a if isinstance(a, Fr) else Fr(a)
        self.b = b if isinstance(b, Fr) else Fr(b)

    def __add__(s, o):
        if not isinstance(o, QF): o = QF(o)
        return QF(s.a + o.a, s.b + o.b)
    __radd__ = __add__

    def __sub__(s, o):
        if not isinstance(o, QF): o = QF(o)
        return QF(s.a - o.a, s.b - o.b)

    def __rsub__(s, o):
        return QF(o) - s

    def __neg__(s):
        return QF(-s.a, -s.b)

    def __mul__(s, o):
        if not isinstance(o, QF):
            o = Fr(o)
            return QF(s.a * o, s.b * o)
        if s.b == 0:
            return QF(s.a * o.a, s.a * o.b)
        if o.b == 0:
            return QF(s.a * o.a, s.b * o.a)
        return QF(s.a * o.a - QF.d * s.b * o.b, s.a * o.b + s.b * o.a)
    __rmul__ = __mul__

    def inv(s):
        n = s.a * s.a + QF.d * s.b * s.b
        return QF(s.a / n, -s.b / n)

    def __truediv__(s, o):
        if not isinstance(o, QF):
            o = Fr(o)
            return QF(s.a / o, s.b / o)
        return s * o.inv()

    def iszero(s):
        return s.a == 0 and s.b == 0

    def __repr__(s):
        return f"({s.a}+{s.b}r)"


def vq(x, p):
    if x == 0: return None
    n, dd = x.numerator, x.denominator
    v = 0
    while n % p == 0: n //= p; v += 1
    while dd % p == 0: dd //= p; v -= 1
    return v


def vqf(x, p):
    vs = [v for v in (vq(x.a, p), vq(x.b, p)) if v is not None]
    return min(vs) if vs else None


# ---------------------------------------------------------------- series (lists of QF, length M+1)
def smul(A, B, n):
    C = [QF(0) for _ in range(n + 1)]
    for i, ai in enumerate(A[:n + 1]):
        if ai.iszero(): continue
        for j in range(0, n + 1 - i):
            bj = B[j]
            if bj.iszero(): continue
            C[i + j] = C[i + j] + ai * bj
    return C


def sinv(A, n):
    a0i = A[0].inv()
    B = [QF(0) for _ in range(n + 1)]
    B[0] = a0i
    for k in range(1, n + 1):
        s = QF(0)
        for j in range(1, k + 1):
            if not A[j].iszero() and not B[k - j].iszero():
                s = s + A[j] * B[k - j]
        B[k] = -(s * a0i)
    return B


def sexp(A, n):
    """exp(A), A[0] = 0.  E' = A' E."""
    assert A[0].iszero()
    E = [QF(0) for _ in range(n + 1)]
    E[0] = QF(1)
    for k in range(1, n + 1):
        s = QF(0)
        for j in range(1, k + 1):
            if not A[j].iszero():
                s = s + (j * A[j]) * E[k - j]
        E[k] = s / k
    return E


def spow_num(A, e, n):
    """A^e for A[0] = 1, e rational (binomial via log-free recursion: E' A = e A' E)."""
    assert A[0].a == 1 and A[0].b == 0
    E = [QF(0) for _ in range(n + 1)]
    E[0] = QF(1)
    for k in range(1, n + 1):
        s = QF(0)
        for j in range(1, k + 1):
            if A[j].iszero(): continue
            s = s + A[j] * E[k - j] * (e * j - (k - j))
        E[k] = s / k
    return E


def scale(A, c):
    """A(c u)."""
    out = []
    ck = QF(1)
    for a in A:
        out.append(a * ck)
        ck = ck * c
    return out


def compose(A, U, n):
    """A(U(S)), U[0] = 0."""
    R = [QF(0) for _ in range(n + 1)]
    R[0] = A[n]
    for k in range(n - 1, -1, -1):
        R = smul(R, U, n)
        R[0] = R[0] + A[k]
    return R


# ---------------------------------------------------------------- curve data
def curve_series(a4, a6, s2, n):
    g2 = -4 * Fr(a4); g3 = -4 * Fr(a6)
    # wp = z^-2 + sum_{k>=2} c_k z^{2k-2}
    c = {2: g2 / 20, 3: g3 / 28}
    for k in range(4, n + 2):
        c[k] = Fr(3, (2 * k + 1) * (k - 3)) * sum(c[m] * c[k - m] for m in range(2, k - 1))
    P = [QF(0) for _ in range(n + 1)]; P[0] = QF(1)
    Q = [QF(0) for _ in range(n + 1)]; Q[0] = QF(-2)
    Ls = [QF(0) for _ in range(n + 1)]
    for k in range(2, n + 1):
        P[k] = QF(c[k]); Q[k] = QF((2 * k - 2) * c[k])
        Ls[k] = QF(-c[k] / ((2 * k - 1) * (2 * k)))
    Ls[1] = Ls[1] - QF(s2) * Fr(1, 2) if not isinstance(s2, QF) else Ls[1] - s2 * Fr(1, 2)
    tau = [x * (-2) for x in smul(P, sinv(Q, n), n)]      # T/z as series in u = z^2
    # formal group: w = T^3 v(S), v = 1 + a4 S^2 v^2 + a6 S^3 v^3 ;  omega = 1 + S v'/v ; z = T lam(S)
    v = [Fr(0)] * (n + 1); v2 = [Fr(0)] * (n + 1); v3 = [Fr(0)] * (n + 1)
    for k in range(n + 1):
        val = Fr(1) if k == 0 else Fr(0)
        if k >= 2: val += a4 * v2[k - 2]
        if k >= 3: val += a6 * v3[k - 3]
        v[k] = val
        v2[k] = sum(v[i] * v[k - i] for i in range(k + 1))
        v3[k] = sum(v2[i] * v[k - i] for i in range(k + 1))
    V = [QF(x) for x in v]
    dV = [QF((k + 1) * v[k + 1]) for k in range(n)] + [QF(0)]
    om = smul(dV, sinv(V, n), n)          # v'/v
    om = [QF(1)] + om[:n]                 # 1 + S v'/v
    lam = [om[k] / (2 * k + 1) for k in range(n + 1)]
    U = [QF(0)] + smul(lam, lam, n)[:n]   # u = S lam^2
    # consistency: u tau(u)^2 = S
    chk = compose(smul(tau, tau, n), U, n)
    chk = smul(chk, U, n)
    assert all((chk[k] - (QF(1) if k == 1 else QF(0))).iszero() for k in range(min(n, 12) + 1)), "T/z mismatch"
    return P, Q, Ls, tau, lam, U, c


def minval(A, p, start=0):
    vals = [(vqf(x, p), k) for k, x in enumerate(A) if k >= start and not x.iszero()]
    return min(vals) if vals else (None, None)


def first_neg(A, p):
    for k, x in enumerate(A):
        if not x.iszero() and vqf(x, p) < 0:
            return k, vqf(x, p)
    return None


def run(name, d, a4, a6, s2true, primes, alphas, es, s2tests):
    QF.d = d
    print("=" * 100)
    print(f"{name}: y^2 = x^3 + ({a4})x + ({a6}),  true s2 = {s2true},  S-degree M = {M} (T-degree {2 * M})")
    for s2 in s2tests:
        t0 = time.time()
        P, Q, Ls, tau, lam, U, c = curve_series(Fr(a4), Fr(a6), s2, M)
        tag = "TRUE s2" if s2 == s2true else "wrong s2"
        print(f"  -- s2 = {s2} ({tag})")
        # PH: exp(-ph) = sigma*(z)/T = lam(S) * exp(L*(u(S)))
        if s2 == s2true:
            EL = compose(sexp(Ls, M), U, M)
            PH = smul(lam, EL, M)
            for p in primes:
                fn = first_neg(PH, p)
                mv = minval(PH, p)
                print(f"     PH  exp(-ph)=sigma*/T        p={p:2d}: min v_p = {mv[0]} (at T^{2 * mv[1]});  first negative at "
                      f"{'T^%d (v=%d)' % (2 * fn[0], fn[1]) if fn else 'none'}")
            for e, ename in es:
                # K = sqrt(P(u) - e u) / lam ... T*K(z) = (T/z) * z K = sqrt(P - e u)(u(S)) / lam(S)
                Pe = [x for x in P]; Pe[1] = Pe[1] - e
                sq = compose(spow_num(Pe, Fr(1, 2), M), U, M)
                KR = smul(sq, sinv(lam, M), M)
                for p in primes:
                    fn = first_neg(KR, p)
                    print(f"     KR  T*K_t, x(t)={ename:10s} p={p:2d}: first negative coefficient: "
                          f"{'T^%d (v=%d)' % (2 * fn[0], fn[1]) if fn else 'none (integral to T^%d)' % (2 * M)}")
        for al, Nal, aname in alphas:
            al2 = al * al
            # R(u) = tau(al^2 u) tau(u)^-N exp(N L*(u) - L*(al^2 u))
            A = smul(scale(tau, al2), spow_num(tau, -Nal, M), M)
            Lal = scale(Ls, al2)
            Ex = [Ls[k] * Nal - Lal[k] for k in range(M + 1)]
            R = smul(A, sexp(Ex, M), M)
            RS = compose(R, U, M)
            for p in primes:
                fn = first_neg(RS, p)
                print(f"     NR  alpha={aname:8s} N={Nal}   p={p:2d}: first negative coefficient: "
                      f"{'T^%d (v=%d)' % (2 * fn[0], fn[1]) if fn else 'none (integral to T^%d)' % (2 * M)}")
        print(f"     [{time.time() - t0:.1f}s]")


def main():
    which = sys.argv[2] if len(sys.argv) > 2 else "all"
    if which in ("all", "i"):
        QF.d = 1
        i = QF(0, 1)
        run("Z[i]", 1, -1, 0, 0, [7, 11], [(QF(1, 1), 2, "1+i"), (QF(2, 1), 5, "2+i"), (QF(2), 4, "2")],
            [(QF(0), "0"), (QF(1), "1")], [0, 1])
    if which in ("all", "w"):
        QF.d = 3
        w = QF(Fr(-1, 2), Fr(1, 2))
        run("Z[w]", 3, 0, 1, 0, [5, 11], [(QF(1) - w, 3, "1-w"), (QF(2) + w, 3, "2+w"), (QF(2), 4, "2")],
            [(QF(-1), "-1"), (QF(Fr(1, 2), Fr(1, 2)), "(1+r)/2")], [0, 1])
    if which in ("all", "7"):
        QF.d = 7
        w = QF(Fr(1, 2), Fr(1, 2))
        run("O_K d=7", 7, -35, -98, 1, [5, 13], [(w, 2, "w"), (QF(1) + w, 4, "1+w"), (QF(2), 4, "2")],
            [(QF(7), "7"), (QF(Fr(-7, 2), Fr(1, 2)), "(-7+r)/2")], [1, 0, 2])


if __name__ == "__main__":
    main()
