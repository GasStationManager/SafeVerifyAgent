"""NODE-INTINERT rank-2 check (auditor's own computation).

Curve y^2 = x^3 - x (CM by Z[i], s2 = 0), Weierstrass parameter T = -x/y, z = log_W(T).
psi(u) = ph as a function of z, u = z^2:  ph(T) = -log(sigma*(z)/T).
For a 2x2 matrix A, w = A z, test integrality in (T1, T2) of
    E_A = exp( ph(T1) + ph(T2) - ph(T(w1)) - ph(T(w2)) ),
which (since T(w_i) = [a]T1 +_F [b]T2 is integral) is equivalent to the IntInert claim
    sigma*(w1) sigma*(w2) T1 T2 / (sigma*(z1) sigma*(z2))  integral,
for the product theta in the orthonormal frame A.
Usage: python3 -I rot_check.py D
"""
import sys, time
from fractions import Fraction as Fr
sys.setrecursionlimit(10000)

D = int(sys.argv[1]) if len(sys.argv) > 1 else 20


class QF:
    __slots__ = ("a", "b")
    d = 1

    def __init__(s, a, b=0):
        s.a = a if isinstance(a, Fr) else Fr(a)
        s.b = b if isinstance(b, Fr) else Fr(b)

    def __add__(s, o):
        if not isinstance(o, QF): o = QF(o)
        return QF(s.a + o.a, s.b + o.b)
    __radd__ = __add__

    def __sub__(s, o):
        if not isinstance(o, QF): o = QF(o)
        return QF(s.a - o.a, s.b - o.b)

    def __neg__(s):
        return QF(-s.a, -s.b)

    def __mul__(s, o):
        if not isinstance(o, QF):
            o = Fr(o)
            return QF(s.a * o, s.b * o)
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


# ---------- univariate (lists) ----------
def smul(A, B, n):
    C = [QF(0) for _ in range(n + 1)]
    for i, ai in enumerate(A[:n + 1]):
        if ai.iszero(): continue
        for j in range(0, n + 1 - i):
            if not B[j].iszero():
                C[i + j] = C[i + j] + ai * B[j]
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


def slog1(A, n):
    """log(A), A[0] = 1:  L' = A'/A."""
    dA = [A[k + 1] * (k + 1) for k in range(n)] + [QF(0)]
    q = smul(dA, sinv(A, n), n)
    return [QF(0)] + [q[k - 1] / k for k in range(1, n + 1)]


def compose(A, U, n):
    R = [QF(0) for _ in range(n + 1)]
    R[0] = A[n]
    for k in range(n - 1, -1, -1):
        R = smul(R, U, n)
        R[0] = R[0] + A[k]
    return R


def curve(a4, a6, s2, n):
    g2 = -4 * Fr(a4); g3 = -4 * Fr(a6)
    c = {2: g2 / 20, 3: g3 / 28}
    for k in range(4, n + 2):
        c[k] = Fr(3, (2 * k + 1) * (k - 3)) * sum(c[m] * c[k - m] for m in range(2, k - 1))
    P = [QF(0) for _ in range(n + 1)]; P[0] = QF(1)
    Q = [QF(0) for _ in range(n + 1)]; Q[0] = QF(-2)
    Ls = [QF(0) for _ in range(n + 1)]
    for k in range(2, n + 1):
        P[k] = QF(c[k]); Q[k] = QF((2 * k - 2) * c[k])
        Ls[k] = QF(-c[k] / ((2 * k - 1) * (2 * k)))
    Ls[1] = Ls[1] - QF(s2) * Fr(1, 2)
    tau = [x * (-2) for x in smul(P, sinv(Q, n), n)]   # T/z in u = z^2
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
    om = smul(dV, sinv(V, n), n)
    om = [QF(1)] + om[:n]
    lam = [om[k] / (2 * k + 1) for k in range(n + 1)]   # z = T lam(T^2)
    return Ls, tau, lam


# ---------- bivariate dicts truncated at total degree D ----------
def bmul(A, B):
    C = {}
    for (i, j), x in A.items():
        for (k, l), y in B.items():
            if i + j + k + l <= D:
                key = (i + k, j + l)
                C[key] = C.get(key, QF(0)) + x * y
    return {k: v for k, v in C.items() if not v.iszero()}


def badd(A, B, s=1):
    C = dict(A)
    for k, v in B.items():
        C[k] = C.get(k, QF(0)) + (v if s == 1 else -v)
    return {k: v for k, v in C.items() if not v.iszero()}


def bscal(A, c):
    return {k: v * c for k, v in A.items()}


def bexp(A):
    E = {(0, 0): QF(1)}
    term = {(0, 0): QF(1)}
    for k in range(1, D + 1):
        term = bscal(bmul(term, A), Fr(1, k))
        if not term: break
        E = badd(E, term)
    return E


def run(p_list, mats, a4=Fr(-1), a6=Fr(0)):
    n = D // 2 + 1
    Ls, tau, lam = curve(a4, a6, 0, n)
    psi = [QF(0) - Ls[k] for k in range(n + 1)]
    lt = slog1(tau, n)
    psi = [psi[k] + lt[k] for k in range(n + 1)]       # ph as series in u = z^2
    # z(T) univariate in T (degree D)
    zT = [QF(0) for _ in range(D + 1)]
    for k in range(n + 1):
        if 2 * k + 1 <= D: zT[2 * k + 1] = lam[k]
    zpow = [[QF(1)] + [QF(0)] * D]
    for i in range(1, D + 1):
        zpow.append(smul(zpow[-1], zT, D))
    for name, (a, b, c, d) in mats:
        t0 = time.time()
        z1 = {(1, 0): QF(1)}; z2 = {(0, 1): QF(1)}
        w1 = badd(bscal(z1, a), bscal(z2, b)); w2 = badd(bscal(z1, c), bscal(z2, d))

        def psi_of(w):
            u = bmul(w, w)
            R = {}
            for k in range(n, -1, -1):
                R = bmul(R, u) if R else {}
                if not psi[k].iszero():
                    R = badd(R, {(0, 0): psi[k]})
            return R
        X = badd(badd(psi_of(z1), psi_of(z2)), badd(psi_of(w1), psi_of(w2)), -1)
        X.pop((0, 0), None)
        G = bexp(X)   # in z-variables
        # substitute z_k = log_W(T_k)
        H = {}
        for (i, j), g in G.items():
            for m in range(i, D + 1):
                cm = zpow[i][m]
                if cm.iszero(): continue
                for l in range(j, D + 1 - m):
                    cl = zpow[j][l]
                    if cl.iszero(): continue
                    H[(m, l)] = H.get((m, l), QF(0)) + g * cm * cl
        for p in p_list:
            bad = [(m + l, (m, l), vqf(x, p)) for (m, l), x in H.items() if not x.iszero() and vqf(x, p) < 0]
            if bad:
                first = min(bad)
                worst = min(b[2] for b in bad)
                print(f"  {name:28s} p={p:2d}: NOT integral; first negative at total degree {first[0]} "
                      f"T1^{first[1][0]}T2^{first[1][1]} (v={first[2]}); worst v={worst}; #neg={len(bad)}")
            else:
                print(f"  {name:28s} p={p:2d}: integral up to total degree {D}")
        print(f"     [{time.time() - t0:.1f}s]")


if __name__ == "__main__" and len(sys.argv) > 2 and sys.argv[2] == "w":
    QF.d = 3
    w = QF(Fr(-1, 2), Fr(1, 2)); wb = QF(Fr(-1, 2), Fr(-1, 2))
    mats = [
        ("unitary 5/13,12w/13", (QF(Fr(5, 13)), w * Fr(12, 13), wb * Fr(-12, 13), QF(Fr(5, 13)))),
        ("cols norm1, not orthog", (QF(Fr(5, 13)), w * Fr(12, 13), QF(Fr(12, 13)), w * Fr(5, 13))),
        ("Kronecker exp(-be(x,y))", (QF(1), QF(1), QF(0), QF(0))),
    ]
    print(f"y^2 = x^3 + 1 (Z[w]), D = {D}")
    run([5, 11, 7, 13], mats, Fr(0), Fr(1))
    sys.exit(0)

if __name__ == "__main__":
    i = QF(0, 1)
    mats = [
        ("unitary 3/5,4i/5", (QF(Fr(3, 5)), i * Fr(4, 5), i * Fr(4, 5), QF(Fr(3, 5)))),
        ("unitary real 3/5,4/5", (QF(Fr(3, 5)), QF(Fr(4, 5)), QF(Fr(-4, 5)), QF(Fr(3, 5)))),
        ("C-orthogonal 5/4,3i/4", (QF(Fr(5, 4)), i * Fr(3, 4), i * Fr(-3, 4), QF(Fr(5, 4)))),
        ("cols norm1, not orthog", (QF(Fr(3, 5)), i * Fr(4, 5), QF(Fr(4, 5)), i * Fr(3, 5))),
        ("shear [[1,1],[0,1]]", (QF(1), QF(1), QF(0), QF(1))),
        ("Kronecker exp(-be(x,y))", (QF(1), QF(1), QF(0), QF(0))),
        ("identity", (QF(1), QF(0), QF(0), QF(1))),
    ]
    print(f"y^2 = x^3 - x, D = {D}")
    run([3, 7, 11, 19, 23, 13, 17], mats)
