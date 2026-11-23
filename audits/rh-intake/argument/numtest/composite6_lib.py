"""composite6_lib: smallest faithful archimedean model of the composed jet maps K_m o ... o K_1.

Auditors' own code (numpy + standard library).  Nothing from the Lean tree is executed.

Model (identifications with the Lean are listed in NODE-NUMTEST6.md, section 2):
  * one CM embedding tau, Gaussian growth exp(|z|^2/2) (r = 1), cD = 1, hence Omega = 1;
  * the theta kernel of step j on M_{b x a}(C) is the product over matrix entries of a
    one-variable principal theta function of a CM lattice L of area pi,
        theta(z) = sum_{l in L} alpha(l) exp(z*conj(l) - |l|^2/2)        (alpha a semi-character),
    optionally Heisenberg-translated by a half period (the Lean's vacuum th0 is a translate);
  * jet of G at 0: J(m) = prod_entries d_{m_entry},  d_p = theta^{(p)}(0);
  * the step map (ThDistC.jetMap):  P  |->  [ (P * det^n)(Z^T Y)  paired with J ],
    i.e. P(Y) |-> E[(P det^n)(xi^T Y)] where E is the 'moment functional' E[xi^p] = d_p,
    entries of xi independent (product kernel);
  * norms: Fischer form <z^m,z^m> = m!, divided by the Fischer norm of the extremal vector
    (CoefMod.pairK with G = 1; NormFockLSqLe:71-77).
For weight (A,0,...,0) the space VV is Sym^A of the first column, and we work in scaled
orthonormal coordinates  c~_s = (coefficient of y^s/sqrt(s!)) / sqrt(A!)  so that the normalised
norm is sum |c~_s|^2.  A step K then satisfies  K = sqrt(A!) * K~  with entries of K~ bounded by
sums of |prod d~|, d~_p = d_p/sqrt(p!).
"""
import math, cmath
import numpy as np

LOG2PI = math.log(2 * math.pi)


def ph(y):
    y = float(y)
    return 0.0 if y <= 0 else y * math.log(y) - y


def lfact(n):
    return math.lgamma(n + 1)


# ---------------------------------------------------------------- lattices and moments
def lattice(name):
    """Return (w1, w2) with area |Im(w1 conj w2)| = pi (principal polarisation for H = z conj(w)/pi)."""
    if name == 'Zi':
        c = math.sqrt(math.pi)
        return complex(c, 0), complex(0, c)
    if name == 'Zw':          # Z[omega], area sqrt(3)/2 per unit
        c = math.sqrt(math.pi / (math.sqrt(3) / 2))
        return complex(c, 0), c * complex(0.5, math.sqrt(3) / 2)
    if name == 'O7':          # Z[(1+sqrt(-7))/2], area sqrt(7)/2
        c = math.sqrt(math.pi / (math.sqrt(7) / 2))
        return complex(c, 0), c * complex(0.5, math.sqrt(7) / 2)
    if name == 'O23':         # Z[(1+sqrt(-23))/2]
        c = math.sqrt(math.pi / (math.sqrt(23) / 2))
        return complex(c, 0), c * complex(0.5, math.sqrt(23) / 2)
    raise ValueError(name)


def lattice_points(name, R2, scale=1.0):
    w1, w2 = lattice(name)
    w1 *= scale; w2 *= scale
    # bound on coefficients
    area = abs((w1.conjugate() * w2).imag)
    M = int(math.sqrt(R2) * max(abs(w1), abs(w2)) / area * 2) + 3
    pts = []
    for x in range(-M, M + 1):
        for y in range(-M, M + 1):
            l = x * w1 + y * w2
            if abs(l) ** 2 <= R2:
                pts.append((x, y, l))
    return pts


def moments(name, Pmax, shift=0.0, scale=1.0, semichar=True):
    """d~_p = d_p / sqrt(p!) for p = 0..Pmax, where
       d_p = sum_l alpha(l) e^{i Im(t conj l)} e^{-|l - t|^2/2} conj(l - t)^p
    (Heisenberg translate by t = shift*w1 of the principal theta; shift=0: zero characteristic).
    scale != 1 gives a lattice of area pi*scale^2 (wrong-normalisation control)."""
    w1, w2 = lattice(name)
    t = shift * w1 * scale
    R2 = Pmax + 14 * math.sqrt(Pmax + 1) + 80
    pts = lattice_points(name, R2 + 4 * abs(t) * math.sqrt(R2) + abs(t) ** 2 + 10, scale)
    xs = np.array([p[0] for p in pts]); ys = np.array([p[1] for p in pts])
    ls = np.array([p[2] for p in pts])
    alpha = np.where(((xs * ys) % 2 == 0) | (not semichar), 1.0, -1.0)
    phase = np.exp(1j * np.imag(t * np.conj(ls)))
    u = np.conj(ls - t)
    r2 = np.abs(ls - t) ** 2
    pref = alpha * phase
    out = np.zeros(Pmax + 1, dtype=complex)
    logabs = np.log(np.maximum(np.abs(u), 1e-300))
    ang = np.angle(u)
    zero = np.abs(u) < 1e-12
    for p in range(Pmax + 1):
        lg = p * logabs - r2 / 2 - 0.5 * lfact(p)
        if p > 0:
            lg = np.where(zero, -np.inf, lg)
        else:
            lg = -r2 / 2
        out[p] = np.sum(pref * np.exp(lg + 1j * p * ang))
    out[np.abs(out) < 1e-10] = 0.0    # exact zeros forced by the unit group, up to rounding
    return out


def sup_growth(name, shift=0.0, scale=1.0, grid=120, semichar=True):
    """S_1 = sup_z |theta(z)| exp(-|z|^2/2); the function is L-periodic in z."""
    w1, w2 = lattice(name)
    w1 *= scale; w2 *= scale
    pts = lattice_points(name, 200.0, scale)
    xs = np.array([p[0] for p in pts]); ys = np.array([p[1] for p in pts])
    ls = np.array([p[2] for p in pts])
    alpha = np.where(((xs * ys) % 2 == 0) | (not semichar), 1.0, -1.0)
    best = 0.0
    for i in range(grid):
        s = (i + 0.5) / grid
        zs = s * w1 + (np.arange(grid) + 0.5)[:, None] / grid * w2   # (grid,1)
        # |theta(z)| e^{-|z|^2/2} = |sum alpha e^{-|z-l|^2/2 + i Im(z conj l)}|
        e = -np.abs(zs - ls[None, :]) ** 2 / 2 + 1j * np.imag(zs * np.conj(ls[None, :]))
        val = np.abs(np.sum(alpha[None, :] * np.exp(e), axis=1))
        best = max(best, float(val.max()))
    return best


# ---------------------------------------------------------------- the Lean's step bound
def log_tmax(a, b, nu, logS1, logOm=0.0):
    """log of tmax (PaddedWittNormSquare:32-34) for one tau: G on M_{b x a}, S = S_1^{ab}."""
    nn = sum(nu)
    return (2 * a * b * logS1 + 1.0 + 2 * a * b * math.log(2 * nn + 2)
            + sum(ph(x) for x in nu) - nn * logOm)


# ---------------------------------------------------------------- Sym^A steps (weight (A,0,..))
def step_1to2(dt, A):
    """K_1 applied to the unique (extremal) level-0 vector 1 (1x1, det^A = x^A), into Sym^A(C^2).
    Scaled orthonormal coordinates c~_s, s = exponent of y0.  log||K_1 1||^2 = lfact(A) + log||v||^2."""
    return np.array([dt[s] * dt[A - s] for s in range(A + 1)], dtype=complex)


def lbinom(n, k):
    return lfact(n) - lfact(k) - lfact(n - k)


def _normvec(logs, vals):
    m = float(np.max(logs))
    return np.exp(logs - m) * vals, m


def step_square2(dt, A):
    """K~ for the square step 2 -> 2 on Sym^A(C^2) (weight (A,0), lastEntry 0, so no det factor).
    K~[S, r] = sum_{i+l=S} sqrt(C(r0,i)C(r1,l)/C(A,S)) d~_i d~_{r0-i} d~_l d~_{r1-l}."""
    K = np.zeros((A + 1, A + 1), dtype=complex)
    lbA = np.array([lbinom(A, S) for S in range(A + 1)])
    for r0 in range(A + 1):
        r1 = A - r0
        i = np.arange(r0 + 1)
        a, ca = _normvec(0.5 * np.array([lbinom(r0, x) for x in i]), dt[i] * dt[r0 - i])
        l = np.arange(r1 + 1)
        b, cb = _normvec(0.5 * np.array([lbinom(r1, x) for x in l]), dt[l] * dt[r1 - l])
        K[:, r0] = np.convolve(a, b) * np.exp(ca + cb - 0.5 * lbA)
    return K


_LF = np.array([math.lgamma(n + 1) for n in range(6000)])


def step_square2_detw(dt, A, w):
    """Square step with weight nu = (A+w, w) on 2x2 (persistent w-row = det^w factor):
    det(X)^w P(X), X = xi^T Y  ->  det(Y)^w * E[det(xi)^w P(xi^T y0)];  the output det(Y)^w Q(Y) has the
    normalised norm of Q, so the operator acts on Sym^A(C^2) (scaled orthonormal coordinates).
    Returns K~ = K / sqrt((A+w)! w!)  (log||K||^2 = lfact(A+w)+lfact(w)+log||K~||^2).
    det(xi)^w = sum_q C(w,q)(-1)^q (xi00 xi11)^{w-q} (xi01 xi10)^q;
    column 0 of xi carries x0 = xi00 y0 + xi10 y1, column 1 carries x1 = xi01 y0 + xi11 y1."""
    LF = _LF
    K = np.zeros((A + 1, A + 1), dtype=complex)
    ref = 0.5 * (LF[A + w] + LF[w])
    sS = np.arange(A + 1)
    lS = 0.5 * (LF[sS] + LF[A - sS])
    for r0 in range(A + 1):
        r1 = A - r0
        col = np.zeros(A + 1, dtype=complex)
        i = np.arange(r0 + 1); l = np.arange(r1 + 1)
        lbi = LF[r0] - LF[i] - LF[r0 - i]
        lbl = LF[r1] - LF[l] - LF[r1 - l]
        for q in range(w + 1):
            la = lbi + 0.5 * (LF[w - q + i] + LF[q + r0 - i])
            a, ca = _normvec(la, dt[w - q + i] * dt[q + r0 - i])
            lb = lbl + 0.5 * (LF[q + l] + LF[w - q + r1 - l])
            b, cb = _normvec(lb, dt[q + l] * dt[w - q + r1 - l])
            c = np.convolve(a, b)
            sgn = -1.0 if q % 2 else 1.0
            E = ca + cb + (LF[w] - LF[q] - LF[w - q]) + lS - 0.5 * (LF[r0] + LF[r1]) - ref
            col += sgn * c * np.exp(E)
        K[:, r0] = col
    return K


# ------------- general Sym^A step N_in -> N_out (homogeneous polys stored densely over the
# ------------- first N_out-1 exponents; last exponent implied)
def multi_indices(N, A):
    if N == 1:
        return [(A,)]
    out = []
    for s0 in range(A, -1, -1):
        for rest in multi_indices(N - 1, A - s0):
            out.append((s0,) + rest)
    return out


def lmultinom(r, s):
    return lfact(r) - sum(lfact(x) for x in s)


def g_poly(dt, r, Nout, A):
    """g_r(y) = sum_{|s|=r} sqrt(multinom(r;s)) prod_b d~_{s_b} y^s, dense over first Nout-1 exps
    (array shape (A+1,)*(Nout-1))."""
    G = np.zeros((A + 1,) * (Nout - 1), dtype=complex)
    for s in multi_indices(Nout, r):
        v = 1.0 + 0j
        for x in s:
            v *= dt[x]
            if v == 0:
                break
        if v == 0:
            continue
        G[s[:-1]] = v * math.exp(0.5 * lmultinom(r, s))
    return G


def poly_mul(P, Q, A):
    """Product of two dense homogeneous polys (arrays over first exps), truncated to size A+1."""
    out = np.zeros_like(P)
    nz = np.argwhere(P != 0)
    dims = P.ndim
    for idx in nz:
        sl_out = tuple(slice(int(i), A + 1) for i in idx)
        sl_q = tuple(slice(0, A + 1 - int(i)) for i in idx)
        out[sl_out] += P[tuple(idx)] * Q[sl_q]
    return out


def step_general(dt, A, Nin, Nout, cols=None):
    """K~ for Sym^A(C^Nin) -> Sym^A(C^Nout), as a dense matrix over multi_indices (columns = inputs).
    K~[S, r] = (prod_alpha g_{r_alpha})[S] / sqrt(multinom(A;S))."""
    ins = multi_indices(Nin, A)
    outs = multi_indices(Nout, A)
    oidx = {s: i for i, s in enumerate(outs)}
    lmS = np.array([lmultinom(A, s) for s in outs])
    gs = {r: g_poly(dt, r, Nout, A) for r in range(A + 1)}
    K = np.zeros((len(outs), len(ins)), dtype=complex)
    sel = range(len(ins)) if cols is None else cols
    for c in sel:
        r = ins[c]
        P = None
        for ra in r:
            P = gs[ra].copy() if P is None else poly_mul(P, gs[ra], A)
        vec = np.array([P[s[:-1]] for s in outs])
        K[:, c] = vec * np.exp(-0.5 * lmS)
    return K, ins, outs


def apply_general(dt, A, Nin, Nout, v, ins=None):
    """K~ v without forming the matrix (v over multi_indices(Nin, A))."""
    ins = multi_indices(Nin, A) if ins is None else ins
    outs = multi_indices(Nout, A)
    gs = {r: g_poly(dt, r, Nout, A) for r in range(A + 1)}
    acc = np.zeros((A + 1,) * (Nout - 1), dtype=complex)
    for c, r in enumerate(ins):
        if abs(v[c]) < 1e-300:
            continue
        P = None
        for ra in r:
            P = gs[ra].copy() if P is None else poly_mul(P, gs[ra], A)
        acc += v[c] * P
    lmS = np.array([lmultinom(A, s) for s in outs])
    return np.array([acc[s[:-1]] for s in outs]) * np.exp(-0.5 * lmS), outs


def lnorm2(v):
    n = float(np.vdot(v, v).real)
    return math.log(n) if n > 0 else -math.inf


def lopnorm2(K):
    s = np.linalg.svd(K, compute_uv=False)
    return 2 * math.log(s[0]) if s[0] > 0 else -math.inf


# ---------------------------------------------------------------- hook / Young diagrams
def log_hook(rows):
    """log of the product of hook lengths of the Young diagram with given row lengths."""
    rows = sorted([int(r) for r in rows if r > 0], reverse=True)
    if not rows:
        return 0.0
    cols = [sum(1 for r in rows if r > c) for c in range(rows[0])]
    tot = 0.0
    for i, r in enumerate(rows):
        for c in range(r):
            tot += math.log(r - c + cols[c] - i - 1)
    return tot


def log_hook_frob(rows):
    """Frobenius form: H = prod l_i! / prod_{i<j}(l_i - l_j), l_i = rows_i + p - 1 - i."""
    rows = sorted([int(r) for r in rows], reverse=True)
    p = len(rows)
    l = [rows[i] + p - 1 - i for i in range(p)]
    s = sum(lfact(x) for x in l)
    for i in range(p):
        for j in range(i + 1, p):
            s -= math.log(l[i] - l[j])
    return s
