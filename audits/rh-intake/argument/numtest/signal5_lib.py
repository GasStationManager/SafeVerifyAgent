"""NODE-NUMTEST5 engine: the capped signal-place law in the regime cap ~ a/p (see NODE-NUMTEST5.md).

Kernels (all exact; jets are finite Leibniz sums of the exact integer jets T_n = th0^(n)(0) of kernel3_lib, so there is
no series truncation anywhere; the only approximation is reduction mod p^K, and every jet with v >= K is flagged):

 (I)  n' = 2 signal place (h = 0; NUMTEST3 / NODE-SIGNAL Sec. 5):  Theta(z0, z1) = th0(z0 + z1) th0(c (z0 - z1)),
      c in Z_{p^2} with c c^sigma = -1.  z0 = position 0 (top, at w), z1 = position 1 (the partner at w-bar).
      Every odd e lands on position 1, so the cap is the same nu at e = 1, 3, 5, ...
      J2(a, nu) = d_{z0}^a d_{z1}^nu Theta(0)       (kernel3_lib.jets_grid, T reduced mod p^K first).
 (II) n' = 4 orbit (kernel4_lib instance, Z[w], p = 5):  Theta = prod_k th0(sum_s sigma^s(f_k) z_s).
      e = 1 -> position 1, e = 3 -> position 3, e = 5 -> position 1 again.
      J4(a, n1, n3) = d_{z0}^a d_{z1}^{n1} d_{z3}^{n3} Theta(0)  (new pair engine below; cross-checked against
      kernel4_lib.final_jet, an independent algorithm, in signal5_validate.py).
 (III) 2x2 block at the n' = 2 place (Lean kernel = product over matrix entries, LateralTheory.lean:34,157):
      operator (xi1 X11 + xi2 X21)^a * det(Y)^nu,  X = position-0 block, Y = position-1 block: nu minors at the partner.
"""
import os, sys
from math import comb, log
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kernel3_lib import th0_jets, Zp2, vp_fact, gam
from kernel4_lib import Ring, coeffs

CURVES = {'Zw': (0, 4, 1), 'Zi': (4, 0, 1)}


# ------------------------------------------------------------------ (I) n' = 2, all (a, nu) on a grid
def grid2(Tq, R, c, amax, numax):
    """dict (a, nu) -> Zp2 element, for a <= amax, nu <= numax, a + nu even (odd total order vanishes: th0 even).
    Same algorithm as kernel3_lib.jets_grid, with T reduced mod q."""
    q = R.q
    N = amax + numax + 1
    cp = [(1, 0)]
    for _ in range(N): cp.append(R.mul(cp[-1], c))
    g = [((Tq[k] * cp[k][0]) % q, (Tq[k] * cp[k][1]) % q) for k in range(N)]
    out = {}
    for w in range(numax + 1):
        S = [comb(w, k) * (-1) ** (w - k) % q for k in range(w + 1)]   # [x^k y^{w-k}] (x - y)^w
        for a in range(amax + 1):
            n = a + w
            if n % 2 == 0:
                acc0 = acc1 = 0
                for k in range(0, n + 1, 2):
                    s = S[k]
                    if s == 0: continue
                    f = Tq[k] * s
                    gg = g[n - k]
                    acc0 += f * gg[0]; acc1 += f * gg[1]
                out[(a, w)] = (acc0 % q, acc1 % q)
            S = [((S[k] if k < len(S) else 0) + (S[k - 1] if k >= 1 else 0)) % q for k in range(len(S) + 1)]
    return out


def j2_double_sum(Tq, R, c, a, w):
    """independent formula: d^a_{z0} d^w_{z1} [f(z0+z1) g(z0-z1)] = sum_{i,j} C(a,i) C(w,j) (-1)^{w-j}
       f^{(i+j)} g^{(a-i+w-j)},  f = th0, g(u) = th0(c u)."""
    q = R.q
    acc = (0, 0)
    cpow = {}
    for i in range(a + 1):
        for j in range(w + 1):
            k = i + j; l = a - i + w - j
            if k % 2 or l % 2: continue
            if l not in cpow:
                x = (1, 0)
                for _ in range(l): x = R.mul(x, c)
                cpow[l] = x
            s = comb(a, i) * comb(w, j) * (-1) ** (w - j) * Tq[k] * Tq[l]
            acc = R.add(acc, R.smul(s % q, cpow[l]))
    return acc


# ------------------------------------------------------------------ (II) n' = 4 pair engine
def pair_D(R, Tq, rA, rB, amax, jlist, lmax):
    """D[(j, l)][i] = d_{z0}^i d_{z1}^j d_{z3}^l [th0(LA) th0(LB)] at 0, LA = sum_s rA[s] z_s (rB likewise), packed.
    Uses d_{z_s} = rA[s] d_u + rB[s] d_v:  D = sum_k [x^k y^{n-k}] prod_s (rA[s] x + rB[s] y)^{order_s} T_k T_{n-k}."""
    q = R.q
    A0, B0 = R.pack(rA[0]), R.pack(rB[0])
    A1, B1 = R.pack(rA[1]), R.pack(rB[1])
    A3, B3 = R.pack(rA[3]), R.pack(rB[3])
    ONE = R.pack((1, 0, 0, 0))

    def mul_lin(S, A, B):
        n = len(S)
        out = [0] * (n + 1)
        for k in range(n + 1):
            t = 0
            if k < n: t += B * S[k]
            if k >= 1: t += A * S[k - 1]
            out[k] = R.reduce7(t)
        return out

    TT = {}
    def tt(k, n):
        key = (k, n)
        if key not in TT: TT[key] = Tq[k] * Tq[n - k] % q
        return TT[key]

    D = {}
    for l in range(lmax + 1):
        base_l = [ONE]
        for _ in range(l): base_l = mul_lin(base_l, A3, B3)
        jmax = max(jlist)
        S = base_l
        for j in range(jmax + 1):
            if j in jlist:
                Si = S
                tab = [0] * (amax + 1)
                for i in range(amax + 1):
                    n = i + j + l
                    if n % 2 == 0:
                        acc = 0
                        for k in range(0, n + 1, 2):
                            acc += tt(k, n) * Si[k]
                        tab[i] = R.reduce4(acc)
                    if i < amax: Si = mul_lin(Si, A0, B0)
                D[(j, l)] = tab
            S = mul_lin(S, A1, B1)
    return D


def _pair_worker(args):
    p, K, Tq, rA, rB, amax, jlist, lmax = args
    R = Ring(p, K)
    return pair_D(R, Tq, rA, rB, amax, set(jlist), lmax)


def pair_D_parallel(p, K, Tq, rA, rB, amax, jmax, lmax, nproc=4):
    """split j over processes (each recomputes its base power, O(j^2), negligible)."""
    import multiprocessing as mp
    chunks = [[j for j in range(jmax + 1) if j % nproc == r] for r in range(nproc)]
    with mp.get_context('fork').Pool(nproc) as pool:
        parts = pool.map(_pair_worker, [(p, K, Tq, rA, rB, amax, ch, lmax) for ch in chunks if ch])
    D = {}
    for d in parts: D.update(d)
    return D


def final4(R, D12, D34, a, n1, n3, combrow):
    q = R.q
    acc = 0
    for j in range(n1 + 1):
        for l in range(n3 + 1):
            A1, A2 = D12.get((j, l)), D34.get((n1 - j, n3 - l))
            sub = 0
            for b in range(a + 1):
                x, y = A1[b], A2[a - b]
                if x == 0 or y == 0: continue
                sub += combrow[b] * (x * y)
            acc += (comb(n1, j) * comb(n3, l) % q) * R.reduce7(sub)
    return R.reduce4(acc)


# ------------------------------------------------------------------ (III) 2x2 block at the n' = 2 place
def block_jet(R, G, a, nu, xi):
    """(xi1 X11 + xi2 X21)^a det(Y)^nu applied to prod_{ij} Theta(X_ij, Y_ij); G = grid2 table (one-entry jets).
    det^nu = sum_k C(nu,k)(-1)^{nu-k} (Y11 Y22)^k (Y12 Y21)^{nu-k};  entries: 11:(r,k) 21:(a-r,nu-k) 12:(0,nu-k) 22:(0,k)."""
    q = R.q
    xi1, xi2 = xi
    p1 = [(1, 0)]; p2 = [(1, 0)]
    for _ in range(a): p1.append(R.mul(p1[-1], xi1)); p2.append(R.mul(p2[-1], xi2))
    tot = (0, 0)
    for k in range(nu + 1):
        if (nu - k) % 2 or k % 2: continue          # J(0, odd) = 0
        rest = R.mul(G[(0, nu - k)], G[(0, k)])
        if rest == (0, 0): continue
        sub = (0, 0)
        for r in range(a + 1):
            if (r + k) % 2: continue
            j1, j2 = G[(r, k)], G[(a - r, nu - k)]
            w = R.mul(R.mul(p1[r], p2[a - r]), R.mul(j1, j2))
            sub = R.add(sub, R.smul(comb(a, r) % q, w))
        c = comb(nu, k) * (-1) ** (nu - k) % q
        tot = R.add(tot, R.smul(c, R.mul(sub, rest)))
    return tot


# ------------------------------------------------------------------ predictions
def P1(a, caps, p):
    """ENGINE2 / ledger law = the Lean's baseTerm/topTerm with dTop = infinity (PZF:166-178): the tsum over ALL odd e of
    (a/p^e - cap_e)_+ ; caps: function e -> cap at the partner reached after e.  (Terms with p^e > a contribute a/p^e
    when that cap is 0; the sum is cut at e = 61, where the remainder is < 1e-40.)"""
    s = 0.0
    for e in range(1, 62, 2):
        s += max(0.0, a / p ** e - caps(e))
    return s


def lean_charge(a, caps, p):
    """the Lean's forward charge sum_{e odd} min(cap_e, a/p^e)  (gamma*a - charge = P1 + sum_{p^e > a} a/p^e)."""
    s = 0.0
    for e in range(1, 62, 2):
        s += min(a / p ** e, caps(e))
    return s


def lp_opt(a, partners, p, nprime):
    """best dual-radius bound of Lemma RA without the Lean's row-radius simplifications (and without its digit-sum
    loss), one top z0 of degree a and partners [(n, d)] (degree n at odd forward distance d) on an orbit of length
    nprime:   max_{eps, r_i >= 0}  gamma (a + sum n) - a eps - sum n_i r_i
    s.t. p^alpha eps + p^beta r_i >= 1 for every bad bipower alpha - beta = d_i (mod nprime), alpha, beta >= 0.
    Binding: (alpha, beta) = (d, 0) [forward] and (0, nprime - d) [backward]; so for fixed eps the best
    r_i = max(0, 1 - p^d eps, (1 - eps) / p^(nprime - d)).  Piecewise linear in eps: evaluate at all breakpoints."""
    g = gam(p)
    cands = {0.0, 1.0}
    for (n, d) in partners:
        m = nprime - d
        cands.add(p ** -d)
        cands.add((p ** m - 1) / (p ** (m + d) - 1))      # 1 - p^d eps = (1 - eps)/p^m
    best = -1e18
    for eps in cands:
        tot = g * (a + sum(n for n, _ in partners)) - a * eps
        for (n, d) in partners:
            m = nprime - d
            r = max(0.0, 1 - p ** d * eps, (1 - eps) / p ** m)
            tot -= n * r
        best = max(best, tot)
    return best


def sigma_floor(a, n, p): return (a + n) / (p * p - 1)


def logloss(a, ncoords, p):
    """Lemma RA's digit-sum loss |coords| (log_p a + 1)."""
    return ncoords * (log(max(a, 1)) / log(p) + 1)
