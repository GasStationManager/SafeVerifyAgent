"""SL2(Z) model for Theorem S (auditor's own computation).
Petersson: <P_m,P_n> ~ Delta(m,n) = d_{mn} + 2*pi*i^{-k} sum_c S(m,n;c)/c J_{k-1}(4 pi sqrt(mn)/c).
Normalised correlations r = Delta/sqrt(Delta_mm Delta_nn).
J_n(x) for integer n by the periodic trapezoid rule on (1/2pi) int cos(n t - x sin t) dt (aliasing error ~ J_{N-n}(x)).
"""
import sys, math
import numpy as np

k = int(sys.argv[1]) if len(sys.argv) > 1 else 300
M = int(sys.argv[2]) if len(sys.argv) > 2 else 150
C = int(sys.argv[3]) if len(sys.argv) > 3 else 40
nu = k - 1
D = k // 12 - (1 if k % 12 == 2 else 0)
assert k % 4 == 0

def jn(n, xs):
    xs = np.asarray(xs, float)
    N = int(n + xs.max() + 400)
    t = 2 * np.pi * np.arange(N) / N
    out = np.empty_like(xs)
    for i0 in range(0, len(xs), 2000):
        xx = xs[i0:i0 + 2000]
        out[i0:i0 + 2000] = np.cos(n * t[None, :] - xx[:, None] * np.sin(t)[None, :]).mean(axis=1)
    return out

# sanity: J_0(1)=0.7651976866, J_5(10)=-0.2340615282
assert abs(jn(0, [1.0])[0] - 0.7651976866) < 1e-9 and abs(jn(5, [10.0])[0] + 0.2340615282) < 1e-9

ms = np.arange(1, M + 1)
Delta = np.eye(M)
for c in range(1, C + 1):
    units = np.array([d for d in range(c) if math.gcd(d, c) == 1])
    inv = np.array([pow(int(d), -1, c) if c > 1 else 0 for d in units])
    a = np.arange(c)
    # S[a,b] = sum_d cos(2 pi (a d + b dbar)/c)   (real for level 1)
    S = np.cos(2 * np.pi * (np.outer(a, units)[:, None, :] + np.outer(a, inv)[None, :, :]) / c).sum(axis=2)
    prod = np.outer(ms, ms)
    up, invidx = np.unique(prod, return_inverse=True)
    J = jn(nu, 4 * np.pi * np.sqrt(up) / c)[invidx].reshape(M, M)
    Delta += 2 * np.pi * S[(ms % c)[:, None], (ms % c)[None, :]] / c * J
dg = np.sqrt(np.diag(Delta))
R = Delta / np.outer(dg, dg)
ev = np.sort(np.linalg.eigvalsh(R))[::-1]
print(f"k={k} D=dim S_k={D} M={M} C={C}; k/(4pi)={k/(4*np.pi):.2f}")
print("min diag Delta", Delta.diagonal().min())
print("eigenvalues 1..D+3:", np.round(ev[:D + 3], 6))
print("rank (ev > 1e-6*max):", int((ev > 1e-6 * ev[0]).sum()))
for top in [D - 2, D, D + 2]:
    B = R[:top, :top]
    off = B - np.eye(top)
    print(f"P_1..P_{top}: max|offdiag r|={np.abs(off).max():.3e}, ||G-I||_HS^2={np.sum(off**2):.3e}, min eig={np.linalg.eigvalsh(B).min():.3e}")
# where does near-orthogonality fail: first m with max_{n<m}|r(m,n)| > 1e-3
for m in range(2, M + 1):
    if np.abs(R[m - 1, :m - 1]).max() > 1e-3:
        print("first index with |r(m,n)|>1e-3 for some n<m:", m, " (4 pi m / k =", round(4 * np.pi * m / k, 3), ")")
        break
# tight-frame test for the family P_1..P_M: nonzero eigenvalues of R vs M/D
lam = ev[:D]
print("frame: tr R =", round(ev.sum(), 3), " M/D =", round(M / D, 3), " eig range", round(lam.min(), 3), round(lam.max(), 3),
      " rel HS deviation ||Q-cI||^2/(c^2 D) =", round(float(np.sum((lam - lam.mean())**2) / (lam.mean()**2 * D)), 4))
# per-pair (d=1) Theorem-S analogue in the large-index range
lo = max(2 * D, M // 2)
idx = np.arange(lo, M)
sub = R[np.ix_(idx, idx)]
pairs = sub[~np.eye(len(idx), dtype=bool)]
x = D * pairs**2
print(f"pairs m!=n in [{lo+1},{M}]: mean D|r|^2={x.mean():.3f}, median={np.median(x):.3f}, max={x.max():.2f}, share>1: {np.mean(x>1):.3f}")
# block version: consecutive blocks of size b in the large range
for b in [3, 6, 12, 24]:
    nb = len(idx) // b
    ratios, diag = [], []
    for i in range(nb):
        Ii = idx[i * b:(i + 1) * b]
        diag.append(np.sum((R[np.ix_(Ii, Ii)] - np.eye(b))**2) / b)
        for j in range(nb):
            if i != j:
                Ij = idx[j * b:(j + 1) * b]
                ratios.append(np.sum(R[np.ix_(Ii, Ij)]**2) / (b * b / D))
    ratios = np.array(ratios)
    print(f"blocks b={b}: ||K_uu'||^2/(b^2/D) mean={ratios.mean():.3f} max={ratios.max():.2f}; diag ||K_uu-1||^2/b mean={np.mean(diag):.3f}")
