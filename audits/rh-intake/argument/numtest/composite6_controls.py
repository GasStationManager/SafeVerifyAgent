"""Controls with power for the composition defect, and the isotropy of the true step operator.
(1) Singular-value spread of the true square step K~ (Zi/0, O7/0): log(s_max^2/s_min^2) and the
    spread over the extremal and the middle monomial -- explains why a non-extremal start loses little.
(2) Anisotropic kernel (theta only in entry (0,0), constant 1 in the other entries: d_p = delta_{p0}):
    the step is rank one, and a fixed rotation between steps must cost A*log(1/|u00|^2) per step.
    The engine measures H_m for this chain: it must show the a-proportional loss.
(3) Same rotation with the true (isotropic) kernel, for comparison.
Usage: python3 -I composite6_controls.py
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import composite6_lib as L


def rot_matrix(A, U):
    """Sym^A(U) in scaled orthonormal coordinates (same as composite6_square.rot_matrix)."""
    K = np.zeros((A + 1, A + 1), dtype=complex)
    lbA = np.array([L.lbinom(A, S) for S in range(A + 1)])
    for r0 in range(A + 1):
        r1 = A - r0
        i = np.arange(r0 + 1); l = np.arange(r1 + 1)
        la = 0.5 * np.array([L.lbinom(r0, x) for x in i])
        a = np.exp(la - la.max()) * U[0, 0] ** i * U[1, 0] ** (r0 - i)
        lb = 0.5 * np.array([L.lbinom(r1, x) for x in l])
        b = np.exp(lb - lb.max()) * U[0, 1] ** l * U[1, 1] ** (r1 - l)
        K[:, r0] = np.convolve(a, b) * np.exp(la.max() + lb.max() - 0.5 * lbA)
    return K


print("(1) spread of the singular values of the true 2->2 step K~ (normalised: log s_i^2 - log s_max^2)")
print("kernel | A | min | median | #within 3 of top | ext vector ||K e_ext||^2/s_max^2 (log) | middle vector (log)")
for nm, sh in [('Zi', 0.0), ('O7', 0.0)]:
    dt = L.moments(nm, 800, sh)
    for A in (48, 192, 768):
        K = L.step_square2(dt, A)
        s = np.linalg.svd(K, compute_uv=False)
        ls = 2 * np.log(s[s > 0]) - 2 * math.log(s[0])
        e = np.zeros(A + 1); e[A] = 1
        mvec = np.zeros(A + 1); mvec[A // 2] = 1
        le = L.lnorm2(K @ e) - 2 * math.log(s[0]); lm = L.lnorm2(K @ mvec) - 2 * math.log(s[0])
        nzero = int(np.sum(s <= 1e-12 * s[0]))
        print(f"{nm}/{sh} | {A} | {ls.min():.2f} | {np.median(ls):.2f} | {int(np.sum(ls > -3))} | {le:.3f} | {lm:.3f} | (exact zeros: {nzero})")

th, ph_ = 0.7231, 1.913
U = np.array([[math.cos(th), -math.sin(th) * np.exp(-1j * ph_)], [math.sin(th) * np.exp(1j * ph_), math.cos(th)]])
pred = -math.log(abs(U[0, 0]) ** 2)
print(f"\n(2) rank-one kernel + rotation |u00|^2 = {abs(U[0,0])**2:.4f}: predicted loss per step = A * {pred:.4f}")
print("A | H_8 measured | (m-1)*A*log(1/|u00|^2) | ratio")
dt = L.moments('Zi', 800, 0.0)
for A in (48, 192, 768):
    # rank-one step: x0^A -> d_A y0^A only (entries other than (0,0) carry d_p = delta_{p0})
    K1 = np.zeros((A + 1, A + 1), dtype=complex); K1[A, A] = dt[A]   # scaled coords: d~_A
    R = rot_matrix(A, U)
    v = np.zeros(A + 1, dtype=complex); v[A] = 1.0
    T = 0.0; ops = 0.0
    lop = 2 * math.log(abs(dt[A]))
    for j in range(2, 9):
        vn = K1 @ (R @ v)
        n2 = np.vdot(vn, vn).real
        T += math.log(n2) - L.lnorm2(v)
        v = vn / math.sqrt(n2)
        ops += lop
    H = ops - T
    print(f"{A} | {H:.2f} | {7*A*pred:.2f} | {H/(7*A*pred):.4f}")
print("\n(3) the true kernel with the same rotation: see Control (a') in out_composite6_square.txt (extra <= 3.2 per step)")

print("\n(4) the functional that reads only the extremal coefficient (y0^A (x) det^w): log share |c_ext|^2/||v||^2 after each step")
print("kernel | A | w | log share after steps 1..8 | mean per step (2..8)")
for nm in ('Zi', 'O7'):
    dt = L.moments(nm, 900, 0.0)
    for (A, w) in [(48, 0), (384, 0), (768, 0), (48, 32), (384, 32), (768, 16)]:
        K = L.step_square2_detw(dt, A, w) if w > 0 else L.step_square2(dt, A)
        v = np.zeros(A + 1, dtype=complex); v[A] = 1.0
        sh = []
        for j in range(8):
            v = K @ v; v = v / math.sqrt(np.vdot(v, v).real)
            sh.append(2 * math.log(abs(v[A])) if abs(v[A]) > 0 else -math.inf)
        print(f"{nm} | {A} | {w} | " + " ".join(f"{x:.2f}" for x in sh) + f" | {(sh[-1]-sh[0])/7:.3f}")
