"""E1 + controls: the heavy (top-row) line through m composed jet steps, square tower.
Chain: level 0 = 1x1 (VV one-dimensional, vector 1) --K_1 (1->2, nu=(A), det^A)--> Sym^A(C^2)
       --K_2..K_m (2->2, nu=(A,0), lastEntry 0: BlockBound applies with a=b)--> Sym^A(C^2).
Each K_j has its own fresh matrix variable and its own product theta kernel (fresh lattice sum).
Reported (natural logs, squared norms, normalised Fock norms, Omega = 1):
  B_m   = sum_j log tmax_j                         (the Lean's per-step bounds, PWN:32-34)
  T_m   = log ||K_m...K_1 1||^2                    (true composite on the proof's vector)
  D_m   = B_m - T_m                                (total defect)
  H_m   = sum_j log||K_j||_op^2 - T_m              (Hadamard part: product of true op norms vs composite)
  X_m   = log |<ext, K_m...K_1 1>|^2               (functional reading only the heavy coefficient y0^A)
Controls: (a) start the square chain from the middle-weight unit vector y0^{A/2}y1^{A/2} instead of
the true heavy output; (a') insert a fixed generic unitary rotation of C^2 between steps;
(b) wrong coordinate constant cD = 2^{1/2} with the bound still evaluated at Omega = 1.
Usage: python3 -I composite6_square.py [Amax]
"""
import sys, os, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import composite6_lib as L

Amax = int(sys.argv[1]) if len(sys.argv) > 1 else 768
MMAX = 8
KERNELS = [('Zi', 0.0), ('Zi', 0.5), ('Zw', 0.0), ('O7', 0.0), ('O7', 0.5)]
AS = [A for A in (48, 96, 192, 384, 768, 1536) if A <= Amax]

t0 = time.time()
mom = {}
S1 = {}
for (nm, sh) in KERNELS:
    mom[(nm, sh)] = L.moments(nm, Amax + 2, sh)
    S1[(nm, sh)] = L.sup_growth(nm, sh)
print(f"moments done ({time.time()-t0:.0f}s); S1 = " + ", ".join(f"{k[0]}/{k[1]}:{v:.4f}" for k, v in S1.items()))


def rot_matrix(A, U):
    """Sym^A(U) in orthonormal coords (same convolution formula with moments replaced by U entries)."""
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


def chain(dt1, dts, A, logS1s, v_start=None, between=None):
    """dt1: moments for K_1; dts: list of moments for K_2..K_m. Returns per-m rows."""
    rows = []
    v = L.step_1to2(dt1, A)
    lf = L.lfact(A)
    T = lf + L.lnorm2(v)
    B = L.log_tmax(1, 2, [A], logS1s[0])
    opsum = T                      # K_1 has a one-dimensional source: ||K_1||_op = ||K_1 1||
    if v_start is not None:        # control (a): replace the heavy vector by a given unit vector
        v = v_start / math.sqrt(np.vdot(v_start, v_start).real)
        T = 0.0; B = 0.0; opsum = 0.0
    v = v / math.sqrt(np.vdot(v, v).real)
    X = T + 2 * math.log(abs(v[A])) if abs(v[A]) > 0 else -math.inf
    rows.append((1, B, T, B - T, opsum - T, X, None, None))
    for j, dt in enumerate(dts, start=2):
        K = L.step_square2(dt, A)
        sv = np.linalg.svd(K, compute_uv=False)
        lop = lf + 2 * math.log(sv[0])
        if between is not None:
            v = between @ v
        vn = K @ v
        gain = lf + L.lnorm2(vn) - L.lnorm2(v)
        v = vn / math.sqrt(np.vdot(vn, vn).real)
        T += gain
        B += L.log_tmax(2, 2, [A, 0], logS1s[j - 1])
        opsum += lop
        Xv = abs(v[A])
        X = (T + 2 * math.log(Xv)) if Xv > 0 else -math.inf
        rows.append((j, B, T, B - T, opsum - T, X, lop, gain))
    return rows


print("\n=== E1: square tower, same kernel at every step ===")
print("kernel | A | m | B_m | T_m | D_m | D_m/m | H_m | B_m-X_m | log||K||op^2 (step) | realised gain (step) | step slack log tmax-log||K||op^2")
summary = {}
for (nm, sh) in KERNELS:
    dt = mom[(nm, sh)]
    lS = math.log(S1[(nm, sh)])
    for A in AS:
        if np.all(dt[A - np.arange(A + 1)] * dt[np.arange(A + 1)] == 0):
            continue
        rows = chain(dt, [dt] * (MMAX - 1), A, [lS] * MMAX)
        for (m, B, T, D, H, X, lop, gain) in rows:
            if m in (1, 2, 3, 4, 8):
                slack = (L.log_tmax(2, 2, [A, 0], lS) - lop) if lop is not None else float('nan')
                print(f"{nm}/{sh} | {A} | {m} | {B:.2f} | {T:.2f} | {D:.2f} | {D/m:.2f} | {H:.2f} | {B-X:.2f} | "
                      f"{(lop if lop is not None else float('nan')):.2f} | {(gain if gain is not None else float('nan')):.2f} | {slack:.2f}")
        summary[(nm, sh, A)] = rows
    sys.stdout.flush()

print("\n--- per-step increments of D and H (m -> m+1), averaged over m = 2..8, vs A ---")
print("kernel | A | mean dD per step | mean dH per step | max |dH - mean| | dD/log A | dD/A")
for (nm, sh) in KERNELS:
    for A in AS:
        if (nm, sh, A) not in summary:
            continue
        rows = summary[(nm, sh, A)]
        dD = [rows[i][3] - rows[i - 1][3] for i in range(1, len(rows))]
        dH = [rows[i][4] - rows[i - 1][4] for i in range(1, len(rows))]
        mD = sum(dD) / len(dD); mH = sum(dH) / len(dH)
        print(f"{nm}/{sh} | {A} | {mD:.3f} | {mH:.3f} | {max(abs(x - mH) for x in dH):.3f} | {mD/math.log(A):.3f} | {mD/A:.5f}")

print("\n=== E1b: different kernels at successive steps (Zi/0, Zi/0.5, Zw/0, O7/0, O7/0.5, ...) ===")
print("A | m | D_m | D_m/m | H_m")
for A in AS:
    if A % 12:
        continue
    seq = [KERNELS[i % len(KERNELS)] for i in range(MMAX)]
    rows = chain(mom[seq[0]], [mom[k] for k in seq[1:]], A, [math.log(S1[k]) for k in seq])
    for (m, B, T, D, H, X, lop, gain) in rows:
        if m in (2, 4, 8):
            print(f"{A} | {m} | {D:.2f} | {D/m:.2f} | {H:.2f}")

print("\n=== Control (a): non-extremal start vector y0^{A/2} y1^{A/2} (unit), then 7 square steps; Zi/0 ===")
print("A | per-step realised gain (heavy chain) | per-step realised gain (middle start) | difference per step | difference/A")
for A in AS:
    dt = mom[('Zi', 0.0)]; lS = math.log(S1[('Zi', 0.0)])
    heavy = chain(dt, [dt] * (MMAX - 1), A, [lS] * MMAX)
    vs = np.zeros(A + 1, dtype=complex); vs[A // 2] = 1.0
    mid = chain(dt, [dt] * (MMAX - 1), A, [lS] * MMAX, v_start=vs)
    gh = sum(r[7] for r in heavy[1:]) / (MMAX - 1)
    gm = sum(r[7] for r in mid[1:]) / (MMAX - 1)
    print(f"{A} | {gh:.2f} | {gm:.2f} | {gh-gm:.2f} | {(gh-gm)/A:.4f}")

print("\n=== Control (a'): generic unitary rotation of C^2 inserted between steps (Zi/0) ===")
th, ph_ = 0.7231, 1.913
U = np.array([[math.cos(th), -math.sin(th) * np.exp(-1j * ph_)], [math.sin(th) * np.exp(1j * ph_), math.cos(th)]])
print("A | D_8 aligned | D_8 rotated | extra per step | extra per step / A")
for A in AS:
    dt = mom[('Zi', 0.0)]; lS = math.log(S1[('Zi', 0.0)])
    R = rot_matrix(A, U)
    al = chain(dt, [dt] * (MMAX - 1), A, [lS] * MMAX)
    ro = chain(dt, [dt] * (MMAX - 1), A, [lS] * MMAX, between=R)
    ex = (ro[-1][3] - al[-1][3]) / (MMAX - 1)
    print(f"{A} | {al[-1][3]:.2f} | {ro[-1][3]:.2f} | {ex:.2f} | {ex/A:.4f}")

print("\n=== Control (b): coordinate constant cD = sqrt(2) (jets scaled by 2^{p/2}), bound kept at Omega = 1 ===")
print("A | D_m (m=1..4) correct | D_m wrong | shift per step | shift/(A log 2)")
for A in [x for x in AS if x <= 384]:
    dt = mom[('Zi', 0.0)]; lS = math.log(S1[('Zi', 0.0)])
    dtw = dt * np.array([2.0 ** (p / 2) for p in range(len(dt))])   # cD^p with cD = sqrt(2)
    # each entry of a degree-A monomial picks cD^{exponent}: total cD^{A} per step for K_1 (two entries share A)
    good = chain(dt, [dt] * 3, A, [lS] * 4)
    bad = chain(dtw, [dtw] * 3, A, [lS] * 4)
    sh = [(good[i][3] - bad[i][3]) for i in range(4)]
    per = (sh[-1] - sh[0]) / 3
    print(f"{A} | " + " ".join(f"{r[3]:.1f}" for r in good) + " | " + " ".join(f"{r[3]:.1f}" for r in bad)
          + f" | {per:.2f} | {per/(A*math.log(2)):.4f}")
print(f"\n(total time {time.time()-t0:.0f}s)")
