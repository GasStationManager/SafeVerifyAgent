"""E3: heavy line plus one persistent w-row: weight nu = (A+w, w) on 2x2 at every level.
Chain: v_0 = extremal vector (y0^A (x) det^w), then m square steps
   det(X)^w P(X) |-> det(Y)^w E[det(xi_j)^w P(xi_j^T y0)]     (fresh xi_j, product theta kernel).
Step bound used: log tmax(2, 2, (A+w, w)) (the BlockBound formula; see NODE-NUMTEST6 s.2 for why this
square-with-det case is a surrogate for the rank-growing step).
Also the one-step calibration against the DIV bookkeeping at a top (NODE-STEPE s.2.3):
   T_1 - logHook(a+ = (w)) - ph(A)   vs   w log A.
Usage: python3 -I composite6_wrows.py [Amax]
"""
import sys, os, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import composite6_lib as L

Amax = int(sys.argv[1]) if len(sys.argv) > 1 else 768
MM = 6
t0 = time.time()
KERNELS = [('Zi', 0.0), ('O7', 0.0), ('Zi', 0.5)]
WS = [0, 1, 2, 4, 8, 16, 32]
AS = [A for A in (48, 96, 192, 384, 768) if A <= Amax]
mom = {k: L.moments(k[0], Amax + 2 * max(WS) + 4, k[1]) for k in KERNELS}
S1 = {k: L.sup_growth(k[0], k[1]) for k in KERNELS}

print("kernel | A | w | T_1 | log tmax | step slack (tmax - op) | T_1 - logHook(w) - ph(A) | w log A | "
      "D_m (m=1..6) | mean dD/step | H_6 | ext coeff share at m=6")
res = {}
for k in KERNELS:
    dt = mom[k]; lS = math.log(S1[k])
    for A in AS:
        for w in WS:
            if w > 0 and A > 384 and w > 16:
                continue
            K = L.step_square2_detw(dt, A, w)
            ref = L.lfact(A + w) + L.lfact(w)
            sv = np.linalg.svd(K, compute_uv=False)
            lop = ref + 2 * math.log(sv[0]) if sv[0] > 0 else -math.inf
            lt = L.log_tmax(2, 2, [A + w, w], lS)
            v = np.zeros(A + 1, dtype=complex); v[A] = 1.0
            T = 0.0; Ds = []; ops = 0.0
            for m in range(1, MM + 1):
                vn = K @ v
                n2 = np.vdot(vn, vn).real
                if n2 <= 0:
                    T = -math.inf; break
                T += ref + math.log(n2)
                v = vn / math.sqrt(n2)
                ops += lop
                Ds.append(m * lt - T)
                if m == 1:
                    T1 = T
            if T == -math.inf:
                print(f"{k[0]}/{k[1]} | {A} | {w} | (zero: weight forbidden by the unit group)")
                continue
            H = ops - T
            share = abs(v[A]) ** 2
            cal = T1 - L.log_hook([w]) - L.ph(A)
            dD = (Ds[-1] - Ds[0]) / (MM - 1)
            res[(k, A, w)] = (T1, lt, Ds, dD, H)
            print(f"{k[0]}/{k[1]} | {A} | {w} | {T1:.2f} | {lt:.2f} | {lt - lop:.2f} | {cal:.2f} | {w*math.log(A):.2f} | "
                  + " ".join(f"{x:.1f}" for x in Ds) + f" | {dD:.2f} | {H:.2f} | {share:.3f}")
            sys.stdout.flush()

print("\n--- dependence of the per-step defect on w (difference to w = 0), and on A ---")
print("kernel | A | w | dD(w) - dD(0) | (dD(w)-dD(0))/(w log A) | H_6(w)")
for k in KERNELS:
    for A in AS:
        if (k, A, 0) not in res:
            continue
        for w in WS[1:]:
            if (k, A, w) not in res:
                continue
            x = res[(k, A, w)][3] - res[(k, A, 0)][3]
            print(f"{k[0]}/{k[1]} | {A} | {w} | {x:.2f} | {x/(w*math.log(A)):.3f} | {res[(k, A, w)][4]:.2f}")
print(f"(time {time.time()-t0:.0f}s)")
