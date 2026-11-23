"""E2: the heavy line through the rank-growing tower 1 -> 2 -> 3 (-> 4), t = 0 (rank +1 per step),
weight (A, 0, ..., 0) at every level (the top weight persists; new rows have length 0 = det power n_j).
Each step: fresh matrix variable xi_j in M_{N_j x N_{j-1}}, product theta kernel, Fock norms
normalised by the extremal vector.  Same quantities as composite6_square.py.
Usage: python3 -I composite6_growing.py
"""
import sys, os, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import composite6_lib as L

t0 = time.time()
KERNELS = [('Zi', 0.0), ('Zi', 0.5), ('O7', 0.0)]
mom = {k: L.moments(k[0], 260, k[1]) for k in KERNELS}
S1 = {k: L.sup_growth(k[0], k[1]) for k in KERNELS}

print("kernel | A | levels | B_m | T_m | D_m | H_m | per-step: log||K_j||op^2 - lfact(A) | per-step slack log tmax_j - log||K_j||op^2 | realised gain_j - lfact(A)")
for k in KERNELS:
    dt = mom[k]; lS = math.log(S1[k])
    for (A, top) in [(12, 4), (24, 4), (36, 4), (48, 3), (96, 3), (144, 3), (240, 3)]:
        lf = L.lfact(A)
        v1 = L.step_1to2(dt, A)                      # index s = exponent of y0
        T = lf + L.lnorm2(v1)
        B = L.log_tmax(1, 2, [A], lS)
        ops = [T]; slacks = [B - T]; gains = [T - lf]
        K23, ins2, outs3 = L.step_general(dt, A, 2, 3)
        v = np.array([v1[r[0]] for r in ins2])       # reorder to multi-index order (r0, r1)
        v = v / math.sqrt(np.vdot(v, v).real)
        lop = lf + L.lopnorm2(K23)
        vn = K23 @ v
        g = lf + L.lnorm2(vn)
        T += g; B += L.log_tmax(2, 3, [A, 0], lS)
        ops.append(lop); slacks.append(L.log_tmax(2, 3, [A, 0], lS) - lop); gains.append(g - lf)
        rowsout = [(2, B, T, sum(ops) - T)]
        if top == 4:
            v = vn / math.sqrt(np.vdot(vn, vn).real)
            K34, ins3, outs4 = L.step_general(dt, A, 3, 4)
            assert ins3 == outs3
            lop = lf + L.lopnorm2(K34)
            vn = K34 @ v
            g = lf + L.lnorm2(vn)
            T += g; B += L.log_tmax(3, 4, [A, 0, 0], lS)
            ops.append(lop); slacks.append(L.log_tmax(3, 4, [A, 0, 0], lS) - lop); gains.append(g - lf)
            rowsout.append((3, B, T, sum(ops) - T))
        for (m, Bm, Tm, Hm) in rowsout:
            print(f"{k[0]}/{k[1]} | {A} | 1..{m+1} | {Bm:.2f} | {Tm:.2f} | {Bm-Tm:.2f} | {Hm:.2f} | "
                  + " ".join(f"{x - lf:.2f}" for x in ops[:m]) + " | "
                  + " ".join(f"{x:.2f}" for x in slacks[:m]) + " | "
                  + " ".join(f"{x:.2f}" for x in gains[:m]))
        sys.stdout.flush()
print(f"(time {time.time()-t0:.0f}s)")
