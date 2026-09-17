# Worker _sub-read-struct-8 -- structural files (READ-ONLY, NSE @ f9e8bc5)

Scope: Euler/CylinderDirichletData.lean, Euler/CylinderCompactTranslation.lean,
NavierStokes/ValidDyadicBandCover.lean, NavierStokes/MixedDiagonalSchedule.lean.
No build attempted (no .olean, pinned toolchain). All claims file:line from source + grep.

## 1. Euler/CylinderDirichletData.lean (195 lines, 24 decls, 11 theorems) -- CLEAN, positive control

Contents: `structure Coefficients` (:30-51), 4 lift defs `frame/frameDerivative/frameSecond/hessian`
(:57-60), 5 transfer theorems (:63-90), 8 solver defs (:94-140), 6 theorems (:142-192).

SUPPLY (shape 1) -- **SUPPLIED, with chain**. `Coefficients` is not hypothesis-only:
* constructed at Euler/TransversePacketHistoryData.lean:68 `def coefficients : EulerCylinderDirichlet.Coefficients D.T U Space where` -- every field discharged from `Data U` + `HistoryData D` (:69-83), i.e. a real `where`-construction, not a `P.foo`-from-`P` restatement.
* its input `HistoryData` is itself constructed: Euler/ParentStageDirection.lean:84 `def activationHistory (H : LowBounds A) : HistoryData ((P.activationData hτ hτT).initial τ hτ hτT.le) := A.historyOn H ...`, consumed at Euler/PacketStageGeometry.lean:115-117 `def joinedHistory ... := P.restrictedFrame.activationHistory ...`.
  So the chain is Stage/ParentFrame -> HistoryData -> Coefficients. Terminus (`A.historyOn`, `LowBounds A`) is outside my files; not re-verified here.
* Namespace is heavily reused (`namespace EulerCylinderDirichlet.Coefficients` in >20 other files), so the structure is load-bearing, not orphaned.

JUNK VALUES (shape 4) -- **none**. Grep of the file shows only numeral divisions: `T^2/2` and `1/2` in `small` (:51). No field or theorem inverts a variable. All non-degeneracy guards are IN-SIGNATURE inside the structure that every theorem takes: `time_pos : 0 < T` (:33), `lower_pos : 0 < lower` (:39), `potential_nonneg` (:49). This file is a useful POSITIVE CONTROL for the junk-value sweep.

NON-DEGENERACY (shape 3) -- certified by the type. `lower_pos` + `lower_bound : ∀ t x v, lower*‖v‖^2 ≤ ‖Q t x v‖^2` (:39-40) forces the frame injective with a uniform constant; the strictness is really consumed (`coordinateSolver` :96-97 passes `D.lower_pos` strict into `fixedFrameSolver`, which needs it at Euler/TransverseFixedSpaceInverse.lean:97 `fixedCoercivity_pos`). The weaker `.le` form is used only where a weaker fact suffices (:66), so this is NOT a shape-6 stronger/weaker twin: both forms of the same field are used.

VACUITY (shape 2) -- statements are content-bearing. `potential = 0` IS admitted (only `0 ≤ potential`, :49) and then `small` (:51) is trivial; but `potential=0` does not collapse the conclusions: it only weakens `hessian_upper` (:87) to `⟪Hu,u⟫ ≤ 0`, while `frame_equation` (:81) and `projected_equation` (:185) remain exact non-trivial identities in `frame`, `frameDerivative`, `accelerationPath`. Witness for joint satisfiability: `U=E`, `Q ≡ id`, `Q₁=Q₂=0`, `H=0`, `lower=1`, `potential=0`, any `T>0` -- `lower_bound` holds with equality, both `HasDerivWithinAt` fields hold for constant paths, `jacobi` reads `0 = -(0)`, `small` reads `0 ≤ 1/2`. So the hypothesis set is jointly satisfiable and not empty.

KERNEL RISK (shape 5) -- none. No `inductive`, no `.rec`, no `termination_by`, no `deriving`, no `decide`, no metaprogramming. Largest numeral in the file: `2` (`(2 : ℝ) •`, :187).

VERDICT: 24 decls -- OK 24 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

