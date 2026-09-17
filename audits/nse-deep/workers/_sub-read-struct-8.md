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

## 2. Euler/CylinderCompactTranslation.lean (171 lines, 14 decls, 11 theorems) -- CLEAN

Contents: `structure CompactField` (:28-31, fields `field / compact : HasCompactSupport / smooth`),
`toLp` (:41), `derivative` (:47), and 11 theorems ending in `translation_contDiff` (:166).

SUPPLY (shape 1) + CLOSURE-WITHOUT-A-BASE-CASE check -- **BASE CASE EXISTS**, so this is NOT the
seven-predicate pattern. Inside the file the only constructor is the CLOSURE `def derivative
(A : CompactField P V) : CompactField P (LiftTangent →L[ℝ] V)` (:47-50), which builds a CompactField
only FROM one. The base case is out of file: Euler/PacketTerminalDatum.lean:81-85
`def compactField (δ) (hδ : 0 < δ) (ξ : U) : CompactField period U where field := field δ ξ; compact := field_compact δ ξ; smooth := field_smooth δ hδ ξ`, i.e. the literal datum chi1(y) f_delta(theta) xi (PacketTerminalDatum.lean:24-28), and it is immediately consumed: `terminal := (compactField δ hδ ξ).toLp` (:88) and `terminal_orbit_contDiff := (compactField δ hδ ξ).translation_contDiff` (:94-97). So `translation_contDiff` (:166) is live, not dead.

VACUITY (shape 2) -- the base witness is **not identically zero**, verified two levels down:
`innerCutoff_zero : innerCutoff 0 = 1` (Euler/EulerProof.lean:11663) and `profile_deriv_zero : deriv (profile δ) 0 = δ⁻¹` for `0 < δ` (Euler/EulerProof.lean:11818) force `scalarField δ` (PacketTerminalDatum.lean:24) to be nonzero somewhere; with `xi ≠ 0` the field is nonzero. Compact support is real, not trivial: `innerCutoff_support ⊆ ball 0 (1/2)` (EulerProof.lean:11719). So the orbit-smoothness theorems have content.

JUNK VALUES (shape 4) -- **none**: a grep for `/` and `⁻¹` over all 171 lines returns ZERO hits. Nothing in this file divides or inverts. Second positive control.

NON-DEGENERACY (shape 3) -- nothing assumed. `[Fact (0 < P)]` (:26) is the period guard and is carried in-signature; three theorems explicitly `omit [Fact (0 < P)]` (:37,:52,:62) i.e. they hold with no positivity at all, which is honest, not a hidden gap.

KERNEL RISK (shape 5) -- **low but present, 1 item**: `private theorem translation_contDiff_aux` (:149-163) is by `induction n with | zero | succ n ih` over `ℕ` (:152), so it elaborates to `Nat.rec` with a universe-polymorphic (`universe u`, :24) motive that quantifies over `V` and its instances (:150) -- the induction is over the FIELD/derivative tower, each step applying to `A.derivative` at a bigger type (:163). This is legitimate structural recursion (no `termination_by`, no `Acc.rec`, no `decide`, no `deriving`, no metaprogramming), but it is the one place in the file where the kernel does real work. Largest numeral in the file: `2` (`MemLp M 2`, :83).

NOTE (not a defect): `derivative_bound` (:53) and `increment_bound` (:82) are existential (`∃ C`, `∃ M`) and are consumed only inside this file (:86-87, :106); no downstream theorem sees the constants, so no quantitative claim is exported. Fine for its purpose (dominated differentiation).

VERDICT: 14 decls -- OK 13 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 1 (:149-163, benign `Nat.rec`).

## 3. NavierStokes/ValidDyadicBandCover.lean (182 lines, 18 decls, 10 theorems) -- 1 correction to a prior finding

Contents: `band` (:28-30), `mem_band_iff` (:32), `band_open` (:39), `exists_band` (:49), `Index`/`charts` (:59,:61), `sublevel_covered` (:63), `def Compatible` (:72-73), `def field` (:75), then 8 transfer theorems (:79-180).

### The requested verification of the prior claim -- CONFIRMED, then PARTLY REVERSED

CONFIRMED: `ValidDyadicBandCover.lean:72-73` is EXACTLY a wrapper definition and contains no proof:
```
def Compatible (h : ℝ) (N : ℕ) (f : ℕ → SpaceTime → E) : Prop :=
  ValidBandGluing.Compatible (charts h N) (fun n => f n.val)
```
It is a `def ... : Prop`, one `:=`, no tactic block. And inside this file every single theorem that uses it takes it as a HYPOTHESIS `(hf : Compatible h N f)` -- :80, :86, :93, :101, :110, :123, :137, :169. So within my four files nothing constructs it.

REVERSAL / CORRECTION to the standing verdict `ValidBandGluing.Compatible (ValidBandGluing.lean:22) UNSUPPLIED`: **it IS supplied, one module out, by a real proof.**
* the underlying predicate is only `def Compatible (U : ι → Set D) (f : ι → D → E) : Prop := ∀ i j, EqOn (f i) (f j) (U i ∩ U j)` (NavierStokes/ValidBandGluing.lean:22-23) -- a plain pairwise-agreement Prop, no structure, no fields.
* it is DISCHARGED at NavierStokes/ActualValidBandWaves.lean:260-268:
  `theorem compatible (N : ℕ) : ValidDyadicBandCover.Compatible h N (localPotential x) ∧ ValidDyadicBandCover.Compatible h N (localPressure x) := by constructor · intro n m w hw; exact (local_fields_eq H C hN hS hcore n.val m.val hw.1 hw.2).1 · ... .2`
  This is a genuine proof: it unfolds the wrapper (`intro n m w hw` = the `∀ i j, EqOn` binders) and closes each branch with the band-overlap identity `local_fields_eq` (ActualValidBandWaves.lean:241-258, itself split into the radius-positive case via `local_fields_eq_ordered` and the axis case via `current_local_axis_germs`). It does NOT assume any `Compatible`.
* the result is immediately consumed, so the transfer theorems of MY file are LIVE: `potential_germ` (:271-275) calls `ValidDyadicBandCover.field_germ ... (compatible ...).1`, `pressure_germ` (:278-282) the `.2`.
* its own premises are constructed elsewhere too: `C : ActualCycleCoherence.Coherent x` is concluded at NavierStokes/ActualCyclePreservation.lean:842 `... : ActualCycleCoherence.Coherent (state B N0 j)`. (`H : CycleAnalyticInvariant ...` not chased here.)
So: shape-1 verdict on the wrapper = SUPPLIED (indirectly, by defeq unfolding one module out). The prior "UNSUPPLIED" label should be downgraded to "constructed only for the two concrete families `localPotential`/`localPressure`". Also note a trivial witness always exists (`f n := g` constant in `n` makes `∀ i j, EqOn g g _` immediate), so the predicate is neither vacuous nor unsatisfiable.

JUNK VALUES (shape 4) -- **all guarded, third positive control**. Divisions in this file: `ChartScales.Q n / 2` (:29,:151,:156,:173 -- constant denominator), `physicalQ h w / ChartScales.Q n` (:34), and the constant `1 / 2` (:34,:39 etc.). The only variable denominator is `ChartScales.Q n`, and `ChartScales.Q_pos (n : ℕ) : 0 < Q n` (NavierStokes/ChartScales.lean:76) is UNCONDITIONAL (`Q n = 2 ^ (-n : ℝ)` by `Real.rpow_pos_of_pos`), so no hypothesis is needed and no junk value can arise; `mem_band_iff` even discharges it explicitly (`have hQ := ChartScales.Q_pos n`, :35). Scale guards `hh : 0 < h`, `hh1 : h < 1/2` are IN-SIGNATURE on every theorem that needs smoothness (:39,:49,:85,:92,:100,:109,:122,:136,:147,:168). Nothing is inverted (`⁻¹` absent).

VACUITY (shape 2) -- non-vacuous, with a witness route in the file itself: `exists_band` (:49-57) PRODUCES membership `w ∈ band h n` for any `w ∈ preterminal` with `physicalQ h w ≤ ChartScales.Q N`, using `PhysicalMeanJetBounds.exists_comparable_band` -- so the charts are nonempty whenever the sublevel set is, and `sublevel_covered` (:63-68) turns that into an actual cover of `CutStageEstimates.physicalSublevel h qbig`. The bands are open (:39) and `field` agrees with a chart on a NEIGHBORHOOD (:85-90), so `field_smooth` (:92) / `field_jet_eq` (:100) are real statements, not empty-domain artefacts.

NOTE (design, benign but worth naming) -- `ValidBandGluing.representative` uses `if h : ∃ i, x ∈ U i then f (Classical.choose h) x else 0` (ValidBandGluing.lean:26-28), i.e. a SILENT ZERO DEFAULT off the union (shape 4 in kind). It is not exploited here: every conclusion of my file is either restricted to `physicalSublevel ⊆ domain` (:96,:127) or is a germ at a point already in a band (:88,:103). The `else 0` branch even has an honest lemma `representative_zero` (ValidBandGluing.lean:33). No theorem in my file is true only by the default value.

NOTE -- `field_jet_bound` (:122-131) is *stronger* than a naive gluing bound: the docstring's claim "No chart-count factor is incurred" is justified, since the proof (:129-131) re-selects a comparable chart at each `w` via `field_jet_bound_at` instead of summing over charts. Verified by reading; no hidden `∑` over `Index N`.

KERNEL RISK (shape 5) -- none. No `inductive`, `.rec`, `termination_by`, `deriving`, `decide`, metaprogramming. Largest numeral: `2` (:30 and the index `x 2` coordinate selector, :148).

VERDICT: 18 decls -- OK 16 / NOTE 2 (:72-73 wrapper-only, and the `else 0` default it inherits) / UNCLEAR 0 / ESCALATE 1 (not a defect but a CORRECTION: `ValidBandGluing.Compatible` is NOT unsupplied -- proved at ActualValidBandWaves.lean:260-268) / KERNEL-RISK 0.

## 4. NavierStokes/MixedDiagonalSchedule.lean (344 lines, 28 decls, 10 theorems) -- 1 real NOTE worth naming

Contents: `Component = Fin 3` (:20) + 3 literals (:24-26), `ComponentSpace` (:30-31), 2 instances (:33-41), `family`/`scalarFamily` (:44,:48), `commonRawLoss`/`commonLoss` (:51,:54), 3 max-lemmas (:57-64), **2 structures** `ThreeCutBounds` (:68-72) and `ThreeSmoothSums` (:74-81), `raw_bounds_mono_loss` (:90), `cut_bounds_of_positiveStages` (:108), private `family_raw_bounds` (:121), `exists_three_component_schedule` (:140), `full_sum_eq_initial_add_positive` (:177), `physical_initial_split(_germ/_jets)` (:194,:205,:216), `exists_three_component_schedule_smooth` (:231), `full_sum_smooth_of_initial` (:264), `full_sum_zero_of_sublevel_le` (:285), `exists_three_component_local_schedule` (:302).

SUPPLY (shape 1) -- **both structures are PRODUCED here, not merely assumed.** They are Prop-classes with 3 fields each and are built by anonymous constructor at :167 (`⟨hb Component.potential, hb Component.direct, hb Component.pressure⟩`), :253-256 and :337-343, from inputs that are NOT of their own type (`RawStageBounds` + `ContDiffOn`). They are then consumed in hypothesis position downstream: MixedDiagonalResidual.lean:64,:228-230; LocalResidualFlatness.lean:33,:86,:118; MixedCandidateWitness.lean:29; MixedCandidateAssembly.lean:75; LocalPotentialRebundle.lean:79-122. The upstream input `CutStageEstimates.RawStageBounds` is also genuinely produced elsewhere (NavierStokes/PhysicalStageBounds.lean:484,:499,:513 -- header at :10 states "No `RawStageBounds` is an input"; ActualPhysicalStageBounds.lean:457-463). So nothing here is dead.

VACUITY (shape 2) -- EXHIBITED WITNESS for `exists_three_component_schedule` (:140-167), all hypotheses at once: `h := 1/4` (so `0 < h` and `h < 1/2`), `S := PhysicalWaveSum.preterminal` (so `hS` is `subset_rfl`), `A = B = P := 0`, `g j := j`, `LA = LB = LP := 0`, `CA = CB = CP := 0`, `pA = pB = pP := 0`, `lower` arbitrary. Then `hA/hB/hP` are `contDiffOn_const`; each `RawStageBounds` (def at CutStageEstimates.lean:199-203) reads `‖iteratedFDeriv ℝ m 0 x‖ ≤ 0 * (1+|log q x|)^0 * q x ^ (j - 0)`, i.e. `0 ≤ 0`, true; `hg : ∀ j, 1 ≤ j → 0 < g j` reads `0 < j` for `j ≥ 1`, true. So the hypothesis set is jointly satisfiable -- the theorem is not empty. Its non-triviality is inherited from the real producers cited above, not asserted here.

**NOTE (the one substantive finding, a HALF-OPEN INTERFACE): `ThreeCutBounds` says NOTHING about stage 0.**
`ThreeCutBounds` (:68-72) is three copies of `DiagonalJetBounds.CutStageBounds`, whose definition is
`∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ x ∈ U, ‖iteratedFDeriv ℝ m (cutStage a q A j) x‖ ≤ (1/2)^j * q x ^ (g j - L m)` (NavierStokes/DiagonalJetBounds.lean:196-200) -- the index starts at `1 ≤ j`, so `j = 0` is entirely unconstrained. The same `1 ≤ j` gate sits in `RawStageBounds` (CutStageEstimates.lean:201).
The file then contains the exact transport that CARRIES this gap forward: `cut_bounds_of_positiveStages` (:108-117) converts `CutStageBounds a q (positiveStages A) g L S` into `CutStageBounds a q A g L S`, where `positiveStages A 0 = 0` (CutStageEstimates.lean:433-437). I.e. a bound proved for the family with stage 0 DELETED is re-labelled as a bound "for A". This is sound exactly because of the `1 ≤ j` gate (proof :113-117 rewrites by `positiveStages_of_pos hj`), and it is used in the capstone at :338-340. Consequence, and this is the reportable part: **`ThreeCutBounds a h A B P ...` must not be read as a quantitative bound on the full sums or on `A 0`.** The file supplies stage-0 information only QUALITATIVELY (`full_sum_smooth_of_initial`, :264-281, smoothness; `full_sum_eq_initial_add_positive`, :177-190, exact bookkeeping identity; `full_sum_zero_of_sublevel_le`, :285-295, vanishing beyond validity) -- never a size bound. The docstrings are honest about it (:107 "Suppressing stage zero does not change any positive-stage estimate", :229-230 "The quantitative input still concerns only positive stages"). I checked the sharpest consumer, `LocalResidualFlatness.allResidualJetRates_of_cutBounds` (LocalResidualFlatness.lean:29-35): it does NOT try to derive stage-0 size from `hb`; it takes a separate `E : StageEstimates h qbig A B P` and gets the residual/stage-0 side from `E.finite_residual` / `E.gain_zero` (LocalResidualFlatness.lean:63-67). So no defect is realised at that call site. Classification: NOTE (interface hazard), not ESCALATE.

JUNK VALUES (shape 4) -- **all guards are IN-SIGNATURE. Fourth positive control.** Every division in the file: `g j / 2`, `1 / 2` (constant denominators, :140,:154,:194,:231,:245,:302,:321); `1 / (a j : ℝ)` at :265 (`hrecip : 1 / (a 0 : ℝ) < qbig`) -- accompanied in the SAME signature by `ha0 : 0 < a 0` (:265), which is what forbids the junk reading `1/0 = 0 < qbig`; and at :286 (`hrecip : ∀ j, 1 / (a j : ℝ) < qbig`) -- accompanied by `ha : ∀ j, 0 < a j` (:286). The cast is discharged explicitly (`ha0' : (0:ℝ) < a 0`, :276; `(by exact_mod_cast ha j)`, :293). Nothing is inverted with `⁻¹`. The rpow `q x ^ (g j - L m)` could degenerate at `q x = 0` (Mathlib `0 ^ y = 0` for `y ≠ 0`), but (a) positivity is in-signature where needed (`hpos : ∀ x ∈ S, 0 < q x`, :92, used at :96,:102,:104) and (b) at the physical instantiation `physicalQ_pos hh hh1` is applied on `preterminal` (:165,:203,:252,:335) -- and note the degeneration would make the RHS 0, i.e. STRENGTHEN a conclusion, never create a vacuous one. No junk-value defect.

KERNEL RISK (shape 5) -- **1 item, structural not arithmetic.** `@[reducible] noncomputable def ComponentSpace (c : Component) : Type := if c = 2 then ℝ else Space` (:30-31) is a TYPE-VALUED dependent `if`, while its two instances (:33-36, :38-41) are built by nested `Fin.cases` with motive `fun c => NormedAddCommGroup (ComponentSpace c)`. Typechecking therefore needs whnf of `Decidable (c = 2)` on `Fin 3` literals, and `fin_cases c` (:133, :157, :326) forces exactly those reductions inside proofs, where the goal's norm instance must reduce to the canonical `Space` / `ℝ` instance so that `hA/hB/hP` (stated with the canonical instances) apply. `family` (:44-46) relies on `VelocityField = SpaceTime → Space` (NavierStokes/ProblemStatement.lean:35, an `abbrev`) being defeq to `SpaceTime → ComponentSpace 0`. This is the classic silent-instance-diamond shape; nothing indicates it is wrong, but it CANNOT be re-verified here (no `.olean`, no build possible), so it stays a flagged risk rather than a cleared one. No `inductive`, no `.rec` written by hand, no `Acc.rec`, no `termination_by`, no `deriving`, no `decide`. Largest numeral in the file: `2` (the `Fin 3` literal `2` at :26/:31, `m ≤ j + 2` inherited from CutStageBounds, `2 * a j` at :152,:243,:318).

Minor: `noncomputable def potential/direct/pressure : Component := 0/1/2` (:24-26) marks `Fin 3` literals noncomputable -- cosmetic only, no effect on statements.

VERDICT: 28 decls -- OK 24 / NOTE 3 (stage-0 half-open interface :68-72 + :108-117; `ComponentSpace` if-Type + `Fin.cases` instances :30-41; cosmetic `noncomputable` literals :24-26) / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 1 (:30-41 with :133/:157/:326).

---

## Cross-file summary (this worker)

* No UNSUPPLIED structure in my four files. All three structures + the one Prop-def are either constructed by a real `where`/anonymous-constructor term (Coefficients at TransversePacketHistoryData.lean:68; ThreeCutBounds/ThreeSmoothSums at MixedDiagonalSchedule.lean:167,:253,:337) or proved by unfolding (Compatible at ActualValidBandWaves.lean:260-268).
* CLOSURE-WITHOUT-A-BASE-CASE was a live risk in exactly one place (`CompactField.derivative`, CylinderCompactTranslation.lean:47) and the base case EXISTS (PacketTerminalDatum.lean:81-85), verified nonzero via `innerCutoff_zero = 1` (EulerProof.lean:11663).
* Junk-value sweep: 4 for 4 clean. Every variable denominator in these files is guarded IN ITS OWN SIGNATURE (`ha0 : 0 < a 0` next to `1 / (a 0 : ℝ)`, MixedDiagonalSchedule.lean:265) or by an unconditional lemma (`ChartScales.Q_pos`, ChartScales.lean:76). These files are the positive control the campaign was missing.
* The single most important content finding is the stage-0 gate in `ThreeCutBounds` (MixedDiagonalSchedule.lean:68-72 via DiagonalJetBounds.lean:198), and the most important bookkeeping finding is the CORRECTION on `ValidBandGluing.Compatible`.

