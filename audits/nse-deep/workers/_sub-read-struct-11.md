# Worker _sub-read-struct-11 — structural files, NSE @ f9e8bc5 (READ-ONLY, no build)

## 1. NavierStokes/ValidBandGluing.lean (179 lines, 24 decls, 1 Prop-def) — CLEAN

Generic chart-gluing library over `{ι D E : Type*}`; nothing Navier-Stokes-specific except the last
two curl corollaries.

- Prop-def `Compatible U f := ∀ i j, EqOn (f i) (f j) (U i ∩ U j)` (ValidBandGluing.lean:22-23).
  **SUPPLIED, not orphaned.** Concluded (not assumed) by `ActualValidBandWaves.compatible`
  (NavierStokes/ActualValidBandWaves.lean:259-267), which proves it from `local_fields_eq`
  (ActualValidBandWaves.lean:238) with no `Compatible` in its own hypotheses; consumed one layer up
  as `ValidDyadicBandCover.Compatible` (NavierStokes/ValidDyadicBandCover.lean:72-73) and used at
  GluedStageEstimates.lean:562-570. Also trivially satisfiable (constant family), so no vacuity risk.
  VERDICT OK.
- Junk-value sweep: **no `/`, no `⁻¹`, no `decide`, no `inductive`, no `termination_by`, no
  `deriving`, no metaprogramming, no `.rec`** anywhere in the file. Largest numeral: `2`
  (`nhds`-free, in `𝓝` names only) / `0` for the default value — benign by inspection.
  KERNEL-RISK: none.
- Silent default (shape 4) considered and OK: `representative` returns `0` off the valid union
  (`representative` ValidBandGluing.lean:27-29). That default is not hidden — it is *stated* as the
  content of `representative_zero` (:34) and `representative_zero_germ` (:72-75) — and every transfer
  theorem (`representative_eq_of_mem` :39, `_germ` :65, `_contDiffAt` :93, `_fderiv_eq` :105,
  `_iteratedFDeriv_eq` :120, `_jet_bound` :125, `_jet_bound_on_union` :134, `_finite_jets_bound` :141,
  `_jet_apply_eq` :148, `_spatialCurl_eq` :167) carries an in-signature `hx : x ∈ U i` or
  `x ∈ domain U`. No statement is true merely by the default.
- NOTE (minor, harmless direction — a *redundant* hypothesis, shape-6-adjacent):
  `representative_unique_on_domain` (ValidBandGluing.lean:51-56) assumes BOTH `hf : Compatible U f`
  and `hg : ∀ i, EqOn g (f i) (U i)`. `hf` is derivable from `hg`: for `x ∈ U i ∩ U j`,
  `f i x = g x = f j x`. So the theorem is stated with a strictly stronger hypothesis set than needed.
  Weakening only, no soundness impact.
- `representative_jet_bound_on_union` (:134-139) doc-comment claims "no multiplicity factor" — correct,
  because `representative` picks ONE chart pointwise, not a sum; the proof is a rewrite (:139).
  Docstring matches statement.

Tally: 24 decls read — OK 23 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 2. Euler/TransversePacketForwardBudget.lean (133 lines, 14 decls, 1 structure) — OK, with 1 NOTE

Declares `structure Budget (D : Data U) (ι) [Fintype ι] (q : ℕ)`
(TransversePacketForwardBudget.lean:27-62): a 20-field source-budget record (growth profile `g`,
neighborhood, five radii/constants `Rc C₀ C₁ C Ri R`, four nonnegativity fields, two frame jet bounds,
four radius inequalities, one propagator bound).

(A) IS IT CONSTRUCTED? **YES — a genuine, non-circular construction exists.**
 - `EulerPacketSourcePropagator.shortPhysicalForwardBudget`
   (Euler/PacketShortTimePhysicalGrowth.lean:60-88) returns `Budget D (Fin 4) q`, built by
   `EulerPacketParentForwardBudget.sourceForwardBudget` from analytic hypotheses only (`hdet`, `hF`,
   `hF₁`, `hM`, `hshort`) — no `Budget` in its own hypothesis list. Not the useless `P.foo : P → P` shape.
 - It is applied to real parent data at `EulerParentPacketFrames.LabelData.forwardRaw`
   (Euler/ParentPacketForwardInput.lean:33-37), packaged into `ForwardInputs`
   (ParentPacketForwardInput.lean:18-21) at `forwardInputs` (:39-52), and the base of that chain is
   concrete: `EulerBaseDatum.initialParent` / `initialLabelData` (Euler/BaseEulerState.lean:35-39).
 - `Budget.enlargeRadius` (TransversePacketForwardBudget.lean:72-78) is only `Budget → Budget`
   (supplies nothing), and it is what `Euler/PacketForwardCanonicalRadius.lean:29-31` and
   `Euler/PacketInitializedCanonicalRadius.lean:46-47` use — so those are NOT the base construction;
   the base is `shortPhysicalForwardBudget`. Consumed as a hypothesis in ~15 files
   (e.g. PacketForwardHessianError.lean:52, PacketForwardResidualBounds.lean:18,
   PacketForwardUniformBudget.lean:24, ParentPacketForwardInput.lean:19).

(B) JUNK-VALUE SWEEP — this file is a **useful POSITIVE CONTROL: the only division is guarded
in-signature.** The single `/` is in the `propagator` field, `‖…‖ ≤ C*g t/g s`
(TransversePacketForwardBudget.lean:62). The denominator `g s` is constrained nonzero by a field of the
SAME structure: `positive : ∀ t, 0 < g t` (:29). No `⁻¹` anywhere in the file. The two costs
(`velocityCost` :68, `derivativeCost` :69, `commonCost` :70) are division-free.

(C) NON-VACUITY / SATISFIABILITY, by inspection of the R-monotonicity (shape 2): the four radius fields
are `radius_one : 1 ≤ R` (:51), `frame_radius` (:52), `forcing_radius` (:53), `forward_radius` (:54-56),
and `R` occurs in NO other field and only on the ≥-side of these four (LHS's use only
`Rc, Ri, C, C₀, C₁, T, q, ι`). Hence the field set is never self-contradictory in `R`: any candidate can
be repaired by enlarging `R`. This is exactly the closure `enlargeRadius` (:72-78) exploits — it re-proves
precisely those four fields via `.trans hR` and inherits every other field unchanged, which independently
confirms no other field mentions `R`. So `Budget` is jointly satisfiable, not a dead hypothesis.

(D) DEGENERATE-WITNESS check. The real witness's growth profile is **identically 1**:
`forwardInputs_growth : (…).linear.g = 1` BY `rfl` (Euler/ParentPacketForwardInput.lean:56-57), and
`shortPhysicalForwardBudget` passes the literal constant `(1 : C(Icc 0 D.T,ℝ))`
(PacketShortTimePhysicalGrowth.lean:81). With `g ≡ 1` the propagator field degenerates to
`‖fwd ∘ bwd‖ ≤ C` (`g t/g s = 1`). This is **declared, not hidden** — the module docstring says
"A short interval controlled by the low strain norm supplies H3 with g=1"
(PacketShortTimePhysicalGrowth.lean:3-5) — and it is a *specialization*, not a vacuity: g=1 is a
legitimate positive profile, `positive`/`initial_one` hold, and no theorem in my file needs g nonconstant.
NOTE (not ESCALATE): I found no witness with a NON-constant `g`; every construction path I could trace
(`shortPhysicalForwardBudget` → `forwardRaw` → `forwardInputs` → `enlargeRadius` chains in
PacketForwardCanonicalRadius.lean:29, PacketInitializedCanonicalRadius.lean:46) preserves `g` verbatim,
so the whole forward-packet tower is currently run at `g = 1`. Consequence to be aware of one layer up:
any downstream statement whose only content is the *ratio* `g t/g s` is `= C` on the supplied witness.
The two theorems here (`velocity_unit_bound` :110, `derivative_unit_bound` :121) do not depend on that.

(E) `C₀ = C₁ = C = Rc = 0` is admitted by the type (`*_nonneg` fields :42-45, no positivity). Direction
is SAFE: zero constants make `frame_bound`/`frameDerivative_bound`/`propagator` HARDER to satisfy and make
the two conclusions (`≤ velocityCost*majorant`, `≤ derivativeCost*majorant`) STRONGER, so this cannot
manufacture a true-but-empty theorem. No shape-3 defect.

(F) KERNEL RISK: **none.** No `inductive`, no `.rec`/`Nat.rec`/`Acc.rec`, no `termination_by`, no
`deriving`, no `decide`, no `Fin.cases`, no Type-valued `if`, no metaprogramming. Largest numeral: `18`
(in `forward_radius`, :56); others are `4, 3, 2, 6, 1/2, 1`. All benign by inspection.
The only oddity is `private local instance : NormedRing (U →L[ℝ] U) := inferInstance` (:24-25) — a
re-declaration of an already-inferable instance, `private local`, so no global instance-diamond leak.

Tally: 14 decls read — OK 13 / NOTE 1 (g ≡ 1 is the only supplied witness) / UNCLEAR 0 / ESCALATE 0 /
KERNEL-RISK 0.

## 3. Euler/ParentEulerState.lean (89 lines, 9 decls, 1 structure) — CLEAN, and it is the file that
##    CERTIFIES the Euler content of the parent tower is NOT vacuous

Declares `structure Evolution (A : Parent)` (ParentEulerState.lean:15-28): the actual Euler PDE record
carried by a particle parent — `velocity : ℝ × Space → Space`, `pressure`, `force`, plus
`velocity_match` (:21), `pressure_gradient` (:26), and the two PDE fields
`momentum_zero : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual velocity pressure (t,x) = 0` (:27) and
`divergence_zero : ∀ t ∈ Ioo 0 A.T, ∀ x, divergence (fun y => velocity (t,y)) x = 0` (:28).

(A) IS IT CONSTRUCTED? **YES, and by a genuine local-existence construction, not by a `P → P` step.**
 - `EulerStaticEuler.baseEvolution : Evolution (baseParent …)` (Euler/BaseStaticEuler.lean:119-137)
   fills every field from independently proved lemmas: `momentum_zero` from `localMomentum` (:135-136),
   `divergence_zero` from `localVelocity_divergence` (:137), `pressure_gradient` from
   `localPressure_gradient` (:134). No `Evolution` appears in its hypotheses.
 - Named instances: `EulerBaseDatum.solutionEvolution` (Euler/BaseEulerInput.lean:42-45) and
   `EulerBaseDatum.initialEvolution` (Euler/BaseEulerState.lean:44-45, via my file's `restrictTime`).
 - `Evolution.restrictTime` (ParentEulerState.lean:73-86) is the `Evolution → Evolution` step and
   supplies nothing by itself — correctly, it is NOT the only source.
 - Consumed widely as a hypothesis: PacketStageGeometry.lean:18, ParentOrdinaryEvolution.lean:16,
   ParentHomogeneousPacketLowBounds.lean:19, PacketForwardChildLowBounds.lean:41,
   PacketPressureSymmetry.lean:15, ParentEulerSobolevChild.lean:17, ParentGeometryChoiceRenewal.lean:13.
 - TWIN WARNING (checked, no confusion): there are two unrelated same-named structures,
   `EulerOrdinarySobolev.Evolution T hT` / `OrdinaryEulerDifference.Evolution T hT`
   (Euler/OrdinaryEulerDifference.lean:21) taking `(T, hT)` not `(A : Parent)`. All hits I credited above
   are `Evolution A` with `A : Parent`, i.e. THIS structure.

(B) VACUITY (shape 2) — settled with an explicit witness, not an opinion.
 1. The PDE fields are quantified over `Ioo 0 A.T`, which would be EMPTY if `A.T = 0`. It cannot be:
    `Parent` carries `T_pos : 0 < T` as a field (Euler/ParentPacketFrames.lean:24-25). So the empty-domain
    escape is closed BY THE TYPE, in `Parent` itself. Not a shape-3 defect.
 2. The witness is NOT the identically-zero flow. Trace it to literals:
    `solutionEvolution β hβ ell hell hell1` (BaseEulerInput.lean:42) has
    `velocity` matching `u.field = field (linear β)` at time 0, and
    `solution_initial_velocity` (BaseEulerInput.lean:58-63) plus
    `solution_initial_gradient : fderiv ℝ (velocity.field 0) 0 = linear β`
    (BaseEulerInput.lean:65-72) pin the initial gradient to
    `linear β = (EuclideanSpace.proj 1).smulRight (single 0 1 + β • single 2 1)`
    (Euler/BaseEulerDatum.lean:79-80). **`linear β ≠ 0` for EVERY β** — including β = 0 — because the
    `single 0 1` component is unconditional: `linear β x = x 1 • (e₀ + β e₂)` (BaseEulerDatum.lean:82-83),
    so `linear β (e₁) = e₀ + β e₂ ≠ 0`. Take β = 0, ell = 1 (`hβ : |0| ≤ 1` ✓, `hell : 0 < 1` ✓,
    `hell1 : 1 ≤ 1` ✓): all three side conditions hold at once and the resulting Evolution has a
    NONZERO velocity gradient (`linear 0 = e₀⊗e₁*`, a genuine shear, trace 0 by
    `linear_trace`, BaseEulerDatum.lean:85). So `Evolution` has a NON-DEGENERATE witness. This is the
    opposite of the `cartesianPotential = 0` / `Bc = L = r = 0` situations flagged elsewhere.
 3. All 7 in-cone theorems (`acceleration_match` :34, `velocity_pullback` :39, `force_pullback` :43,
    `velocity_smooth` :47, `force_smooth` :54, `strain_eq` :60, `curvature_eq` :67) are identities
    transported through `E.inverse.right_inverse` / `A.strain_physical` / `A.curvature_physical`; each has
    real content on that witness (they identify `A.strain` with the Eulerian `fderiv` of a nonzero field).

(C) JUNK-VALUE SWEEP: **no `/`, no `⁻¹` anywhere in the 89 lines** (verified by scan). `E.inverse` is a
`ParticleInverse` record (:16), not a numeric inverse; its two uses (`inverse_left`/`inverse_right` in
ParentPacketFrames.lean:96-102) are certified by `frame_det … = 1` (ParentPacketFrames.lean:91-93,
from the `determinant` field ParentPacketFrames.lean:36-38 — an in-type nondegeneracy certificate, i.e.
this tower does NOT leave the Jacobian invertibility to one layer up). Nothing degenerates silently.

(D) KERNEL RISK: **none.** No `inductive` besides the plain `structure`, no `.rec`, no `termination_by`,
no `deriving`, no `decide`, no `Fin.cases`, no Type-valued `if`, no metaprogramming, no `sorry`.
Largest numeral in the file: `0`. Benign by inspection.

(E) Redundancy note (not a defect): `restrictTime` (:73-86) re-proves `momentum_zero` /
`divergence_zero` / `velocity_differentiable` on the smaller `Ioo` by `⟨ht.1, ht.2.trans_le hST⟩`; the
monotonicity direction is correct (smaller time interval = weaker obligation), so the restriction cannot
smuggle in strength.

Tally: 9 decls read — OK 9 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.
