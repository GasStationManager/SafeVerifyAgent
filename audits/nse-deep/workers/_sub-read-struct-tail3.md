# sub-read-struct-tail3 -- structural tail (8 files), NSE @ f9e8bc5, READ-ONLY

## 1. Euler/PacketCorrectionPrimitiveBounds.lean (153 lines) -- CLEAN
Declares `structure CorrectionBounds (Kc : CorrectionCoefficientBudget D P) (X : ℝ) : Prop` with 9
`≤ X` fields (:79-88).
* CONSTRUCTED (not an unsupplied hypothesis): `correctionBudget_bounds` (:102-130) concludes
  `CorrectionBounds D P (correctionCoefficientBudget ...) (primitiveEnvelope P X)` from no
  `CorrectionBounds` hypothesis. Consumed downstream at PacketSourcePrimitiveBounds.lean:23,:35,:53,:65,
  PacketForwardUniformCosts.lean:28, PacketInitializedParameterBounds.lean:41. `CorrectionBounds.mono`
  (:90) is the P.foo-from-P shape and supplies nothing, correctly noted as such.
* JUNK-VALUE SWEEP: POSITIVE CONTROL. Two inversions appear in statements and both are guarded in the
  SAME signature: `c⁻¹ ≤ (1+X)^2` (:20) sits next to `hc : 0 < c` (:18); `((1+X)^2)⁻¹` (:64,:67) has
  `0 ≤ X` derived in-proof from `hR`/`hRX` (:26). No unguarded `/` or `⁻¹`.
* VACUITY: `correction_envelopes` (:17) is satisfiable by a concrete witness -- take
  `c = 1, R = C0 = C1 = CI = 0, X = 0`: hc 0<1 ok, all `0 ≤ 0` ok, all `_ ≤ 0` ok,
  `hci : 1⁻¹ = 1 ≤ (1+0)^2 = 1` ok. Non-degenerate witness also exists: `c = 1, X = 1, R=C0=C1=CI=1`
  (`1 ≤ 4`). Not vacuous.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`.
  `Fin 4` (:42, well under 22). Largest numeral: `64` (:42). Benign by inspection.
VERDICT: 5 decls read -- OK 5 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 2. Euler/LpSmoothFamily.lean (97 lines) -- CLEAN, base case exists
Declares `structure SmoothFamily (μ) (P) (V)` (Type-valued data: `field`,`smooth`,`jet`,`jet_ae`,
`bound`,`bounded`) at :21-28, plus `value` (:34), `derivative` (:45), and 4 theorems.
* CLOSURE-WITHOUT-BASE-CASE CHECK -- NEGATIVE (this one HAS a base). `derivative` (:45-60) is the
  closure operation (SmoothFamily -> SmoothFamily of the derivative type), but a genuine BASE witness
  is constructed from raw analytic data at `EulerMeanForcing.forcingFamily`,
  Euler/MeanForcingTranslation.lean:26-39 (`SmoothFamily (timeMeasure T) Space (L2Space V)` built out
  of a `ℝ → SmoothL2Field V` plus `MemLp` hypotheses -- no SmoothFamily input). It is used
  non-trivially at MeanForcingTranslation.lean:52-77 and downstream in Euler/LpSmoothFamilyJets.lean.
  Not degenerate: the field is `translation a (A t).toLp` for an arbitrary supplied `A`.
* NAME-TWIN WARNING (informational, not a defect): there are three unrelated `SmoothFamily`s in the
  artifact -- this one, `NavierStokes.MeanRankUpdate.SmoothFamily` (MeanRankUpdate.lean:1177, its own
  witness `SmoothFamily.ofReserved` at :1437), and `NavierStokes.CompactSmoothFamily`
  (CompactSmoothFamily.lean:14). Cross-file grep must be namespace-qualified here.
* `derivativeMap` vs `derivativeBundling` (:66 vs :92) is not an inconsistency:
  Euler/LpDerivativeBundling.lean:35-36 gives `derivativeBundling μ D = derivativeMap μ D` by `rfl`.
* JUNK-VALUE SWEEP: zero `/` and zero `⁻¹` in the file. Nothing to degenerate.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`/
  `Fin.cases`. `Fin 0`-style currying equivs only (`continuousMultilinearCurryFin0`, :35). Largest
  numeral: `2` (the Lp exponent). Benign.
VERDICT: 7 decls read -- OK 7 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 3. Euler/MeanStrongEquation.lean (185 lines) -- 1 NOTE (degenerate-witness chain), rest clean
Declares `structure StrongMeanEvolution T hT FInv F F₁ A L u f` (:26-46, 14 fields: label/velocity/
velocityLp/acceleration + AC + `terminal : label T = 0` + `initial_velocity : velocity 0 = L • A (label 0)`
+ derivative + `equation`). Plus `initial_momentum_cancellation` (:50), `ordinary_projected_equation`
(:74), `meanWeakSolution_strong` (:91).
* CONSTRUCTED, and heavily load-bearing. `meanWeakSolution_strong` (:91-183) produces
  `Nonempty (StrongMeanEvolution ...)` from analytic hypotheses only (`refine ⟨{...}⟩` at :147-161).
  Re-exported at MeanStrongInverse.lean:39-41, MeanSourceStrongInverse.lean:37, and a real element is
  extracted by `Classical.choice` at MeanPacketData.lean:120-128 (`Data.evolution`). ~20 downstream
  files consume it as a hypothesis (MeanStrongEstimates/MeanTimeSobolev/MeanClassicalTime/...).
  NOT an unsupplied hypothesis.
* NOTE -- DEGENERATE WITNESS ON THE LIVE PATH, new consequence of a known defect. The `L` slot is
  instantiated as `D.L` at MeanPacketData.lean:121-123, and `D.L := H.L` for `H : LowBounds`
  (ParentPacketSourceData.lean:54,:67 `L := H.L`), and the live initial witness has
  `(initialLowBounds ...).L = 0` BY `rfl` (BaseEulerState.lean:57-58, with `.Bc = 0` at :56 so the only
  guard `L_lower : boundaryLocalizationC1*Bc ≤ L` (MeanPacketData.lean:45) reduces to `0 ≤ 0`).
  CONSEQUENCE: on the live path the advertised field `initial_velocity` (:39) reads `velocity 0 = 0`,
  and the conclusion of `initial_momentum_cancellation` (:56, `(v : L2) = L • A (z : L2)`) likewise
  reads `v = 0`. The docstrings that sell these as "the original initial velocity condition" (:10-11,
  :89-90) and "the derived momentum condition cancels M0" (:48) therefore say only "the initial
  velocity vanishes" on the live instance. NON-DEGENERATE ALTERNATIVE EXISTS: `L` is an arbitrary real
  in `meanWeakSolution_strong` (:87 `(L : ℝ)`) and `initial_momentum_cancellation` (:50), and the
  proofs never use `L = 0`; so the theorems are not vacuous, only the live specialisation is trivial.
  NOTE (not ESCALATE) since the direction is safe and the general statement is real. This is the same
  root cause the audit already recorded for Euler/MeanPacketData, now reaching a second file.
* Also note `hT : 0 ≤ T` admits `T = 0`; then `timeMeasure 0` makes the three `∀ᵐ` fields (:40,:41,:42)
  vacuous and `terminal` collapses into `label 0 = 0`. Guard is caller-side only (`D.T_pos` at
  MeanPacketData.lean:26-27 supplies `0 < T` on the live path), so this is benign -- a positive control
  for the guard-one-layer-up pattern.
* JUNK-VALUE SWEEP: zero `/`, zero `⁻¹`. `hc : 0 < c` (:114) from `meanFrameCoercivity_pos`, so the
  coercivity constant used throughout is certified positive in-proof, not assumed.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`.
  Largest numeral: `2` (the `(2 : ℝ) •` in the equation, :46,:77). Benign.
VERDICT: 4 decls read -- OK 3 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 4. Euler/CylinderEndpointBudget.lean (75 lines) -- CLEAN; POSITIVE CONTROL for the T-inverse guard
Declares `endpointForcingCost` (:19, contains `T⁻¹`), `structure EndpointBudget D ι q` (:26-50, 5 reals
+ 4 nonneg + `time_le_one : T ≤ 1` + 3 ContDiff + 3 jet bounds + 3 radius inequalities), and
`coordinateCost`/`velocityCost`/`derivativeCost` (:66-69) + 3 nonneg lemmas.
* CONSTRUCTED: `EndpointBudget` is built at Euler/TransversePacketPrimaryBudget.lean:49
  (`def endpointBudget : EndpointBudget B.coefficients ι q where`). Consumed as a hypothesis at
  CylinderEndpointBounds.lean:21 and CylinderEndpointUnitBounds.lean:23. Not unsupplied.
* JUNK-VALUE SWEEP -- GUARDS ARE IN-SIGNATURE (the positive control asked for). Two `T⁻¹` sites:
  `endpointForcingCost` (:20) and `coordinateCost` (:66). `T` is NOT constrained in the bare `def`
  signature of :19 (a plain `(T Rc C₁ : ℝ)`), so `endpointForcingCost ι q 0 Rc C₁ = 0` in isolation.
  BUT every theorem that uses either quantity carries `D : Coefficients T U E` in its own signature
  (:54), and `Coefficients` has the field `time_pos : 0 < T` (Euler/CylinderDirichletData.lean:33),
  which is exactly how the nonneg proofs discharge the inverse: `inv_nonneg.mpr D.time_pos.le` at
  :59 and :72. So the guard is in-signature via the data record, not one layer up. Same for
  `traceCost T` (:72 uses `D.time_pos.le`). No unguarded inverse, no division.
* Minor NOTE-grade observation, not a defect: `coordinateCost` ignores its budget argument
  (`_L`, :66) -- it is only there to fix `T` by unification, so `coordinateCost L = T⁻¹+traceCost T`
  for every `L`. Harmless; `velocityCost`/`derivativeCost` (:67-69) do use `L.Rc`,`L.C₀`,`L.C₁`.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`/
  `Fin.cases`. `[Fintype ι]` only, no concrete `Fin n`. Largest numeral: `6` (:20). Benign.
VERDICT: 8 decls read -- OK 8 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 5. Euler/CorrectionStabilityBudget.lean (98 lines) -- CLEAN; second POSITIVE CONTROL (in-field guard)
Declares `structure StabilityBudget period hT D` (:16-55, 20 fields: metric path + continuity +
time derivative + `c` with `c_pos : 0 < c` + symmetry + `coercive : c^2*‖a‖^2 ≤ ⟪...⟫` + `inverse` +
5 uniform bounds + their 5 `_le` fields), `operatorPath` (:58), `growth` (:63),
`comparisonConstant` (:69), and 3 nonneg theorems.
* CONSTRUCTED, and the base bottoms out in concrete data. Direct constructions:
  GevreyStabilityBudget.lean:58-80 (`stabilityBudgetLower ... : StabilityBudget ... where`, repackaging
  a `MetricBudget period T hT D` + a `SpatialBudget`), AllOrderCorrectionStability.lean:18,
  CorrectionAssemblyData.lean:22 and :61. The `MetricBudget` it rests on is itself constructed
  concretely at ConstantCorrectionData.lean:124 (`MetricBudget P T hT ((data P F R).atOrder P 1)`) and
  by `sourceMetricBudget`/AllOrderCorrectionData.lean:101-102, so there is no closure-without-base
  gap here. Consumed as a hypothesis in >=8 files (CorrectionViscosityStability.lean:25,
  ViscosityCauchy.lean:43,:59, InviscidCorrectionUniqueness.lean:26, InviscidCorrectionParity.lean:27,
  CorrectionFamilyCompactness.lean:53, InviscidCorrectionCompatibility.lean:31).
* JUNK-VALUE SWEEP -- GUARD IS INSIDE THE STRUCTURE, i.e. strictly in-signature. `comparisonConstant`
  (:71) divides by `B.c`; `B.c_pos : 0 < c` is a FIELD of the same record (:29), so every statement
  mentioning `B.comparisonConstant` carries the guard automatically. `comparisonConstant_nonneg` (:96)
  uses exactly that (`div_nonneg _ B.c_pos.le`). This is the cleanest guard pattern in my block: the
  non-degeneracy IS certified by the type, contra defect shape 3. `coercive` (:33) uses `c^2`, so `c`
  is genuinely bounded away from 0 by the record itself.
* `hT : 0 ≤ T` again admits `T = 0`: then `hasDeriv`'s `∀ t ∈ Ioo 0 0` is vacuous and
  `comparisonConstant = sqrt(defectConstant B.bound R * 0 * exp 0)/B.c = 0` (:71). `nonneg` (:74) is
  proved AT `t = 0` (:77) so the record is still inhabitable at `T = 0`, but the comparison constant
  then says nothing. No in-file guard; callers supply `hT.le` from a strict `0 < T`
  (AllOrderCorrectionStability.lean:18, CorrectionAssemblyData.lean:22 both pass `hT.le`). NOTE-worthy
  but benign, and the statements are inequalities (not exact identities), so nothing becomes false.
* POINTER for the parent, outside my files: PacketCorrectionGrowth.lean:40 instantiates
  `sourceMetricBudget D P 0 (by norm_num) Z Z 0` -- a zero/zero-field metric-budget witness. If the
  degenerate-witness census is still open, that line is worth a look by whoever owns that file.
* KERNEL RISK: none new. `Fin 3` at :55 and :82 (well under 22, `Finset.univ` sums only). Largest
  numeral: `3` (:55). No `inductive`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`. There IS a
  `decide` nearby but NOT in my file (InviscidCorrectionUniqueness.lean:81, `by decide : (2 : ℕ) ≠ 0`
  -- a 1-bit decision, benign).
VERDICT: 7 decls read -- OK 7 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 6. Euler/ChildParticleFieldTime.lean (107 lines) -- 1 NOTE (dead half), no unsupplied hypothesis
Declares `structure Representation G P P₁ P₂ D D₁ D₂ : Prop` (:17-24, six pointwise field identities),
then 3 value theorems (`childDisplacement` :34, `childVelocity` :39, `childAcceleration` :46) and 3
derivative theorems (`displacement_hasDerivWithinAt` :58, `velocity_hasDerivWithinAt` :71,
`composition_hasDerivWithinAt` :86).
* CONSTRUCTED, exactly once: PhysicalChildParent.lean:79-97 builds a `Representation` literal inside
  `child_fields_match` from six assumed identities `hD/hV/hW/hd/hv/hw` (:68-74). That is not circular:
  the six inputs are plain equations about a SUPPLIED family `E`, and they are discharged one layer up
  at ParentPacketLabelData.lean:88-91 (`rw [hD]; exact L.displacement_match t x`, etc.) inside
  `LabelData.child`, which is on the live parent/child recursion path. So the predicate is reachable,
  not an unsupplied hypothesis.
* NOTE -- HALF THIS FILE IS DEAD. The only consumer (PhysicalChildParent.lean:98) uses just
  `H.childDisplacement`, `H.childVelocity`, `H.childAcceleration`. Artifact-wide grep for
  `Representation.`-projected uses of the derivative trio returns NOTHING: `composition_hasDerivWithinAt`
  (:86) has zero occurrences outside its own definition, and `velocity_hasDerivWithinAt` (:71) has zero
  occurrences anywhere (not even inside the file -- the other hits for those names in Euler/ are
  unrelated same-named theorems in FixedEndpointClassical.lean:73,:90, CylinderDirichletData.lean:156,
  :165, MeanClassicalTime.lean:110, SourceCylinderEquation.lean:82, all with different signatures).
  `displacement_hasDerivWithinAt` (:58) is used only internally, at :94. So the file's claim that the
  L2 child fields are "exactly the actual first and second time derivatives" (:4-5) is PROVED but never
  CONSUMED: the child-field time-derivative property is not fed to any downstream estimate. Direction
  is safe (these are true statements about constructed objects), but the derivative half is inert.
  NOTE, not ESCALATE.
* JUNK-VALUE SWEEP: zero `/`, zero `⁻¹`. Nothing to degenerate.
* `hT : 0 ≤ T` is an IMPLICIT variable (:56 `variable {hT : 0 ≤ T}`) rather than explicit; it is still
  determined by unification from `projIcc 0 T hT` / `TimeDerivative T hT` in each statement, so this is
  a style artefact, not a shadowing escape (contrast PacketKnownTermSums.lean:16-18). `T = 0` is
  admitted; then `Icc 0 0` is a point and the `HasDerivWithinAt` claims are trivial. Guard is
  caller-side (`G.T_pos`), same benign pattern as file 3.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`/
  `Fin`. Largest numeral: `2` (only in subscripted identifiers `P₂`,`D₂`; no arithmetic literal above
  `0` appears). Benign.
VERDICT: 7 decls read -- OK 6 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 7. Euler/TransversePacketBudget.lean (111 lines) -- CLEAN; third in-record guard, base exists
Declares `structure Budget D τ hτ hτT B ι q` (:36-85: growth profile `g` with `positive`+`initial_one`,
a `neighborhood` with measurability/openness/`support_subset`/`neighborhood_halfball`, 7 reals, 5 nonneg,
`history_length : τ ≤ 1`, 3 jet bounds, 6 radius inequalities, and the `propagator` bound), plus
`fullProfile` (:91), `fullProfile_pos` (:94), `radius_bounds` (:97), `velocityCost` (:101),
`derivativeCost` (:105).
* JUNK-VALUE SWEEP -- the sharpest site in my block, and it is GUARDED IN-RECORD. The `propagator`
  field (:77-85) ends in `≤ C*g t/g s`: a division by `g s`. `g` is a field of the same structure and
  `positive : ∀ t, 0 < g t` (:38) is the field immediately after it, so no instance of this record can
  have `g s = 0`. `initial_one : g 0 = 1` (:39) additionally pins the profile away from the zero
  function. Nothing else in the file divides or inverts. VERDICT: guard in-signature, positive control.
* CONSTRUCTED (base exists, though it is 2 hops away). Closure-only routes:
  `TransversePacketPrimaryRadius.lean:51` (`enlargeForPrimary`) and `PacketInitializedCanonicalRadius
  .lean:46` (`initializedJoinedBudget`, `.enlargeRadius`) both consume a `Budget` to make a `Budget`.
  The genuine BASE is `EulerPacketSourceGeometry.Guards.joinedBudget`, PacketGeometryJoinedBudget.lean:
  46-72, which produces `EulerTransversePacketJoin.Budget D τ hτ hτT H (Fin 4) q` from label bounds,
  coefficient identities, a determinant identity and a growth profile obtained by
  `J.halfBall_controlledGrowth` (:21-38), delegating to
  `EulerPacketParentPhysicalBudgets.joinedBudget`. So this is NOT a closure-without-a-base predicate.
* Non-degeneracy of that base witness: its `C` is the explicit `560*P.horizon^10/P.epsilon`
  (PacketGeometryJoinedBudget.lean:67, PacketGeometryControlledGrowth.lean:72,:110). That division is
  itself guarded: `epsilon_pos` is a field of the geometry record (used e.g.
  PacketGeometryControlledGrowth.lean:26-27 `G.epsilon_pos.ne'`, PacketGeometryAssembly.lean:101,:107).
  And `g` is supplied positive (`sourceGrowthProfile_positive`) with `g 0 = 1`
  (`sourceGrowthProfile_initial`), so the witness is NOT the degenerate `g ≡ 0`.
  Note the safe direction of `C_nonneg` (:56): `C = 0` would make `propagator` HARDER (it would force
  the propagator composition to vanish), never trivially true -- the opposite of a junk-value collapse.
* KERNEL RISK: none in-file. `ι` stays abstract with `[Fintype ι]` (:33); the concrete instantiations
  downstream are `Fin 4` with `q = 6` (PacketInitializedCanonicalRadius.lean:19 etc.), far below the
  `Fin 22` threshold. Two `private local instance ... := inferInstance` at :27-28 (NormedRing on
  `U →L[ℝ] U` and on `Space →ᵇ U →L[ℝ] U`) -- instance plumbing, no metaprogramming, no `deriving`.
  Largest numeral: `18` (:76). Benign by inspection.
VERDICT: 8 decls read -- OK 8 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 8. Euler/PacketProfileBudget.lean (62 lines) -- CLEAN
Declares `structure ProfileBudget G S R p : Prop` (:15-24, seven `WordBound 6 R 1 <shift>` fields on
normalized high/mean/corrector/pressure fields), `Field.normalized_wordBound_congr` (:26),
`ProfileBudget.prefixBound` (:39), `ProfileBudget.transfer` (:47).
* CONSTRUCTED without assuming itself: `joinedTerminalPrimary_budget`,
  PacketTerminalPrimaryBudget.lean:27-37, concludes `ProfileBudget (joinedTerminalPrimaryWitness ...)
  S L.R 1` from a joined `Budget`/`Primary.Budget`/`GradeGuards` bundle only (no `ProfileBudget`
  hypothesis); likewise PacketForwardInitializedProfiles.lean:42,:53. `transfer` (:47) and
  PacketProfileBudgetTransport.lean:13 are the P-from-P shape and supply nothing, but the base is real.
  Consumed widely (PacketFiniteApproximationBounds.lean:16, PacketJoinedStepBudget.lean:35,
  PacketForwardStepBudget.lean:33, PacketInitialBounds.lean:72, ...). `normalized_wordBound_congr` (:26)
  is used at PacketPrimaryGradeBounds.lean:100-114 and PacketForwardPrimaryBounds.lean:49-63.
* JUNK-VALUE SWEEP: zero `/`, zero `⁻¹` in the file. The scale arguments that a normalization would
  divide by carry their positivity in-record: `S.high_pos p` / `S.mean_pos p` (fields of `Scales`) are
  passed at every single field (:17-24), and `normalized_wordBound_congr` demands `hg : ∀ t, 0 < g t`
  and `hk : ∀ t, 0 < k t` explicitly (:28). Fully guarded in-signature.
* `normalized_wordBound_congr` (:26-33) is near-trivial (`subst k; exact hb`, sound only because Prop
  proof irrelevance makes `hg`/`hk` interchangeable) -- but it is a legitimate transport lemma with
  five real call sites, not padding.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`/
  `Fin`. Largest numeral: `6` (the fixed Sobolev order, :17-24). Benign.
VERDICT: 4 decls read -- OK 4 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

# BLOCK SUMMARY (8 files, 50 decls)
OK 48 / NOTE 2 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.
* NO ESCALATE and NO KERNEL RISK anywhere in this tail. Explicitly checked and ABSENT in all 8 files:
  `inductive`, `.rec`/`Nat.rec`/`Acc.rec`, `termination_by`, `deriving`, `decide`/`native_decide`,
  `Fin.cases`, Type-valued `if`, metaprogramming. Largest numeral in the whole block: `560` (and that
  is not in my files -- it is the propagator constant `560*P.horizon^10/P.epsilon` at
  PacketGeometryJoinedBudget.lean:67 feeding my file-7 `C` field). In-file maxima: 64, 2, 2, 6, 3, 0,
  18, 6. No `Fin n` with n > 4. So the structural block's flag count stays at two.
* JUNK-VALUE SWEEP RESULT -- ALL FOUR division/inverse sites are guarded IN THEIR OWN SIGNATURE, three
  of them by a FIELD OF THE SAME RECORD (the strongest form, non-degeneracy certified by the type):
  `c⁻¹`/`((1+X)^2)⁻¹` with `hc : 0 < c` (PacketCorrectionPrimitiveBounds.lean:18,:20);
  `T⁻¹` with `Coefficients.time_pos` (CylinderEndpointBudget.lean:20,:66 vs
  CylinderDirichletData.lean:33); `/B.c` with field `c_pos` (CorrectionStabilityBudget.lean:29,:71);
  `C*g t/g s` with field `positive` (TransversePacketBudget.lean:38,:85). ZERO unguarded exact
  identities, so no new instance of the "exact identity collapsing to 0 = 0" pattern.
* NO unsupplied hypothesis and NO closure-without-a-base in this tail: all 8 declared structures are
  constructed -- CorrectionBounds (PacketCorrectionPrimitiveBounds.lean:102), SmoothFamily
  (MeanForcingTranslation.lean:26), StrongMeanEvolution (MeanStrongEquation.lean:147 +
  MeanPacketData.lean:120), EndpointBudget (TransversePacketPrimaryBudget.lean:49), StabilityBudget
  (GevreyStabilityBudget.lean:58), Representation (PhysicalChildParent.lean:79), Budget
  (PacketGeometryJoinedBudget.lean:46), ProfileBudget (PacketTerminalPrimaryBudget.lean:29).
* The two NOTEs: (a) MeanStrongEquation.lean:39 -- `initial_velocity` reads `velocity 0 = 0` on the live
  path because `L = 0` by `rfl` four links away (BaseEulerState.lean:57), a second file reached by the
  already-known MeanPacketData degenerate witness; a non-degenerate `L` is admissible so nothing is
  vacuous in general. (b) ChildParticleFieldTime.lean:58,:71,:86 -- the child-field time-derivative
  trio has no consumer anywhere in the artifact (dead, not wrong).
* Recurrent benign pattern worth recording: five of the eight files take `hT : 0 ≤ T` and admit `T = 0`,
  where `∀ᵐ`/`Ioo 0 T` fields go vacuous; every live caller supplies a strict `0 < T` (`D.T_pos`,
  `M.T_pos`, `G.T_pos`). Guard one layer up, direction safe, statements are inequalities.

