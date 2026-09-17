# Junk-value triage 3 — NSE @ f9e8bc5 (READ-ONLY)

Rule under test: flag only if denominator reaches a subterm on ONE side of the statement.

## 1. Euler/PacketPhysicalLowBounds.lean — 2 hits: C, C (both bounds; harmless)

* `Euler/PacketPhysicalLowBounds.lean:57` `shearTerm_norm_le` — CLAIMS a bound
  `‖shearTerm amp slope r w‖ ≤ (amp*(‖r‖*‖w‖))/δ`. Signature has `hamp : 0 ≤ amp`,
  `hslope : |slope| ≤ δ⁻¹` (:58) and NO `δ ≠ 0`.  **Class C.**
  At `δ = 0` the RHS is `.../0 = 0`; but the *hypothesis* also degenerates:
  `δ⁻¹ = 0` so `hslope` becomes `|slope| ≤ 0`, i.e. `slope = 0`, hence
  `shearTerm amp 0 r w = (amp*0) • rankOne … = 0` (def :16-17) and the LHS is
  ALSO 0. Statement collapses to `0 ≤ 0` — a bound, so nothing of value is lost.
  Callers exclude it anyway: `good_step_bounds` :141 `(hδ : 0 < δ)`, used at :154;
  `absolute_step_bounds` :173 `(hδ : 0 < δ)`, used at :186.

* `Euler/PacketPhysicalLowBounds.lean:65` `pressureTerm_norm_le` — CLAIMS a bound
  `‖pressureTerm amp slope M r w‖ ≤ 2*‖M‖*(amp*(‖r‖*‖w‖))/δ`. Same shape: only
  `hamp`, `hslope : |slope| ≤ δ⁻¹` (:66). **Class C.** At `δ = 0`, `hslope` forces
  `slope = 0`, and `pressureTerm` (def :19-20) has `slope` as a factor of its
  scalar, so LHS = 0; RHS = 0. Collapses to `0 ≤ 0`. Callers: :141/:155-158 and
  :173/:188-192, both with `0 < δ`.

NOTE (new FP kind, kind (iii)): here the denominator ALSO occurs in a hypothesis
(`|slope| ≤ δ⁻¹`) whose own degeneration pins the LHS to the same junk value. The
collapse is coordinated, not silent-in-one-direction. Worth adding to the tool.

## 2. Euler/PacketPressureFastHessian.lean — 2 hits (same theorem), both FALSE POSITIVES

* `Euler/PacketPressureFastHessian.lean:49` `fastHessianRemainder_norm_le` — CLAIMS a bound
  `‖fastHessianRemainder a k m Y J x‖ ≤ |k⁻¹| * (…)`. No `k ≠ 0` in the signature.
  **Class B (symmetric collapse; the ONE-SIDE rule filters it).**
  `k⁻¹` is the outer scalar of the definition (:19-23, `k⁻¹ • (…)`) and appears
  EXPLICITLY as the outer factor `|k⁻¹|` of the RHS (:52). At `k = 0` both sides are
  literally `0`, so the statement is `0 ≤ 0` and the inequality's shape is preserved
  by the same junk value on both sides — no asymmetric loss of content. It is a bound,
  not an exact value, so nothing was claimed there anyway.
  (The instrument reported this row twice: once as `denom k`, once as
  `denom k (via fastHessianRemainder)` — the same `k⁻¹` seen syntactically and
  through the definition. Dedupe those.)
  Caller also guards: `Euler/PacketPressureFastBounds.lean:28` `(hk : 0 < k)`, use at
  `PacketPressureFastBounds.lean:59-61` (`abs_of_pos (inv_pos.mpr hk)`).
  Note :25 `fastForce_hasFDerivAt` in the SAME file DOES carry `(hk : k ≠ 0)`, i.e. the
  author guards exactly where the identity would otherwise be exact — evidence the
  unguarded :49 is deliberate, not an oversight.

## 3. Euler/PacketScaledRay.lean — 2 hits (same theorem), both FALSE POSITIVES

* `Euler/PacketScaledRay.lean:14` `physicalTime_hasDerivAt` — CLAIMS the derivative of
  the time reparametrisation: `HasDerivAt (physicalTime t₀ a ε) (ε/a) τ`, where
  `physicalTime t₀ a ε τ = t₀ + (ε/a)*τ` (:12). **Class B (junk value is the TRUE value).**
  At `a = 0` the function becomes the CONSTANT `t₀ + 0*τ = t₀` and the claimed derivative
  becomes `ε/0 = 0`, which is the correct derivative of a constant. The theorem is true
  and non-vacuous for every `a`, including 0; nothing is lost because `ε/a` occurs both in
  the function and in the derivative slot (prompt FP kind (i), shared subterm).
  Both hit rows (`denom a` and `denom a (via physicalTime)`) are this one theorem.
  For contrast, the two real consumers in the same file DO carry `(ha : a ≠ 0)`:
  `scaledRay_hasDerivAt` :42 and `scaledRay_hasDerivWithinAt` :63 (needed by
  `scaledRayRate_algebra` :25, which is stated WITH `ha : a ≠ 0`).

## 4. NavierStokes/RadialModulation.lean — 2 hits, both FALSE POSITIVES (B)

* `NavierStokes/RadialModulation.lean:47` `modulatedE_contDiffAt` — CLAIMS smoothness:
  `ContDiffAt ℝ ∞ (uncurry (modulatedE n E A)) (X,η)` given `hE`, `hA`, `hX : X ≠ 0`.
  Denominator `n` enters via `modulatedE n E A X η = E X η * exp (A (phasePoint n X η) / n)` (:39-40).
  **Class B (no collapse to triviality).** At `n = 0`, `A(…)/0 = 0`, so the function becomes
  `E X η * exp 0 = E X η` and the conclusion becomes `ContDiffAt ℝ ∞ (uncurry E) (X,η)` — still a
  genuine, non-vacuous claim (and true from `hE`). The conclusion is a PREDICATE about a function,
  not an equation with `n` on one side; nothing degenerates into `0 = 0`.
* `NavierStokes/RadialModulation.lean:56` `modulatedU_contDiffAt` — same, with
  `modulatedU n U B X η = U X η + B (phasePoint n X η)/n` (:42-43); at `n = 0` it degenerates to
  `ContDiffAt ℝ ∞ (uncurry U) (X,η)`. **Class B.**
  Its caller `NavierStokes/ParametricModulation.lean:466-476` `realized_profiles_contDiffAt` also
  has no `n ≠ 0`, consistent with the guard being unnecessary here.
  Strong counter-evidence that the file's guard discipline is deliberate: every neighbouring
  theorem whose conclusion IS an exact derivative identity carries `hn : n ≠ 0` — :93, :106,
  :138, :154 — and the estimate lemmas carry `hn : 0 < n` (:169, :189).

## 5. Euler/GevreyGrowthBudget.lean — 2 hits, both FALSE POSITIVES (B, symmetric)

* `Euler/GevreyGrowthBudget.lean:21` `growthBase_budget` — CLAIMS a majorant (bound):
  `growthBase period K K' c ≤ growthBudgetBase c D L`. No `c ≠ 0`/`0 < c`.
  **Class B (symmetric collapse; ONE-SIDE rule filters it).** `c` divides on BOTH sides:
  LHS `growthBase … c = (‖K'‖+2*heatEnergyConstant period K c)/(2*c^2)`
  (`Euler/GevreyGrowthCoefficient.lean:16-17`, with `heatEnergyConstant = 2*F^2/c^2`,
  `Euler/CylinderViscousEnergy.lean:17-18`); RHS `growthBudgetBase c D L = (D+4*L^2/c^2)/(2*c^2)`
  (:13). At `c = 0` both outer divisions give 0, so the claim is `0 ≤ 0` — a bound, no content lost.
* `Euler/GevreyGrowthBudget.lean:44` `viscousGrowth_budget` — CLAIMS
  `viscousGrowthCoefficient … c ν B ≤ growthBudgetBase c D L + growthBudgetSlope c L * B`.
  **Class B, same reason.** LHS is `(…)/(2*c^2)` (`Euler/WeightedCylinderEnergy.lean:37-40`),
  RHS terms are `(…)/(2*c^2)` (:13) and `2*L/(2*c^2)` (:16); at `c = 0` everything is 0,
  giving `0 ≤ 0`.
  The downstream consumer that needs real content does guard: `viscousGrowth_fixed_metric`
  :55 `(hc : 0 < c)` (it must, since `metricVelocityBound_coe` is used at :62, and
  `metricAmplification c = 1+√5461/c`, `Euler/GevreyMetricEstimate.lean:27`).

## 6. Euler/PacketForwardInitializedTimeBounds.lean — 2 hits (same theorem): C (mild)

* `Euler/PacketForwardInitializedTimeBounds.lean:32` `forwardInitializedNormalizedField_time`
  — CLAIMS that the derivative field really is the time derivative of the normalized field:
  `TimeDerivative D.T_pos.le (forwardInitializedNormalizedField … N k)
     (forwardInitializedNormalizedDerivativeField … N k)`. No `k ≠ 0` / `4 ≤ k`.
  **Class C (with a strong B flavour).** `k` enters symmetrically: `k⁻¹` is the profile
  parameter of BOTH fields (:29-30, and `Euler/PacketForwardInitializedCorrectionData.lean:22-23`),
  and both are built by `coordinateField/coordinateTimeField … k`
  (`Euler/PacketCoordinateJets.lean:87-91`) whose raw value is `k • (…)`.
  At `k = 0` both fields are the ZERO field, so the claim degenerates to "the zero path has
  derivative zero" — true, and the correct statement about the degenerate object (same shape as
  `physicalTime_hasDerivAt`), but it says nothing. Content-free, NOT wrong.
  Note the underlying `coordinateField_time` (`PacketCoordinateJets.lean:93`) needs no `k ≠ 0`
  at all — `k` is a MULTIPLIER there, not a divisor; only `k⁻¹` inside the profile parameter is
  the "division", and it is passed identically to both arguments.
  Callers all exclude `k = 0`: `Euler/PacketForwardUniformFlow.lean:36 (hk : 4 ≤ k)` used at :189,
  and `Euler/PacketForwardInitializedFlowBounds.lean:48 (hk : 4 ≤ k)` used at :161.
  Same file, :62 `forwardInitializedNormalizedDerivativeField_bound` carries `(hk : 4 ≤ k)`.
  (Both instrument rows — `via forwardInitializedNormalizedField` and
  `via forwardInitializedNormalizedDerivativeField` — are this one theorem; dedupe.)

## 8-PREVIEW. Euler/PacketInitializedTimeBounds.lean:33 — identical twin, same verdict (C)

* `Euler/PacketInitializedTimeBounds.lean:33` `initializedNormalizedField_time` is the
  history-initialized copy of the above, definitions at :28-31 and
  `Euler/PacketInitializedCorrectionData.lean:23-24`. Same symmetric `k⁻¹`/`smul k`; at `k = 0`
  it degenerates to `TimeDerivative 0 0`. **Class C.** Callers with `hk : 4 ≤ k`:
  `Euler/PacketInitializedUniformFlow.lean:38` (use at :192) and
  `Euler/PacketInitializedFlowAndShear.lean:50` (use at :169).

## 7. Euler/PacketForwardScalarPressureGrade.lean — 2 hits, both FALSE POSITIVES (A)

Both rows blame `C`, which is NEVER a denominator: `grep -rn '/ *C[^a-zA-Z0-9_]\|C⁻¹' Euler`
returns only a prose comment (`Euler/PacketKnownDecomposition.lean:4`). `C` is the GradeGuards
amplitude (`Euler/TransversePacketForwardGradeBounds.lean:48 structure GradeGuards (C : ℝ)`), used
only multiplicatively (`(c*C)*majorant …`, :43/:45/:64/:66). Instrument misattribution.

The genuine division in the closure of `angularField` is the PROFILE reciprocal in
`Field.normalized` (`Euler/PacketCylinderFieldWeight.lean:45-47`,
`(g (projIcc 0 T hT z.1))⁻¹ • raw z`) — and that operator DEMANDS a term-level positivity proof
`(hg : ∀ t, 0 < g t)`, i.e. it is impossible to write the division without certifying it (same
pattern as `WeightedClasses.StripData.epsilon_pos`; cf. `normalize` in
`Euler/ContinuousTimeWeight.lean:30-35`, `reciprocal … (hg t).ne'`).

* `Euler/PacketForwardScalarPressureGrade.lean:60` `angular_grade_bound` — CLAIMS a WordBound
  (grade/amplitude bound) for the normalized angular pressure-gradient field.
  **Class A: guarded in the signature** — `(c : ℝ) (hc : 0 < c)` :62, and the profile positivity
  witness `smul_profile_pos L.g L.positive c hc` is passed INSIDE the statement (:67-68).
* `Euler/PacketForwardScalarPressureGrade.lean:112` `primary_scalar_and_angular_grade_bound`
  — same claim shape for the primary forcing. **Class A**: `(α : ℝ) (hα : 0 < α)` :114 with
  `smul_profile_pos L.g L.positive α hα` inside the statement (:117-120).

## 9. Euler/PacketMatrixContinuity.lean — 2 hits: C, C (continuity claims)

* `Euler/PacketMatrixContinuity.lean:37` `scaledRayEntry_continuousOn` — CLAIMS
  `∀ i j, ContinuousOn (fun τ => scaledRayEntry a ε (M τ) (S τ) i j) U` from entrywise
  continuity of `M`,`S`. No `a ≠ 0`. **Class C.**
  `scaledRayEntry a ε M S i j = -(ε/a)*(rayScale ε j/rayScale ε i)*(M j i - S j i)`
  (`Euler/EulerProof.lean:16050-16051`). At `a = 0` the whole entry is the CONSTANT `0`
  (`ε/0 = 0`), so the claim degenerates to "the zero function is continuous on U" — true,
  content-free, and it no longer says anything about the frame matrices. It is a qualitative
  property, not an exact value, so the loss is mild.
  Callers exclude it: `Euler/PacketPhysicalNeighbor.lean:23 (ha : 1/2 ≤ a)` (`0 < a` derived
  at :90), use at :103; `Euler/PacketPhysicalStage.lean:24 (ha : 1/2 ≤ a)` (:85), use at :98.
* `Euler/PacketMatrixContinuity.lean:45` `scaledVelocityEntry_continuousOn` — same claim for
  `scaledVelocityEntry a ε M i j = (…)*(…)*M i j / a` (`Euler/EulerProof.lean:16261-16263`).
  **Class C**, same degeneration to `ContinuousOn 0 U`. Callers as above
  (`PacketPhysicalNeighbor.lean:105,107`; `PacketPhysicalStage.lean:100,102`), and every
  algebraic identity about these entries DOES carry `ha : a ≠ 0`
  (`Euler/PacketFrameRenewalAlgebra.lean:20,35`; `Euler/EulerProof.lean:16266`;
  `Euler/PacketScaledRay.lean:25,42,63`) — the exact-identity/continuity split is deliberate.

## 10. Euler/PacketTangentNorm.lean — 2 hits, both FALSE POSITIVES (B, shared evaluation point)

Both rows blame `a` reached only through `physicalTime t₀ a ε τ = t₀ + (ε/a)*τ`
(`Euler/PacketScaledRay.lean:12`). This is exactly FP kind (i): `physicalTime t₀ a ε τ` is a
SHARED EVALUATION POINT occurring in the hypotheses and on both sides of the conclusion, so
`a = 0` merely re-evaluates the whole statement at `t₀`. Nothing degenerates.
* `Euler/PacketTangentNorm.lean:12` `scaled_pair_le_physical_norm` — CLAIMS
  `|V 0|+|V 1| ≤ (2/ε)*‖w (physicalTime …)‖`. **Class B.** The real denominator here is `ε`, and
  it IS guarded in the signature: `(hε : 0 < ε)` :13. At `a = 0` the claim becomes the same true
  bound at time `t₀`.
* `Euler/PacketTangentNorm.lean:38` `physical_velocity_le_scaled_state` — CLAIMS
  `‖w (physicalTime …)‖ ≤ 7*Θ^2*(|V 0|+|V 1|)`. **Class B**, same reason; `a` appears ONLY inside
  `physicalTime`, on both sides and in every hypothesis (:41-48); the other denominators are
  guarded: `(hs₀ : s₀ ≠ 0)` :40, `(hε : 0 < ε)` :40.

## 11. Euler/WholeSpaceGaussianTimeKernel.lean — 2 hits: C, C (the second is the PulseCovariance shape)

Junk arithmetic in play: `normalization t = (π*t)^(-(3:ℝ)/2)` (`Euler/WholeSpaceGaussian.lean:19`),
so `normalization 0 = 0` by `Real.zero_rpow` (exponent ≠ 0), hence `kernel 0 x = 0*exp 0 = 0`
(`Euler/WholeSpaceGaussian.lean:21-22`), and `timeKernel 0 y = (0*‖y‖^2-0)*0 = 0` (:13-14).
Every positivity lemma about these objects IS guarded (`normalization_pos`
`WholeSpaceGaussian.lean:24`, `kernel_pos` :27), so the unguarded ones stand out.

* `Euler/WholeSpaceGaussianTimeKernel.lean:36` `timeKernel_continuous` — CLAIMS
  `Continuous (timeKernel t)` for ALL `t`, no `0 < t`. **Class C.** At `t = 0`, `timeKernel 0 = 0`
  and the claim degenerates to "the zero function is continuous". Qualitative property, mild loss.
  Callers all guard: `timeKernel_integrable` :63 `(ht : 0 < t)` (use at :65),
  `Euler/WholeSpaceGaussianEvolution.lean:17 (ht : 0 < t)` (use at :28).

* `Euler/WholeSpaceGaussianTimeKernel.lean:41` `timeKernel_second_sum` — **C, and this is the
  `PulseCovariance:74` shape you asked me to hunt: an EXACT IDENTITY, not a bound.**
  CLAIMS `timeKernel t y = (1/4) * ∑ i, secondKernel t e_i e_i y`, i.e. the time derivative kernel
  is exactly a quarter of the traced second spatial kernel. Signature has NO `0 < t`.
  At `t = 0`: LHS `= 0` (above); RHS each `secondKernel 0 a b y = (4*0*…-2*0*…)*kernel 0 y = 0`
  (`Euler/WholeSpaceGaussianKernel.lean:19-20`) — both by `t⁻¹ = 0` AND by `kernel 0 y = 0`.
  So the exact identity collapses to `0 = 0`, i.e. the heat-kernel trace identity says NOTHING at
  `t = 0`, surviving only because `Real.zero_rpow` and `inv 0` conspire on both sides.
  Benign only because every consumer guards: `timeKernel_bound` :48 `(ht : 0 < t)` (use at :50),
  `Euler/WholeSpaceGaussianEvolution.lean:55 timeIntegral_eq_secondAverage (ht : 0 < t)` (use at :64).
  RULE NOTE: `t` occurs on BOTH sides here, so the ONE-SIDE rule would have suppressed this — and
  it would equally have suppressed `PulseCovariance:74` (`b` is in the LHS integrand AND in
  `sqrt(π/b)`). The rule is wrong for exact identities.

## 8. Euler/PacketInitializedTimeBounds.lean — see "8-PREVIEW" above (2 hits = 1 theorem, C).

## 12. Euler/MeanCutoffTaylor.lean — 1 hit: FALSE POSITIVE (B)

* `Euler/MeanCutoffTaylor.lean:121` `Cutoff.differenceError_fderiv` — CLAIMS an exact identity:
  `fderiv (χ.differenceError a h).field x = h⁻¹ • (fderiv χ.field (x+h•a) - fderiv χ.field x)
   - fderiv (fderiv χ.field) x a`. No `h ≠ 0`. **Class B: the `h = 0` instance is NOT content-free.**
  `differenceError a h = (differenceQuotient a h).sub (directional a)` (:107-108), and
  `(χ.differenceQuotient a h).field x = h⁻¹*(χ.field (x+h•a) - χ.field x)`
  (`Euler/MeanBoundaryDifference.lean:40-44`). At `h = 0` the quotient field is the CONSTANT 0, so
  LHS `= -fderiv (χ.directional a).field x = -fderiv (fderiv χ.field) x a` (`:63-64`
  `directional_fderiv`), and RHS `= 0 • (…) - fderiv (fderiv χ.field) x a` — the SAME nonzero
  second-derivative term. So the identity remains true AND informative at `h = 0`; only the
  quotient term drops out, symmetrically on both sides.
  Caller also guards: `cutoffBound_differenceError` :137 `(hh : h ≠ 0)`, use at :142.
  (Same story for the unflagged `differenceQuotient_fderiv`,
  `Euler/MeanCutoffDifferenceBound.lean:57`: at `h = 0` it is `0 = 0`, symmetric and harmless;
  the quantitative lemmas that need `h⁻¹` cancellation DO carry `hh : h ≠ 0` —
  `MeanCutoffTaylor.lean:44`, `MeanCutoffDifferenceBound.lean:39-55`.)

# TALLY (23 hit rows; 4 pairs are duplicate rows for one theorem → 19 distinct theorems)

**A = 2, B = 11, C = 10, D = 0.**

* A (guarded in signature): `PacketForwardScalarPressureGrade.lean:60, :112`.
* B (certified / symmetric / junk value is the true value): `PacketPressureFastHessian:49` (x2 rows),
  `PacketScaledRay:14` (x2 rows), `RadialModulation:47, :56`, `GevreyGrowthBudget:21, :44`,
  `PacketTangentNorm:12, :38`, `MeanCutoffTaylor:121`.
* C (guarded by callers only, statement alone says less): `PacketPhysicalLowBounds:57, :65`,
  `PacketForwardInitializedTimeBounds:32` (x2 rows), `PacketInitializedTimeBounds:33` (x2 rows),
  `PacketMatrixContinuity:37, :45`, `WholeSpaceGaussianTimeKernel:36, :41`.
* D: NONE. Every hit is either guarded in its own signature, symmetric/true at the junk value, or
  excluded by every caller I could find by grep.

## Verdict on the ONE-SIDE rule
It held as a SUFFICIENT filter for false positives on BOUNDS (`PacketPressureFastHessian:49`,
`GevreyGrowthBudget:21/:44` are exactly "same divisor both sides → `0 ≤ 0`"), and FP kind (i)
(shared evaluation point `physicalTime`) accounted for 4 of the 11 B's.
But it FAILS on EXACT IDENTITIES: `WholeSpaceGaussianTimeKernel:41` has `t` on both sides and still
collapses to a fully content-free `0 = 0` — and the same is true of your model case
`PulseCovariance:74` (`b` sits in the LHS integrand and in the RHS `sqrt(π/b)`), which the rule
would have suppressed. Proposed patch: apply the one-side rule ONLY when the goal's head is `≤`/`<`
or a predicate (`Continuous`, `ContDiffAt`, `Integrable`, `HasDerivAt`, `WordBound`); for `=` goals,
instead evaluate BOTH sides at the junk point and flag when both reduce to the SAME constant
(0 or the same single surviving term is the discriminator: `MeanCutoffTaylor:121` keeps a real
term → FP; `WholeSpaceGaussianTimeKernel:41` keeps nothing → report).
Second patch (new FP kind (iii)): if the divisor also occurs in a HYPOTHESIS (`|slope| ≤ δ⁻¹`,
`PacketPhysicalLowBounds:58/:66`), the degenerate hypothesis can pin the LHS to the junk value —
coordinated, not silent.
Third patch: `C` in `PacketForwardScalarPressureGrade` is never a denominator
(`grep -rn '/ *C[^a-zA-Z0-9_]\|C⁻¹' Euler` → nothing); and dedupe rows that differ only by
`(via <def>)`. Also whitelist `Field.normalized`/`normalize`
(`Euler/PacketCylinderFieldWeight.lean:45`, `Euler/ContinuousTimeWeight.lean:30-35`): those
divisions cannot be written without a term-level `∀ t, 0 < g t` witness, exactly like
`StripData.epsilon_pos`.

