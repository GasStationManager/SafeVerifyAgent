# Junk-value triage tranche 4 — NSE @ f9e8bc5 (READ-ONLY)

Instrument: source read only (no `lake build`; 0 .olean, pinned lean4:v4.34.0-rc2).
Classes: A guarded-in-signature, B certified-by-type/construction, C guarded-by-callers-only,
D genuinely unguarded. Appended file-by-file in the order given.

## 1. NavierStokes/BasePrefixIdentity.lean:111 `prefixSwirl_radial` — denom `C` — **C (caller-guarded)**

CLAIM: exact identity `-partialS (prefixSwirl J h C d) p = slowSwirl J h C (profiles h d) p`
(the finite Borel swirl prefix's radial derivative EQUALS the slow swirl field). Signature
(BasePrefixIdentity.lean:111-113) has `(C : ℝ)` with no hypothesis at all.

COLLAPSE AT C = 0. The swirl channel is `C⁻¹` on both sides:
* `SlowBorelBase.coefficientBundle`:1137 slot 1 = `-C⁻¹ * primitive (d.phi j)`, exported as
  `bundleComponent C d 1` (SlowBorelBase.lean:1153).
* LHS: `BaseResidual.prefixSwirl`:614-615 = `physicalUncutPrefix h (1/2 - A h) (bundleComponent C d 1) J`;
  `physicalUncutPrefix` (SlowBorelBase.lean:885-886) is `q^b • uncutPrefix` of that family, so with the
  family identically 0 (because `(0:ℝ)⁻¹ = 0`) the prefix is the zero function and `partialS 0 = 0`.
* RHS: `SlowExpansionResidual.slowSwirl`:553-554 = `C⁻¹ * finiteProfile ...` = 0.
So at C = 0 the theorem reads `-0 = 0`, i.e. `0 = 0`. This is the PulseCovariance:74 shape: an EXACT
identity surviving by two conspiring junk values (`0⁻¹ = 0` on each side independently), not a bound.

WHY C, NOT D. Nothing in this file constrains C — the internal caller `prefixVelocity_eq_profiles`:157-158
and `prefixVelocity_eq_slowVelocity`:235-237 and `prefixVelocity_germ`:260-262 all keep `(C : ℝ)` free.
Positivity only appears at the instantiation layer, where C is always `…axis.normalization`:
* NavierStokes/ConstructedSlowBase.lean:219 and :346, NavierStokes/EntranceAlignedBase.lean:364
  (`BasePrefixIdentity.CoefficientMatches F.data.h W.axis.normalization …`);
* NavierStokes/BaseWitnessClosure.lean:92 (`BaseResidual.FiniteIdentities ActualPrimary.h
  ActualPrimary.nominal.axis.normalization`), with :54-60 exhibiting `0 < …axis.normalization` via
  `NominalProfile.AxisStage.normalization_pos` (NominalProfile.lean:79-81, derived from the
  `normalization_large` field at NominalProfile.lean:69-70).
So the degenerate branch is unreachable in the assembled proof, but the theorem AS STATED says nothing at
C = 0, and no type records that. Benign-but-weakened; matters because it is an exact identity, and because
the whole swirl channel (:86, :112, :133, :158, :237, :262) inherits the same free `C`.

## 2. NavierStokes/ClosedNativeWaveIdentities.lean:279 `curlRemainder_contDiffAt` — denom `K` — **D (unguarded, but LOW severity)**

CLAIM: a REGULARITY statement — `ContDiffAt ℝ ∞ (curlRemainder K R Vr Vθ Vz B) x` from smoothness of
R, Vr, Vθ, Vz, B and `R x ≠ 0`. `(K : ℝ)` is explicit and unconstrained (:279).

COLLAPSE AT K = 0. `CurlClassBounds.curlRemainder`:269-271 is `(1 / K) • (Complex.I • cylindricalCurl …)`,
so at K = 0 the function is identically `0` and the conclusion becomes `ContDiffAt ℝ ∞ (fun _ => 0) x`,
provable without any hypothesis. Nothing guards it: `WaveCoefficients.frequency : ℕ → ℝ` is a bare field
(LinearWaveBounds.lean:185, no positivity/nonzero field), and the only caller
`RawJetsAt.curlCorrection` (ClosedNativeWaveIdentities.lean:564-565) passes `a.frequency n` while
`RawJetsAt` (:545-552) carries only `cutoff`, `radius_ne`, `normal_ne` — no `frequency ≠ 0`.
The sibling record `LocalizedCurlRealization.RawData`:55 DOES carry `frequency : ∀ n, a.background.frequency n ≠ 0`,
which is the guard that this chain omits.

SEVERITY: low. This is the "bound collapsing to 0 ≤ 0" kind — a smoothness claim, and smoothness of
`c • f` is insensitive to c anyway. Report it only as a missing-hypothesis hygiene item, not as a
content-free EXACT identity. (Class-A/B it is not: nothing at all excludes K = 0.)

## 3. NavierStokes/CopyAngularInvariance.lean:327 `curlRemainder_invariant` — denom `K` — **D (unguarded, LOW severity)**

CLAIM: a STRUCTURAL property — `Invariant θ (curlRemainder K R Vr Vθ Vz a)` (translation invariance of the
stripped curl error), proved at :331-332 by `.map (fun v => (1 / K) • (Complex.I • v))`. `(K : ℝ)` free (:329).

COLLAPSE AT K = 0: `curlRemainder` becomes the zero function (CurlClassBounds.lean:269-271, `1/0 = 0`), so
the conclusion is `Invariant θ (fun _ => 0)` — trivially true, hypotheses unused. Nothing anywhere in the
chain constrains K (same bare `WaveCoefficients.frequency : ℕ → ℝ`, LinearWaveBounds.lean:185); the
consumer `realizedCoefficient_invariant`:333-338 also takes `(K : ℝ)` free.

SEVERITY: very low, and lower than #2 — invariance of `c • f` follows from invariance of `f` for every c
including 0, so the theorem loses nothing usable. Hygiene only, NOT an "exact value" collapse.

## 4. NavierStokes/FlatPrimitiveFactor.lean:128 `transformed_integrand` — denom `t` — **A (guarded in signature)**

FALSE POSITIVE. Claim: the change-of-variables Jacobian identity
`|-(x³/(2·denominator x t³))| * integrand c j b (coordinate x t) = scale c j x * kernel c j b x t`.
The signature (:129) carries BOTH `hx : 0 < x` and `ht : 0 ≤ t`. Every denominator in sight is then
nonzero: `denominator x t = sqrt (1 + x² t)` with `denominator_pos` from `ht` (:41-42, used at :133),
`x ^ j`/`x ^ 3` in `integrand`/`scale` (FlatPrimitive.lean:25-26, :33-34) from `hx`, and `edge`'s `-c / x²`
is the guarded branch of `if x ≤ 0` (FlatCutoff.lean:26-27). No degeneration is possible.

## 5. NavierStokes/Flatness.lean:30 `fixed_power_loss_bound` — denom `scale` — **A (guarded in signature)**

FALSE POSITIVE, textbook case: the signature is `(hscale : scale ≠ 0)` (Flatness.lean:31). Claim is the
bound `|x / scale ^ loss| ≤ C * |scale| ^ n`. Denominator explicitly nonzero; the proof uses it at :34.

## 6. NavierStokes/PeriodicPhaseAssembly.lean:28 `intervalCutoff_contDiff` — denom `d` — **D (unguarded, LOW severity)**

CLAIM: `ContDiff ℝ ∞ (intervalCutoff a b d)` — a REGULARITY claim about the explicit cutoff
`smoothTransition ((x - (a - 2d))/d) * smoothTransition (((b + 2d) - x)/d)` (:24-26). `(a b d : ℝ)` all free.

COLLAPSE AT d = 0: both arguments become `_/0 = 0`, `smoothTransition 0 = 0`
(`Real.smoothTransition.zero_of_nonpos`, used in this file at :47), so `intervalCutoff a b 0 = fun _ => 0`
and the conclusion is "the zero function is smooth". Unguarded: no `0 < d` here, in contrast with the
NEIGHBOURING lemmas `intervalCutoff_one`:32 and `intervalCutoff_support`:39, which both take `hd : 0 < d`.

SEVERITY: low. The proof (:29-30, `div_const d`) is uniform in d, so the d = 0 instance is a genuinely
correct trivial statement rather than a false-looking one, and the plateau/support content that a reader
cares about IS guarded (:32, :39). Hygiene only.

## 7. NavierStokes/ZerothStressIdentity.lean:253 `scheme_zero_densities_eq` — denom `C` — **B (certified by type)**

FALSE POSITIVE. Claim: the assembled scheme's zeroth theta- and z-densities agree with the leading
profiles' at `(R, eta)`. `thetaDensity h C f n w = w.1 ^ 3 / C * angularCoefficient …`
(SlowResidualMatching.lean:417-418) does divide by C, and the signature's `{h C : ℝ}` (:253) is bare —
BUT the very next argument is `(s : GlobalSlowProfiles.Scheme S h C)` (:254), and that structure carries
the field `nonzero_scale : C ≠ 0` (GlobalSlowProfiles.lean:732). C = 0 is therefore uninhabitable here:
the type records the guard, exactly like `WeightedClasses.StripData.epsilon_pos`.
(Additional margin: the second conjunct uses `zDensity h`, SlowResidualMatching.lean:421-422, which has no
C at all, so even a hypothetical C = 0 would leave that half of the conjunction with full content.)

## 8. Euler/AnglePrimitiveMap.lean:18 `primitive_map` — denom `P` — **B (nondegenerate by construction)**

FALSE POSITIVE, and of a kind worth naming. Claim: a bounded linear map commutes with the mean-zero
angular primitive, `L (primitive P f θ) = primitive P (L ∘ f) θ`. `(P : ℝ)` is free (:18).
`primitive P f θ = rawPrimitive f θ - P⁻¹ • ∫ s in 0..P, rawPrimitive f s`
(Euler/AngleMeanZeroPrimitive.lean:25-26): the `P⁻¹` sits in a SUBTRACTED CORRECTION term, so at P = 0 both
`P⁻¹ = 0` and `∫ 0..0 = 0`, and `primitive 0 f = rawPrimitive f`. The statement then reads
`L (rawPrimitive f θ) = rawPrimitive (L ∘ f) θ` — the FULL-content commuting identity of :14-16, not `0 = 0`.
No term is lost; the mean-removal is simply switched off. Nothing collapses.

## 9. Euler/AnglePrimitiveSpatialRegularity.lean:32 `primitive_joint_contDiff` — denom `P` — **B (nondegenerate by construction)**

FALSE POSITIVE, same mechanism as #8. Claim: joint smoothness in `(x, θ)` of the mean-zero angular
primitive. Signature (:32) has `(P : ℝ) (hP : 0 ≤ P)`, so P = 0 is allowed — but at P = 0 the `P⁻¹`-weighted
mean term vanishes and `primitive 0 f = rawPrimitive f` (Euler/AngleMeanZeroPrimitive.lean:25-26), so the
conclusion becomes the FULL-content joint smoothness of `rawPrimitive` (:25-26 of this file). Nothing
collapses to a trivial statement.

## 10. Euler/CorrectionStabilityConstants.lean:69 `growthConstant_nonneg` — denom `c` — **C (caller-guarded), severity NIL**

CLAIM: a sign/BOUND statement `0 ≤ growthConstant c Kb Kx Kt V L`, where
`growthConstant = (Kt+2*Kx*V+4*Kx^2/c^2+2*Kb*L+1)/c^2` (:22-23). `(c : ℝ)` free (:69).
At c = 0 both `/c^2` become `/0 = 0`, so the constant IS 0 and the claim is `0 ≤ 0`.
Guarded one layer up: the only consumer is `StabilityBudget.growth_nonneg`
(Euler/CorrectionStabilityBudget.lean:85-91), which instantiates c := `B.c` for
`B : StabilityBudget`, and that structure carries `c_pos : 0 < c`
(Euler/CorrectionStabilityBudget.lean:27-29); the quantitative user
`difference_metric_deriv_bound` (Euler/CorrectionDifferenceMetric.lean:25) has `hc : 0 < c` at :30.
SEVERITY: nil — a nonnegativity bound collapsing to `0 ≤ 0`, exactly the harmless kind.

## 11. Euler/FixedEvolutionSobolev.lean:29 `traceCost_nonneg` — denom `T` — **C (caller-guarded), severity NIL**

CLAIM: `0 ≤ traceCost T` for `traceCost T = T⁻¹*sqrt T + 2*sqrt T` (:27), with only `hT : 0 ≤ T` (:29).
At T = 0 BOTH terms vanish (`0⁻¹ = 0`, `sqrt 0 = 0`), so the claim is `0 ≤ 0`. Every caller supplies a
STRICTLY positive time: Euler/CylinderEndpointBudget.lean:72 (`D.time_pos.le`),
Euler/PacketInitializedRadiusPolynomial.lean:174, :235, :335, :360 (`hτ.le` from `0 < τ`),
Euler/CylinderDirichletPhysicalBounds.lean:86, :112, :118 (`D.time_pos.le`),
Euler/TransversePacketNormalBudget.lean:81, :90, Euler/PacketParentJoinedBudget.lean:80.
SEVERITY: nil — nonnegativity bound; `positivity` proves it uniformly.

## 12. Euler/MeanStrongContinuousGevrey.lean:21 `coordinateTraceCost_nonneg` — denom `T` — **C (caller-guarded), severity NIL**

Identical to #11: `coordinateTraceCost T = T⁻¹*sqrt T + 2*sqrt T` (:19), claim `0 ≤ …` with `hT : 0 ≤ T`
(:21); at T = 0 it is `0 ≤ 0`. Callers pass strict positivity: Euler/PacketInitializedRadiusPolynomial.lean:466
(`M.T_pos.le`), Euler/PacketParentMeanBudget.lean:135 (`D.T_pos.le`), Euler/MeanPressureSobolev.lean:63.
SEVERITY: nil.

## 13. Euler/PacketCorrectionPrimitiveBounds.lean:17 `correction_envelopes` — denom `R`/`c` — **A (guarded in signature) + B**

FALSE POSITIVE twice over. Claim: the constructed correction envelopes are dominated by the polynomial
envelopes (five conjoined `≤`). The signature (:18) already carries `hc : 0 < c` for the `pressureCost c …`
channel (`correctionPressureEnvelope`, Euler/PacketCorrectionCoefficientBudget.lean:63-65), and the target
`pressureEnvelope X = 1 + pressureCost ((1+X)^2)⁻¹ …`
(Euler/PacketCorrectionPrimitivePolynomial.lean:19-21) inverts `(1+X)^2` with `0 ≤ X` derived at :26 —
the `1 + (nonneg)` construction, nondegenerate exactly like `Euler/TransversePacketData`.

## 14. Euler/PacketEarlyPhysical.lean:52 `early_physical_size_suppression` — denom `a` — **B (false positive, shared-evaluation-point kind (i))**

Claim: early physical amplitude products are exponentially small relative to the center target,
`(‖r ξ (physicalTime t₀ a ε τ)‖*‖w ξ …‖)/(‖r center (physicalTime t₀ a ε T)‖*‖w center …‖) ≤ 8232*exp 9*Θ^5*exp (-(1/(4σ)))`.
`physicalTime t₀ a ε τ = t₀ + (ε/a)*τ` (Euler/PacketScaledRay.lean:12), and `{a : ℝ}` is unconstrained (:54).
At a = 0 `physicalTime` becomes the CONSTANT t₀, so every occurrence — in the hypotheses hm/hv/hmv/hrw/hP/hQ/hN/herror
(:59-74) and on both sides of the conclusion (:75-79) — is re-evaluated at the SAME point. No factor is
multiplied by 0: the bound still reads `(‖r ξ t₀‖*‖w ξ t₀‖)/(‖r center t₀‖*‖w center t₀‖) ≤ 8232*exp 9*Θ^5*exp(-(1/(4σ)))`
with the RHS independent of a, so the statement keeps content (indeed the hypotheses hP/hQ (:63-64) then demand a
constant to track `σ²τ²`/`-2σ²τ` within `ρ ≤ 1/2`, which is even harder). The other divisors — `s₀*rayScale ε i`
in `scaledRay` (Euler/PacketScaledRay.lean:35-36) and `velocityScale ε i` in `scaledVelocity`
(Euler/PacketScaledVelocity.lean:18-19) — ARE guarded in the signature by `hs₀ : 0 < s₀`, `hε : 0 < ε` (:55).
This is exactly the parent's exempt kind (i).

## 15. Euler/PacketExactPhysicalEuler.lean:47 `exact_source_euler` — denom `k` — **A (guarded in signature, via `k*κ = 1`)**

## 16. Euler/PacketExactPhysicalMomentum.lean:27 `exact_source_momentum` — denom `k` — **A (same)**

FALSE POSITIVES. Both claim the classical Euler/momentum(+divergence) equations for the parent velocity plus
the constructed packet, with pressure `p + physicalPressure (S.rawGraphPotential k) Y` (PacketExactPhysicalEuler:64-67,
PacketExactPhysicalMomentum:41-42) — genuine EXACT identities, so a collapse here would matter. It cannot
happen: both signatures carry `(k : ℝ) (hk : k*κ = 1)` (PacketExactPhysicalEuler.lean:48,
PacketExactPhysicalMomentum.lean:28). `k*κ = 1` forces `k ≠ 0` AND `κ ≠ 0` — a nonzero-denominator guard
stated as an equation instead of a `≠`. The proof uses it exactly there
(`S.rawGraphPotential_smooth k hk`, `rawGraphPotential_gradient k hk`, PacketExactPhysicalMomentum.lean:59-60;
`rawGraphPotential` is `graphPotential`/`graphPressure k` with the `k⁻¹`-type normalization,
Euler/ExactLiftedGraphPressure.lean:36-37, :60-61, :63). Instrument note: a `k*κ=1`-style guard should be
whitelisted; it is the same information as `k ≠ 0`.

## 17. Euler/PacketForwardInitializedFieldParity.lean:41 `forwardInitializedNormalizedField_odd` — denom `k` — **C (caller-guarded), severity LOW**

CLAIM: a PARITY property — `(forwardInitializedNormalizedField … N k).ReflectionOdd`, i.e. the normalized
initialized packet field is odd under reflection. `(k : ℝ)` free (:41).
`forwardInitializedNormalizedField N k = ((forwardInitializedPacketField … k⁻¹).smul k).changeTime`
(Euler/PacketForwardInitializedCorrectionData.lean:22-23), so at k = 0 the field is `0 • (…)` = the zero
field and the claim degenerates to "the zero field is odd" — content-free but true.
GUARD ONE LAYER UP: the sole consumer `forwardInitializedCorrectionParityData`
(Euler/PacketForwardInitializedCorrectionParity.lean:20-27, use at :37) takes `(k : ℝ) (hk : 4 ≤ k)` (:25);
the sibling lemmas in this same family also carry `hk : 4 ≤ k`
(PacketForwardInitializedFieldParity.lean:64-65, PacketForwardInitializedCorrectionData.lean:26, :55, :62).
SEVERITY: low — a parity property, not an exact value; and the k ≥ 4 users are unaffected.

## 18. Euler/PacketInitializedFieldParity.lean:43 `initializedNormalizedField_odd` — denom `k` — **C (caller-guarded), severity LOW**

Exact twin of #17 for the history-initialized packet. CLAIM: `(initializedNormalizedField … N k).ReflectionOdd`;
`(k : ℝ)` free (:43). `initializedNormalizedField N k = ((initializedPacketField … k⁻¹).smul k).changeTime`
(Euler/PacketInitializedCorrectionData.lean:23-24), so at k = 0 it is the zero field and the parity claim is
vacuous. GUARDED BY THE SOLE CALLER `initializedCorrectionParityData`
(Euler/PacketInitializedCorrectionParity.lean:21-29, use at :39) which requires `(k : ℝ) (hk : 4 ≤ k)` (:27);
the sibling `initializedNormalizedResidualField_odd`:66-67 also carries `hk : 4 ≤ k`.
SEVERITY: low (parity property, not an exact value).

## 19. Euler/PacketKnownTermSums.lean:18 `angleMean_congr_at` — denom `P` — **C (caller-guarded), severity NIL**

CLAIM: a CONGRUENCE — if `f (t,(x,θ)) = g (t,(x,θ))` for all θ then `angleMean P f (t,(x,θ)) = angleMean P g …`.
`angleMean P f z = P⁻¹ • ∫ θ in 0..P, f …` (Euler/PacketProfileRecursion.lean:40-41), so at P = 0 both sides
are `0 • 0 = 0` and the statement is `0 = 0` (both sides collapse independently — formally the
PulseCovariance:74 shape). Mechanism worth noting: the file's section variable is `{P T : ℝ} [Fact (0 < P)]`
(:16), but this theorem re-binds its own explicit `(P : ℝ)` (:18) and thereby SHADOWS the positivity instance.
The caller `PrefixFields.meanForce_decomposition` (:63, use at :71) is inside that section, so it applies the
lemma to the `P` that does carry `[Fact (0 < P)]`.
SEVERITY: nil — it is a congruence lemma (`f = g` in, means equal out); no exact value is advertised.

## 20. Euler/PacketParentNormalBudget.lean:22 `amplitude_nonneg` — denom `C` — **A (instrument artefact: there is no division)**

FALSE POSITIVE. `amplitude C C₁ = 9*C^2 + 27*C^2*C₁` (:15) — a POLYNOMIAL, no inverse and no division at all;
the claim `0 ≤ amplitude C C₁` with `hC₁ : 0 ≤ C₁` (:22) is true for every C by `positivity`. The instrument
must have matched the `1/(…)`-free `inverseRadius`/`gramCost` names or a downstream `C`-inverse; nothing in
this theorem's statement can degenerate.

## 21. Euler/StaticEulerCorrection.lean:37 `amplitude_pos` — denom `C` — **B (certified by type; and a STRICT-positivity claim cannot silently degenerate)**

FALSE POSITIVE, twice over. Claim: `0 < amplitude P C R hC hR` where
`amplitude P C R hC hR = (scales P C R hC hR).value` (:35) and the proof is the structure FIELD
`Scale.positive : 0 < value` (Euler/SmallCorrectionScales.lean:38-40, used at :38).
(a) The guard is in the type: `scales` (:29-33) is built by `scale` which demands `0 ≤ C`, `0 ≤ R`,
`0 < residualCost …` (Euler/SmallCorrectionScales.lean:47) and whose inverses are all of the
`1/(… + 1)` form (:48-52) — the "+1" nondegeneracy construction.
(b) Structurally, a `0 < x` conclusion is IMMUNE to junk-value degeneration: if the channel collapsed to 0 the
theorem would be FALSE, not content-free. Same remark applies to `amplitude_le_one`:40.

## 22. Euler/PacketParentTransverseCosts.lean:120 `inverseRadius_bound` — denom `c` — **B (nondegenerate by construction: `1 + c⁻¹*(…)`)**

FALSE POSITIVE. Claim: the bound `2*EulerTimeLpGramGevrey.gramCost c C 1*(R+1) ≤ inverseRadius R C`, with
`(c : ℝ)` free and only the REVERSE guard `hi : c⁻¹ ≤ gramInverseEnvelope C` (:121) — which is satisfied, not
violated, at c = 0. But nothing collapses: `gramCost c C D = 1 + c⁻¹*(3*C^2+D+1)`
(Euler/TimeLpGramGevrey.lean:23), so at c = 0 the LHS is `2*1*(R+1) = 2*(R+1)`, NOT 0, and the RHS
`inverseRadius R C = 2*(1+gramInverseEnvelope C*(3*C^2+2))*(R+1)` (Euler/PacketParentTransverseCosts.lean:30-31)
with `gramInverseEnvelope C = (3*C^2+1)^2 ≥ 0` (Euler/PacketParentMeanCoercivity.lean:21) still dominates it.
The `1 +` is the same nondegeneracy device as `Euler/TransversePacketData`'s `1 + ‖F.field‖`.

## 23. Euler/PacketScalarPressureGrade.lean:197 `Budget.angular_grade_bound` — denom `C` — **A/B (guarded; the C-inverse does not exist)**

FALSE POSITIVE. Claim: a Gevrey-type norm BOUND — `((angularField …).normalized … (α • L.fullProfile) …).WordBound 6 L.R 1 (highShift 1)`.
Two reasons it cannot degenerate:
(a) There is no `C⁻¹` anywhere in the file (`grep -n 'C⁻¹\|/C'` on Euler/PacketScalarPressureGrade.lean: no
match); `C` is an AMPLITUDE constant occurring only multiplicatively in `hYb`'s `(α*C)*majorant …` (:202-203),
and `W : Budget.GradeGuards … C` supplies `terminal_nonneg : 0 ≤ C`
(Euler/PacketPrimaryGradeBounds.lean:30, used at :183-184).
(b) The only real division is the profile normalization `normalize g hg f t = (g t)⁻¹ • f t`
(Euler/ContinuousTimeWeight.lean:30-38), and it is impossible to even WRITE it without the pointwise
positivity proof `hg : ∀ t, 0 < g t` — supplied here as
`smul_profile_pos L.fullProfile L.fullProfile_pos α hα` with `hα : 0 < α` in the signature (:201, :204-205).
This is the strongest form of guard: the divisor's nonvanishing is an argument of the DEFINITION.

## 24. Euler/PacketTangentInvariant.lean:24 `rescaled_tangentPairing_zero` — denom `a` — **B (false positive, shared-evaluation-point kind (i))**

Claim: the exact identity `∀ τ ∈ Icc 0 T, ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0`
(tangency propagates), with `{a : ℝ}` free (:25). `physicalTime t₀ a ε τ = t₀ + (ε/a)*τ`
(Euler/PacketScaledRay.lean:12): at a = 0 the path degenerates to the constant t₀ and the conclusion becomes
`⟪r t₀, w t₀⟫_ℝ = 0` — which is precisely the HYPOTHESIS `h0` at :31, not `0 = 0`. Both the hypotheses
(hmap, hr0 at :26, :30) and the conclusion are re-evaluated at the same point; no factor is annihilated.
The other divisor, `‖r t‖^2` in the velocity ODE (:15, :29), is guarded by `hr0` (:16, :30) and used as
`pow_ne_zero 2 …` at :20. Exempt kind (i).

### Addendum to #2 (ClosedNativeWaveIdentities:279)

Contrast INSIDE the same file confirms the omission is deliberate-and-harmless rather than load-bearing: the
substantive curl-realization identities `native_realizes_curl_at`:645-651 and `native_divergence_zero_at`:657-664
DO take `hK : a.background.frequency n ≠ 0` (:647, :660). Only the two smoothness/invariance wrappers
(:279 here, CopyAngularInvariance:327) drop it. So the K = 0 degeneration never reaches an exact identity.

## 25. Euler/PacketTargetAmplification.lean:41 `physical_target_exponential_lower` — denom `a` — **B (false positive, shared-evaluation-point kind (i))**

CLAIM: `0 < ‖r (physicalTime t₀ a ε T)‖*‖w …‖ ∧ s₀*exp (1/(4σ)) ≤ 4*Θ*(‖r …‖*‖w …‖)` — a strict positivity
plus an exponential lower bound. `{a : ℝ}` free (:42), appearing ONLY inside
`physicalTime t₀ a ε T = t₀ + (ε/a)*T` (Euler/PacketScaledRay.lean:12).
At a = 0 every occurrence — hm, hv, hmv, hN, hV (:45-48) and both conclusion conjuncts (:53-54) — is
re-evaluated at the constant time t₀; the RHS `s₀*exp (1/(4σ))` and `4*Θ` do not involve a, so the bound keeps
full content. Note also the first conjunct is a STRICT positivity, which cannot silently degenerate (it would
become false, not vacuous). The genuine divisors are guarded in the signature: `hs₀ : 0 < s₀`, `hε : ε ≠ 0`
(:43) for `scaledRay`/`scaledVelocity` (Euler/PacketScaledRay.lean:35-36, Euler/PacketScaledVelocity.lean:18-19),
and `Z T > 0` is derived at :57 before the `…/Z T` in hV is used (:58-62). Exempt kind (i).

---

# SUMMARY (25 hits)

**A = 7** (guarded in signature): FlatPrimitiveFactor:128, Flatness:30, PacketCorrectionPrimitiveBounds:17,
PacketExactPhysicalEuler:47, PacketExactPhysicalMomentum:27, PacketParentNormalBudget:22 (no division exists),
PacketScalarPressureGrade:197.
**B = 8** (certified by type / by construction / shared-eval-point kind (i)): ZerothStressIdentity:253
(`Scheme.nonzero_scale`), AnglePrimitiveMap:18, AnglePrimitiveSpatialRegularity:32 (`P⁻¹` only in a subtracted
mean; `primitive 0 = rawPrimitive`), PacketEarlyPhysical:52, PacketTangentInvariant:24,
PacketTargetAmplification:41 (all three kind (i) `physicalTime`), PacketParentTransverseCosts:120
(`1 + c⁻¹*(…)`), StaticEulerCorrection:37 (`Scale.positive`; strict-positivity conclusions cannot degenerate).
**C = 7** (caller-guarded only): BasePrefixIdentity:111 (**material** — exact identity, guard ~5 layers away),
CorrectionStabilityConstants:69, FixedEvolutionSobolev:29, MeanStrongContinuousGevrey:21 (all three `0 ≤ …`
bounds, severity nil), PacketForwardInitializedFieldParity:41, PacketInitializedFieldParity:43 (parity of a
field that becomes 0), PacketKnownTermSums:18 (congruence; `(P : ℝ)` shadows `[Fact (0 < P)]`).
**D = 3** (genuinely unguarded, ALL low-severity property claims, none an exact value):
ClosedNativeWaveIdentities:279 (`ContDiffAt ∞ (fun _ => 0)`), CopyAngularInvariance:327
(`Invariant θ (fun _ => 0)`), PeriodicPhaseAssembly:28 (`ContDiff ∞ (fun _ => 0)`).

RULE OF THUMB CONFIRMED BY THIS TRANCHE (offered for the instrument):
1. `hk : k*κ = 1` is a nonzero-guard — whitelist equation-shaped guards.
2. `1 + c⁻¹*(…)` and `1/(… + 1)` never collapse (the `+1` device); `x⁻¹` inside a SUBTRACTED mean-removal term
   never collapses either (the main term survives).
3. `0 < …` conclusions are immune: degeneration would make them FALSE, so they cannot silently say nothing.
4. `c⁻¹ ≤ envelope`-style hypotheses are REVERSE guards: they are satisfied at c = 0, not violated.
5. Denominator inside a shared evaluation point (`physicalTime t₀ a ε τ`) = exempt kind (i).

