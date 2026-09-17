# Junk-value degeneration audit (worker sub-junkvalue-2), NSE @ f9e8bc5, READ-ONLY


## 1. NavierStokes/PhaseCalculus.lean -- 10 hits, ALL FALSE POSITIVES (B)

`phase` (:44-46): `phase ε p pz x0 F G q = p*θ + (pz/ε)*Z + x0*R - v*(p*F+pz*G)`.
Key structural fact: `pz/ε` enters ONLY as a *constant coefficient* of the `Z` slot. It is
never a hypothesis-bearing denominator: for any ε (incl. 0) `pz/ε` is just some real `c`, and
every theorem below is the corresponding statement for the phase with axial coefficient `c`.
So at ε=0 the theorems remain TRUE and NON-VACUOUS (they become the statements for the
Z-independent phase). Nothing collapses to `0 = 0`.

Evidence the author guards where a guard is actually needed (i.e. the tool's ε-detector is
firing on the wrong theorems): `hε : ε ≠ 0` IS present at :110 (`phaseNormal_formula`),
:149 (`signedMaterialOp_phase`), :167 (`backwardMaterialOp_phase`), :251
(`hasDerivAt_phaseNormal_slot`) -- exactly the places where `field_simp [hε]` is used
(:120, :161).

Per-hit:
- :49 `fderiv_phase_apply` -- CLAIMS: full Frechet differential of the phase. `(pz/ε)*w.1.2.1`
  appears on the RHS as literally the same subterm as in the def, so ε occurs on BOTH sides
  (one-side rule: symmetric -> harmless). At ε=0 it is the correct differential of the
  Z-independent phase. **B.**
- :70 `phase_dR` -- CLAIMS: `∂R Φ = x0 - v*(p F_R + pz G_R)`. ε-free RHS, and the R-derivative
  does not see the Z coefficient at all; true and nontrivial for every ε. **B.**
- :76 `phase_dTheta` -- CLAIMS: `∂θ Φ = p` (exact). ε-free, true for all ε. **B.**
- :83 `phase_dZ` -- CLAIMS: `∂Z Φ = pz/ε - v*(p G_Z ...)` (exact). ε appears on BOTH sides in the
  identical subterm `pz/ε`; at ε=0 both sides become `-v*(...)`, still an exact nontrivial
  derivative identity. FP kind (i) (shared subterm, not shared eval point). **B.**
- :89 `phase_dT`, :95 `phase_dV` -- CLAIMS: exact `∂T Φ`, `∂v Φ`. ε-free statements, true for
  all ε. **B.**
- :123 `contDiff_phase` -- CLAIMS: joint `C^n` smoothness. Not an identity; holds for all ε
  (proof :126-132 uses no ε fact). **B.**
- :180 `phase_angularShift` -- CLAIMS: `Φ(θ+h) = Φ(θ) + p*h` (exact). ε appears symmetrically
  (same `pz/ε` term on both sides); true for all ε. **B.**

VERDICT: file is entirely B. The detector should not treat a `/ε` that is a *coefficient
constant appearing identically on both sides* as a channel.


## 2. NavierStokes/SquaredPartition.lean -- 5 hits, ALL FALSE POSITIVES (B)

`gridMask δ k x = lineMask k (x / δ)` (:174). So δ enters ONLY as a **shared evaluation
point**: at δ=0 the mask becomes the constant function `x ↦ lineMask k 0`. This is exactly the
previous triage's FP kind (i). And `lineMask` itself is nondegenerate BY CONSTRUCTION: its
denominator is `Real.sqrt (denominatorSquared x)` with `denominatorSquared_pos` proved for
EVERY x (used at :120-121, :130, :144, :147), so no inner junk value ever appears.

Author does guard where δ=0 would break truth: `hδ : 0 < δ` at :185 `gridMask_support`,
:194 `gridMask_tsupport`, :198 `gridMask_compactSupport`, :248, :260, :330, :352. The 5 hits
are precisely the statements that stay TRUE at δ=0.

- :179 `gridMask_smooth` -- CLAIMS: `ContDiff ℝ ∞ (gridMask δ k)`. At δ=0 it is the constant
  function, still smooth. True, and the δ≠0 content is untouched. A smoothness claim, not an
  exact value, so a trivial instance costs nothing. **B.**
- :182 `gridMask_sum_sq` -- CLAIMS: exact partition identity `∑ᶠ k, gridMask δ k x ^ 2 = 1`.
  Proof (:183) is `lineMask_sum_sq (x / δ)`, and `lineMask_sum_sq` (:143) holds at EVERY real
  point, including 0. So at δ=0 the identity is `∑ᶠ k, lineMask k 0 ^ 2 = 1` -- exactly true,
  not a `0 = 0`. Shared evaluation point. **B.**
- :203 `gridMask_locallyFinite` -- CLAIMS: local finiteness of the support family. At δ=0 the
  family is `{ℝ for k = 0, ∅ otherwise}` (since `support (lineMask 0) = Ioo (-1) 1 ∋ 0`,
  :123-124), which is locally finite. True; proof (:205-208) uses no δ fact. **B.**
- :235 `productMask_support` -- CLAIMS: support of the product = intersection of coordinate
  preimages. δ occurs on BOTH sides inside `gridMask δ ...` (ONE-SIDE rule kills it), and the
  proof (:237-238) is pure `Finset.prod_ne_zero_iff`, valid for any δ. **B.**
- :343 `productMask_eq_rescale` -- CLAIMS: exact rescaling identity
  `productMask δ k x = productMask 1 0 (δ⁻¹ • x - k)`. This is the one hit where δ is truly
  one-sided (`δ` left, `δ⁻¹` right), i.e. the shape worth checking. Checked: at δ=0,
  LHS_j = `lineMask (k j) 0` and RHS_j = `lineMask 0 (-(k j))`, and these are EQUAL by the
  unconditional translate identity `lineMask_eq_translate` (:170, itself resting on
  `denominatorSquared_sub_int` :165, the 1-periodicity of the denominator). So the identity is
  genuinely true at δ=0, not a junk coincidence; the proof (:345-349) uses no `hδ`, confirming
  it is unconditional. **B.**

VERDICT: file is entirely B.


## 3. Euler/PhysicalL2Scaling.lean -- 3 hits (2 distinct theorems): 1 B, 1 C

`scale ell f = fun x => ell • f (ell⁻¹ • x)` (:48). At ell=0 BOTH the prefactor and the
evaluation point die (`(0:ℝ)⁻¹ = 0`), so `scale 0 f = 0` (the zero function) identically.

- :50 `scale_contDiff` -- CLAIMS: `ContDiff ℝ ∞ (scale ell f)`. At ell=0 this is "the zero
  function is smooth": true, trivially. Regularity claim, no exact value at stake; the ell≠0
  content is intact and the proof (:52) needs no `hell`. **B (harmless).**
- :54 `iteratedFDeriv_scale` -- CLAIMS: the EXACT jet formula
  `iteratedFDeriv ℝ n (scale ell f) x = (ell*(ell⁻¹)^n) • iteratedFDeriv ℝ n f (ell⁻¹ • x)`.
  At ell=0: LHS = jets of the zero function = 0; RHS prefactor `ell*(ell⁻¹)^n = 0*0^n = 0`
  (also 0 at n=0, where `(ell⁻¹)^0 = 1` and the surviving factor is `ell = 0`), so RHS = 0.
  The statement becomes `0 = 0` -- CONTENT-FREE at ell = 0, and it is an exact identity, the
  shape that matters. `ell` is one-sided in the tool's sense but degenerates on both sides.
  NOT guarded in its own signature (:54-55 has only `hf`, `n`, `x`).
  GUARDED BY CALLERS: every consumer carries `hell : 0 < ell` --
    * :64-66 `scale_jet_memLp (ell) (hell : 0 < ell) ...`, applies it at :69;
    * :73-76 `lpNorm_scale_jet (ell) (hell : 0 < ell) ...`, applies it at :79;
    * :86-90 `lpNorm_scale_jet_le (hell) (hell1 : ell ≤ 1) ...`, via :91.
  **C.** Benign in this file, but the lemma alone advertises an exact dilation jet law that
  says nothing at ell = 0.

(The two "hits" at :54 -- `ell` and `ell via scale` -- are one theorem.)


## 4. NavierStokes/ActivationCone.lean -- 3 hits (all one theorem, :363): FALSE POSITIVE (B)

`projectionError` (:335-336), `crossError` (:338-339), `sizeError` (:341-342) contain `B / A`
and `B ^ 2 / A`.

- :363 `cone_error_bounds` -- CLAIMS: three uniform BOUNDS
  `|projectionError| , |crossError| , |sizeError| ≤ comparisonConstant M`. The signature does
  not say `A ≠ 0`, but it does not need to: the hypotheses bound the quotients THEMSELVES,
  `hBA : |B / A| ≤ M` (:365) and `hB2A : |B ^ 2 / A| ≤ M` (:365). The theorem is a statement
  about whatever real number `B / A` is, junk value included. At A = 0 the conclusion does NOT
  collapse -- e.g. `projectionError = dA + 0 + 0 = dA` and the claim `|dA| ≤ M + 2M^2 + M^3`
  is still real content; the proof (:376-394) uses only `hBA`/`hB2A`/`gcongr`, never `A ≠ 0`.
  Moreover it is a bound, not an exact value, so a degenerate instance costs nothing.
  **B (three hits, one theorem).**

Author guards where an IDENTITY needs it: `hA : A ≠ 0` at :346 `cone_error_factorizations`
(used by `field_simp [hA]` :355, :357) and at :410 `cone_comparison_from_stock_bounds`.


## 5. Euler/AngleMeanZeroPrimitive.lean -- 3 hits, ALL FALSE POSITIVES (B)

`primitive P f θ = rawPrimitive f θ - P⁻¹ • (∫ s in 0..P, rawPrimitive f s)` (:25-26).
At P = 0 BOTH factors of the subtracted constant vanish honestly (`(0:ℝ)⁻¹ = 0`, and
`∫ s in 0..0 = 0`), so `primitive 0 f = rawPrimitive f`. The mean-removal term is a pure
CONSTANT, so it cannot damage any of the three hit statements.

- :40 `primitive_hasDerivAt` -- CLAIMS: `HasDerivAt (primitive P f) (f θ) θ`. Proof (:42) is
  `(rawPrimitive_hasDerivAt ...).sub_const _`, valid for every P. At P=0 it is the (true,
  non-vacuous) derivative statement for `rawPrimitive`. **B.**
- :45 `primitive_continuous` -- CLAIMS: continuity. Same argument (:47, `.sub continuous_const`).
  **B.**
- :61 `primitive_periodic` -- CLAIMS: `Function.Periodic (primitive P f) P`. At P=0 the claim IS
  trivial, but only because `Periodic g 0` is trivially true for any g -- and the hypotheses
  `hper : Periodic f 0` and `hmean : ∫ θ in 0..0, f θ = 0` are then trivial too. The degeneracy
  is in the period-0 statement schema, not in the `P⁻¹` channel; no exact value is lost and
  nothing is silently false. **B (harmless, not a junk-value channel).**

Author guards exactly the exact-value theorems: `hP : P ≠ 0` at :68 `primitive_mean_zero`
(needs `mul_inv_cancel₀ hP`, :73) and :76 `primitive_unique` (:97).


## 6. Euler/PacketScaledVelocity.lean -- 3 hits, ALL FALSE POSITIVES (B), FP kind (i)

`physicalTime t₀ a ε τ = t₀ + (ε/a)*τ` (Euler/PacketScaledRay.lean:12). This is exactly the
previous triage's FP kind (i): `a` sits ONLY inside a SHARED EVALUATION POINT. In each hit the
same term `physicalTime t₀ a ε τ` occurs on both sides (on the left inside
`scaledRay`/`scaledVelocity`, whose defs -- PacketScaledRay.lean:36 and this file :18-19 --
evaluate the moving fields at that same time), so a = 0 simply re-evaluates both sides at
`t₀`. The identities stay exactly true and non-vacuous. The genuine denominators ARE guarded:
`hs₀ : s₀ ≠ 0`, `hε : ε ≠ 0` in every signature (:22, :28, :41), and `ha : a ≠ 0` appears
where `a` really is a divisor (:50 `movingFlux_scaling`, :92 `scaledVelocity_hasDerivWithinAt`).

- :21 `scaledRay_restore` -- CLAIMS: exact restoration `s₀*rayScale ε i*scaledRay ... =
  movingRay ... (physicalTime ...)`. It is `s₀*rs*(X/(s₀*rs)) = X` with X evaluated at the
  shared time; `a`-independent. **B.**
- :27 `scaledVelocity_restore` -- CLAIMS: the same exact restoration for the velocity row. **B.**
- :40 `movingDenominator_scaling` -- CLAIMS: exact scaling law
  `movingDenominator ... (physicalTime ...) = s₀^2 * rayDenominator ε (scaledRay ...)`.
  Again `a` only in the shared time argument on both sides (:42-44). **B.**


## 7. Euler/ParentChoiceInitialSupport.lean -- 3 hits, ALL FALSE POSITIVES (B)

`k` enters via `forwardInitializedInitialHigh/Mean` (Euler/PacketForwardInitialSupport.lean
:22-24, :26-28) as the frequency argument `k⁻¹` plus the fast coordinate `k*inner ℝ D.m₀ x`.

- :20 `forwardInitializedInitialMean_support` and :28
  `forwardInitializedInitial_common_support` -- CLAIM: SUPPORT LOCALIZATION,
  `tsupport (...) ⊆ Metric.closedBall 0 2`. Two reasons these are false positives:
  1. The `k⁻¹` is only a frequency PARAMETER handed to `EulerPacketInitial.mean/high`; the
     supporting lemmas `mean_scaled_support` (Euler/PacketInitialSupport.lean:63-68) and
     `high_scaled_support` (:48-53) are proved for ARBITRARY `κ k : ℝ` with no nonzero
     hypothesis -- their only positivity is `hell : 0 < ell`, supplied here by the structure
     field `M.ℓ_pos` (used at :22, :37), i.e. CERTIFIED BY TYPE, exactly like `StripData`.
  2. The conclusion is an inclusion in a k-free ball, so at k=0 it is still a genuine
     localization claim about the k=0 field, not `0 = 0`. Nothing exact degenerates.
  **B (3 hits, 2 theorems).**


## 8. Euler/TransverseHistoryLipschitz.lean -- 3 hits, ALL FALSE POSITIVES (B)

`historyDifferenceCost` (Euler/TransverseHistoryBounds.lean:105-108) contains `c⁻¹` through
`traceCost T (2*c⁻¹*q*q₁)` and `generatorDifferenceCost c q q₁ ...`
(Euler/TransverseGeneratorDifference.lean:67-68). `c⁻¹` is a POLYNOMIAL ATOM here: every
statement in this file is an algebraic (in)equality in which `historyDifferenceCost` occurs
with the SAME `c` on both sides.

- :15 `historyDifferenceCost_linear` -- CLAIMS: exact linearity in the three difference slots,
  `HDC(x,y,z) = HDC(1,0,0)*x + HDC(0,1,0)*y + HDC(0,0,1)*z`. `c` occurs in all four terms
  (both sides): symmetric, so the ONE-SIDE rule already discards it. Proof (:20-22) is
  `unfold ...; ring`, i.e. valid for ANY real value of the atom `c⁻¹`, so at c=0 the identity
  is still the same nontrivial linear-decomposition identity, not `0 = 0`. **B.**
- :24 `historyDifferenceCost_nonneg` -- CLAIMS: `0 ≤ historyDifferenceCost ...`. Signature has
  `hc : 0 ≤ c` (:25); `positivity` (:31) needs only `0 ≤ c⁻¹`, which holds at c=0 too. A
  nonnegativity claim about a still-nonzero expression. **B.**
- :33 `historyDifferenceCost_le_scale` -- CLAIMS: the scaling BOUND
  `HDC(x,y,z) ≤ HDC(L₀,L₁,LH)*s`. Same `c` on both sides; a bound, not an exact value. **B.**

Extra note for the tool: `traceCost T b = (1+T)*(T⁻¹+2*b)`
(Euler/TimeH1GeneratorBounds.lean:29) and `affineCost T = (1+T)*|T⁻¹|`
(Euler/TransverseEndpointBounds.lean:150) put an UNGUARDED `T⁻¹` in the same three statements
(only `hT : 0 ≤ T`), and it is harmless for exactly the same symmetric reason. The real
consumer :71 `historyVelocity_sub_norm_le_of_coefficient_bounds` anyway carries `hc : 0 < c`
(variable block :57) and `hTpos : 0 < T` (:71).


## 9. NavierStokes/HeatProfileExtension.lean -- 2 hits (one theorem, :206): C

`scaledProfile a X ν = extension a (2 * ν / X)` (:191). At X = 0 this is the CONSTANT function
`ν ↦ extension a 0`.

- :206 `iteratedDeriv_scaledProfile {a} (ha : 1 < a) (n : ℕ) (X ν : ℝ)` -- CLAIMS: the EXACT
  derivative-scaling law
  `iteratedDeriv n (scaledProfile a X) ν = (2 / X) ^ n * iteratedDeriv n (extension a) (2*ν/X)`.
  At X = 0: LHS = jets of a constant = 0 for every n ≥ 1; RHS = `(2/0)^n * ... = 0^n * ... = 0`.
  So for all n ≥ 1 the statement is exactly `0 = 0` -- CONTENT-FREE, and it is an exact
  identity (the n = 0 case survives honestly: `0^0 = 1` and both sides are `extension a 0`).
  Note the sibling statements in the same file DO carry the guard: :193
  `scaledProfile_contDiffOn` restricts to `Ioi 0 ×ˢ univ`, :200 `scaledProfile_eq_profile`
  (`hX : 0 < X`), :219 `scaledProfile_derivative_bound` (`hX : 0 < X`), :229
  `scaledProfile_sub_one_bound` (`hX : 0 < X`). So the missing `0 < X` at :206 is an outlier.
  CALLERS that exclude X = 0:
    * NavierStokes/HeatProfileExtension.lean:219-222 `scaledProfile_derivative_bound`, `hX : 0 < X`;
    * NavierStokes/ExtendedHeatDebts.lean:135 inside `correctionJet_succ` -- this caller is
      itself UNGUARDED (:123 `{h} (hh : 0 < h) (K X ν : ℝ) (n : ℕ)`), and its own conclusion
      `correctionJet h K (n+1) ν X = switch K X * (2/X)^(n+1) * iteratedDeriv (n+1) ...`
      likewise collapses to `0 = 0` at X = 0 (LHS: jets in ν of a ν-constant; RHS: `0^(n+1)`).
      That propagated instance is finally guarded one layer further up, by
      ExtendedHeatDebts.lean:149-150 `correctionJet_continuousOn_X` (domain `Ioi 0`) and
      :167 `correctionJet_bound` (`hX : 1 ≤ X`).
  **C.** Benign in the current call graph, but two exact jet identities (:206 here and
  ExtendedHeatDebts:123) advertise scaling laws that say nothing at X = 0.


## 10. NavierStokes/R3/ParabolicSupport.lean -- 2 hits (one theorem, :18): FALSE POSITIVE (B)

- :18 `isCompact_affineSpacetime_image {K} (hK : IsCompact K) (b c d : ℝ)` -- CLAIMS: the image
  of a compact set under `z ↦ ((z.1 - d)/c, b⁻¹ • z.2)` is compact. `b`, `c` unguarded, but the
  claim is "continuous image of a compact set is compact", and the map is continuous for EVERY
  b, c (proof :21-22 uses `.div_const c` and `.const_smul b⁻¹`, no nonzero facts). At b = 0 or
  c = 0 the map merely becomes degenerate/constant in that coordinate and its image is still
  compact -- the statement is true and not vacuous (a nonempty compact image, not `0 = 0`).
  No exact value at stake. **B (2 hits, 1 theorem).**
  For the record, the consumer `CompactPositiveTimeSupport.affineScale` (:26-28) does carry
  `hb : b ≠ 0` and `hc : 0 < c`, which it needs at :43 (`field_simp`) and :45.


## 11. NavierStokes/R3/RadialKernelBounds.lean -- 2 hits: 1 A, 1 B

- :78 `levelset_measure_le_ball {f} {q t} (hq : q < 0) (ht : 0 < t) (hf : ∀ z, f z ≤ ‖z‖ ^ q)`
  -- the flagged denominator is `q` in `t ^ q⁻¹` (:80). The signature contains `hq : q < 0`
  (:79), which already forces `q ≠ 0`; the proof even uses `hq.ne` at :87 and
  `Real.le_rpow_inv_iff_of_neg ... hq` at :90. **A -- GUARDED IN SIGNATURE, false positive.**
  (Tool fix: treat `q < 0`, `0 < q`, `q ≠ 0`, and `0 < q`-style order hypotheses on the
  denominator variable as guards.)
- :33 `radialCommutatorKernel_measurable (R : ℝ)` -- CLAIMS: `Measurable
  (radialCommutatorKernel R)`, where `radialCommutatorKernel R z = ‖z‖^(-3) * min (‖z‖/R) 1`
  (:25-26). At R = 0 the kernel is identically 0 (`min 0 1 = 0`) and the claim becomes "the
  zero function is measurable" -- true, trivial, no exact value lost; `fun_prop` (:36) proves it
  for every R. **B.**


## 12. NavierStokes/R3/SpatialSupportScaling.lean -- 2 hits, FALSE POSITIVES (B)

- :18 `isCompact_spatialScale_image` and :36 `isCompact_spacetimeSpatialScale_image` -- CLAIM:
  the image of a compact set under `x ↦ b⁻¹ • x` (resp. `z ↦ (z.1, b⁻¹ • z.2)`) is compact.
  Same shape as ParabolicSupport:18: continuous image of a compact set, continuity holding for
  every b (:20, :39). At b = 0 the map collapses the fibre to 0 and the image is still compact;
  a compactness claim, no exact value. **B (2 hits, 2 theorems).**
  Consumers that do need it carry `hb : b ≠ 0`: :26 `tsupport_spatialScale_subset` (used at :33)
  and :44 `CompactPositiveTimeSupport.spatialScale` (used at :54).

---

## SUMMARY (41 hits)

**A = 1, B = 36, C = 4, D = 0.**

* A (guarded in signature): RadialKernelBounds.lean:78 (`hq : q < 0`).
* C (guarded by callers only) -- 4 hits, 2 theorems, both EXACT jet-scaling identities:
  1. Euler/PhysicalL2Scaling.lean:54 `iteratedFDeriv_scale`; at ell = 0 it is `0 = 0`.
     Callers with `0 < ell`: :64, :73, :86.
  2. NavierStokes/HeatProfileExtension.lean:206 `iteratedDeriv_scaledProfile`; at X = 0 it is
     `0 = 0` for every n ≥ 1. Callers: HeatProfileExtension:219 (`0 < X`) and
     ExtendedHeatDebts:123 `correctionJet_succ`, which is ITSELF unguarded (same `0 = 0`
     collapse) and only guarded a further layer up (ExtendedHeatDebts:149-150 domain `Ioi 0`,
     :167 `1 ≤ X`).
* D: NONE in this batch.

**ONE-SIDE RULE: held up, 41/41, and can be sharpened.** Every FP had the denominator either
(a) symmetric on both sides (PhaseCalculus:83 `pz/ε`, SquaredPartition:235, all of
TransverseHistoryLipschitz), (b) inside a SHARED EVALUATION POINT -- kind (i) --
(SquaredPartition `x/δ`, PacketScaledVelocity `physicalTime t₀ a ε τ`), (c) reaching only a
statement whose content is REGULARITY / MEASURABILITY / COMPACTNESS / SUPPORT / a BOUND
(ParabolicSupport:18, SpatialSupportScaling:18+36, RadialKernelBounds:33, ActivationCone:363,
ParentChoiceInitialSupport, `*_contDiff` lemmas), or (d) confined to an additive CONSTANT
(AngleMeanZeroPrimitive `P⁻¹ • ∫`).
Sharpening: the ONLY two non-FPs share one narrow shape -- the one-sided occurrence is a
MULTIPLICATIVE PREFACTOR of an EXACT identity (`ell*(ell⁻¹)^n`, `(2/X)^n`) whose vanishing is
matched by an independent LHS vanishing (jets of a function that degenerated to a constant).
That is the PulseCovariance:74 "two junk values conspire" shape. Rule to implement:
flag only when (i) the conclusion is an equality (not ≤ / ⊆ / ContDiff / Measurable), AND
(ii) the denominator occurs on exactly one side, AND (iii) it occurs as a factor of that whole
side (or inside a `^n`), AND (iv) the other side degenerates for an independent reason.

