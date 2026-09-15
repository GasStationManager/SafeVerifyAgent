# NS uniqueness — worker report: the PRESSURE-FLUX BOUND (`hpressure`)

Repo audited (READ-ONLY): `/home/gsm/.openclaw/workspace/repos/NSE`
(clone of `openai/NavierStokesAndEuler` @ `f9e8bc5`). No `lake build` was run: every claim below
is source-level reading of statements and proof terms, re-read from the original files.
All line numbers were re-verified against the files at audit time.
Docstrings are the claimant's prose and are treated as evidence about the author only.

**Bottom line.** I looked for vacuity, name-vs-statement inflation, hidden competitor
regularity, junk-value (`toReal`/Bochner-0) exploitation, assumed-instead-of-derived
integrability, circularity and kernel risk in the flux bridge. **I found no defect of
those kinds in this scope.** The bridge from pressure recovery to `hpressure` is
hypothesis-clean: the competitor's pressure `q` is used only through (i) smoothness on the
slab, (ii) the pointwise PDE, and (iii) pairings against *compactly supported* tests. The
three residual risks I can name are all one level below or beside this scope and are listed
as escalations (harmonic-functional vanishing inside `PressureRecovery`, the heat-kernel
commutator kernel bound, and the Young/Gronwall absorption in `ComparisonRateBound`).

## Scope

Files and declaration counts (counted by `^(private|noncomputable)* (theorem|lemma|def|structure|instance)` at
audit time):

| file | lines | decls | how read |
|---|---|---|---|
| `NavierStokes/R3/PressureFlux.lean` | 600 | 46 (35 thm, 10 def, 1 instance) | **read line-by-line, all 600 lines** |
| `NavierStokes/R3/PressureFluxTest.lean` | 358 | 24 (21 thm, 3 def) | **read line-by-line, all 358 lines** |
| `NavierStokes/R3/PressureFluxIdentity.lean` | 176 | 11 (9 thm, 2 def) | **read line-by-line, all 176 lines** |
| `NavierStokes/R3/ActualPressureFlux.lean` | 60 | 3 thm | **read line-by-line, all 60 lines** |
| `NavierStokes/R3/PressureFunctionals.lean` | 289 | 17 (10 thm, 7 def) | skimmed; only `pressurePairLinear` (:245) and `integrable_l1_riesz_pair` (:63) inspected — the only two entry points used by this chain |
| `NavierStokes/R3/PressureTestBounds.lean` | 281 | 21 (20 thm, 1 def) | **not read** — it is not imported by `PressureFlux.lean`; it enters only transitively via `PressureFunctionals.lean:1`. Nothing in the flux chain I traced calls it directly. |

Supporting declarations read in full (statement + proof) outside the nominal file list, because
the flux bound rests on them: `PressureRecovery.lean:33-44` (`Hypotheses`), `:353-405`
(`time_test_gradient_difference_zero`, `gradient_recovery_complex`), `:407-414`
(`gradient_recovery`); `ComparisonSetup.lean:28-54` (`comparisonLpNorm`, `gradientSq`,
`dissipationRoot`, `cutoffL6`, `tensorDiff`); `ComparisonFourierSetup.lean:15-25`
(`ComplexTest`, `rieszTest`, `pressurePair`); `ComparisonCutoffs.lean:25-38, 104-135, 143-203`
(cutoff family, `derivativeConstant`, `cutoff_fderiv_le`, `cutoff_second_fderiv_le`);
`ProblemStatement.lean:71-83` (`SquareIntegrableAtTime`, `kineticEnergy`, `UniformFiniteEnergy`);
`ComparisonFiniteEnergy.lean:80-99, 175-231`; `LocalizedTensorBounds.lean:170-200`;
`RieszTestOperators.lean:184-239`; `RieszPairing.lean:31-34`;
`HeatKernelCommutator.lean:97-113`; `HeatKernelPairedBound.lean:26-35, 133-151`;
`WholeSpaceComparisonClosure.lean:25-52, 80-157`; `WholeSpaceUniqueness.lean:30-119`.

## Answers to the four asked questions

### 1. The exported theorem and every field of `PressureRecovery.Hypotheses`

`NavierStokesR3.PressureFlux.exists_uniform_actual_pressure_flux_bound`,
`NavierStokes/R3/PressureFlux.lean:576-589`, verbatim statement:

```lean
theorem exists_uniform_actual_pressure_flux_bound {T : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (M₀ U₀ G₀ : ℝ) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : ∀ t ∈ Icc 0 T, MemLp (fun x => (u - v) (t, x)) 2 volume ∧
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀)
    (hU : ∀ t ∈ Icc 0 T, MemLp (fun x => u (t, x)) 3 volume ∧
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀)
    (hG : ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T,
      |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ))
```

`PressureRecovery.Hypotheses` is `structure ... : Prop` at `PressureRecovery.lean:33-44`, ten
fields. Provenance at `WholeSpaceUniqueness.lean:46-47`
(`⟨hT, hu, hv, hp, hq, hdu, hdv, (fun t ht x => by simpa using hNS t ht x), heu, hev⟩`):

| field | file:line | content | where the consumer gets it | competitor-defect? |
|---|---|---|---|---|
| `positive` | :34 | `0 < T` | `hT0` from `by_cases` at `WholeSpaceUniqueness.lean:82` | no |
| `smooth_u` | :35 | `ContDiffOn ℝ ∞ u (slab 0 T)` | CANDIDATE, `CandidateProperties.velocity_smooth` (`WU:86`) | no |
| `smooth_v` | :36 | `ContDiffOn ℝ ∞ v (slab 0 T)` | COMPETITOR smoothness — allowed | no |
| `smooth_p` | :37 | `ContDiffOn ℝ ∞ p (slab 0 T)` | CANDIDATE pressure (`WU:87`) | no |
| `smooth_q` | :38 | `ContDiffOn ℝ ∞ q (slab 0 T)` | COMPETITOR pressure, **smoothness only** — no decay/support/growth | no |
| `div_u` | :39 | `∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0` | CANDIDATE | no |
| `div_v` | :40 | same for `v` | COMPETITOR div-free — allowed | no |
| `equation` | :41-42 | `∀ t ∈ Ioo 0 T, ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x` | pointwise PDE for both (`WU:47`, `simpa` only fixes `ν = 1` notation) | no |
| `energy_u` | :43 | `UniformFiniteEnergy (Icc 0 T) u` | DERIVED from compact support: `CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp` (`WU:45`) | no |
| `energy_v` | :44 | `UniformFiniteEnergy (Icc 0 T) v` | COMPETITOR uniform kinetic-energy bound, i.e. exactly `∃E ≥ 0, ∀t ∈ Icc 0 T, SquareIntegrableAtTime v t ∧ kineticEnergy v t ≤ E` (`ProblemStatement.lean:81-83`) | no |

**Verdict on question 1: clean.** No field is an extra regularity/decay/integrability assumption
on the competitor. In particular there is no field asserting `q` decays, is normalized,
is the Riesz/Leray pressure of `v`, or that `∇v ∈ L²`.

The three *extra* explicit hypotheses of the flux theorem itself (`hM`, `hU`, `hG`) are also not
new competitor assumptions; the consumer derives them:
* `hM` ← `uniformFiniteEnergy_sub` (`ComparisonFiniteEnergy.lean:80`) + `uniformFiniteEnergy_lpNorm_two_bound`
  (`:197`) at `WU:54-56`. Uses only `AEStronglyMeasurable` slices (from smoothness) and the two
  `UniformFiniteEnergy` facts.
* `hU` ← `CompactComparisonBounds.exists_lpNorm_three_bound hu.continuousOn hK hsupp` (`WU:57-58`) —
  this is the **candidate's** `L³` norm, from compact support. The competitor's `L³` is never needed.
* `hG` ← `uniformFiniteEnergy_tensorDiff_lpNorm_one_bound` (`ComparisonFiniteEnergy.lean:214`,
  via `:175 uniformFiniteEnergy_tensorDiff_bound`) at `WU:59`. `tensorDiff u v t i j =
  u_i u_j - v_i v_j` (`ComparisonSetup.lean:53-54`); its `L¹` bound is `Mu + Mv`, i.e. the two
  squared-`L²` energies. Derived, not assumed.

### 2. Is the decay in `R` real, and is `CP` independent of `R` and `t`?

Yes to both, with one important caveat that I state loudly.

*Quantifier order.* `∃ CP, 0 ≤ CP ∧ ∀ R ≥ 1, ∀ t ∈ Ioo 0 T, |...| ≤ CP * (...)`
(`PressureFlux.lean:585-589`). `CP` is produced *before* `R` and `t` are introduced, and is
literally `9 * uniformCoefficient localPairConstant commutatorConstant M₀ U₀ G₀`
(`:560`, from `:546-559`), where `uniformCoefficient` (`:380-382`) is a closed expression in
`M₀ U₀ G₀` and the two global constants `localPairConstant` (`:284`) and `commutatorConstant`
(`:451-453`). Neither constant mentions `R` or `t`:
`localPairConstant = 3 * WeightedSobolev.sobolevConstant * PressureFluxTest.cutoffDerivativeConstant`
(`:279-284`, `PressureFluxTest.lean:323-325`), `commutatorConstant =
(rieszCommutatorConstant * max (2 * derivativeConstant 1) 1) * (8 * derivativeConstant 1)`.
The auxiliary lemma that strips `R` from the constants, `uniform_expression_bound`
(`:391-443`), takes `hR : 0 < R` and keeps `A/R`, `1/R^2`, `R^(-7/4)` symbolic — it never
divides a constant by `R`. **No hidden `R`- or `t`-dependence in `CP`.**

*Where each negative power of `R` comes from* (traced to source, not to prose):
1. `1/R` in `(B^{1/2}+1)·A/R`: `riesz_rTest_bound` (`:289-305`) → `cutoffTest_derivative_bound`
   (`PressureFluxTest.lean:331-356`) → `memLp_and_lpNorm_fderiv_r_two_le` (`:228-267`) with
   `L = derivativeConstant 1 / R` from `ComparisonCutoffs.cutoff_fderiv_le` (`:190-195`).
   That `1/R` is genuine dilation scaling: `cutoff R x = baseCutoff (R⁻¹ • x)` (`:32`) and
   `cutoff_iteratedFDeriv_le` uses `‖dilation R‖ ≤ R⁻¹` (`:160-164`).
2. `1/R²` in `(B^{1/2}+1)·1/R²`: same lemma's second term, `40L² + 8J` with
   `J = derivativeConstant 2 / R²` from `cutoff_second_fderiv_le` (`:197-203`); both are
   bounded by `cutoffDerivativeConstant / R²`. The velocity factor `M/R²` is replaced by
   `M₀·(1/R²)` in `uniform_expression_bound` (`:417-420`).
3. `R^(-7/4)`: product of the heat-kernel commutator's `R^(-3/4)`
   (`HeatKernelCommutator.lean:97-106`, `riesz_commutator_pair_bound`, requiring only
   `|φ x - φ y| ≤ (L/R)‖x-y‖`, supplied by `PressureFlux.cutoff_lipschitz` (`:58-66`, mean value
   theorem) with `L = derivativeConstant 1`) and the `L⁴` test bound's `1/R`
   (`rTest_four_bound` `:307-313` → `cutoffTest_four_bound` `PressureFluxTest.lean:309-320`);
   combined by `rpow_three_fourths_div` (`:445-448`, `R^(-3/4)/R = R^(-7/4)`, proved). **Exact,
   no slack.**

**Caveat (LOUD, and the reason my scope alone cannot certify the closure).** The envelope is
*not* `O(1/R)` on its own, because both envelope arguments depend on `R` and are not assumed
bounded:
`A = dissipationRoot (cutoff R) (u-v) t = sqrt (∫ cutoff R x ^ 8 * gradientSq w x)`
(`ComparisonSetup.lean:47-48`) and
`B = cutoffL6 (cutoff R) (u-v) t = comparisonLpNorm 6 (cutoff R ^ 4 • w)` (`:50-51`)
both increase with `R`, and the competitor is *never* assumed to have finite global dissipation
or finite `L⁶` norm. So `B^{1/2}·A/R` need not tend to `0` by itself. The closure is aware of
this: `WholeSpaceComparisonClosure.lean:90-103` derives `hSob : B ≤ weightedSobolevConstant *
(A + derivativeConstant 1 * M / R)`, which turns the pressure term into
`≈ A^{3/2}/R + A^{3/4} R^{-7/4}`, and hands the absorption to
`ComparisonRateBound.exists_uniform_rate_bound` (`:64`, applied at `:140`). Young then needs
`A^{3/2}/R ≤ ε A² + C_ε R^{-4}` and `A^{3/4}R^{-7/4} ≤ ε A² + C_ε R^{-14/5}`; both are true
exponent-wise, but I did **not** read `ComparisonRateBound` — see Escalation E3. Within my scope
the correct statement is: *the flux bound carries the advertised explicit negative powers of `R`
with an `R`- and `t`-free constant; the decay only becomes `o(1)` after the closure's
Sobolev + Young step.*

*Exponent bookkeeping cross-check (a place where a mismatch would have been fatal, and there is
none):* `weight R = cutoff R ^ 8` and `multiplier R = cutoff R ^ 2` (`ComparisonCutoffs.lean:35,38`);
`r φ w = 8 φ^5 · Dφ[w]` (`PressureFluxTest.lean:23-24`); `multiplier_r_eq_weight_deriv` (`:26-34`)
is the exact algebraic identity `φ² · r = D(φ⁸)[w]` (`8φ⁷ = φ² · 8φ⁵`). `dissipationRoot` uses
`φ^8` exactly as `riesz_rTest_bound` (`PressureFlux.lean:292`) and the closure's
`weightedDissipation (weight R)` (`WholeSpaceComparisonClosure.lean:87-89`); `cutoffL6` uses
`φ^4 • w` exactly as `rTest_four_bound` (`:311`). No power mismatch anywhere in the chain.

### 3. Integrability: derived, or could the bound be vacuous through a Bochner 0?

Derived. Every integral in the chain is paired with an `Integrable`/`MemLp` proof, and the
`LHS` integral of the exported theorem is provably integrable:
* `ActualPressureFlux.actual_pressure_flux_integrable` (`ActualPressureFlux.lean:28-34`) →
  `PressureFluxIdentity.integrable_pressure_flux` (`:41-46`): integrability of
  `x ↦ (p-q)(t,x) · D(weight R)[w]` follows from continuity of `p-q` (slab smoothness) and
  **compact support of the weight** — it needs nothing about `q` at infinity.
* `PressureFlux.actual_flux_integrable_and_le_canonicalNorm` (`:221-232`) returns integrability
  *and* the bound as a conjunction.
* Canonical pairings: `canonical_pair_integrable` (`:129-135`), `RieszPairing.integrable_mul_rieszTest`
  (`RieszPairing.lean:31-34`), `integrable_commutator_pair` (`:238-249`), `integrable_holder_pair`
  (`:78-81`), `localized_pair_bound` (`:316-336`, integrability is conjunct `.1`).
* `pressurePair_decomposition` (`:251-267`) splits the pairing using `integral_sub` with both
  integrability side conditions supplied — no illegal splitting of a divergent integral.
* `A` and `B` are genuine finite reals here, not junk: their integrands are continuous with
  compact support (`cutoff R ^ 8 · gradientSq w`, `cutoff R ^ 4 • w`), for `0 < R`.

Junk-value survey (`ENNReal.toReal ∞ = 0`, Bochner-0, `fderiv = 0` off differentiability):
* `comparisonLpNorm p f = (eLpNorm f p volume).toReal` (`ComparisonSetup.lean:28-29`) is `0` for a
  non-`MemLp` `f`. In this chain every occurrence of `comparisonLpNorm` is on the **right** of a
  `≤`, where a junk `0` would make the claim *stronger*, not vacuous; and each such factor is
  accompanied by the corresponding `MemLp` proof anyway (`memLp_rieszTest_six`,
  `weighted_tensorDiff_bound.1`, `hw2`, `hu3`).
* `fderiv` junk: all `fderiv` uses are on `ContDiff ℝ ∞` functions with explicit
  differentiability arguments (`:56`, `:63`, `PressureFluxTest.lean:145-150`), so no `fderiv = 0`
  loophole.
* `rieszCommutatorConstant` (`HeatKernelPairedBound.lean:30-31`) contains
  `comparisonLpNorm (4/3) (radialCommutatorKernel 1)`, a `toReal`. Finiteness is established
  (`RadialKernelBounds.radialCommutatorKernel_memLp`, used at `HeatKernelPairedBound.lean:95,109,122,143`),
  so the constant is a real bound, not a silently-zeroed one. **Not a finding.**

### 4. Any place where the arbitrary competitor pressure `q` is treated as if it decayed?

**None found in this scope.** `q` enters in exactly three ways:
1. `H.smooth_q` — smoothness on the slab.
2. `H.equation` — the pointwise residual identity, which pins `∇(p-q)` **pointwise** (so `p-q` is
   determined up to a function of `t` only; a `t`-only additive term is annihilated by the flux
   because `D(weight R)[w] = Σ_k ∂_k (weight R · w_k)` for divergence-free `w`, see
   `PressureFluxIdentity.sum_partial_weightedComponent` `:61-74`). This is why the argument does
   **not** need `q` to decay, and it is the structurally right way to do it.
3. `PressureRecovery.gradient_recovery` (`:407-414`), whose test functions are *always* smooth and
   compactly supported (`hψ`, `hcψ`), consumed by
   `PressureFluxIdentity.pressure_flux_eq_of_gradient_identification` (`:114-127`) as hypothesis
   `hgrad`. The bridge is a pure compact integration-by-parts: `weightedComponent χ w k = χ · w_k`
   is compactly supported (`:57-59`), `CompactEnergy.integral_mul_partial` does the by-parts, and
   `div w = 0` collapses the sum. I checked the `hdiv` input is genuinely derived from the two
   `div_u`/`div_v` fields (`ActualPressureFlux.lean:47-53`), not assumed.

The only place where "decay-like" information could still be smuggled in is *below* this scope,
inside `gradient_recovery` itself (the harmonic/Liouville step). Its statement takes only
`H` and a compact test, and the proof (`PressureRecovery.lean:391-405`) goes
`pressure_gradient_pairing_continuousOn` + `canonical_sum_continuousOn` +
`TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests` +
`time_test_gradient_difference_zero` (`:353-405`), all parameterized by `H` alone. So no extra
hypothesis on `q` is *stated* anywhere; whether the harmonic-functional vanishing theorem it
ultimately invokes is mathematically valid is Escalation E1.

## Per-declaration findings

`PressureFlux.lean` (all 35 theorems / 10 defs examined; near-duplicates grouped).

| decl | file:line | what the statement says (my words) | actual proof mechanism | verdict |
|---|---|---|---|---|
| `lpNorm_ofReal` | PressureFlux.lean:27 | `Lᵖ` norm is unchanged by the real→complex cast | `eLpNorm_congr_norm_ae` + `Complex.norm_real` | OK |
| `norm_fderiv_ofReal` | :32 | `‖fderiv(ofReal ∘ f)‖ = ‖fderiv f‖` at a point of differentiability | `ofRealCLM.hasFDerivAt.comp`, then two `opNorm_le_bound` | OK |
| `lpNorm_fderiv_realTest` | :49 | same for the Schwartz-packaged real test | `eLpNorm_congr_norm_ae` with the above, differentiability from `ContDiff ∞` | OK |
| `cutoff_lipschitz` | :58 | `\|χ_R x - χ_R y\| ≤ (C₁/R)‖x-y‖` | `Convex.norm_image_sub_le_of_norm_fderiv_le` on `univ` + `cutoff_fderiv_le` | OK (real MVT, real `1/R`) |
| `holder_six_fifths_six` (instance) | :68 | `1/(6/5) + 1/6 = 1/1` as `HolderTriple` | `ENNReal` arithmetic, `norm_num` | OK |
| `integrable_holder_pair` / `norm_holder_pair_le` | :78 / :83 | `L^{6/5}×L⁶ → L¹` product integrability and Hölder bound | `MemLp.integrable_mul`; `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` + `toReal_mono` with **both `ne_top` side conditions supplied** | OK |
| `fluxFunction` (def) | :107 | `x ↦ fderiv χ x (w x)` | — | OK |
| `fluxFunction_smooth` / `_compact` | :110 / :115 | smooth and compactly supported | `fderiv_right.clm_apply`; support monotonicity | OK |
| `canonicalFlux` (def) | :125 | `Σ_{i,j} pressurePair i j (g i j) (realTest f)` | — | OK |
| `canonical_pair_integrable` | :129 | each canonical integrand is integrable given `g i j ∈ L¹` | `RieszPairing.integrable_mul_rieszTest` (bounded Riesz test × `L¹`) | OK — integrability derived |
| `norm_canonicalFlux_le` | :137 | componentwise bound `C` ⇒ total `≤ 9C` | `norm_sum_le` twice, `Finset.sum_le_sum` | OK |
| `rTest`, `fluxTest` (defs) | :153, :159 | Schwartz packagings of `8χ⁵Dχ[w]` and `D(χ⁸)[w]` | — | OK |
| `fluxTest_eq_multiplier_rTest` | :173 | `fluxTest = cutoff² • rTest` pointwise | `PressureFluxTest.cutoffTest_flux_identity`, exact algebra `8φ⁷ = φ²·8φ⁵` | OK (no inequality slack) |
| `lpNorm_rTest`, `lpNorm_fderiv_rTest` | :179, :184 | norms transfer through the cast | previous cast lemmas | OK |
| `canonicalCutoffFlux` (def) + `_eq_sum` | :191, :198 | canonical flux of the difference slice; `rfl` unfolding | definitional | OK |
| `norm_canonicalCutoffFlux_le` | :204 | componentwise ⇒ `9C` | reuse of `:137` | OK |
| `actual_flux_eq_canonicalCutoffFlux` | :211 | the *physical* flux integral equals `Re` of the canonical flux | `ActualPressureFlux.pressure_flux_eq_canonical` (compact by-parts + `gradient_recovery`) | OK — the load-bearing identity, hypotheses = `H` only |
| `actual_flux_integrable_and_le_canonicalNorm` | :221 | the flux integrand **is integrable** and `\|∫\| ≤ ‖canonical‖` | `actual_pressure_flux_integrable` + `Complex.abs_re_le_norm` | OK — the anti-vacuity witness |
| `commutatorPair` (def) | :235 | `∫ g·(R_{ij}ψ_h - h·R_{ij}ψ)` | — | OK |
| `integrable_commutator_pair` | :238 | that integrand is integrable given `g ∈ L¹`, `h·g ∈ L^{6/5}` | `integrable_mul_rieszTest` + `integrable_holder_pair`, `hq.sub hl` | OK |
| `pressurePair_decomposition` | :251 | `pressurePair(g, ψ_h) = ∫ (h·g)·R_{ij}ψ + commutator` | `integral_sub` **with both integrability proofs**, `integral_congr_ae` | OK — no divergent-integral splitting |
| `norm_pressurePair_le_local_commutator` | :269 | triangle + Hölder on the decomposition | `norm_add_le`, `norm_holder_pair_le` | OK |
| `rieszSobolevConstant`, `localPairConstant` (+ `_nonneg`) | :279-287 | fixed constants, `R`-free, `t`-free | `WeightedSobolev.sobolevConstant` = Mathlib `eLpNormLESNormFDerivOfEqInnerConst` | OK |
| `riesz_rTest_bound` | :289 | `‖R_{ij}(rTest)‖₆ ≤ C·(A/R + ‖w‖₂/R²)` | Mathlib Sobolev via `RieszTestOperators.lpNorm_six_rieszTest_le` (`≤ 3C‖∇ψ‖₂`, itself via `lpNorm_two_fderiv_rieszTest_le`) + `cutoffTest_derivative_bound` | OK |
| `rTest_four_bound` | :307 | `‖rTest‖₄ ≤ (8C₁/R)‖w‖₂^{1/4} B^{3/4}` | `cutoffTest_four_bound` (endpoint interpolation `L²`–`L⁶`) | OK |
| `localized_pair_bound` | :316 | local part is integrable **and** `≤ C(‖w‖₂^{3/2}B^{1/2} + 2‖w‖₂‖u‖₃)(A/R + ‖w‖₂/R²)` | `LocalizedTensorBounds.weighted_tensorDiff_bound` (Hölder `L^{6/5}`, exact interpolation, see note below) × `riesz_rTest_bound` | OK |
| `norm_cutoff_pressurePair_le_local_commutator` | :355 | one component ≤ local part + commutator | decomposition + previous | OK |
| `uniformCoefficient` (+`_nonneg`) | :380, :384 | the collected constant in `M₀ U₀ G₀` | `positivity` | OK |
| `uniform_expression_bound` | :391 | replaces the `t`-dependent norms by `M₀ U₀ G₀`, keeping `A/R`, `1/R²`, `R^{-7/4}` | `Real.rpow_le_rpow` monotonicity, `nlinarith only [...]` with explicit nonneg facts | OK — I checked no constant absorbs a power of `R` |
| `rpow_three_fourths_div` | :445 | `R^{-3/4}/R = R^{-7/4}` | `rpow_neg_one`, `rpow_add`, `norm_num` | OK |
| `commutatorConstant` (+`_nonneg`) | :451, :455 | `R`-free commutator constant | `positivity` | OK |
| `cutoff_commutator_bound` | :463 | commutator `≤ C‖g‖₁‖w‖₂^{1/4} R^{-7/4} B^{3/4}` | `Comparison.riesz_commutator_pair_bound` (heat-kernel commutator) + `rTest_four_bound`; Lipschitz input from `cutoff_lipschitz` | OK in this file; kernel estimate itself = E2 |
| `cutoff_pressurePair_bound` | :496 | one component, both parts explicit | `.trans` of the two previous | OK |
| `canonicalCutoffFlux_bound` | :516 | full flux with `‖tensorDiff‖₁ ≤ G` | `norm_canonicalCutoffFlux_le` + componentwise | OK |
| `exists_uniform_canonicalCutoffFlux_bound` | :546 | one `CP(M₀,U₀,G₀)` for all `R ≥ 1`, all slices meeting the norm bounds | `uniform_expression_bound` + previous; `CP = 9·uniformCoefficient …` | OK — `∃CP` precedes `∀R`, `∀t` |
| **`exists_uniform_actual_pressure_flux_bound`** | :576 | the exported `hpressure` | `actual_flux_integrable_and_le_canonicalNorm … .2.trans (hbound …)`; slices from `spatial_smooth H.smooth_u/v` | OK, one cosmetic remark (F-3 below) |

`PressureFluxTest.lean` (all 24 decls examined; the ones that matter):

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `r` (def) | PressureFluxTest.lean:23 | `8φ⁵·Dφ[w]` | — | OK |
| `multiplier_r_eq_weight_deriv` | :26 | `φ²·r = D(φ⁸)[w]` | `hasDerivAt_pow 8` composition, `ring` | OK (exact identity) |
| `r_smooth`, `r_hasCompactSupport`, `memLp_r`, `memLp_fderiv_r` | :36-59 | smooth, compact support, in every `Lᵖ` | continuity + compact support | OK — `MemLp` derived |
| `norm_r_le` | :61 | `‖r‖ ≤ 8L‖φ³•w‖` using `0 ≤ φ ≤ 1` | `le_opNorm`, `nlinarith` | OK |
| `memLp_and_lpNorm_r_four_le` | :82 | `r ∈ L⁴` and `‖r‖₄ ≤ 8L‖w‖₂^{1/4}‖φ⁴•w‖₆^{3/4}` | `WeightedInterpolation.cutoff_interpolation_four` | OK (exponents `1/4,3/4` are the correct `L²`–`L⁶` endpoints for `L⁴`) |
| `norm_fderiv_r_le_raw`, `norm_fderiv_r_le_amplitude` | :139, :187 | pointwise derivative bound with `L`, `J = ‖D²φ‖` | product rule, `fderiv_clm_apply`, `nlinarith` | OK |
| `memLp_and_lpNorm_fderiv_r_two_le`, `lpNorm_fderiv_r_two_le` | :228, :269 | `∇r ∈ L²` and `‖∇r‖₂ ≤ 24L·sqrt(∫φ⁸\|∇w\|²) + (40L²+8J)‖w‖₂` | `WeightedSobolev.memLp_cutoffGradientAmplitude`, `lpNorm_add_le` | OK — this is where `A` (weighted dissipation) is *the only* gradient quantity used; no global `∇w ∈ L²` needed |
| `cutoffTest` (def) + `_flux_identity`/`_smooth`/`_hasCompactSupport`/`memLp_*` | :284-307 | specialization to `φ = cutoff R` | — | OK |
| `cutoffTest_four_bound` | :309 | `‖cutoffTest‖₄ ≤ (8C₁/R)‖w‖₂^{1/4}B^{3/4}` | previous with `L = C₁/R` | OK — `1/R` genuine |
| `cutoffDerivativeConstant` (+`_pos`) | :323, :327 | `max(24C₁, 40C₁²+8C₂)` | `le_max_left` | OK |
| `cutoffTest_derivative_bound` | :331 | `‖∇cutoffTest‖₂ ≤ (C/R)·A + (C/R²)‖w‖₂` | previous with `L = C₁/R`, `J = C₂/R²`, `field_simp` + `div_le_div` | OK — `1/R`, `1/R²` genuine |

`PressureFluxIdentity.lean` (all 11 decls examined):

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `fluxFunction_smooth`/`_hasCompactSupport` | :26, :31 | smoothness/compact support of `Dχ[w]` | `fderiv_right.clm_apply`; support of `fderiv χ` | OK |
| `integrable_pressure_flux` | :41 | `π·Dχ[w]` integrable for *any* continuous `π` | `ConservativeDifference.integrable_mul_test` — continuity × compactly supported | OK — **the reason no decay of `q` is needed** |
| `weightedComponent` (+ smooth/compact) | :49-59 | `χ·w_k` | — | OK |
| `sum_partial_weightedComponent` | :61 | `Σ_k ∂_k(χ w_k) = Dχ[w]` when `div w = 0` | `LocalizedDifferenceEnergy.divergence_weighted` with `hdiv x` | OK — div-free is used, as it must be |
| `sum_partial_realTest_weightedComponent` | :77 | same identity inside the Schwartz packaging | `partialCLM_realTest`, `map_sum` | OK |
| `canonicalPressureLinear` (+`_apply`) | :94, :98 | the `9`-term canonical functional as a `ℂ`-linear map | `PressureFunctionals.pressurePairLinear` | OK — linearity is what lets the `Σ_k` pass inside |
| `integrable_canonical_flux_terms` | :103 | integrability of each canonical term | `PressureFunctionals.integrable_l1_riesz_pair` | OK |
| `pressure_flux_eq_of_gradient_identification` | :114 | given the *compact-test* gradient identification `hgrad` and `div w = 0`, the flux integral equals `Re` of the canonical sum | compact by-parts `CompactEnergy.integral_mul_partial`, `integral_finsetSum` with `hint k`, `map_sum` on `reCLM` and on `Q` | OK — clean, no pressure hypothesis at infinity |

`ActualPressureFlux.lean` (all 3 decls examined):

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `difference_slice_smooth` | :23 | slices of `u-v` are smooth | `spatial_smooth (H.smooth_u.sub H.smooth_v)` | OK |
| `actual_pressure_flux_integrable` | :28 | the physical flux integrand is integrable | `integrable_pressure_flux` (continuity + compact `χ`) | OK |
| `pressure_flux_eq_canonical` | :38 | physical flux = `Re Σ_{i,j} pressurePair(tensorDiff, realTest(Dχ[u-v]))`, "with no additional pressure hypothesis" | `pressure_flux_eq_of_gradient_identification` fed `H.tensor_bound.1` (integrability), `hdiv` from `div_u`/`div_v`, and `gradient_recovery H` | OK — docstring claim matches the statement; the recovery is the only deep input |

`PressureFunctionals.lean` (skimmed): `pressurePairLinear` (:245) packages `pressurePair` as a
`ℂ`-linear map given `Integrable g`; `integrable_l1_riesz_pair` (:63) is the `L¹ × bounded`
integrability used above. Both consistent with their use. `PressureTestBounds.lean`: not read
(not in the flux chain — see Residue).

### Name-vs-statement check (hunt (b))

I checked every name in the chain against its statement. The only inflations I can argue for are
mild and I list them for completeness, none is a defect:
* `exists_uniform_actual_pressure_flux_bound` — "actual pressure flux" is specifically
  `∫ (p-q)·D(cutoff R ^ 8)[u-v]`, one weight family and the *difference* of pressures, not a
  general pressure flux. Statement is what the closure needs, so the name is fair.
* `localized_pair_bound`'s docstring "is an actual integrable pairing" is honest: the
  `Integrable` conjunct is in the statement (`:320-321`).
* `PressureFlux.lean:574-575` docstring "All hypotheses on the pressure are exactly those already
  present in pressure recovery" — **verified true**: the theorem's own pressure hypotheses are
  exactly `H.smooth_p`, `H.smooth_q`, `H.equation`; `hM/hU/hG` mention only velocities.
* `WholeSpaceUniqueness.lean:8-13` docstring "No growth, decay, support or derivative bound is
  assumed for the competing pressure or velocity" — verified for the flux route in this scope.

## Kernel-risk

Repo-wide scan patterns `decide`, `native_decide`, `axiom`, `sorry`, `unsafe`, `partial def`,
`macro`, `elab`, `syntax`, `set_option`, `termination_by`, `WellFounded` over
`PressureFlux.lean`, `PressureFluxIdentity.lean`, `PressureFluxTest.lean`,
`PressureFunctionals.lean`, `PressureTestBounds.lean`, `ActualPressureFlux.lean`:
**zero hits.** Counts: `decide` 0, `native_decide` 0, `axiom` 0, `sorry` 0, `unsafe` 0,
`partial` 0, custom syntax/metaprogramming 0, `set_option` 0, `termination_by` 0,
`WellFounded.fix` 0.

Other kernel-relevant observations in scope:
* No `Nat.pow/div/mod/gcd`, no numerals beyond small literals (`8`, `9`, `24`, `40`, `6/5`,
  `7/4`); all rational exponents are `Real.rpow` with `norm_num`-discharged side goals, no
  `decide`.
* No recursion, no `.rec`, no structure-eta `rfl` on recursive data. The three `rfl`s in scope
  (`PressureFlux.lean:167`, `:171`, `:202`) are unfoldings of non-recursive `def`s
  (`rTest_apply`, `fluxTest_apply`, `canonicalCutoffFlux_eq_sum`) — cheap and safe.
* `Classical.choose` is used for `ComparisonCutoffs.derivativeConstant` (`:151`), backed by a
  *proved* existence (`exists_derivative_bound`, `:143-148`, from compact support + continuity of
  iterated derivatives). Not an axiom, no kernel risk; it does mean the constants are
  non-explicit, which is fine for this argument.
* `nlinarith only [...]` / `positivity` are used in the arithmetic-collection lemmas
  (`:414`, `:420`, `:443`, `PressureFluxTest.lean:67, 77, 197, 281`). These are elaboration-time
  tactics producing ordinary proof terms; no kernel reduction risk.

## Escalations (ranked)

**E1 (highest). The harmonic/Liouville step behind `gradient_recovery` is the single deep input of
this scope.** `PressureRecovery.lean:391-405` (`gradient_recovery_complex`), reached from
`ActualPressureFlux.lean:58`. Question an expert must answer: *does
`TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests` + `time_test_gradient_difference_zero`
(`PressureRecovery.lean:353-405`) plus the `HarmonicTestFunctionals` vanishing theorem really force
`∫ ∂_k(p-q)·ψ = -Re Σ pressurePair(tensorDiff, ∂_kψ)` for a competitor with only
`UniformFiniteEnergy` — i.e. is the harmonic remainder killed without any decay of `q` or of
`∇v`?* What would settle it: read the `HarmonicTestFunctionals` vanishing statement and check
(i) which Sobolev-type finiteness it demands of the harmonic functional, (ii) that this finiteness
is supplied by time-averaged `L²`/`L¹` bounds from `energy_u`/`energy_v` only
(`PressureRecovery.lean:60-112`), and (iii) that it is not the *time-averaged* pressure whose
harmonicity is only formal. Note this is inside the sibling recovery worker's scope; my scope
consumes it as a black box, and it is the only black box.

**E2. The heat-kernel commutator bound supplies the `R^{-3/4}` and therefore all of the third
envelope term.** `HeatKernelCommutator.lean:97-113` (`riesz_commutator_pair_bound`), used at
`PressureFlux.lean:471-475`. Question: *is `‖∫ g·([R_{ij}, φ²]ψ)‖ ≤ C·max(2L,1)·R^{-3/4}‖g‖₁‖ψ‖₄`
correct, and is the heat-kernel representation `riesz_commutator_eq_heatKernel` valid for a merely
`L¹` `g` and `L⁴` `ψ` (Fubini/interchange)?* What would settle it: check
`HeatKernelPairedBound.lean:133-151` (the `L^{4/3}×L⁴` Hölder step and
`radialCommutatorKernel_lpNorm_scale hR`, which is where the `R^{-3/4}` scaling is created) and
that `radialCommutatorKernel_memLp` covers the exponent actually used. The `R`-power arithmetic on
my side (`rpow_three_fourths_div`, `PressureFlux.lean:445`) is exact.

**E3. The envelope is only useful after Young; the absorption exponents live outside my scope.**
`WholeSpaceComparisonClosure.lean:64` and `:140` (`ComparisonRateBound.exists_uniform_rate_bound`),
consuming `hSob` (`:94-95`) and `hpressure` (`:49-52`). Question: *does the rate lemma absorb
`CP·((B^{1/2}+1)(A/R + 1/R²) + R^{-7/4}B^{3/4})` with `B ≤ C(A + C₁M/R)` into
`ε·A² + (something summable in R → 0)`, with `ε` small enough to be dominated by the `-A²`
dissipation of the energy balance?* What would settle it: read `ComparisonRateBound` and verify
the Young exponents (`A^{3/2}/R ≤ εA² + C R^{-4}`, `A^{3/4}R^{-7/4} ≤ εA² + C R^{-14/5}`) and that
the final `R → ∞` limit in `WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound` uses a rate that
actually tends to `0`.

**E4 (low, cosmetic but worth a line).** `exists_uniform_actual_pressure_flux_bound`
(`PressureFlux.lean:585-589`) exports only the inequality, dropping the `Integrable` conjunct that
its own helper proves at `:221-230`. Read in isolation the statement *could* be satisfied by a
junk `0` integral. Question: *is integrability of `(p-q)·D(weight R)[u-v]` available wherever the
closure needs the flux term to be the real energy flux?* Settled by: `:229`
(`ActualPressureFlux.actual_pressure_flux_integrable`, needs only smoothness + compact weight) and
`LocalizedDifferenceEnergy.difference_energy_balance` (used at
`WholeSpaceComparisonClosure.lean:135-139`), which must itself carry the integrability. I regard
this as a presentation issue, not a defect; but a reviewer who reads only the exported statement
would be right to ask.

## Residue (what I could not check, and why)

* **No compilation.** No `lake build` (no built Mathlib, disk full), so I cannot certify that
  these files typecheck, that the `simpa only [...]`/`convert!` steps close their goals, or that no
  `simp` set silently uses a `sorry`-carrying lemma elsewhere. All verdicts are
  statement-and-proof-shape verdicts. Notably `PressureFlux.lean:217` and `:246` use `using!`
  and `convert!` (`simpa … using!`, `convert! hq.sub hl using 1`), which are tactics whose success
  I cannot confirm by reading.
* **`PressureTestBounds.lean` (281 lines, 21 decls): not read.** It is not imported by
  `PressureFlux.lean` and no declaration in the flux chain I traced calls it; it reaches this
  namespace only via `PressureFunctionals.lean:1`. If a reviewer wants completeness for
  `PressureFunctionals`, that file is the gap.
* **`PressureFunctionals.lean`: skimmed only** (2 of 17 decls inspected).
* **Downstream of `gradient_recovery`:** `HarmonicTestFunctionals`, `TemporalTestUniqueness`,
  `RieszLinearityDecay`, `ComparisonTimeAverages`, `WeakTimeContinuity` — not read (E1).
* **Sideways of the commutator:** `HeatKernelPairedBound`, `HeatKernelFubini`,
  `RadialKernelBounds`, `HeatKernelTimeBound` — only the statements/defs quoted above were read
  (E2).
* **Downstream in the closure:** `ComparisonRateBound`, `WholeSpaceEnergyLimit`,
  `LocalizedFluxEstimates`, `WeightedSobolev.cutoffL6_le` — read only where quoted (E3).
* **Mathlib lemmas taken on trust**: `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`,
  `Convex.norm_image_sub_le_of_norm_fderiv_le`, `eLpNormLESNormFDerivOfEqInnerConst` (the `L⁶`
  Sobolev constant), `MemLp.integrable_mul`, `SchwartzMap` API.
* **Numeric plausibility of the interpolation exponents** I re-derived by hand rather than by
  machine: `‖φ²|w|²‖_{6/5} ≤ ‖w‖₂^{3/2}‖φ⁴w‖₆^{1/2}` (exact: `φ²|w|² = |w|^{3/2}(φ⁴|w|)^{1/2}`,
  Hölder with `10/9` and `10`) and `‖f‖₄ ≤ ‖f‖₂^{1/4}‖f‖₆^{3/4}`. Both check out, which is a point
  in the claimant's favour: the exponent bookkeeping in `LocalizedTensorBounds.lean:170-180` and
  `PressureFluxTest.lean:82-88` is not fudged.
