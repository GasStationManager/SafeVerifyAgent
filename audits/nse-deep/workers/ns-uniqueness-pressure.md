# Worker report C — THE PRESSURE (NS uniqueness chain)

Audit target: `/home/gsm/.openclaw/workspace/repos/NSE` (clone of openai/NavierStokesAndEuler @ f9e8bc5).
Read-only. No `lake build` was run (no built Mathlib). All line numbers re-read from the original files.
Docstrings are the claimant's own prose and are treated as evidence about the author, not the proof.

## Scope

Primary (read line-by-line, 100%):

| file | lines | decls |
|---|---|---|
| `NavierStokes/R3/PressureRecovery.lean` | 441 | 23 |
| `NavierStokes/R3/PressureRecoveryHelpers.lean` | 190 | 12 |
| `NavierStokes/R3/HarmonicTestFunctionals.lean` | 113 | 6 |

Dependencies followed because they carry the real content of the key theorem
(`PressureRecovery.lean:407 gradient_recovery`). Read line-by-line in the cited regions,
skimmed elsewhere:

| file | lines | decls | how read |
|---|---|---|---|
| `R3/ConservativeDifference.lean` | 472 | 29 | :200-472 line-by-line (the weak identities), :1-200 skimmed |
| `R3/PressureFunctionals.lean` | 290 | 21 | :100-290 line-by-line, :1-100 skimmed |
| `R3/PressureTestBounds.lean` | 282 | 21 | :1-100 and :230-282 line-by-line, middle skimmed |
| `R3/RieszTestOperators.lean` | 304 | 21 | :240-304 line-by-line, decl list of the rest |
| `R3/RieszLinearityDecay.lean` | 84 | 9 | 100% |
| `R3/RieszSymbolRegularity.lean` | 121 | 15 | :50-121 line-by-line |
| `R3/ComparisonFourierSetup.lean` | 31 | 5 | 100% |
| `R3/FourierSobolevWeights.lean` | 162 | 21 | :40-162 line-by-line |
| `R3/WeakFourierUniqueness.lean` | 103 | 4 | 100% |
| `R3/HilbertFunctionalExtension.lean` | 47 | 1 | 100% |
| `R3/SchwartzCompactApproximation.lean` | 240 | 20 | :18-55, :185-240 line-by-line, tail estimates skimmed |
| `R3/TemporalTestUniqueness.lean` | 52 | 3 | 100% |
| `R3/PressureTemporalIdentity.lean` | 210 | 9 | :122-210 read, rest by decl list |
| `R3/ComparisonTimeAverages.lean` | 533 | 30 | :20-40, :300-380, :455-533 read; rest skimmed |
| `R3/ComparisonFiniteEnergy.lean` | 231 | 17 | :150-231 read |
| `R3/ComparisonSetup.lean`, `ProblemStatement.lean`, `R3/ProblemStatement.lean` | — | — | only the definitions used (`tensorDiff`, `navierStokesResidual`, `UniformFiniteEnergy`) |
| `R3/WholeSpaceUniqueness.lean`, `R3/PressureFlux.lean` | — | — | only the call sites (:41-70; :576-599) to see which field carries which hypothesis |

Total: 3 files fully read, 18 files inspected, ~110 declarations examined at statement level,
~55 at proof-term level.

## Answers to the three assigned questions

### 1. The exact theorem at `PressureRecovery.lean:407`, and how `p - q` gets pinned

`PressureRecovery.lean:407` is **`NavierStokesR3.PressureRecovery.gradient_recovery`**
(its ℂ-valued twin is `gradient_recovery_complex`, :391; the hypothesis-unbundled export is
`pressure_gradient_recovery`, :419). Statement (:407-412), verbatim shape:

```
theorem gradient_recovery {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      -(∑ i, ∑ j, pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))).re
```

All hypotheses come from the record `Hypotheses` (:33-44): `0 < T`; `ContDiffOn ℝ ∞` for
`u, v, p, q` on `Comparison.slab 0 T = Icc 0 T ×ˢ univ`; `spatialDivergence u = 0` and
`= 0` for `v` on `Ioo 0 T`; the **residual equality** `navierStokesResidual u p = navierStokesResidual v q`
on `Ioo 0 T` (:41-42, viscosity 1 form, `NavierStokes/ProblemStatement.lean:82`); and
`UniformFiniteEnergy (Icc 0 T)` for **both** `u` and `v` (`R3/ProblemStatement.lean:81`
= `SquareIntegrableAtTime` at each `t` plus one finite bound `E`). Plus `t ∈ Ioo 0 T`,
`ψ` smooth with compact support, and a coordinate `k`. Nothing else. No decay, no growth,
no support and no integrability assumption on `p`, `q`, or on `v` beyond that.

The representation used: `pressurePair i j g ψ = ∫ g · rieszTest i j ψ`
(`ComparisonFourierSetup.lean:24`), with `rieszTest i j ψ = 𝓕⁻¹( rieszSymbol i j · 𝓕ψ )`
(:20-22) and `rieszSymbol i j ξ = -(ξ i * ξ j)/‖ξ‖²` (:17-18). That symbol is exactly
`(-Δ)⁻¹ ∂ᵢ∂ⱼ`: `𝓕(∂ᵢ∂ⱼf) = -4π²ξᵢξⱼ 𝓕f`, `𝓕(Δf) = -4π²‖ξ‖²𝓕f`, and the file proves the
multiplier identity `rieszTest i j (Δψ) = -∂ᵢ∂ⱼψ` (`RieszTestOperators.lean:243-275`,
via `rieszSymbol_mul_norm_sq`, `RieszSymbolRegularity.lean:50`). So the "canonical pressure"
is the honest singular integral `π_can = Σᵢⱼ (-Δ)⁻¹∂ᵢ∂ⱼ(uᵢuⱼ - vᵢvⱼ)`, tested against the
Schwartz test (the operator is moved onto the test, never onto the pressure).

How the ambiguity dies (this is the load-bearing part, and it is NOT done on the pressure side):

1. `weak_pressure_poisson` (`ConservativeDifference.lean:431-469`) proves, by integration by
   parts against a **compactly supported** test only,
   `∫ (p-q)(t,·) Δψ = -Σₖᵢ ∫ tensorDiff u v t k i · ∂ᵢ∂ₖψ`. Its ingredients:
   the pointwise residual equality (`weak_pressure_gradient`, :223-277), the div-free
   condition to kill two terms (`integral_divergence_free_test`, :342;
   `integral_time_derivative_divergence_free`, :385), and IBP (`integral_gradient_pairing`, :403).
   `gradient_poisson_test` (`PressureRecoveryHelpers.lean:116-158`) differentiates this once more.
2. A linear functional `F` on **Schwartz space** is formed out of the *velocity* data only:
   `averagedPressureDifference W0 W1 G` (`PressureFunctionals.lean:256`) with
   `W0 = ∫ a(t)(u-v)ₖ dt`, `W1 = ∫ a'(t)(u-v)ₖ dt`, `G_{ij} = ∫ a(t)(uᵢuⱼ-vᵢvⱼ) dt`
   (`PressureRecovery.lean:46-51`). `F` satisfies the uniform bound
   `‖F ψ‖ ≤ C √(fourierHNormSq 3 ψ)` — i.e. `F ∈ H^{-3}` — where `C` depends only on
   `‖W0‖_{L²}, ‖W1‖_{L²}, ‖G‖_{L¹}` (`PressureFunctionals.lean:169-243`, :279).
3. `F` annihilates Laplacians of compact tests, because the two Poisson identities cancel
   (`averaged_value_real_harmonic`, `PressureRecovery.lean:259-281`); this is upgraded to all
   Schwartz tests by density (`SchwartzCompactApproximation.lean:188,213`) and continuity from
   the same `H^{-3}` bound (`HarmonicTestFunctionals.lean:42-50,100-110`).
4. Liouville step (`HarmonicTestFunctionals.lean:29-95`): the `H^{-3}` bound gives, by
   Hahn-Banach + Riesz on the weighted Fourier embedding `B` (`HilbertFunctionalExtension.lean:22`,
   `FourierSobolevWeights.lean:67-88,144`), a genuine representative `q̂ ∈ L²(ℝ³)` with
   `F ψ = ⟪q̂, Bψ⟫`. Harmonicity says `∫ q̄̂ (1+‖ξ‖²)² ‖ξ‖² φ = 0` for every Schwartz `φ`,
   hence `q̂ (1+‖ξ‖²)²‖ξ‖² = 0` a.e. (fundamental lemma, `WeakFourierUniqueness.lean:75-100`),
   hence `q̂ = 0` a.e. **because `{0}` is Lebesgue-null** — the atom at frequency zero, which is
   exactly the harmonic/polynomial ambiguity (`c(t)` and `a(t)·x`), cannot be seen by an `L²`
   function. So `F = 0`.
5. `F = 0` at a bump `a(t)` supported in `Ioo 0 T` gives
   `∫₀ᵗ a(t)[⟨∂ₖ(p-q)(t),ψ⟩ + Σ pressurePair] dt = 0` (`time_test_gradient_difference_zero`, :353),
   and the temporal fundamental lemma with time-continuity of both pairings
   (`TemporalTestUniqueness.lean:40`, `pressure_gradient_pairing_continuousOn`
   `PressureRecoveryHelpers.lean:162`, `canonical_sum_continuousOn` :319) removes the time test.

So the additive-function-of-`t` ambiguity is not "chosen away": the theorem only ever claims
the **gradient** pairing, which is the object the momentum equation contains, and the
constant/linear-in-x harmonic part is eliminated by the frequency-zero-null argument, driven by
finite energy of the velocities. Verdict: this is the standard argument, done honestly.

### 2. Does the argument need a decay/growth hypothesis the Clay statement does not give?

**No — not in this chain, and I looked for it hard.** Evidence:

* The pressure `p - q` is only ever paired with compactly supported `ψ` or its derivatives
  (`ConservativeDifference.lean:431`, `PressureRecoveryHelpers.lean:116`,
  `PressureRecovery.lean:407`). Every IBP is between a smooth function and a compactly supported
  test, so no boundary term at infinity is ever needed.
* The `H^{-3}` bound that powers the Liouville step is computed from
  `MemLp (velocityAverage ...) 2` (`PressureRecovery.lean:60-64`) and
  `Integrable (tensorAverage ...)` (:66-70), both **derived** from `UniformFiniteEnergy`:
  `tensorDiff_integrable` / `tensorDiff_norm_integral_le` / `uniformFiniteEnergy_tensorDiff_bound`
  (`ComparisonFiniteEnergy.lean:150,160,175`) use only `‖u(t)‖₂² + ‖v(t)‖₂²` and the pointwise
  bound `|uᵢuⱼ - vᵢvⱼ| ≤ ‖u‖² + ‖v‖²`; the `L²` bound on the time averages comes from a
  Minkowski-type argument in `ComparisonTimeAverages.lean:334,359`. No pressure norm appears.
* Fubini steps assume nothing extra either: they are gated by explicit integrability plus a
  uniform-in-`t` `L¹`/`L²` bound (`ComparisonTimeAverages.lean:461`, `:510`).
* The only place in the wider uniqueness proof where a norm beyond `L²` is required is
  `PressureFlux.lean:581-582`: `hU : MemLp (u (t,·)) 3 ∧ ‖u(t)‖_{L³} ≤ U₀`. In the call site
  `WholeSpaceUniqueness.lean:57-58` this is discharged by
  `CompactComparisonBounds.exists_lpNorm_three_bound hu.continuousOn hK hsupp`, i.e. from the
  **candidate's** compact spatial support. `u` is the candidate, `v` the competitor
  (`WholeSpaceUniqueness.lean:30-43`, `candidate_unique_on_Icc` :74-100). So this is allowed, not
  a smuggled competitor hypothesis.
* The competitor's inputs, traced to `candidate_global_agrees_before_one`
  (`WholeSpaceUniqueness.lean:104`) via `GlobalFiniteEnergySolution`, are exactly:
  smooth on the slab, div-free, the PDE, `v(0,·) = 0`, uniform finite energy. Matches the
  challenge list. I found no `tendsto ... atInfinity`, `HasCompactSupport`, `MemLp q`, or growth
  hypothesis on `q` anywhere in the recovery chain.

One genuine narrowing, not about decay: viscosity is hard-wired to `1`
(`Hypotheses.equation`, `PressureRecovery.lean:41-42` uses the `ν ≡ 1` residual of
`NavierStokes/ProblemStatement.lean:82`; the caller passes `navierStokesResidual 1`,
`WholeSpaceUniqueness.lean:41`). Whether the top-level claim needs all `ν > 0` is outside my
files — escalated below.

### 3. Honest weak identity, or an assumed representation formula?

**Honest.** The Poisson equation for `p - q` is derived, never assumed:
`weak_pressure_gradient` (`ConservativeDifference.lean:223-277`) is pure pointwise algebra from
the residual equality plus IBP against a compact test; `weak_pressure_poisson` (:431-469) sums it
over `k` and integrates by parts again; `gradient_poisson_test`
(`PressureRecoveryHelpers.lean:116-158`) transfers one more derivative onto the test. The Riesz
representation is not asserted of `p - q`; it is *derived* as the conclusion, and the operator
identity that makes it work (`rieszTest i j (Δψ) = -∂ᵢ∂ⱼψ`, `RieszTestOperators.lean:243`) is
proved on the test side by the multiplier computation, with the `ξ = 0` case handled explicitly
(`RieszSymbolRegularity.lean:52-54`). The `H^{-3}` estimate on the Schwartz functional is proved
term by term with Cauchy-Schwarz and a *proved finite* weight integral
(`PressureTestBounds.lean:20-27` `integrable_inverse_weight_sq` via
`integrable_rpow_neg_one_add_norm_sq` in dimension 3; `:30` `fourierMomentConstant`;
`:37-79`; `:253-279`). I found no step of the form "assume `p = -(-Δ)⁻¹∂ᵢ∂ⱼ(uᵢuⱼ)`".

## Per-declaration findings

Statement paraphrases are mine. "Mechanism" is what the proof term/tactic block actually does.

| decl | file:line | what the statement says (my words) | actual proof mechanism | verdict |
|---|---|---|---|---|
| `Hypotheses` | PressureRecovery.lean:33 | record: `0<T`, 4 smoothness-on-slab, 2 div-free on `Ioo`, residual equality, both fields uniform-finite-energy | structure, no proof | OK (non-vacuous: satisfied by the candidate/competitor pair at `WholeSpaceUniqueness.lean:44`) |
| `continuous_deriv_of_smooth` | :53 | `deriv a` continuous for `C^∞ a` | `ContDiff.fderiv_right` + `clm_apply` | OK |
| `Hypotheses.velocityAverage_memLp` | :60 | time average of `(u-v)ₖ` is in `L²` | delegates to `timeAverage_difference_component_memLp_two` | OK, derived from energy |
| `Hypotheses.tensorAverage_integrable` | :66 | time average of `uᵢuⱼ-vᵢvⱼ` is `L¹` | delegates to `timeAverage_tensorDiff_integrable` | OK, derived |
| `Hypotheses.tensor_bound` | :72 | one `M ≥ 0` bounds `∫‖tensorDiff‖` for all `t ∈ Icc 0 T`, with integrability | `uniformFiniteEnergy_tensorDiff_bound` | OK (`0 ≤ M` here is harmless: `M` is an upper bound in a *proved* inequality, not a hypothesis) |
| `velocityAverage_pairing` | :81 | Fubini for `∫ (time-avg)·ψ` | `timeAverage_complex_pairing_of_memLp_two` with explicit `L²` bounds | OK |
| `tensorAverage_pairing` | :98 | same for the tensor, bounded test | `timeAverage_complex_pairing_of_bounded` with `L¹` bound + sup bound of `ψ` | OK |
| `pressurePair_tensorAverage` | :116 | Fubini through the Riesz test | same + `exists_bound_rieszTest` (sup bound of the Riesz test) | OK |
| `noncanonical_average_identity` | :129 | averaged velocity terms = averaged physical `∂ₖ(p-q)` pairing | `pressure_time_identity` (time IBP moving `∂ₜ` onto `a`) + the two pairing lemmas | OK |
| `averaged_value_realTest` | :173 | value of the functional on a real compact test = physical term + Riesz terms | `unfold` + rewrite | OK |
| `averaged_gradient_poisson` | :188 | `∫a ∫∂ₖ(p-q)Δψ = Σ ∫ tensorAvg ∂ᵢ∂ⱼ∂ₖψ` | pointwise `gradient_poisson_test` for `t ∈ Ioo`, `a t = 0` off `tsupport a`, then Fubini | OK — note the clean use of `image_eq_zero_of_notMem_tsupport` (:216) instead of assuming anything at the endpoints |
| `averaged_gradient_poisson_complex` | :229 | ℂ version | `Complex.ofReal` transport | OK |
| `averaged_value_real_harmonic` | :259 | functional kills `Δ` of real compact tests | the two Poisson identities cancel via `pressurePair_laplacianCLM` | OK — the pressure term cancels; this is the crux and it is honest |
| `averaged_value_zero` | :286 | the whole Schwartz functional is `0` | `averagedPressureDifference_bound` (`H^{-3}`) + `compact_harmonic_of_real` + `eq_zero_of_compact_harmonic` | OK |
| `pressurePair_continuousOn` | :309 | `t ↦ pressurePair(tensorDiff t)` continuous on `Icc 0 T` | `WeakTimeContinuity.continuousOn_pairing` with uniform `L¹` bound + `rieszTest` decay | OK (decay lemma only skimmed, see Escalation 1) |
| `canonical_sum_continuousOn` / `canonical_sum_timeAverage` | :319, :326 | finite sums / Fubini | routine | OK |
| `time_test_gradient_difference_zero` | :353 | every compact time test annihilates (physical + canonical) | `averaged_value_zero` re-expanded, `integral_add` with proved integrabilities | OK |
| `gradient_recovery_complex` | :391 | pointwise-in-`t` recovery, ℂ valued | `TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests` + continuity | OK |
| **`gradient_recovery`** | **:407** | for every interior `t` and every compact `ψ`: `∫∂ₖ(p-q)ψ = -Σ Re pressurePair(tensorDiff)(∂ₖψ)` | `Complex.re` of the previous | OK — name matches statement |
| `pressure_gradient_recovery` | :419 | same with hypotheses spelled out | packs `Hypotheses` | OK — docstring claim "both pressures allowed on all of Euclidean space" is accurate |
| `realTest` & simp lemmas | Helpers:32,38,52,60,75 | embed real compact test into Schwartz; `∂`, `Δ` commute with the embedding | `CompactSchwartz.ofCompactSupport`, `fderiv` of `ofRealCLM ∘ ψ` | OK |
| `compact_test_decomposition` | Helpers:89 | complex compact test = real + `i`·imag part | `Complex.ext` | OK |
| `compact_harmonic_of_real` | Helpers:101 | harmonicity on real compact tests ⇒ on complex compact tests | linearity | OK |
| `gradient_poisson_test` | Helpers:116 | `∫∂ₖ(p-q)Δψ = Σ ∫ tensorDiff ∂ᵢ∂ⱼ∂ₖψ` at fixed interior `t` | IBP (`CompactEnergy.integral_mul_partial`) + `weak_pressure_poisson` + `partial_comm` | OK, honest distributional identity |
| `pressure_gradient_pairing_continuousOn` | Helpers:162 | `t ↦ ∫∂ₖ(p-q)ψ` continuous on `Ioo 0 T` | rewrites the pressure pairing into velocity terms via `weak_pressure_gradient_on_slab`, then continuity of those | OK — clever: continuity of the *pressure* pairing is obtained from the equation, not assumed |
| `exists_inner_representation_of_fourierHNormSq_bound` | Harmonic:29 | `H^{-3}`-bounded functional has an `L²` Fourier representative | Hahn-Banach + Riesz (`HilbertFunctionalExtension.lean:22`) via injective `B` | OK |
| `continuous_of_fourierHNormSq_bound` | Harmonic:42 | such a functional is Schwartz-continuous | continuity of `B` | OK |
| `representative_eq_zero_of_harmonic` | Harmonic:53 | an `L²` representative annihilating `Δ` is `0` | multiplier `-4π²`, then `WeakFourierUniqueness.eq_zero_of_integral_weight_normSq_test_eq_zero` | OK — the Liouville kill |
| `eq_zero_of_harmonic`, `eq_zero_of_compact_harmonic` | Harmonic:84,100 | harmonic + `H^{-3}` ⇒ `F = 0`; compact harmonicity suffices | density of compact tests in Schwartz | OK; names match statements |
| `weak_pressure_gradient` | ConservativeDifference:223 | tested momentum-difference identity | pointwise `conservative_difference_equation` + IBP; every integrability discharged by compact support | OK |
| `weak_pressure_gradient_on_slab` | :281 | slab version | `spatial_smooth`, `time_differentiable_at_interior` | OK |
| `integral_divergence_free_test` | :342 | compact test sees `div w = 0` | IBP | OK |
| `integral_time_derivative_divergence_free` | :385 | `div ∂ₜw = 0` distributionally | differentiate a pairing that is locally constant `0` | OK, neat |
| `integral_gradient_pairing` | :403 | `Σ∫∂ₖf ∂ₖψ = -∫f Δψ` | IBP | OK |
| `weak_pressure_poisson` | :431 | `∫(p-q)Δψ = -Σ∫tensorDiff ∂ᵢ∂ₖψ` | the above three + `linarith` | OK; docstring "no pressure normalization, growth hypothesis, or integrability at infinity is used" is, as far as I can check, TRUE |
| `rieszSymbol`, `rieszTest`, `pressurePair`, `fourierHNormSq` | ComparisonFourierSetup:17,20,24,27 | the `-ξᵢξⱼ/‖ξ‖²` multiplier, its inverse-FT test, the `L¹`-pairing, the Fourier `H³` norm | definitions | OK; `ξ=0` junk `0/0=0` is used but consistently (see Escalation 3) |
| `averagedPressureDifferenceValue` / `_bound` | PressureFunctionals:122,169 | the functional and its `H^{-3}` estimate | triangle inequality + `norm_l2_pair_le` + `exists_uniform_test_bound` | OK; `C = M·B` with `M` built from the actual `L²`/`L¹` masses — no free constant to game |
| `averagedPressureDifference` / `_bound` | :256,279 | same as an honest `→ₗ[ℂ]` | sums/comps of linear pairings | OK |
| `integrable_inverse_weight_sq`, `fourierMomentConstant`, `integral_first_moment_le`, `exists_uniform_test_bound` | PressureTestBounds:20,30,37,253 | `∫(1+‖ξ‖²)⁻² < ∞` in ℝ³; the weighted Cauchy-Schwarz; one constant for all four test bounds | `integrable_rpow_neg_one_add_norm_sq` with `r = 4 > 3 = dim`; Hölder 2-2 | OK — finiteness is proved, so `fourierMomentConstant` is not a junk `0` |
| `rieszTest_laplacianCLM`, `pressurePair_laplacianCLM` | RieszTestOperators:243,278 | `R_{ij}Δψ = -∂ᵢ∂ⱼψ`; hence the canonical pairing solves the test Poisson equation | multiplier algebra + Fourier inversion on Schwartz | OK |
| `integrable_rieszMultiplier`, `exists_bound_rieszTest` | RieszSymbolRegularity:68,115 | symbol·`𝓕ψ` is `L¹`; `rieszTest` is bounded by `‖𝓕ψ‖_{L¹}` | `|rieszSymbol| ≤ 1` domination | OK |
| `rieszTest_tendsto_zero` | RieszLinearityDecay:77 | `rieszTest i j ψ → 0` at spatial infinity | `Real.fourierInv_eq_fourier_comp_neg` + `tendsto_integral_exp_inner_smul_cocompact _` | UNCLEAR — the `_` should be the `Integrable` side condition; cannot check without a build (Escalation 1). The mathematical claim is true (Riemann-Lebesgue, and `integrable_rieszMultiplier` is available) |
| `B`, `B_injective`, `sqrt_fourierHNormSq_three_le_norm_B`, `inner_B_eq_integral` | FourierSobolevWeights:72,84,144,151 | weighted Fourier embedding of Schwartz into `L²`, injective, dominating the `H³` norm | `SchwartzMap.toLpCLM`, weight `(1+‖ξ‖²)²`, `H³ ≤ H⁴` | OK |
| `locallyIntegrable_weighted_star`, `eq_zero_of_integral_weight_normSq_test_eq_zero` | WeakFourierUniqueness:56,75 | polynomial-weighted `L²` function is `L¹_loc`; if all Schwartz pairings vanish it is `0` | Mathlib fundamental lemma + `{0}` is null | OK — this is exactly where the harmonic ambiguity is killed |
| `exists_inner_representation` | HilbertFunctionalExtension:22 | bounded-through-`B` functional is an inner product with some `q` | `LinearEquiv.ofInjective`, `mkContinuous`, `exists_extension_norm_eq`, `toDual` | OK |
| `truncate`, `tendsto_approximate`, `dense_hasCompactSupport`, `continuous_zero_of_compactSupport` | SchwartzCompactApproximation:25,188,206,213 | cutoff truncation converges in the Schwartz topology; compact tests are dense; continuous functionals vanishing there vanish | seminorm tail estimates with `SchwartzMap.seminorm` | OK (tail estimates :39-175 skimmed, spot-checked :39-50) |
| `eq_zero_on_open_of_tests`, `eq_zero_on_Ioo_of_setIntegral_tests` | TemporalTestUniqueness:16,40 | continuous function annihilated by all compact time tests is `0` on the open set | Mathlib `ae_eq_zero_of_integral_contDiff_smul_eq_zero` + `Measure.eqOn_open_of_ae_eq` | OK |
| `pressure_time_identity(_interval)` | PressureTemporalIdentity:122,187 | time-tested momentum identity, `∂ₜ` moved onto `a` | `compact_time_integration_by_parts` with `tsupport a ⊆ Ioo 0 T` | OK (proof read to :186 partially) |
| `timeAverage` + Fubini lemmas | ComparisonTimeAverages:25,334,359,461,510 | the averages and their `L²`/`L¹` properties; interchange of `t` and `x` integrals | explicit slice integrability + uniform bound, `integrable_slab_of_integral_norm_le` | OK — integrability is derived, never assumed |
| `tensorDiff_integrable`, `tensorDiff_norm_integral_le`, `uniformFiniteEnergy_tensorDiff_bound` | ComparisonFiniteEnergy:150,160,175 | `uᵢuⱼ-vᵢvⱼ ∈ L¹` with bound `‖u‖₂²+‖v‖₂²` uniformly in `t` | pointwise `|·| ≤ ‖u‖²+‖v‖²` + `MemLp` from `SquareIntegrableAtTime` | OK — the only nonlinear integrability input, and it is genuinely derived from the challenge's energy bound |
| `spatial_smooth` | PeriodicUniqueness:37 | slices of a slab-`ContDiffOn` field are globally `C^∞` in `x` | `ContDiffOn.comp_contDiff` | OK modulo Mathlib's lemma (relies on Mathlib, not on the author) |

No declaration in my scope was found vacuous, and no lemma name over-claims its statement.
The one asymmetry I checked deliberately — that `Hypotheses` demands `UniformFiniteEnergy` of
`u` *and* `v` — is discharged for the candidate from compact support
(`WholeSpaceUniqueness.lean:44`, `CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab`),
so no hidden competitor hypothesis.

## Kernel-risk

Repo-wide grep over the 18 files in scope for
`sorry|admit|axiom |native_decide|set_option|macro|elab |syntax |unsafe|partial def|termination_by|decide`:

* `sorry` / `admit`: **0**
* `axiom` / `native_decide` / `macro` / `elab` / `syntax` / `set_option` / `unsafe` / `partial def`: **0**
* `termination_by` / `WellFounded.fix` / `.rec` reduction: **0**
* `decide`: **1** — `NavierStokes/R3/FourierSobolevWeights.lean:107`,
  `pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg ‖ξ‖)) (by decide)`, deciding `3 ≤ 4` in ℕ.
  Negligible kernel cost, no bignum.
* Huge numerals / `Nat.pow|div|mod|gcd`: none. Largest literals are `3`, `4`, `2*π`, `4π²`.
* Structure-eta `rfl` on recursive data: none. The `rfl`s I read
  (`PressureRecoveryHelpers.lean:39`, `PressureFunctionals.lean:115,118,252,276`,
  `PressureRecovery.lean:304`) are definitional unfoldings of `SchwartzMap` coercions and
  `LinearMap` applications.

Kernel risk in this sub-chain: essentially zero. The risk here is mathematical/elaboration, not kernel.

## Escalations

Ranked by how much they could damage the pressure argument.

1. **`RieszLinearityDecay.lean:81` — does the Riemann-Lebesgue call actually discharge its side
   condition?** The proof is `exact tendsto_integral_exp_inner_smul_cocompact _`, with a bare `_`.
   In Mathlib the Riemann-Lebesgue lemma needs `Integrable f`; the needed fact exists in this repo
   (`RieszSymbolRegularity.lean:68 integrable_rieszMultiplier`) but is not cited here.
   *Question for an expert:* in Mathlib `v4.34.0-rc2`
   (`rev 85e3a25e006c35636f0e53b0e9296caca2685bc0`), what is the exact signature of
   `tendsto_integral_exp_inner_smul_cocompact`, and does `_` unify with a provable argument?
   *What settles it:* `lake build NavierStokes.R3.RieszLinearityDecay` (or reading that Mathlib
   file). I judge the mathematical content true; this is an elaboration question only. It matters
   because `rieszTest_tendsto_zero` is used for time-continuity of the canonical pairing
   (`PressureRecovery.lean:317`), which the temporal fundamental lemma needs.
2. **Viscosity is pinned to 1 in the whole uniqueness chain.** `Hypotheses.equation`
   (`PressureRecovery.lean:41-42`) uses the `ν ≡ 1` residual `NavierStokes/ProblemStatement.lean:82`,
   and `WholeSpaceUniqueness.lean:41` passes `navierStokesResidual 1`, while the repo also has a
   `ν`-parametrised residual (`R3/ProblemStatement.lean:57`).
   *Question:* does the top-level theorem in `R3/Theorem.lean` claim anything for `ν ≠ 1`, and if
   so where is the scaling reduction? *Settles it:* read `R3/Theorem.lean` +
   `R3/ParabolicScaling.lean` (outside my scope; hand to the worker owning Theorem.lean).
3. **Junk-value use at frequency zero.** `rieszSymbol i j 0 = -(0·0)/0 = 0` by Lean's `div_zero`
   (`ComparisonFourierSetup.lean:17-18`), and `rieszSymbol_mul_norm_sq`
   (`RieszSymbolRegularity.lean:50-54`) proves the multiplier identity at `ξ = 0` by
   `simp [hξ, rieszSymbol]`, i.e. `0 = 0`. This is used *pointwise* in
   `rieszTest_laplacianCLM` (`RieszTestOperators.lean:246-269`).
   *Question:* is the pointwise (not just a.e.) multiplier identity still the correct operator?
   My reading: yes — both sides vanish at `ξ = 0` and `{0}` is null for every integral used,
   so nothing is smuggled. Flagged only because it is a junk-value site by construction.
4. **Recovery holds only on the open interval `Ioo 0 T`** (`PressureRecovery.lean:392`, and the
   temporal fundamental lemma can do no better). *Question for the closure worker:* does
   `WholeSpaceComparisonClosure.eq_of_pressure_flux_bound` ever need the pressure identity at
   `t = 0` or `t = T`? If it integrates the differential inequality over `Icc`, the endpoint
   null set is harmless; if it evaluates at `T`, it must go through continuity.
   *Settles it:* the flux hypothesis of that theorem is stated on `Ioo 0 T`
   (`WholeSpaceUniqueness.lean:69-70` supplies `∀ t ∈ Ioo 0 T`), which is consistent — but the
   consumer's own use of `t = T` should be re-checked in file B's scope.
5. **`Hypotheses.equation` is residual *equality*, not "both solve NS".** That is strictly weaker
   than assuming both residuals vanish, so it is a generalisation, not a defect; and the caller
   supplies it from `residual u p = f = residual v q` (`WholeSpaceUniqueness.lean:96-97`).
   Recorded so that nobody mistakes it for a hidden strengthening.

## Residue

* **No build.** Nothing here was elaborated by Lean. I verified statements, proof scripts and
  dependency structure by reading source. Any claim of the form "this proof term type-checks" is
  outside what I can assert. Mathlib names used heavily and unverifiable at this commit:
  `FourierTransform.fourierCLE`, `FourierTransform.fourierInv`, `Real.fourierInv_eq_fourier_comp_neg`,
  `tendsto_integral_exp_inner_smul_cocompact`, `SchwartzMap.toLpCLM`, `schwartz_withSeminorms`,
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, `integrable_rpow_neg_one_add_norm_sq`,
  `ContDiffOn.comp_contDiff`.
* **Skimmed, not line-by-line:** `SchwartzCompactApproximation.lean:39-175` (the seminorm tail
  estimates behind Schwartz-density), `PressureTestBounds.lean:100-230`,
  `RieszTestOperators.lean:1-240` (the `MemLp`/`L⁶` bounds on `rieszTest`, used by the flux
  worker rather than by recovery), `ComparisonTimeAverages.lean:40-300`,
  `PressureTemporalIdentity.lean:1-121`, `WeakTimeContinuity.lean` (only
  `continuousOn_pairing`'s statement was used), `CompactEnergy.integral_mul_partial`
  (the basic IBP lemma; its statement is used many times and I read its use sites, not its proof).
* **Not in my scope, therefore unchecked:** whether the recovered gradient identity is *used
  correctly* in `ActualPressureFlux.lean:58` and `PressureFlux.lean:576`, and the whole Gronwall /
  `R → ∞` closure. I only confirmed which field carries the `L³` hypothesis there.
* I did not attempt to construct a counterexample pair `(v, q)` satisfying `Hypotheses` with a
  nonzero harmonic pressure ambiguity; the `L²`-representative argument appears to exclude it, but
  a proof-side falsification attempt would need a build.
