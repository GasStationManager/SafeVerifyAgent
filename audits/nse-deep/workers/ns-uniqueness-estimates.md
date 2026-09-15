# NS uniqueness — ESTIMATE LAYER audit (worker: ns-uniqueness-estimates)

Target: `/home/gsm/.openclaw/workspace/repos/NSE` (clone of openai/NavierStokesAndEuler @ f9e8bc5).
READ-ONLY source audit. No `lake build` was run: every claim below is a statement/proof-term
reading with file:line, re-read from the original files. Docstrings are treated as authorial
claims, not evidence.

## Scope

Read LINE BY LINE (all declarations inspected, statement + full proof term/tactic script):

| file | lines | decls | how read |
|---|---|---|---|
| `NavierStokes/R3/LocalizedFluxEstimates.lean` | 267 | 22 | line-by-line, all 22 |
| `NavierStokes/R3/WeightedSobolev.lean` | 247 | 22 | line-by-line, all 22 |
| `NavierStokes/R3/CompactComparisonBounds.lean` | 157 | 9 | line-by-line, all 9 |
| `NavierStokes/R3/ComparisonFiniteEnergy.lean` | 230 | 17 | line-by-line, all 17 |
| `NavierStokes/R3/ComparisonRateBound.lean` | 150 | 3 | line-by-line, all 3 |
| `NavierStokes/R3/ComparisonYoung.lean` | 161 | 5 | line-by-line, all 5 |

Read in FULL because a scoped inequality depended on it (not in the assigned list):

| file | lines | decls | how read |
|---|---|---|---|
| `NavierStokes/R3/WeightedInterpolation.lean` | 230 | 11 | line-by-line (Hölder engine behind `transport_flux_bound`) |
| `NavierStokes/R3/ComparisonSetup.lean` | 56 | 11 | line-by-line (all definitions: `comparisonLpNorm`, `cutoffL6`, `dissipationRoot`, …) |

Skimmed / statement-level only (to judge whether a cited inequality is real):
`ComparisonCutoffs.lean` (272 lines, 51 decls — read defs 1–30, 60–160, 190–266),
`WholeSpaceComparisonClosure.lean:1–159` (the CONSUMER: read in full to check that the
estimate-layer lemmas are instantiated with matching constants and signs),
`GradientOperator.lean:30–55`, `LocalizedDifferenceEnergy.lean:102–132` (statement of
`difference_energy_balance` + first 30 proof lines), `WholeSpaceEnergyLimit.lean:70–92`
(statement of `eq_zero_of_weighted_rate_bound`), `PeriodicUniqueness.lean:142–151`
(`nonlinear_energy_bound`). Not read: `LocalizedTransport.lean`, `LocalizedLaplacian.lean`,
`LocalizedTensorBounds.lean`, `SmoothSobolevL6.lean` — not needed, nothing in my scope cites
them (the Sobolev step goes through Mathlib directly, see below).

Key definitions (all in `ComparisonSetup.lean`), needed to read every statement below:
- `comparisonLpNorm p f := (eLpNorm f p volume).toReal` (:28) — **toReal, hence 0 on ⊤ (junk value)**
- `l2Sq f := ∫ ‖f x‖^2` (:31); `gradientSq f x := ∑ i, ‖∂ᵢ f x‖^2` (:34)
- `weightedEnergy χ w t := ∫ χ x * ‖w(t,x)‖^2` (:37)
- `dissipationRoot φ w t := √(∫ φ^8 * gradientSq w)` (:47) = the `A` of the Young step
- `cutoffL6 φ w t := comparisonLpNorm 6 (fun x => φ x^4 • w (t,x))` (:50) = the `B`

## Per-declaration findings

### 1. `LocalizedFluxEstimates.lean` (22/22)

| decl | file:line | what the statement says (my words) | actual proof mechanism | verdict |
|---|---|---|---|---|
| `coupling_integrable` | :26 | `χ·⟪w, (∇u)w⟫` is integrable when χ is continuous with compact support, u is C¹, w continuous | continuity × compact support (`integrable_cutoff_mul`) | OK |
| `neg_coupling_le_weightedEnergy` | :37 | `-(∫ χ ⟪w,(∇u)w⟫) ≤ G · weightedEnergy χ w t` given `∀x ‖∇u(t,x)‖ ≤ G`, `χ ≥ 0`, χ cont. cpt. supp., u C¹, w cont. | `integral_mono` against the pointwise Cauchy–Schwarz/operator-norm bound `PeriodicUniqueness.nonlinear_energy_bound` (:142–151: `-⟪w,Aw⟫ ≤ ‖A‖‖w‖²` via `abs_real_inner_le_norm` + `le_opNorm`), then `nlinarith` with `χ ≥ 0`. Both integrability side conditions supplied (`coupling_integrable`, `integrable_weighted_energy`) | OK |
| `fderiv_cutoff_eight` | :59 | `∇(φ^8) = 8φ^7 ∇φ` | chain rule `hasDerivAt_pow` | OK |
| `norm_fderiv_cutoff_eight_apply_le` | :66 | `‖∇(φ^8)(x)[z]‖ ≤ 8L φ(x)^6 ‖z‖` when `0≤φ≤1`, `‖∇φ‖≤L` | operator norm + `φ^7 ≤ φ^6` (from φ ≤ 1) — **the drop from 7 to 6 powers is exactly what makes the weight pair with `cutoffL6 = ‖φ^4 w‖₆` (needs φ^6 = (φ²)³)** | OK |
| `transport_flux_bound` | :90 | Given φ C¹ compactly supported, `0≤φ≤1`, `‖∇φ‖≤L`, `w=u−v ∈ L²`, u,v continuous, and `hvanish : ∀x, ∇(φ^8)(x)[u(t,x)] = 0`: the integrand `‖w‖²·∇(φ^8)[v]` is integrable and `|∫ ‖w‖² ∇(φ^8)[v]| ≤ 8L · ‖w(t,·)‖_{L²}^{3/2} · cutoffL6 φ (u−v) t ^{3/2}` | (a) `hswitch` (:107): `∇(φ^8)[v] = −∇(φ^8)[w]` using linearity and `hvanish`; (b) pointwise `‖w‖²·‖∇(φ^8)[w]‖ ≤ 8L φ^6 ‖w‖³`; (c) `norm_integral_le_of_norm_le` + `integral_const_mul`; (d) the L³ interpolation `∫ φ^6‖w‖³ ≤ ‖w‖₂^{3/2}‖φ⁴w‖₆^{3/2}` imported from `WeightedInterpolation.cutoff_transport_bound` (:195) | OK |
| `continuous_laplacian` | :137 | Laplacian of a C^∞ scalar is continuous | sum of second partials | OK |
| `laplacian_flux_bound` | :145 | `|∫ ‖w‖² Δχ| ≤ K‖w‖_{L²}²` when `‖Δχ‖ ≤ K` and `w ∈ L²` | `integral_mono`/`norm_integral_le_of_norm_le` + `lpNorm_two_sq_eq_l2Sq` (needs `MemLp`, supplied) | OK |
| `baseWeight`, `_smooth`, `_hasCompactSupport` | :167,:169,:172 | the unscaled weight is `baseCutoff^8`, smooth, compactly supported | delta + `HasCompactSupport.comp_left` | OK |
| `exists_weight_second_derivative_bound` | :176 | ∃ C>0 bounding `‖D²baseWeight‖` everywhere | compact support + continuity of `iteratedFDeriv` ⇒ `exists_bound_of_continuous`; then `max 1 C` | OK (real bound, not a postulate) |
| `weightSecondDerivativeConstant` (+`_pos`, `_le`) | :184,:186,:189 | `Classical.choose` of the above; positive; and it really bounds `‖D²baseWeight‖` | `Classical.choose_spec` — **the spec carries the inequality, so this is a derived constant, not an axiom** | OK |
| `weightDilation`, `norm_weightDilation_le` | :193,:196 | `x ↦ x/R` has operator norm ≤ 1/R | `opNorm_le_bound` | OK |
| `weight_iteratedFDeriv_two_le` | :205 | `‖D²(weight R)(x)‖ ≤ weightSecondDerivativeConstant / R²` | `iteratedFDeriv_comp_right` + multilinear composition norm + `(R⁻¹)²` | OK (genuine R⁻² scaling) |
| `weight_second_fderiv_le` | :227 | same in `fderiv (fderiv …)` form | `norm_iteratedFDeriv_fderiv` | OK |
| `weightLaplacianConstant` (+`_pos`) | :237,:239 | `3 ×` the second-derivative constant | definition | OK |
| `weight_laplacian_le` | :242 | `‖Δ(weight R)(x)‖ ≤ weightLaplacianConstant / R²` | triangle inequality over 3 coordinates, each `≤ C/R²` | OK |
| `weight_laplacian_flux_bound` | :258 | For `R>0` and `w(t,·) ∈ L²`: the Laplacian flux is integrable and `|∫ ‖w‖² Δ(weight R)| ≤ (weightLaplacianConstant/R²)·‖w(t,·)‖_{L²}²` | direct instantiation of `laplacian_flux_bound` with `weight_laplacian_le` | OK |

**Answer to question 1.** All three named inequalities are honestly proved, with real constants:
- `neg_coupling_le_weightedEnergy` (:37–56) — Cauchy–Schwarz + operator norm, pointwise then `integral_mono`; both integrability hypotheses are *proved*, not assumed away. Nothing junk: the integrals are Bochner integrals of integrable functions (integrability certificates at :44,:45).
- `weight_laplacian_flux_bound` (:258–265) — explicit constant `3·C_{D²}` and honest `R⁻²`; the `MemLp … 2` hypothesis is the only integrability input and it is genuinely needed for `lpNorm_two_sq_eq_l2Sq`.
- `transport_flux_bound` (:90–135) — the exponents are exactly what Hölder + Sobolev gives.
  Bookkeeping check I redid by hand: `‖w‖³φ^6 = ‖φ²w‖³`; Hölder with `1/3 = 1/(2/(1/2)) + 1/(6/(1/2)) = 1/4 + 1/12` gives `‖φ²w‖₃ ≤ ‖w‖₂^{1/2}‖φ⁴w‖₆^{1/2}`, cube ⇒ `∫φ^6‖w‖³ ≤ ‖w‖₂^{3/2}‖φ⁴w‖₆^{3/2}`. That is literally `WeightedInterpolation.cutoff_transport_bound` (:195–228), proved from Mathlib's `eLpNorm'_le_eLpNorm'_mul_eLpNorm'` (`WeightedInterpolation.lean:56`) — a real Hölder, not a postulate. Combined with `L = derivativeConstant 1 / R` (`ComparisonCutoffs.lean:190`) the closure instantiates it as `(8·C₁·M^{3/2})/R · B^{3/2}` (`WholeSpaceComparisonClosure.lean:118–133`), i.e. exactly the advertised `M^{3/2}B^{3/2}/R`. Confirmed shape.
  Note the exponents `^(3/2 : ℝ)` are `Real.rpow` (real exponent), and bases are `comparisonLpNorm … ≥ 0`, so no `rpow`-of-negative surprises.

### 2. `WeightedSobolev.lean` (22/22)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `sobolevConstant` | :25 | `(eLpNormLESNormFDerivOfEqInnerConst volume 2 : ℝ)` — **Mathlib's own** Sobolev constant | definition (coercion of an `ℝ≥0`) | OK |
| `sobolevConstant_nonneg` | :28 | `0 ≤ sobolevConstant` | `NNReal.coe_nonneg` | OK |
| `memLp_of_compact` | :32 | continuous + compact support ⇒ `MemLp` at every `p` (incl. ∞) | Mathlib | OK |
| `lpNorm_six_le` | :39 | for C¹ compactly supported `f`: `‖f‖₆ ≤ sobolevConstant · ‖Df‖₂` | **Mathlib `eLpNorm_le_eLpNorm_fderiv_of_eq_inner`** with `finrank ℝ Space = 3`, `p=2`, `p'=6`; finiteness of the RHS proved so that `ENNReal.toReal_mono` is legitimate | OK — the Sobolev inequality is DERIVED |
| `hasCompactSupport_cutoff_pow_smul`, `memLp_cutoff_pow_smul` | :55,:63 | `φ^n • w` is compactly supported / in every `Lᵖ` even if `w` is not | compact support of `φ^n` | OK |
| `fderiv_cutoff_four`, `norm_fderiv_cutoff_four_le` | :72,:79 | `∇(φ⁴w) = φ⁴∇w + 4φ³(∇φ)⊗w`, with the norm bound | product rule + `norm_smulRight_apply` | OK |
| `cutoffGradientAmplitude` (+ 5 lemmas) | :103–133 | `φ⁴√(gradientSq w)`, nonneg, continuous, compactly supported, in every `Lᵖ`, and its square is `φ^8 gradientSq w` | routine | OK |
| `integrable_weighted_gradientSq` | :136 | `φ^8·gradientSq w` is integrable (local regularity only) | continuity × compact support | OK — dissipation integral is genuinely finite, not a junk 0 |
| `lpNorm_cutoffGradientAmplitude` | :144 | its `L²` norm equals `√(∫ φ^8 gradientSq w)` = `dissipationRoot` | `lpNorm_two_eq_sqrt_l2Sq` (with `MemLp`) | OK |
| `norm_fderiv_cutoff_four_le_amplitude` | :153 | `‖∇(φ⁴w)‖ ≤ 3·amplitude + 4L‖w‖` | `GradientOperator.norm_fderiv_le_three_mul_sqrt_gradientSq` (`GradientOperator.lean:39`, proved by `opNorm_le_bound` + coordinate expansion; factor 3 = dimension, honest) + `φ³ ≤ 1` | OK |
| `lpNorm_fderiv_cutoff_four_le` | :177 | `‖∇(φ⁴w)‖₂ ≤ 3√(∫φ^8 gradientSq w) + 4L‖w‖₂` | `lpNorm_mono_of_norm_le` + triangle inequality, all with `MemLp` certificates | OK |
| `weightedSobolevConstant` (+`_pos`) | :210,:212 | `4·sobolevConstant + 1` | definition; `positivity` | OK |
| `weighted_sobolev` | :219 | `‖φ⁴w‖₆ ≤ (4S+1)(√(∫φ^8|∇w|²) + L‖w‖₂)` | composes `lpNorm_six_le` (Mathlib Sobolev) with the derivative bound; `nlinarith` closes the constant arithmetic | OK |
| `cutoffL6_le` | :237 | the same in the closure's notation: `cutoffL6 φ w t ≤ weightedSobolevConstant·(dissipationRoot φ w t + L·‖w(t,·)‖₂)` | literally `weighted_sobolev` (definitional unfolding) | OK |

**Answer to question 2.** The Sobolev inequality is **DERIVED, not assumed**. `cutoffL6_le`
(`WeightedSobolev.lean:237`) reduces to `weighted_sobolev` (:219), which reduces to `lpNorm_six_le`
(:39), which is Mathlib's `eLpNorm_le_eLpNorm_fderiv_of_eq_inner` specialised to `ℝ³, p=2, p'=6`
(:44–45, with `finrank = 3` discharged at :43). `weightedSobolevConstant := 4 * sobolevConstant + 1`
(:210) where `sobolevConstant` is *Mathlib's* `eLpNormLESNormFDerivOfEqInnerConst` (:25) — i.e. it is
not a postulated `∃ C, 0 < C`; the theorem that it multiplies is proved. The only `Classical.choose`
constants in my scope (`derivativeConstant`, `weightSecondDerivativeConstant`) also come with
specification lemmas that carry the *inequality*, not just positivity
(`ComparisonCutoffs.lean:143–158`, `LocalizedFluxEstimates.lean:176–191`). **No finding here.**

### 3. `ComparisonYoung.lean` (5/5) and `ComparisonRateBound.lean` (3/3)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `exists_rpow_absorption` | `ComparisonYoung:23` | `p < 2`, `C,δ ≥ 0/>0` ⇒ ∃D≥0 ∀A≥0 `C·A^p ≤ δA² + D` | split at `K = max 1 b` where `b` is from `tendsto_rpow_atTop`; small-A case uses monotonicity, large-A case uses `C ≤ δA^{2−p}` | OK |
| `exists_shifted_rpow_absorption` | :57 | same with `(A+1)^p` | apply previous at `A+1`, `(A+1)² ≤ 2A²+2` | OK |
| `exists_scaled_shifted_rpow_absorption` | :71 | `C/R·(A+1)^p ≤ δA² + D/R` for all `R ≥ 1` | multiply by `R⁻¹ ≤ 1`; **δ coefficient is not degraded and D keeps the full `1/R`** | OK |
| `cutoff_expression_le` | :89 | the three-term cutoff remainder at `x = A+R⁻¹` is `≤ 4C/R·(A+1)^{3/2}` for `R ≥ 1` | `R^{−2}, R^{−7/4} ≤ R⁻¹`; `(A+R⁻¹) ≤ (A+1)`; `x^{1/2}+1 ≤ 2(A+1)^{1/2}`; `(A+1)^{1/2}(A+1) = (A+1)^{3/2}` | OK |
| `exists_cutoff_absorption` | :148 | ∃D≥0 ∀A≥0 ∀R≥1: three-term remainder `≤ δA² + D/R` | previous two, with `p = 3/2 < 2` | OK — this is a real Young absorption |
| `rpow_le_square_mul_rpow` | `RateBound:17` | `B ≤ Qx`, `Q ≥ 1`, `0≤p≤2` ⇒ `B^p ≤ Q²x^p` | `rpow` monotonicity in base and exponent | OK |
| `exists_uniform_flux_absorption` | :31 | ∃D≥0 ∀R≥1 ∀A,B≥0 with `B ≤ S(A + M/R)`: `C1/R·B^{3/2} + C2·[(B^{1/2}+1)(A/R+1/R²) + R^{−7/4}B^{3/4}] ≤ δA² + D/R` | replaces every `B^p` by `Q²(A+R⁻¹)^p` with `Q = max 1 (S·max 1 M)`, then `exists_cutoff_absorption` | OK |
| `exists_uniform_rate_bound` | :127 | ∃D≥0 ∀R≥1 ∀A,B≥0 with `B ≤ S(A+M/R)`, ∀E,E',G: from `(1/2)E' + A² ≤ G·E + C0/R² + C1/R·B^{3/2} + C2·envelope` conclude `E' ≤ 2G·E + D/R`, with `D = 2(C0+D_flux)` | `δ = 1/2`; `C0/R² ≤ C0/R` (uses `R ≤ R²`, i.e. `R ≥ 1`); `nlinarith only [henergy, hbound, hC0radius, sq_nonneg A]` | OK |

**Answer to question 3.** The algebra is valid for **all** `R ≥ 1` and **all** `A,B ≥ 0` (the only
extra input is the Sobolev link `B ≤ S(A + M/R)`, supplied by `cutoffL6_le`), and the dissipation is
absorbed with the **correct sign**. Reconstruction: the hypothesis has `A²` (the dissipation) on the
LEFT with a `+`; the flux bound gives `flux ≤ (1/2)A² + D_flux/R`; hence
`(1/2)E' + A² ≤ G E + C0/R + (1/2)A² + D_flux/R`, so `(1/2)E' ≤ G E + (C0+D_flux)/R − (1/2)A²`, and
the leftover `−(1/2)A² ≤ 0` is DROPPED (valid weakening) giving `E' ≤ 2G E + 2(C0+D_flux)/R`. The
returned constant is exactly `2*(C0 + D)` (:139) — matches. No term is dropped with the wrong sign,
and `δ = 1/2 < 1` is what makes the absorption legal. `0 ≤ C0,C1,C2,S,M` are the only sign
hypotheses; `G` and `E` are unconstrained in sign (docstring claim at :8–9 is accurate).
Cross-check of the instantiation (`WholeSpaceComparisonClosure.lean:54–66, 140–155`): `C0 =
weightLaplacianConstant·M²/2`, `C1 = 4·derivativeConstant 1·M^{3/2}`, `S = weightedSobolevConstant`,
`M_param = derivativeConstant 1 · M`; the energy identity supplied is
`LocalizedDifferenceEnergy.difference_energy_balance` (:102–121) whose LHS is
`(1/2)·weightedEnergyRate + weightedDissipation` — dissipation positive on the left, as required, and
`A² = weightedDissipation` is proved at closure `:87` via `Real.sq_sqrt` with a nonnegativity lemma.
The factors `1/2` on the Laplacian and transport fluxes in the identity match the halving of `C0`
and of `8·derivativeConstant 1` into `C1 = 4·…`. Consistent; no coefficient laundering found.

### 4. `CompactComparisonBounds.lean` (9/9)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `hasCompactSupport_slice` | :24 | if every slice's tsupport sits in one compact `K`, each slice is compactly supported | closed subset of a compact set | OK |
| `exists_gradient_bound` | :33 | ∃`G ≥ 0` with `‖∇u(t,x)‖ ≤ G` for all `t ∈ [0,T]` and **all** `x ∈ ℝ³` | on `K`: `PeriodicUniqueness.exists_gradient_bound` (compactness of `Icc × K` + continuity); off `K`: `fderiv_of_notMem_tsupport` gives `∇u = 0` and `0 ≤ G` | OK — the "all x" upgrade is honest (derivative genuinely vanishes off the support) |
| `memLp_three_slice` | :49 | each slice is in `L³` | continuity + compact support | OK |
| `continuousOn_integral_norm_cube` | :58 | `t ↦ ∫‖u(t,x)‖³` is continuous on `[0,T]` | `CompactTimeIntegral.continuousOn_integral` with the off-support vanishing supplied | OK |
| `lpNorm_three_eq_integral_norm_cube_rpow` | :71 | for `f ∈ L³`, `comparisonLpNorm 3 f = (∫‖f‖³)^{1/3}` | `MemLp.eLpNorm_eq_integral_rpow_norm` + `toReal_ofReal` (nonnegativity discharged) — **the `MemLp` hypothesis is what excludes the toReal junk value** | OK |
| `exists_lpNorm_three_bound` | :85 | ∃`U ≥ 0`: for every `t ∈ [0,T]`, the slice is in `L³` AND `‖u(t,·)‖₃ ≤ U` | sup of a continuous function on the compact `Icc`, then `(max C 0)^{1/3}`; `MemLp` returned alongside the bound | OK |
| `weight_fderiv_eq_zero_of_norm_lt` | :102 | `‖x‖ < R ⇒ ∇(weight R)(x) = 0` | `weight R ≡ 1` on a neighbourhood (open set `‖·‖ < R`), `Filter.EventuallyEq.fderiv_eq` | OK |
| `exists_radius_weight_derivative_zero` | :112 | ∃`R₀ ≥ 1` such that **for all `R ≥ R₀`** and all `t ∈ [0,T]`, `x`: `∇(weight R)(x)[u(t,x)] = 0` | `K` bounded by `C`; take `R₀ = max 1 (C+1)`; if `x ∈ K` then `‖x‖ ≤ C < R` ⇒ previous lemma ⇒ `0 [u] = 0` (`rfl`); else `u(t,x) = 0` off the tsupport ⇒ `map_zero` | OK — **not** a for-all-R statement |
| `uniformFiniteEnergy_of_compact_slab` | :133 | smooth on the slab + one compact spatial support ⇒ `UniformFiniteEnergy (Icc 0 T) u` | `t ↦ ∫‖u‖²` continuous on a compact `Icc` ⇒ bounded by `max C 0`; `MemLp 2` from continuity + compact support; the energy constant is `(1/2)max C 0` | OK |

**Answer to question 4.** All four really follow from compactness + continuity, with the `MemLp`
certificates returned rather than assumed. On the specific worry:
`exists_radius_weight_derivative_zero` (:112–129) is **correctly quantified** — it asserts existence
of a threshold `R₀ = max 1 (C+1)` (where `C` bounds `K`) and the vanishing only for `R ≥ R₀`. It is
NOT the statement that a flux term vanishes for all `R`. Two honest halves: inside `K` the weight is
on its plateau (`weight ≡ 1` on the ball of radius `R`, `ComparisonCutoffs.lean:137`), outside `K`
the *candidate* vanishes. The consumer respects the quantifier: the closure takes it as
`hvanish : ∀ R ≥ R₀ …` (`WholeSpaceComparisonClosure.lean:47`) and the limit lemma only ever uses
`R ≥ max 1 R₀` (`WholeSpaceEnergyLimit.lean:75`). I also checked the cutoff is non-degenerate, so
this is not a vacuity trick: `baseBump : ContDiffBump 0 = ⟨1, 2, …⟩` (`ComparisonCutoffs.lean:25`)
is `1` on the unit ball and `0` outside radius 2, with `derivativeConstant 1 > 0` and
`‖∇(cutoff R)‖ ≤ derivativeConstant 1 / R` (:190) — the transport term is genuinely `O(1/R)` and
genuinely nonzero, i.e. the argument really has to beat it by dissipation.

### 5. `ComparisonFiniteEnergy.lean` (17/17)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `squareIntegrableAtTime_iff_memLp` | :24 | with slice measurability, `SquareIntegrableAtTime u t ↔ MemLp (u(t,·)) 2` | `memLp_two_iff_integrable_sq_norm` | OK |
| `continuous_slice_of_continuousOn` | :31 | joint continuity on `times ×ˢ univ` ⇒ each slice continuous | composition, `continuousAt` | OK |
| `l2Sq_nonneg` | :42 | `0 ≤ l2Sq f` with no integrability | `integral_nonneg` (true also when the Bochner integral is the junk `0`) | OK (statement is honest about needing nothing) |
| `norm_sub_sq_le_twice` | :47 | `‖a−b‖² ≤ 2(‖a‖²+‖b‖²)` | `nlinarith` | OK |
| `squareIntegrableAtTime_sub` | :53 | difference of two square-integrable slices is square integrable | `MemLp.sub` — **DERIVED** | OK |
| `l2Sq_sub_le` | :64 | `l2Sq (f−g) ≤ 2(l2Sq f + l2Sq g)` for `f,g ∈ L²` | `integral_mono` with integrability certificates for all three integrands | OK |
| `uniformFiniteEnergy_sub` | :80 | if `u,v` have uniform finite energy (and measurable slices) then so does `u−v`, with `E = 2(Eu+Ev)` | the two lemmas above, `linarith` | OK — **derives** the difference's integrability |
| `uniformFiniteEnergy_sub_of_continuousOn` | :101 | same with continuity supplying measurability | previous | OK |
| `uniformFiniteEnergy_l2Sq_bound` | :111 | uniform finite energy ⇒ ∃`M ≥ 0` with `l2Sq(u(t,·)) ≤ M` and square integrability at each `t` | `kineticEnergy = (1/2)l2Sq`, so `M = 2E` | OK |
| `norm_component_mul_le_sq`, `tensorDiff_norm_le` | :124,:131 | `‖aᵢaⱼ‖ ≤ ‖a‖²`; `‖tensorDiff‖ ≤ ‖u‖² + ‖v‖²` | `PiLp.norm_apply_le` + triangle | OK |
| `tensorDiff_aestronglyMeasurable` | :139 | components measurable from slice measurability | coordinate projections are continuous linear | OK |
| `tensorDiff_integrable` | :150 | each component of `u⊗u − v⊗v` is in `L¹` when both slices are in `L²` | `Integrable.mono'` against `‖u‖²+‖v‖²` | OK — **DERIVED**, this is the honest `L²·L² → L¹` step |
| `tensorDiff_norm_integral_le` | :160 | `∫‖tensorDiff‖ ≤ l2Sq u + l2Sq v` | `integral_mono` + `integral_add` | OK |
| `uniformFiniteEnergy_tensorDiff_bound` | :175 | one `M` for all `t` and all `i,j`, with integrability | previous lemmas | OK |
| `uniformFiniteEnergy_lpNorm_two_bound` | :197 | ∃`M ≥ 0`: for each `t`, `MemLp (u(t,·)) 2` AND `comparisonLpNorm 2 (u(t,·)) ≤ M` | `M = √(2E)`, `lpNorm_two_eq_sqrt_l2Sq` needs `MemLp` — **membership is returned with the bound, closing the toReal-junk loophole** | OK |
| `uniformFiniteEnergy_tensorDiff_lpNorm_one_bound` | :214 | same in `comparisonLpNorm 1` form | `lpNorm_one_eq_integral_norm` with the integrability certificate | OK |

**Answer to question 5.** All three **DERIVE** the difference's integrability from the two fields'
integrability; nothing is assumed. `uniformFiniteEnergy_sub` (:80) goes through
`squareIntegrableAtTime_sub` (:53) = `MemLp.sub`, and the constant is the honest `2(Eu+Ev)`.
`uniformFiniteEnergy_lpNorm_two_bound` (:197) and
`uniformFiniteEnergy_tensorDiff_lpNorm_one_bound` (:214) both *return* the `MemLp`/`Integrable`
certificate next to the numeric bound, which is exactly the discipline that prevents the
`comparisonLpNorm = (…).toReal = 0` junk value from making a bound vacuous. The `L¹` tensor bound is
the elementary `‖u⊗u − v⊗v‖ ≤ ‖u‖² + ‖v‖²`, which is true but *lossy* — it does not use the
difference structure at all (see Escalation 2).

## Kernel-risk

Repo-wide grep over my scope (`LocalizedFluxEstimates`, `WeightedSobolev`, `CompactComparisonBounds`,
`ComparisonFiniteEnergy`, `ComparisonRateBound`, `ComparisonYoung`, plus `WeightedInterpolation`,
`ComparisonCutoffs`, `ComparisonSetup`) for
`decide|native_decide|macro|elab|syntax|set_option|axiom|unsafe|partial |termination_by|WellFounded|\.rec\b|sorry|Nat\.(pow|div|mod|gcd)`:

- `native_decide`: **0**
- custom metaprogramming (`macro`/`elab`/`syntax`/`set_option`): **0**
- `axiom` / `sorry` / `unsafe` / `partial`: **0**
- `termination_by` / `WellFounded.fix` / explicit `.rec`: **0**
- `decide`: **2**, both trivial and both only proving a `≠ 0` side condition for `zero_pow`:
  `CompactComparisonBounds.lean:68` (`(by decide : (3 : ℕ) ≠ 0)`) and
  `CompactComparisonBounds.lean:145` (`(by decide : (2 : ℕ) ≠ 0)`). These reduce `Nat.decEq 3 0` /
  `Nat.decEq 2 0` on single-digit literals — no bignum, no `Nat.pow/div/mod/gcd`, negligible kernel work.
- Huge numerals: none. The largest literals in scope are `8` (weight power), `6`, `4`, `3`, `2`,
  `-7/4`, `12/5`, `3/2` (the last four as `ℝ`/`ℝ≥0∞` exponents handled by `norm_num`, not `decide`).
- Structure-eta `rfl` on recursive data: none. The one `rfl` worth naming is
  `CompactComparisonBounds.lean:125` (`(0 : Space →L[ℝ] Space) (u (t,x)) = 0`) — a `ContinuousLinearMap`
  zero application, trivial.
- All non-Mathlib constants in scope are `Classical.choose` of an `∃ C, 0 < C ∧ ∀ x, bound`
  (`ComparisonCutoffs.lean:143`, `LocalizedFluxEstimates.lean:176`): noncomputable but kernel-cheap
  and, importantly, their `choose_spec` carries the inequality.

**Verdict: no kernel risk in this layer.**

## Escalations

Ranked. None of these is a proof-breaking defect that I could establish from source; the estimate
layer is, as far as I can read it, honest mathematics. The items are where an expert should look.

1. **(Highest) The pressure-flux envelope is a POSTULATED SHAPE that my layer takes on faith.**
   `WholeSpaceComparisonClosure.lean:25-27` defines
   `pressureEnvelope R A B = (B^{1/2} + 1)(A/R + 1/R²) + R^{−7/4}B^{3/4}`, and
   `ComparisonRateBound.exists_uniform_flux_absorption` (`ComparisonRateBound.lean:31–37`) is built
   to absorb **exactly** those two monomials and nothing else. Question an expert must answer: does
   `PressureFlux.exists_uniform_actual_pressure_flux_bound` really produce this envelope with these
   exponents (in particular the `R^{−7/4}B^{3/4}` term and the additive `+1` inside the first
   factor), for the *competitor* `v` whose only hypotheses are smooth/div-free/NS/`v(0,·)=0`/uniform
   finite energy? What would settle it: read `PressureFlux.lean` + `PressureRecovery.lean` and check
   (a) the exponents match `pressureEnvelope` literally, (b) no hypothesis on `v` beyond the four is
   used, (c) `CP` does not secretly depend on `R`. My layer proves the absorption is valid for any
   `CP ≥ 0` uniform in `R`, so the whole load sits on the uniformity of `CP`. (Owner: pressure worker.)
2. **The `L¹` tensor bound throws away the difference structure.**
   `ComparisonFiniteEnergy.lean:160` bounds `∫‖uᵢuⱼ − vᵢvⱼ‖` by `l2Sq u + l2Sq v`, i.e. by the SUM of
   energies, not by anything that is small when `u ≈ v`. That is fine for a *finiteness/uniformity*
   input, and I traced it into the pressure layer rather than the energy inequality, so it is not
   used where smallness would be needed. Question: is `uniformFiniteEnergy_tensorDiff_lpNorm_one_bound`
   ever used at a place where a *difference-small* bound is required (e.g. inside a Gronwall factor)?
   Settle by grepping its call sites in the pressure modules; if it only feeds a uniform-in-`R`
   constant, no issue.
3. **`comparisonLpNorm` is `toReal`-based, so upper bounds on it are vacuous off `MemLp`.**
   `ComparisonSetup.lean:28`. In my scope every producer returns `MemLp` beside the bound
   (`ComparisonFiniteEnergy.lean:197,214,85`) and every consumer that needs realness re-derives it
   (`LocalizedFluxEstimates.lean:165`, `WeightedSobolev.lean:148`, `CompactComparisonBounds.lean:71`),
   so I found no exploit. Question for an expert: is there any *hypothesis* of the form
   `comparisonLpNorm p f ≤ M` anywhere upstream of `candidate_global_agrees_before_one` that is NOT
   accompanied by a `MemLp p f` hypothesis or certificate? Settle by grepping every occurrence of
   `comparisonLpNorm` in a hypothesis position (in the closure, `hM` at
   `WholeSpaceComparisonClosure.lean:40` is paired with `hwu` at `:39` — this one is clean).
4. **`G` (the candidate's uniform gradient bound) is the Gronwall exponent, and it must stay finite as
   `T ↑ 1`.** `CompactComparisonBounds.lean:33` produces `G` from compactness of `Icc 0 T × K`; the
   closure uses `K = 2G` (`WholeSpaceComparisonClosure.lean:68`) and the Gronwall factor is
   `exp(K T)` (`WholeSpaceEnergyLimit.lean:81`). This is fine for each fixed `T < 1` but the
   candidate blows up at `t = 1`. Question: does `candidate_global_agrees_before_one`
   (`WholeSpaceUniqueness.lean:104`) really only ever instantiate a fixed `T < 1` per point (so
   `G = G(T)` blowing up is harmless), or is a `T → 1` limit taken with a `T`-independent constant?
   Settle by reading `WholeSpaceUniqueness.lean:30–120`. (Owner: uniqueness-top worker.)
5. **`uniformFiniteEnergy_of_compact_slab` shows the *candidate* trivially satisfies the competitor
   hypothesis — check the argument is not symmetric-by-accident.** `CompactComparisonBounds.lean:133`.
   The competitor `v` gets `UniformFiniteEnergy` only by hypothesis, and the estimate layer uses `v`
   only through `hw2 : MemLp (u−v)(t,·) 2` and continuity (`LocalizedFluxEstimates.lean:90–96`) — no
   bound on `∇v`, no decay of `v`, which is the honest and impressive part of the design. Question:
   is `hvanish` (needing compact support of **`u`** only) the *only* asymmetry? If some upstream
   module also needs compact support of `v`, the theorem would be much weaker than its name.
   Settle by checking that no hypothesis of `eq_of_pressure_flux_bound`
   (`WholeSpaceComparisonClosure.lean:32–52`) constrains `v` beyond smooth/div-free/NS/`L²`.
   From the statement I read, none does.

## Residue

- **No `lake build`.** I could not check that the files compile, that `Classical.choose` constants
  elaborate, or that `nlinarith`/`convert!` steps actually close (e.g.
  `ComparisonRateBound.lean:122,148`, `WholeSpaceComparisonClosure.lean:153–155`). A `nlinarith only`
  that fails would be a build error, not a silent hole, so this is a compile-risk, not a soundness-risk
  — but it is unverified.
- **Mathlib lemma semantics assumed.** I took `eLpNorm_le_eLpNorm_fderiv_of_eq_inner`,
  `eLpNorm'_le_eLpNorm'_mul_eLpNorm'`, `MemLp.eLpNorm_eq_integral_rpow_norm`,
  `ContinuousMultilinearMap.norm_compContinuousLinearMap_le` and
  `HasCompactSupport.iteratedFDeriv` at their names/signatures without opening Mathlib source. If
  any of these has different hypotheses than I assume, the Sobolev and Hölder steps would need
  re-reading. The elaborated argument lists at the call sites (`WeightedSobolev.lean:44–45`,
  `WeightedInterpolation.lean:56–61`) look consistent with the standard statements.
- **Not audited (out of scope, other workers):** `PressureFlux.lean`, `PressureRecovery.lean`
  (Escalation 1), `LocalizedDifferenceEnergy.lean` beyond the statement of
  `difference_energy_balance` (:102–121) — i.e. I did **not** verify the integration-by-parts energy
  identity itself, only that my estimates plug into it with matching signs and coefficients;
  `WholeSpaceEnergyLimit.lean` / `ComparisonGronwall.lean` beyond the statement of
  `eq_zero_of_weighted_rate_bound` (:70–77) — the `R → ∞` monotone-limit step and the Gronwall
  integration are unaudited by me.
- **`ComparisonCutoffs.lean` read selectively** (defs + plateau/derivative lemmas, ~120 of 272 lines,
  51 decls of which I inspected ~20). The pieces I depended on
  (`baseBump = ⟨1,2,…⟩`, `cutoff_eq_one`, `cutoff_fderiv_le`, `weight_eq_one`,
  `cutoff_hasCompactSupport`) I read in full.

## Verdict counts (declarations examined line-by-line, 78 total)

- OK: 78
- UNCLEAR: 0
- KERNEL-RISK: 0 (2 trivial `decide` noted, both harmless)
- SUSPICIOUS: 0

I looked specifically for the six failure modes and did not find them in this layer: no vacuous or
trivially-true statement, no name over-claiming its statement, no hypothesis satisfiable only by the
zero field, no unsatisfiable hypothesis, no `0 ≤ C`-style empty estimate (the constants are
`Classical.choose` of *proved* bounds), no junk-value exploitation (every `Lᵖ` bound travels with its
`MemLp`; every `∫` bound travels with its `Integrable`), no integrability assumed where it could be
derived, and no circularity (the dependency order is
`ComparisonYoung → ComparisonRateBound → WholeSpaceComparisonClosure` and
`WeightedInterpolation/WeightedSobolev → LocalizedFluxEstimates`, all strictly downhill).
