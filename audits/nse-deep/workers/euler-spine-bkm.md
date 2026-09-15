# euler-spine-bkm — BKM sub-chain of the ordinary Euler blowup claim

Auditor: read-only worker (`euler-spine-bkm`). Repo under audit: `/home/gsm/.openclaw/workspace/repos/NSE`
(clone of `openai/NavierStokesAndEuler` @ `f9e8bc5`, Lean 4 v4.34.0-rc2, Mathlib rev `85e3a25e`).
No build was possible (disk full) — this is SOURCE-LEVEL reading. Nothing under the repo was modified.
Mathlib statements were checked against
`raw.githubusercontent.com/leanprover-community/mathlib4/85e3a25e006c35636f0e53b0e9296caca2685bc0/...`.

## Scope

Entry point `Euler/OrdinaryEulerBKM.lean` (39 lines) read in full, then every cited name chased into its
defining file, then one more level for load-bearing steps.

READ IN FULL (statements + proof terms):
`Euler/OrdinaryEulerBKM.lean` (3 decls), `Euler/OrdinaryBKMReduction.lean` (2), `Euler/OrdinaryLogarithmicGradient.lean` (5),
`Euler/OrdinaryMaximalVorticityIntegral.lean` (10), `Euler/OrdinaryEulerVorticity.lean` (13),
`Euler/OrdinaryMaximalVorticity.lean` (11), `Euler/OrdinaryEulerGradientControl.lean` (12),
`Euler/MeanCutoffCurlBound.lean` (12), `Euler/OrdinaryEulerLifespan.lean` (8), `Euler/OrdinaryEulerContinuation.lean` (7),
`Euler/OrdinaryEulerLogarithmicControl.lean` (7), `Euler/OrdinaryVariableGronwall.lean` (1),
`Euler/NonnegativeImproperIntegral.lean` (2), `Euler/OrdinaryVorticityCoordinates.lean` (6),
`Euler/WholeSpaceLogarithmic.lean` (4), `Euler/LogarithmicCutoffOptimization.lean` (1),
`Euler/WholeSpaceGaussianElliptic.lean` (4), `Euler/WholeSpaceGaussianHigh.lean` (1),
`Euler/OrdinaryEulerEndpoint.lean` (5), `Euler/OrdinaryEulerMaximal.lean` (lines 1–110).

SKIMMED / TARGET-READ (specific decls only): `Euler/MeanSobolevBoundedField.lean:104–124`,
`Euler/LpSmoothField.lean:31–55`, `Euler/OrdinaryEulerDifference.lean:21–55`,
`Euler/WholeSpaceGaussian.lean:104–130`, `Euler/WholeSpaceGaussianScale.lean:39–90`,
`Euler/WholeSpaceGaussianFields.lean:55–104`, `Euler/OrdinaryEulerCauchy.lean:80–123`,
`Euler/OrdinaryGradientLimit.lean:1–45`, `Euler/OrdinaryEulerKineticEnergy.lean:30–46`,
`Euler/EulerProof.lean:10830–10870` (`curl`, `partialDerivative`), `Euler/MeanVectorIdentities.lean:95–130`,
`Euler/MeanBoundaryOperator.lean:27–39`, `Euler/PacketPotentialRegularity.lean:16–23`,
`Euler/LpSmoothJetField.lean:1–40`, `Euler/PacketFiniteLifespan.lean:30–60`.

MACHINE SCAN: the transitive `import` closure of `Euler/OrdinaryEulerBKM.lean` is **927 repo files /
114,557 lines**; every line of all 927 files was regex-scanned for `sorry`, `axiom`, `native_decide`,
`set_option`, `macro`/`elab`/`syntax`/`notation`/`macro_rules`, `unsafe`, `partial`, `Acc.rec`,
`Nat.rec`/`strongRecOn`, `termination_by`/`decreasing_by`, `decide`, `Classical.choose`, `admit`.
Counts: sorry 0, axiom 0, native_decide 0, set_option 0, macro/elab/syntax 0, unsafe/partial 0,
`Acc.rec` 0, `Nat.rec` 1, `termination_by` 10, `decide` 53, `Classical.choose` 24 (see Kernel-risk).

## Per-declaration findings

Format: name — file:line — what the statement really says — actual proof mechanism — verdict.

### Entry point (`Euler/OrdinaryEulerBKM.lean`)

- `EulerOrdinarySobolev.FiniteLifespan.vorticityIntegral_unbounded` — `Euler/OrdinaryEulerBKM.lean:19` —
  for every real `G` there is `S ∈ (0, L.duration)` and `t ∈ [0,S]` with `G < (L.evolution S ..).vorticityIntegral t`.
  Proof term: `vorticity_unbounded_of_logarithmic logarithmicGradientConstant logarithmicGradientConstant_nonneg
  logarithmic_gradient_bound_solenoidal L G` (lines 22–24) — i.e. the reduction's three `variable` hypotheses
  `C`, `hC`, `hlog` are instantiated with the constant `36*splitCost`, its nonnegativity, and the **proved**
  whole-space estimate. **This is where the logarithmic hypothesis is discharged.** — OK
- `...vorticityIntegral_tendsto_atTop` — `Euler/OrdinaryEulerBKM.lean:29` — `Tendsto L.maximalVorticityIntegral
  (atTop : Filter L.Time) atTop`, with `L.Time = Ico 0 L.duration` (`Euler/OrdinaryEulerMaximal.lean:17`). Proof:
  feeds the previous theorem into `maximalVorticityIntegral_tendsto_atTop`. `L.Time` is inhabited
  (`initialTime`, `Euler/OrdinaryEulerMaximal.lean:19`, needs `duration_pos`) and linearly ordered with no
  greatest element, so `atTop ≠ ⊥` and the statement is not filter-vacuous. — OK
- `...vorticity_lintegral_eq_top` — `Euler/OrdinaryEulerBKM.lean:36` —
  `∫⁻ r in Ico 0 L.duration, ENNReal.ofReal (L.maximalVorticityDensity r) = ⊤`. Extended (lintegral) form, so
  the Bochner "non-integrable ⇒ 0" convention cannot hide divergence. — OK

### Reduction, and the use of maximality (`Euler/OrdinaryBKMReduction.lean`)

- section `variable`s `C`, `hC : 0 ≤ C`, `hlog` — `Euler/OrdinaryBKMReduction.lean:16-19` — `hlog` is exactly
  `∀ A W, A.toLp ∈ solenoidalSpace → (∀ x, ‖vectorCurl A.field x‖ ≤ W) → ∀ x, ‖fderiv ℝ A.field x‖ ≤
  C*(1+‖A.toLp‖+W*log (exp 1+tensorNorm 3 A))`. Argument order matches
  `logarithmic_gradient_bound_solenoidal` (`Euler/OrdinaryLogarithmicGradient.lean:63`) exactly. — OK
- `Evolution.gradientIntegral_of_vorticity_bound` — `Euler/OrdinaryBKMReduction.lean:23` — if the vorticity
  integral of a closed-interval evolution is `≤ G` everywhere, then `gradientIntegral t ≤
  exp (logarithmicGronwallConstant C (u₀) * (Tmax+G))`. Mechanism: `gradientIntegral_logarithmic_uniform`
  (log-Grönwall) with `W := U.vorticityNormPath`; the pointwise input is discharged by `hlog` applied to
  `U.velocity s`, `U.solenoidal s`, `U.pointwise_vorticity_le s` (line 32). **The bound depends only on
  `Tmax`, `G` and the initial datum — not on `T`** — which is what makes the uniform-in-`S` contradiction work. — OK
- `FiniteLifespan.vorticity_unbounded_of_logarithmic` — `Euler/OrdinaryBKMReduction.lean:34` — the same
  statement as the entry theorem, with `C, hC, hlog` still hypothetical. Mechanism (lines 38–46):
  `by_contra` + `push Not` gives a uniform bound `G` on all shorter-interval vorticity integrals; the previous
  lemma turns it into a uniform gradient-integral bound; `L.endpoint_of_bounded_gradient`
  (`Euler/OrdinaryEulerLifespan.lean:77`) produces `HasEulerEvolution A L.duration`; `L.no_endpoint`
  (`Euler/OrdinaryEulerContinuation.lean:53`) contradicts it. `no_endpoint` is proved from `h.extend`
  (`:43`, local existence + concatenation) and the structure field `L.maximal`. **So maximality of the
  lifespan is genuinely load-bearing: remove `L.maximal` and there is no proof.** The conclusion is not a
  junk value: `vorticityIntegral` is a real Bochner interval integral (see below), and `G` is universally
  quantified after the contradiction, not produced by a default. — OK

### The logarithmic (BKM) gradient estimate — PROVED, not assumed

- `logarithmicGradientConstant` — `Euler/OrdinaryLogarithmicGradient.lean:19` — `36*splitCost`, and
  `splitCost = lowCost+middleCost+3` (`Euler/WholeSpaceLogarithmic.lean:16`). Concrete, positive
  (`:21`, `:24`). — OK
- `logarithmic_gradient_bound` — `Euler/OrdinaryLogarithmicGradient.lean:29` — for a smooth L² field with
  `divergence A.field y = 0` for all `y` and `‖vectorCurl A.field y‖ ≤ W` for all `y`:
  `‖fderiv ℝ A.field x‖ ≤ 36*splitCost*(1+‖A.toLp‖+W*log (exp 1+tensorNorm 3 A))`. Mechanism: per matrix entry
  `‖(fderiv A x (axis i)) j‖ ≤ K := 4*splitCost*(...)` from `elliptic_derivative_logarithmic` applied to the
  scalar component `componentField A j` with right-hand side the two vorticity components
  `ω_{j+1}, ω_{j+2}` (lines 48–53), then `operator_norm_le_of_entries` (`9*K`, line 58) and `36 = 9*4`
  (line 59). Real analysis, no hypothesis left dangling. — OK
- `logarithmic_gradient_bound_solenoidal` — `Euler/OrdinaryLogarithmicGradient.lean:63` — same conclusion with
  `hdiv` replaced by `A.toLp ∈ solenoidalSpace`, discharged via `solenoidal_representative_divergence`
  (line 68). This is the term passed at `Euler/OrdinaryEulerBKM.lean:24`. — OK
- `by decide : 3 ∈ range (3+1)` — `Euler/OrdinaryLogarithmicGradient.lean:47` — the only `decide` in the
  BKM chain; decides membership of `3` in `Finset.range 4` (`Nat.decLt` on numerals ≤ 4). — OK (noted)
- `elliptic_derivative_logarithmic` — `Euler/WholeSpaceLogarithmic.lean:28` — for scalar `A` with the *literal*
  elliptic identity `Δ A.field y = ∂_a G.field y − ∂_b J.field y`, `‖G‖_∞,‖J‖_∞ ≤ W`, `‖A.jetLp 3‖ ≤ H`:
  `‖∂_j A.field x‖ ≤ 4*splitCost*(1+‖A.toLp‖+W*log (exp 1+H))`. Mechanism: `EulerLogarithmicCutoff.optimize`
  fed with the ε-family bound `elliptic_derivative_split`. — OK
- `EulerLogarithmicCutoff.optimize` — `Euler/LogarithmicCutoffOptimization.lean:13` — from
  `∀ ε ∈ (0,1), X ≤ c*(L+W*(−log ε)+ε^{1/4}*H)` concludes `X ≤ 4c*(1+L+W*log(e+H))`. Mechanism: substitutes
  the honest minimiser `ε := exp (−4 log (e+H)) ∈ (0,1)` (lines 23–27), uses `ε^{1/4} = (e+H)⁻¹` (line 29,
  `rpow` algebra) and `(e+H)⁻¹H ≤ 1` (line 34), then `nlinarith`. The `W log` terms cancel exactly; no sign
  assumption on `W` is smuggled in. — OK
- `elliptic_derivative_split` — `Euler/WholeSpaceGaussianElliptic.lean:91` — `‖∂_j A.field x‖ ≤
  lowCost*‖A.toLp‖ + middleCost*W*(−log ε) + 3*ε^{1/4}*‖A.jetLp 3‖` for `0 < ε ≤ 1`. Mechanism: the honest
  three-scale telescope `v = (v−m)+(m−l)+l` with `m = average ε (∂_j A) x`, `l = average 1 (∂_j A) x`, and the
  three bounds `derivative_high_remainder`, `derivative_elliptic_middle`, `average_field_first_bound`. — OK
- `derivative_elliptic_middle` — `Euler/WholeSpaceGaussianElliptic.lean:54` — the log term:
  `‖average ε − average 1‖ ≤ middleCost*W*(−log ε)` by integrating the genuine `1/t` derivative bound
  (`secondAverage_elliptic_bound`, `:38`) over `[ε,1]` with `∫ dt/t = −log ε` (line 79–84). — OK
- `secondAverage_elliptic` — `Euler/WholeSpaceGaussianElliptic.lean:19` — uses the *given* elliptic identity and
  `secondAverage_eq_laplacian` (`Euler/WholeSpaceGaussianFields.lean:94`). — OK
- `derivative_high_remainder` — `Euler/WholeSpaceGaussianHigh.lean:20` —
  `‖fderiv A.field x (axis j) − average ε (∂_j A) x‖ ≤ 3ε^{1/4}‖A.jetLp 3‖`. Mechanism: FTC on
  `t ↦ scaledAverage t (∂_j A) x` between `0` and `ε` with derivative `(1/4)•secondAverage t` and
  `∫_0^ε (3/4)t^{−3/4} = 3ε^{1/4}`; the `t=0` endpoint is `scaledAverage 0 f x = f x`
  (`Euler/WholeSpaceGaussianScale.lean:61`). — OK
- `average` — `Euler/WholeSpaceGaussian.lean:109` — `∫ y, kernel t y • f (x+y)`: a genuine Gaussian
  convolution against a normalized kernel (`integral_kernel` gives mass 1; used at `:129`). NOT a junk
  definition, NOT an `sSup`, no division by zero (the `t=0` case is handled by the dilated
  `scaledAverage`, `Euler/WholeSpaceGaussianScale.lean:44`, and `scaledAverage_eq` at `:47` identifies the
  two for `t>0`). — OK
- `average_field_first_bound` / `average_field_second_bound` — `Euler/WholeSpaceGaussianFields.lean:79`, `:84` —
  the low term `‖average 1 (∂_a A) x‖ ≤ lowCost*‖a‖*‖A.toLp‖` and the `t⁻¹` second-derivative bound. Statements
  read; their proofs delegate to `average_first_L2_bound` / `average_second_bound` in
  `Euler/WholeSpaceGaussianLow.lean` / `...Evolution.lean`, which I did **not** read. — UNCLEAR (see Escalation E2)

### Is `vorticityIntegral` an honest integral of a sup-norm of the curl?

- `vectorCurl` — `Euler/MeanCutoffCurlBound.lean:16` — `curl (fun i x => f x i)` with
  `curl ψ x i = ∂_{i+1} ψ_{i+2} − ∂_{i+2} ψ_{i+1}` (`Euler/EulerProof.lean:10840-10847`) and
  `partialDerivative f i x = fderiv ℝ f x (EuclideanSpace.single i 1)` (`:10836`). The true 3-D curl in
  cyclic `Fin 3` coordinates. — OK
- `vorticityField` / `vorticityField_apply` — `Euler/OrdinaryEulerVorticity.lean:17`, `:20` —
  `(vorticityField A).field x = vectorCurl A.field x`, proved through `vectorCurl_eq_matrix`
  (`Euler/MeanBoundaryOperator.lean:27`) with differentiability supplied by `A.smooth` — so no `fderiv`
  junk value (`fderiv = 0` off differentiability) is ever exploited: every `fderiv` in this chain is applied
  to a `SmoothL2Field.field`, which carries `ContDiff ℝ ∞` (`Euler/LpSmoothField.lean:31-34`). — OK
- `vorticityNorm` — `Euler/OrdinaryEulerVorticity.lean:30` — `‖finiteField (vorticityField A)‖`, the norm of a
  **bundled bounded continuous function** `Space →ᵇ Space` with `finiteField A x = A.field x`
  (`Euler/MeanSobolevBoundedField.lean:104`, `:108`; the boundedness is constructed from the L² jets, not
  assumed). Hence it is the genuine finite `⨆_x ‖curl u(x)‖`, not an `sSup` of an unbounded set and not a
  `⊤`/0 fallback. — OK
- `vorticityNorm_le_iff` — `Euler/OrdinaryEulerVorticity.lean:34` — `vorticityNorm A ≤ K ↔ ∀ x,
  ‖vectorCurl A.field x‖ ≤ K`. Proof uses Mathlib `BoundedContinuousFunction.norm_le_of_nonempty`, whose real
  statement I verified in Mathlib `Mathlib/Topology/ContinuousMap/Bounded/Normed.lean`
  (`‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M` for `[Nonempty α]`; `Space = EuclideanSpace ℝ (Fin 3)` is nonempty).
  This is an **exact** characterisation in both directions, so the "sup" cannot be secretly larger or smaller
  than the pointwise supremum. — OK
- `Evolution.vorticityNormPath` / `pointwise_vorticity_le` — `:49`, `:59` — a `C(Icc 0 T, ℝ)` path (continuity
  from `vorticityNorm_continuous`), with the pointwise bound extracted from `le_rfl` through the iff. — OK
- `Evolution.vorticityIntegral` — `Euler/OrdinaryEulerVorticity.lean:63` —
  `realIntegral T hT U.vorticityNormPath t`, and `realIntegral f t = ∫ s in (0:ℝ)..t, extendPath T hT f s`
  (`Euler/ContinuousTimeIntegral.lean:53`) with `extendPath f t = f (projIcc 0 T hT t)`
  (`Euler/VolterraConvolution.lean:20`). So `vorticityIntegral t = ∫_0^t ‖curl u(s)‖_∞ ds` literally, with
  clamping that is the identity on `[0,T]`. No junk fallback. — OK
- `vorticityIntegral_nonneg` / `_initial` / `_continuous` / `_mono` — `:65`, `:69`, `:72`, `:78` — standard
  interval-integral facts; `_mono` uses nonnegativity of the integrand. — OK
- `vorticityIntegral_le_const` — `Euler/OrdinaryEulerVorticity.lean:84` — `∀ t x, ‖curl u_t(x)‖ ≤ K ⇒
  vorticityIntegral t ≤ K*t`; `integral_mono_on` against the constant. — OK
- `vorticityNormPath_le_gradient` — `:95` — `‖ω‖_∞ ≤ ‖curlOperator‖*‖∇u‖_∞` via the operator norm of
  `curlOperator` (`Euler/PacketPotentialRegularity.lean:21`). Not load-bearing for the BKM conclusions. — OK

### Half-open (maximal) side

- `FiniteLifespan` — `Euler/OrdinaryEulerLifespan.lean:29` — four fields: `duration`, `0 < duration`,
  `shorter : ∀ S, 0 < S → S < duration → HasEulerEvolution A S`, `maximal : ∀ S, duration < S →
  ¬ HasEulerEvolution A S`. No contradictory field; the structure is inhabited in the repo at
  `Euler/PacketFiniteLifespan.lean:46-54` (via `exists_finite_lifespan`, `:35`, from local existence and a
  no-solution-at-`baseHorizon` claim). — OK
- `FiniteLifespan.evolution` — `Euler/OrdinaryEulerLifespan.lean:60` — `(L.shorter S hS hST).choose_spec.choose`:
  `Exists.choose` of an existence that is a *structure field*, hence true; `evolution_initial` (`:63`) records
  the datum, `evolution_agrees` (`:67`) removes the choice ambiguity via Euler uniqueness
  (`endpoint_matches_partial`, `Euler/OrdinaryEulerEndpoint.lean:75`). Not a `Classical.choose` of a false
  existence. — OK
- `FiniteLifespan.endpoint_of_bounded_gradient` — `Euler/OrdinaryEulerLifespan.lean:77` — a uniform bound `G`
  on `gradientIntegral` over all shorter intervals yields `HasEulerEvolution A L.duration`, by
  `exists_smooth_endpoint`. — OK (its dependency is escalated, E1)
- `FiniteLifespan.no_endpoint` — `Euler/OrdinaryEulerContinuation.lean:53` — `¬ HasEulerEvolution A L.duration`,
  from `HasEulerEvolution.extend` (`:43`, built on `Evolution.exists_extension`, `:20`, i.e. local existence at
  the terminal time plus concatenation) and the `maximal` field. — OK
- `Evolution` — `Euler/OrdinaryEulerDifference.lean:21` — the record is a genuine smooth Euler solution:
  `velocity`/`pressureForce` as smooth L² fields, jet continuity, `solenoidal : (velocity t).toLp ∈
  solenoidalSpace`, `gradient : pressureForce ∈ gradientSpace`, and `time_law` (lines 28–32) the pointwise
  `HasDerivAt (fun r => u r x) (−(∇u_t x)(u_t x) − (∇p)_t x) t` on `Ioo 0 T`. This is the Euler equation, not a
  weakened surrogate. — OK
- `maximalVorticityNorm` / `_le_iff` / `_continuous` — `Euler/OrdinaryMaximalVorticity.lean:44`, `:49`, `:53` —
  `vorticityNorm (L.maximalField t)`; `maximalField t` is the velocity of the evolution on the intermediate
  horizon `(t+duration)/2` (`Euler/OrdinaryEulerMaximal.lean:46`), independent of the choice by
  `maximalFields_eq_evolution` (`:54`). — OK
- `maximalVorticityIntegral` — `Euler/OrdinaryMaximalVorticity.lean:63` — the vorticity integral of the
  intermediate-horizon evolution at time `t`; `_eq_evolution` (`:67`) shows it agrees with *every* shorter
  evolution, `_mono` (`:93`), `_continuous` (`:84`). — OK
- `maximalVorticityIntegral_tendsto_atTop` — `Euler/OrdinaryMaximalVorticity.lean:121` — from the unbounded-partials
  hypothesis, via `vorticityIntegral_eventually_large_of_unbounded` (`:107`, monotonicity + agreement) and
  `eventually_ge_atTop`. — OK
- `maximalVorticityDensity` — `Euler/OrdinaryMaximalVorticityIntegral.lean:22` — `if r ∈ Ico 0 duration then
  maximalVorticityNorm ⟨r,hr⟩ else 0`. The `0` branch is outside the integration set `Ico 0 duration`, so it
  cannot deflate the lintegral; `_eq` (`:37`) and `_eq_evolution` (`:47`) prove the on-set identification with
  `dite_eq_left` (verified in Mathlib `Mathlib/Logic/Basic.lean`: `dite_eq_left h : dite P A B = A h`). — OK
- `maximalVorticityDensity_measurable` / `_continuousOn` / `_intervalIntegrable` — `:33`, `:55`, `:67` — honest
  measurability/continuity, with local integrability *explicit* (so no "non-integrable ⇒ integral 0" trick). — OK
- `maximalVorticity_lintegral_eq_top` — `Euler/OrdinaryMaximalVorticityIntegral.lean:92` — the lintegral over
  `Ico 0 duration` is `⊤`, from `lintegral_eq_top_of_unbounded_partials`. — OK
- `EulerNonnegativeImproperIntegral.lintegral_eq_top_of_unbounded_partials` —
  `Euler/NonnegativeImproperIntegral.lean:26` — honest: `by_contra`, then instantiates the unboundedness at
  `K := (lintegral).toReal` and contradicts `ofReal_partial_le_lintegral` (`:16`) with
  `ENNReal.lt_ofReal_iff_toReal_lt`. — OK

### Gradient / Grönwall layer

- `Evolution.gradientNormPath` / `_le_iff` / `pointwise_gradient_le` —
  `Euler/OrdinaryEulerGradientControl.lean:20`, `:30`, `:37` — `‖finiteField (velocity t).derivative‖`, again a
  true bounded-continuous-function sup norm with an exact iff. — OK
- `Evolution.gradientIntegral` — `Euler/OrdinaryEulerGradientControl.lean:41` — `∫_0^t ‖∇u(s)‖_∞ ds`. — OK
- `gradientIntegral_le_const`, `h3_energy_gradientIntegral`, `wordBound_of_gradientIntegral`,
  `h3_tensorNorm_of_gradientIntegral` — `:49`, `:68`, `:103`, `:114` — the H³ energy inequality
  `E₃(t) ≤ E₃(0) exp(c ∫‖∇u‖_∞)` via `variable_linear_stability`, then `WordBound`/`tensorNorm` conversions. — OK
- `logarithmicGronwallConstant` — `Euler/OrdinaryEulerLogarithmicControl.lean:20` —
  `C*(1+‖u₀‖+logEnergyBase u₀+gradientEnergyConstant)`: depends only on the initial datum. — OK
- `Evolution.logarithmic_h3_bound` — `:32` — `log (e+tensorNorm 3 u_t) ≤ logEnergyBase u₀ +
  gradientEnergyConstant*gradientIntegral t`; the standard `log(ab) = log a + log b` + `log x ≤ x−1` step. — OK
- `gradient_logarithmic_envelope` — `:76` — turns the log estimate into `‖∇u_t‖_∞ ≤ c(1+W t)(1+∫‖∇u‖)`, using
  L² energy conservation `velocity_norm_conserved` (`Euler/OrdinaryEulerKineticEnergy.lean:41`, itself from
  `kineticEnergy_conserved`, `:33`) to replace `‖u_t‖_{L²}` by `‖u₀‖_{L²}`. — OK
- `gradientIntegral_logarithmic_bound` / `_uniform` — `:109`, `:141` — Grönwall on `X = 1+∫‖∇u‖` giving
  `X t ≤ exp(c(t+∫W))`, then `t ≤ Tmax`, `∫W ≤ G`. — OK
- `variable_linear_stability` — `Euler/OrdinaryVariableGronwall.lean:14` — genuine variable-coefficient Grönwall
  via the integrating factor `exp(−C∫K)` and a one-sided derivative monotonicity lemma
  (`linear_stability_within`). — OK
- `Evolution.gradientIntegral_mono` — `Euler/OrdinaryEulerContinuation.lean:35` — OK
- `FiniteLifespan.gradientIntegral_unbounded`, `gradient_unbounded`, `gradient_unbounded_near_endpoint`,
  `gradientIntegral_agrees`, `gradientIntegral_eventually_large` — `Euler/OrdinaryEulerContinuation.lean:58`,
  `:65`, `:86`, `:107`, `:124` — the same contradiction pattern; `_near_endpoint` correctly localises using a
  midpoint horizon `R` and the finite path norm on `[0,R]`. — OK
- `exists_smooth_endpoint` — `Euler/OrdinaryEulerEndpoint.lean:39` — from solutions on every `S < T` with a
  *common* gradient-integral bound `G`, produces a solution on `[0,T]` with the same datum. Mechanism: rescale
  `U n` on `[0, endpointScale n * T]` to `[0,T]` via the Euler scaling symmetry (`rescale`, line 52), uniform
  H³ bound `gradientTensorBound` (line 56, from `h3_tensorNorm_gradient_uniform`,
  `Euler/OrdinaryGradientLimit.lean:23`), then `limitEvolutionOfH3` (`Euler/OrdinaryEulerCauchy.lean:97`). — UNCLEAR (E1)

### Coordinate / elliptic identity layer

- `componentField` / `_apply` / `_toLp_norm` / `_jetLp_norm` — `Euler/OrdinaryVorticityCoordinates.lean:16`,
  `:19`, `:22`, `:27` — scalar components via `EuclideanSpace.proj j`, with norm-`≤1` postcomposition. — OK
- `componentField_partial` — `:40` — `∂_i (u_j) x = (fderiv u x (axis i)) j`, from `fderiv_coordinate` with
  differentiability from smoothness. — OK
- `componentField_laplacian` — `Euler/OrdinaryVorticityCoordinates.lean:44` — `Δ u_j x =
  ∂_{j+2} ω_{j+1} x − ∂_{j+1} ω_{j+2} x` under `∀x, divergence u x = 0`. Mechanism: the *proved* vector identity
  `vectorCurl (vectorCurl f) = gradient (divergence f) − Δ f` (`Euler/MeanVectorIdentities.lean:105`, proved by
  `fin_cases` + commuting second derivatives, not assumed), the vanishing of `gradient (divergence u)` (lines
  49–51), and coordinate rewrites; closed by `linarith` on the two sign conventions. I checked the index
  bookkeeping against the call site: `Euler/OrdinaryLogarithmicGradient.lean:49-51` passes
  `G := ω_{j+1}`, `J := ω_{j+2}`, `a := j+2`, `b := j+1`, which matches `hΔ` of
  `elliptic_derivative_logarithmic` (`Δ A = ∂_a G − ∂_b J`) term for term. — OK
- `operator_norm_le_of_entries` — `Euler/OrdinaryVorticityCoordinates.lean:66` — `(∀ i j, ‖(L (axis i)) j‖ ≤ K)
  ⇒ ‖L‖ ≤ 9K`. Honest and correctly conservative (two ℓ¹-over-`Fin 3` steps). The `36` in
  `logarithmicGradientConstant` is exactly `9*4`. — OK
- `EulerMeanCutoffCurl.norm_vectorCurl_le` — `Euler/MeanCutoffCurlBound.lean:48` — `‖curl f x‖ ≤ 6‖∇f x‖`
  (differentiability hypothesis explicit). — OK
- `homogeneous_sobolev`, `lpNorm_norm_mul_le`, `vectorCurl_memLp`, `cutoff_curl_lpNorm_le`,
  `cutoff_curl_bound`, `integral_cutoff_curl_bound` — `Euler/MeanCutoffCurlBound.lean:24`, `:76`, `:91`,
  `:102`, `:168`, `:185` — genuine Sobolev/Hölder estimates from Mathlib
  (`eLpNorm_le_eLpNorm_fderiv_of_eq_inner`, `HolderTriple 3 6 2`); `sobolevConstant` (`:20`) is Mathlib's
  constant, not a fudge factor. These are **not** used by the BKM chain (only `vectorCurl` is); read because
  the task listed the file. — OK

## Kernel-risk assessment

1. **No metaprogramming, no `sorry`, no `axiom`, no `native_decide`, no `set_option`, no `unsafe`/`partial`,
   no `Acc.rec`** anywhere in the 927-file / 114,557-line transitive import closure of
   `Euler/OrdinaryEulerBKM.lean` (regex scan of every line of every file in the closure).
2. **`decide`: 53 occurrences, all trivial.** In the BKM chain proper there is exactly one:
   `Euler/OrdinaryLogarithmicGradient.lean:47`, `(by decide : 3 ∈ range (3+1))`. The rest (e.g.
   `Euler/EulerProof.lean:16615` `pow_le_pow_right₀ hΘ (by decide)` for `4 ≤ 5`,
   `zero_pow (by decide : 2 ≠ 0)`, `(by decide : Even 6)`, `show (⟨2, by decide⟩ : Fin 3) = 2 from rfl`) are
   `Nat`/`Fin` decisions on numerals ≤ ~40. Kernel cost is microscopic; no GMP-scale numeral arithmetic and no
   `Decidable` instance over a large search space anywhere in the closure.
3. **`Nat.rec`: 1 occurrence** — `Euler/LpSmoothJetField.lean:17`, a type-level recursion defining
   `jetFieldAux`, with `rfl`-proved unfolding lemmas `jetField_zero`/`jetField_succ` (`:29`, `:34`). The BKM
   chain only ever instantiates order `3` (`tensorNorm 3`, `jetLp 3`), so at most 3 unfolding steps. No
   forced deep reduction.
4. **`termination_by`: 10 occurrences**, all in the *periodic-lift jet* machinery
   (`Euler/EulerProof.lean:3202,3233,3291,3331,3399,4703,4712`; `Euler/H6Pressure.lean:28,53,93`) —
   `CoefficientJet.productConstant`, `SpatialJet.multiply`, `solvePressure`, `SpatialJet.word`, `levelNorm`,
   `boundLevel`. These are structural recursions on a `ℕ` jet order. They are in the import closure (via
   `Euler/MeanCutoffCurlBound.lean:1 import Euler.EulerProof`) but **no declaration in the BKM chain mentions
   them**; nothing in this chain forces well-founded unfolding. Residual risk: without a build I cannot prove
   that no `simp`/`rfl` in the chain triggers their equation lemmas.
5. **`Classical.choose`: 24 occurrences**, each immediately paired with the matching `Classical.choose_spec`
   of a *hypothesis or proved existence* (e.g. `Euler/OrdinaryEulerLocalExistence.lean:112`/`:116`). The
   chain's own choice, `FiniteLifespan.evolution` (`Euler/OrdinaryEulerLifespan.lean:60`), chooses from the
   structure field `shorter`, i.e. a true existence. No `Classical.choose` of a false/unproved existence in
   this chain.
6. **Junk-value audit.** `fderiv` is applied only to `SmoothL2Field.field`, which carries `ContDiff ℝ ∞`
   (`Euler/LpSmoothField.lean:33`), and every curl/derivative rewrite passes an explicit differentiability
   proof (`Euler/OrdinaryEulerVorticity.lean:22`, `Euler/OrdinaryVorticityCoordinates.lean:42`). Sup norms are
   `BoundedContinuousFunction` norms with an exact two-sided characterisation, not `sSup` of a possibly
   unbounded set. The divergence claim uses the extended (`lintegral`) integral, so the Bochner
   "non-integrable ⇒ 0" convention is not exploited. No division by a possibly-zero quantity appears in the
   chain's definitions (`intermediateHorizon` divides by the literal `2`,
   `Euler/OrdinaryEulerMaximal.lean:21`).

Verdict: **no kernel-exploiting construct in this sub-chain.**

## Escalations (ranked)

**E1 (highest). `exists_smooth_endpoint` → `limitEvolutionOfH3`: the step that could make the BKM conclusion
unsound rather than vacuous.** `Euler/OrdinaryEulerEndpoint.lean:39`, delegating to
`Euler/OrdinaryEulerCauchy.lean:97` (`limitEvolutionOfH3`) and thence `limitEvolution`
(`Euler/OrdinaryEulerLimit.lean`). In this chain the endpoint theorem is used only to derive a
*contradiction*; so if it proves too much, `vorticityIntegral_unbounded` becomes a false theorem with a
"valid" proof, and the whole Euler blowup statement inherits the flaw.
Precise question for an expert: **does `limitEvolution` construct an `Evolution T hT` whose `time_law` field
(`Euler/OrdinaryEulerDifference.lean:28`) is genuinely verified for the limit — i.e. is the pointwise
`HasDerivAt` of the limit velocity derived from locally-uniform convergence of the nonlinear right-hand side
`−(u·∇)u − ∇p`, and is the limit pressure still in `gradientSpace` — or is some field obtained by an
`Exists.choose`/limit whose defining property is only asserted for the approximants?**
What would settle it: read `limitEvolution`, `Evolution.all_order_bounds_of_h3`
(`Euler/OrdinaryEulerCauchy.lean`, near `:60-92`) and `Evolution.cauchyPath_of_initial` in full, checking that
the `time_law` of the limit is proved (not inherited) and that `Evolution.rescale`
(`Euler/OrdinaryEulerRescaling.lean`) preserves `time_law` with the correct Euler scaling
`u_c(t,x) = c·u(ct,x)`, `p_c = c²p`.

**E2. The two unread Gaussian bound lemmas that carry the constants of the log estimate.**
`average_first_L2_bound` and `average_second_bound` (called at `Euler/WholeSpaceGaussianFields.lean:81` and
`:88`; defined in `Euler/WholeSpaceGaussianLow.lean` / `Euler/WholeSpaceGaussianEvolution.lean`), plus
`secondAverage_directional_bound` (used at `Euler/WholeSpaceGaussianHigh.lean:35`).
Precise question: **is `‖average 1 (∂_a A) x‖ ≤ lowCost‖a‖‖A.toLp‖` obtained by moving the derivative onto the
kernel and Cauchy–Schwarz with `‖∂ kernel 1‖_{L²} < ∞` (legitimate), and is
`‖average t (∂_a∂_b A) x‖ ≤ C t⁻¹‖a‖‖b‖‖A‖_∞` obtained by two integrations by parts against the kernel
(legitimate `t⁻¹` scaling), or does either silently use the *unproved* boundedness of a derivative it has not
bounded?** What would settle it: read those two lemmas' statements and proof terms and confirm the kernel
moment estimates they cite (`kernel_sq_integrable`, `sqrt_normalization_le`,
`Euler/WholeSpaceGaussian.lean:82-102`).

**E3. Inhabitation of `FiniteLifespan` — i.e. whether the BKM conclusions are about anything.**
`Euler/PacketFiniteLifespan.lean:46-54` builds `lifespan : FiniteLifespan initialDatum` from
`initialDatum_local` and `initialDatum_no_base` (`:31`). My chain is fully conditional on that datum.
Precise question: **is `initialDatum_no_base` (no Euler evolution up to `baseHorizon`) genuinely proved from the
packet construction, and is `initialDatum` a nonzero solenoidal smooth L² field?** What would settle it: the
packet/stage audit (another worker's scope) — specifically `Stage.initialDataLimit_no_euler` and
`Euler/PacketFiniteLifespan.lean:38` (`initialDatum_solenoidal`).

**E4 (low). Unverifiable definitional steps.** Several load-bearing rewrites are `change`/`rfl`/`simp only`
steps whose correctness is definitional and unchecked without a build, most notably
`Euler/OrdinaryVorticityCoordinates.lean:60-63` (the `change` that fixes the sign convention of
`curl curl u` before `linarith`) and `Euler/OrdinaryEulerGradientControl.lean:35` (`rfl` closing the
gradient-norm iff). Precise question: **do these elaborate?** What would settle it: one successful
`lake build Euler.OrdinaryEulerBKM` on a machine with disk space.

## Residue (not checked, and why)

- **No build.** Disk is full, no Mathlib olean cache: I could not typecheck a single declaration. Everything
  above is source reading; a `simp only`/`rfl`/`change`/`positivity`/`nlinarith` step that silently fails to
  close its goal would be invisible to me (though it would also mean the repo does not compile).
- Not read in full (one level below my chain): `limitEvolution`, `Evolution.all_order_bounds_of_h3`,
  `Evolution.cauchyPath_of_initial` (`Euler/OrdinaryEulerCauchy.lean`), `Evolution.rescale`
  (`Euler/OrdinaryEulerRescaling.lean`), `localEvolution` + `regularizer` local existence
  (`Euler/OrdinaryEulerLocalExistence.lean`), `Evolution.concatenate`
  (`Euler/OrdinaryEulerConcatenation.lean`), `restrictTime`, `velocity_eq_of_initial` (Euler uniqueness,
  `Euler/OrdinaryEulerUniqueness.lean`), `h3_energy_gradient` and `gradientEnergyConstant`
  (`Euler/OrdinaryGradientEnergy.lean`), `wordEnergy`/`tensorNorm`/`wordCount`/`WordBound` definitions,
  `linear_stability_within` (`Euler/OrdinaryEulerL2Stability.lean`), `average_first_L2_bound`,
  `average_second_bound`, `secondAverage_directional_bound`, the Gaussian `kernel` definition itself
  (I verified only that it is normalized and used as a convolution weight, `Euler/WholeSpaceGaussian.lean:82-129`),
  `solenoidalSpace`/`gradientSpace`/`solenoidal_representative_divergence`.
- I could not spawn helper children (RLM depth limit reached: `RLM_DEPTH=2, RLM_MAX_DEPTH=2`), so the two
  sub-audits I would have delegated (Gaussian layer, curl/coordinate layer) were done by me at reduced depth;
  E2 is the visible cost.
- The 10 `termination_by` definitions are in the import closure but I could not prove (without a build) that
  no tactic in the chain forces their well-founded unfolding; see Kernel-risk item 4.
