# Worker report — `NavierStokes/CorrectionStep.lean` (+ delegated `InitialPhysicalData.lean`, `TerminalEdgeFactor.lean`)

Worker: `ns-correction-step`. Read-only audit of `/home/gsm/.openclaw/workspace/repos/NSE`
@ `f9e8bc5`. No file under that path was modified. No `lake build` was run (no Mathlib on box);
everything below is source-level reading of statements and proof terms.

All `file:line` references are to `NavierStokes/CorrectionStep.lean` unless another file is named.

## Scope

| file | lines | decls (my parse) | of which `theorem` | `def` | `structure` | `abbrev` | in-cone (CONE.csv mark 4) |
|---|---|---|---|---|---|---|---|
| `NavierStokes/CorrectionStep.lean` | 9,849 | 559 | 418 | 113 | 23 | 5 | 384 decls, **264 theorems** |
| `NavierStokes/InitialPhysicalData.lean` | 2,854 | 230 | 177 | 48 | 0 | 5 | 167 theorems (delegated) |
| `NavierStokes/TerminalEdgeFactor.lean` | 1,675 | 235 | 173 | 61 | 0 | 1 | 151 theorems (delegated) |

The in-cone theorem count I derive for `CorrectionStep.lean` (264) matches `COVERAGE.md` exactly,
so my decl parse and the audit's cone extraction agree on this file.

**What I read.** 110 declarations of `CorrectionStep.lean` line-by-line, statement *and* proof term
(67 theorems, 36 defs, 7 structures); 93 of those 110 are in-cone. Plus, because this file's meaning
is carried entirely by imported predicates, I read line-by-line the *definitions it estimates
against*, in other files: `WeightedClasses.lean:31-115` (`StripData`, `majorant`, `MemClass`,
`MeanClass`, `WaveClass`), `WeightedClasses.lean:191-227` (`mono_exponent`, `add`),
`LabelSumBounds.lean:32-56` (`UniformClass`, `UniformWaveClass`, `each`),
`UniformHarmonicInteraction.lean:24-27` (`UniformVelocity`),
`MeanIncrementBounds.lean:44-75` (`Operators.dr/dz/time/radialDiv/viscosity`),
`MeanIncrementBounds.lean:305-360` (`thetaResidual`, `axialResidual`, `gr`, the six flux fields),
`MeanIncrementBounds.lean:387-396` (`CumulativeBounds`, `IncrementBounds`),
`HarmonicWaveInteraction.lean:277` (`ZeroMode`), `ChartScales.lean:24-30` and
`BaseContextAssembly.lean:31` (the *concrete* `epsilon`/`slow`).

**What I skimmed.** The remaining ~449 decls: I ran a full mechanical scan of every line of the
file (tactic fingerprints, numerals, `if`/`fderiv`/division/quantifier patterns, section map) and
read statement headers of the ~130 further decls in the sections I sampled. I did **not** read the
proof bodies of the ~350 structural congruence/`simp only` lemmas in
`TemporalComposition`…`CoherentReferenceParticular`.

**Sampling scheme** (chosen to cover proof *patterns*, not a prefix). I fingerprinted all 418
theorem proofs by tactic set: **158 distinct fingerprints**; **374 of 418 proofs contain no
arithmetic tactic at all** (no `linarith`/`nlinarith`/`calc`/`norm_num`/`omega`/`positivity`), and
106 are pure term-mode. I then sampled:
1. every one of the 20 sites carrying the numeric hypothesis `κ ≤ 1/100000` (the quantitative
   payloads) — owners listed in §Per-declaration;
2. the 6 largest arithmetic proofs (`fourStage_mean_gain` 125 lines, `waveStages_residual_gain` 124,
   `meanStages_constructed` 109, `mean_gain_from_waves` 105, `finish_mean_stages` 95,
   `bandNativeSignedStage_mean_debt` 85);
3. the definitional core (`FullCalculus` :227-361, `FullFields` :363-426, `ActualCycle` :4981-5151,
   `ActualRecurrence` :6786-6994) — every `def` that a consumer's `change`/`rfl` step unfolds;
4. `MovingSupport` :4447-4601 in full (the only `fderiv` cluster);
5. the whole of the "only" occurrences of each risky token: 1 `norm_num` (:7349), 2 `omega`
   (:6900, :6932), 3 `fderiv` statements (:1025, :4337, :4503), 9 statements with a division by an
   identifier, 0 `if`-`then`-`else`;
6. `ConstructedSignedLinear` :3814-3982 (largest section) as the representative of the
   "control-record → block bounds" pattern.

**Correction to the briefing.** The brief describes this file as "long `nlinarith`/`calc` chains".
It is not: `CorrectionStep.lean` contains **zero `nlinarith`, zero `calc`, one `norm_num`, two
`omega`, 85 `linarith`**. It is a *transport/bookkeeping* file: definitional unfolding
(`simp only [<defs>]`, `change … ; ring`) plus exponent arithmetic through
`MemClass.mono_exponent`. That matters for where the risk is (see §Escalations E1).

## Per-declaration findings

Cone status is from `CONE.csv` (mark 4). "✓" = `in_cone=True`.

### A. Definitional core — the fields every later bound is *about*

| decl | line | cone | statement (my words) | mechanism | verdict |
|---|---|---|---|---|---|
| `thetaCovarianceChange` | :70 | ✓ | `radialDiv 2 (X 0 1) + dz (X 2 1)` | def | OK |
| `axialCovarianceChange` | :73 | ✓ | `radialDiv 1 (X 0 2) + dz (X 2 2)` | def | OK |
| `radialCovarianceChange` | :76 | ✓ | `-radialDiv 1 (X 0 0) - dz (X 2 0) + invRadius * X 1 1` | def | OK (see note S1) |
| `thetaResidual_covariance_change` | :91 | ✓ | replacing covariance `W` by `W+X` changes the θ-residual by exactly `thetaCovarianceChange o X`, pointwise on `U` | rewrites `W+X` splits, then `o.radialDiv_add`/`o.dz_add` linearity (which *do* carry smoothness side-conditions `hb`,`hm`,`hW`,`hX`), then `ring` | OK |
| `axialResidual_covariance_change` | :113 | ✓ | same for the axial residual | same | OK |
| `gr_covariance_change` | ~:135 | ✓ | same for the radial residual `gr` | same | OK |
| `radialDirection`/`axialDirection`/`angularDirection`/`timeDirection` | :367,:371,:374,:376 | ✓ | the four graph directions; `timeDirection = fastCoefficient • vT - epsilon • eT` | def | OK (note S2) |
| `complexBase`, `complexPerturbation`, `complexPressure` | :379,:382,:387 | ✓ | complexification of (radial, angular, axial) base and of mean+oscillation, index order 0/1/2 | def | OK — index order agrees with `Triple` field order used in `MeanIncrementBounds` |
| `virtualDivergence` | :390 | ✓ | `![0, -(radialDiv 2 virtualTheta), -(radialDiv 1 virtualAxial)]` | def | OK — the weights 2 (θ) and 1 (z) agree with `thetaResidual`/`axialResidual` (`MeanIncrementBounds.lean:328,333`) |
| **`fullResidual`** | :396 | ✓ | the actual PDE residual: `Re(nonlinearResidual …) + virtualDivergence + u.errors.base` | def, real Fréchet derivatives via `HarmonicCalculus.along`/`transport`/`cylindricalVectorLaplacian` | **UNCLEAR** — see E2: it is the residual *plus* two additive terms |
| `fullGoodResidual` | :402 | ✓ | `fullResidual - u.errors.total` | def | **UNCLEAR** — E2 |
| `fullResidual_eq_good_add_excluded` | :414 | ✓ | `fullResidual = fullGoodResidual + errors.total` | `simp [fullGoodResidual]` — trivially true by the def above | OK (vacuous content, honest) |
| `fullResidual_decomposition` | :418 | ✓ | residual = angular-nonconstant part + angular mean + excluded total | `funext; simp only [defs]; ring` — pure algebra of `f = (f - mean f) + mean f` | OK |
| `nonlinearResidual` | :338 | ✓ | `linearResidual + transport a a` | def | OK |
| `nonlinearResidual_add_sub` | :342 | ✓ | the exact cross-term expansion of perturbing `a↦a+b`, `p↦p+q`: `linearResidual b q + transport a b + transport b a + transport b b` | `linearResidual_add` (:315) + bilinearity of `transport` + `abel`; every use of derivative-linearity carries a `ContDiffOn` hypothesis and is discharged at `x` via `contDiffAt.differentiableAt` | **OK, and load-bearing**: this is the file's docstring claim ("every old/new cross term is retained") and the proof really does retain all four terms |
| `linearResidual_add`, `transport_add_left/right`, `twiceAlong_add`, `cylindricalLaplacian_add`, `cylindricalVectorLaplacian_add`, `gradient_add` | :315,:237,:245,:256,:270,:285,:307 | ✓ | additivity of each differential operator at a point | each carries the differentiability hypotheses it needs (`ha`,`hb`,`hp`,`hq`,`hU`,`hx`) and uses Mathlib's `along_add`/`fderiv_add`; none silently assumes differentiability | OK — no junk-derivative shortcut here |

### B. `MovingSupport` (:4447-4601) — the only `fderiv` cluster

`GaugeSupported a b ell U f := ∀ n, SupportedGauge a b ell U (f n)` (:4453), and
`SupportedGauge` (`VariableGaugeMean.lean:67`) has the shape `∀ x ∈ U, f x ≠ 0 → a*ell x ≤ q x ∧ q x ≤ b*ell x`
— i.e. "f can only be nonzero inside the moving radial band". The whole namespace is closure of
that predicate.

| decl | line | cone | statement | mechanism | verdict |
|---|---|---|---|---|---|
| `GaugeSupported.zero` | :4463 | ✓ | `0` is supported | `intro n x hx hn; exact (hn rfl).elim` — the contradiction is `(0:…) ≠ 0`. Confirms the predicate really is guarded by `f x ≠ 0` | OK |
| `.add` | :4468 | ✓ | sum of supported is supported | `by_cases f n x = 0`; if zero, `g` carries the whole value | OK |
| `.neg`,`.sub`,`.mul_right`,`.mul_left`,`.smul` | :4476-4501 | ✓ | closure under `-`, `-`, `f*g`, `g*f`, `t•f` | `neg_ne_zero`, `left/right_ne_zero_of_mul` — sound direction each time (a nonzero product forces the *supported* factor nonzero) | OK |
| `.directional` | :4503 | ✓ | `fun n x => fderiv ℝ (f n) x v` is supported when `f` is, given `IsOpen U` and `ContinuousOn ell U` | one application of `VariableGaugeMean.fderiv_apply_supportedGauge` (`:2870`) | OK, **but see S3**: no differentiability hypothesis. The lemma is still *true* — a junk `fderiv = 0` trivially satisfies a support predicate — so the junk value can only make this lemma weaker, never false |
| `.dr`,`.dz`,`.time`,`.radialDiv`,`.viscosity` | :4508-4539 | ✓ | closure under the five operators | built from `.directional` + `.mul_left` + `.smul`; `dr` uses `convert! … using 1; funext; simp only [Operators.dr, graphDerivative,…]; ring` — an *honest* unfolding of the operator, not a `simp` that could hide a factor | OK |
| `gr_supportedGauge` | :4555 | ✓ | `gr o base m W` is supported if the mean triple and covariance are | assembles exactly the 5 terms of `MeanIncrementBounds.gr` (:338 there) in the same order, closing with `.neg` | OK — and this is the cross-check that fixes note S1 |
| `state_gr_moving_regular` | :4574 | ✓ | on a `SlowRegion`, `u.gr c` is both `SmoothOn` the slow domain and gauge-supported | converts the *moving* band into a *fixed* annulus `[a₀,b₀]` via `qLength_reference_bounds` for the smoothness half only, and keeps the moving band for the support half | OK — the docstring's claim ("the annulus supplies smoothness only") is exactly what the proof does |

### C. `ActualCycle` (:4981-5151) — the one-cycle construction

| decl | line | cone | statement | mechanism | verdict |
|---|---|---|---|---|---|
| `CycleCoefficients` | :4993 | ✓ | `labels : ℕ → Finset ι`, `blocks`, `gaussian`, `aliasCoefficients`, `residualBand : ℕ` | structure | OK |
| `CycleParameters` | :5002 | ✓ | fixed geometric data: gauge, strip, patch, coordinate, timeExponent, commonIndex, axial, per-label `particular`/`signed`, rank | structure | OK |
| `particularBlock`, `particularGaussianBlock` | :5018,:5026 | ✓ | the particular solve, conjugated through the isometry `cycleAssoc` (`StateReindex.block … cycleAssoc` ∘ `…cycleAssoc.symm`) | def | OK — the reindex is by a `≃ₗᵢ[ℝ]` (:4988), so no information is created |
| `signedRequest` | :5048 | ✓ | the signed request is recomputed from `afterParticular`, not supplied | def | OK — matches its docstring, and this is the non-circularity point that matters |
| `afterParticular`,`afterSigned`,`afterTemporal`,`afterRank`,`next` | :5042,:5066,:5073,:5079,:5084 | ✓ | the four stages plus the pressure-alias refresh | def | OK |
| `finalBlock` | :5087 | ✓ | `addBlock (addBlock (v.blocks l) (particularBlock l)) (signedBlock l)` | def | OK — this is the def that :8635 and :9843 unfold |
| `next_oscillation`,`next_oscillatoryPressure` | :5102,:5108 | ✓ | the wave field after a cycle is `old + particular + signed` | `simp only [next, gaugeRefreshPressureAlias, afterRank, rankStageState, …, add_zero]` — pure unfolding | OK |
| `next_mean` | :5115 | ✓ | the mean after a cycle is `updated (updated u.mean temporalIncrement) rankIncrement` — i.e. **the two wave stages do not move the mean** | `change` + `he : (afterSigned).mean = u.mean` by unfolding (`updated_zeroTriple`) | OK — verified consistent: `afterParticular`/`afterSigned` are built with mean increment `⟨0, gaussian, 0⟩` (:5044,:5068) |
| `next_base_error` | :5124 | ✓ | the base error is untouched by a cycle | unfolding | OK |
| `next_gaussian_error`,`next_alias_error` | :5129,:5136 | ✓ | exact additive accounting of the two error channels | unfolding + one `change` | OK |
| `next_reconstructed` | :5147 | ✓ | `(reconstructState … (next …)).pressure = (next …).pressure` | `rfl` | OK (definitional, by construction of the alias refresh) |

### D. `ActualRecurrence` (:6786-6994) — the recursion and its invariant

| decl | line | cone | statement | mechanism | verdict |
|---|---|---|---|---|---|
| `CycleRepresentation` | :6798 | ✓ | 4 equations saying the *state's* oscillation / oscillatory pressure / gaussian error / alias error are exactly the label-sums of the *coefficient* data (alias error additionally carries the separate axisymmetric field `axis`) | structure | OK — this is the honesty invariant of the whole construction |
| `CoefficientBands` | :6807 | ✓ | one common integer band bounds blocks, gaussian and alias coefficients | structure | OK |
| `nextCoefficients` | :6824 | ✓ | labels unchanged; blocks ← `finalBlock`; gaussian ← old + two constructed gaussians; alias unchanged; **`residualBand := 2 * max v.residualBand 1`** | def | OK, with **E4**: the band *doubles every cycle* |
| `nextAxisymmetricAlias` | :6832 | ✓ | new axis alias = old + temporal alias + (pressure alias after rank − pressure alias before) | def | OK |
| `finalBlock_oscillation`,`finalBlock_pressure` | :6838,:6846 | ✓ | the final block's field is the literal sum of the three blocks' fields — **only under `hc : ∀ l, SameCarrier (v.blocks l) (signedBlock l)`** | `addBlock_oscillation` twice; `particular_carrier` (:6816) is `⟨rfl,rfl,rfl⟩` so the particular block shares the carrier *by construction*, but the signed block's carrier match is a hypothesis | OK / **E3** |
| `nextCoefficients_gaussian_field` | :6854 | ✓ | the stored gaussian coefficient sum reproduces the two constructed gaussian oscillations | `change` to the `HarmonicFields.field` form, then `field_add` twice + `Complex.add_re` | OK — real-part linearity used correctly |
| `next_representation` | :6871 | ✓ | one cycle preserves `CycleRepresentation` | 4 goals, each `rw [next_*]` then `simp only [… , Finset.sum_add_distrib]`; the alias goal ends in `ring` | OK |
| `next_coefficient_bands` | :6898 | ✓ | one cycle preserves `CoefficientBands` at the doubled band | `omega` twice on `max v.residualBand 1` (symbolic, no numerals) + `HarmonicResidual.residualBlock_band` | OK |
| `CycleState` | :6939 | ✓ | 3-field structure: state, coefficients, axisymmetricAlias | structure | OK |
| `CycleState.step` | :6947 | ✓ | one cycle on the bundled triple | def | OK |
| **`CycleState.iterate`** | :6952 | ✓ | `iterate p c seed 0 = seed`, `iterate p c seed (n+1) = step (iterate … n) (p n) c` | structural recursion on `ℕ` | OK — **the only recursion in the file**; see §Kernel-risk (1) |
| `iterate_zero`,`iterate_succ` | :6957,:6960 | ✓ | the two defining equations | `rfl` | OK — one iota step each |
| `iterate_representation` | :6963 | ✓ | if the seed is represented and *every* iterate's signed blocks share carriers, every iterate is represented | `induction n` + `next_representation` | OK / **E3** (the hypothesis `hc` is quantified over all `n` at the iterate itself) |
| `iterate_bands` | :6975 | ✓ | bands are preserved along the recursion | `induction n` + `next_coefficient_bands` | OK |
| `iterate_residual_band` | :6984 | ✓ | the residual block at step `n+1` is band-limited by the *new* band | term proof applying `(p n).next_residual_band` to `iterate … n` | OK — **off-by-one checked**: step `n+1` uses parameters `p n`, matching `iterate_succ` |

### E. Quantitative payloads — every site carrying `κ ≤ 1/100000`

Owners (line of the theorem, cone status): `meanUpdate_residualBlock_next` :2184 ✗,
`signedTensorRemainder_divergence_mem` :2414 ✗, `twoWaveUpdates_cumulative` :2695 ✗,
`gaugeTemporalStage_next_mean` :3000 ✗, `gaugeRankStage_next_mean` :4417 ✗,
`finish_mean_stages` :5417 ✗, `residual_gain_local` :7370 ✗,
`NativeDynamics.residual_gain_local` :7429 ✗, `nativeSignedStage_mean_debt` :7716 ✗,
**`meanStages_constructed` :8021 ✓**, `uniform_residual_gain` :8185 ✗,
`bandNativeSignedStage_mean_debt` :8253 ✗, `uniform_residual_gain` :8386 ✗,
`fourStage_mean_gain` :8471 ✗, **`finalBlock_uniform_cumulative` :8612 ✓**,
**`meanStages_residual_gain` :8673 ✓**, `mean_gain_from_waves` :9016 ✗,
**`waveStages_residual_gain` :9521 ✓**, **`waveStage_mean_gain` :9665 ✓**,
**`finalBlock_pressure_cumulative` :9833 ✓**.

| decl | line | cone | statement | mechanism | verdict |
|---|---|---|---|---|---|
| `meanIncrement_of_cumulative` | :7347 | ✓ | `CumulativeBounds s m → IncrementBounds s (9/10) m` | `⟨by convert! h.radial using 1; norm_num, h.angular, h.axial⟩`. Checked against `MeanIncrementBounds.lean:387-395`: `CumulativeBounds` = (radial 19/10, angular 9/10, axial 9/10); `IncrementBounds s (9/10)` needs (radial 9/10+1, angular 9/10, axial 9/10). `9/10+1 = 19/10` exactly — **no weakening, no off-by-one** | OK |
| `finalBlock_pressure_cumulative` | :9833 | ✓ | the final block's pressure stays in the *base* class (exponent 1) given old 1, particular 1+σ, signed 1+σ−κ | two `mono_exponent (by linarith)`: needs `1 ≤ 1+σ` and `1 ≤ 1+σ−κ`, true from `σ ≥ 1/5`, `κ ≤ 1e-5` | OK |
| `finalBlock_uniform_cumulative` | :8612 | ✓ | final block velocity stays in class `1/2`, and its distance to a `primary` block stays in `17/25` | `mono_exponent` to `1/2` and to `17/25`; needs `17/25 ≤ 1/2+σ` i.e. `0.68 ≤ 0.7` ✓ and `17/25 ≤ 1/2+σ−κ` i.e. `0.68 ≤ 0.69999` ✓ (margin **1e-5**, not tight-but-false). The second part's `change … ; ring` reorders `(a−p)+b+c` into `a+b+c−p`, using `finalBlock` (:5087) definitionally — I checked that unfolding is real | OK |
| `meanStages_residual_gain` | :8673 | ✓ | the residual block's uniform velocity class survives the two mean stages at exponent `1/2+(σ+1/10)` | conclusion exponent equals hypothesis `hold`'s `1/2+σ+1/10` up to `add_assoc`; the content is `meanStage_residual_uniform` (imported). **This is a transport theorem, not a gain theorem, despite the name** | OK (name is misleading — see E1) |
| `waveStages_residual_gain` | :9521 | ✓ | after both wave stages the residual block is in `UniformVelocity … (1/2+σ+1/10)` and the final block is still mode-solenoidal | 124 lines; the only arithmetic is `mono_exponent (show 1/2+σ+1/10 ≤ 1+σ-3*κ by linarith)` (⟺ `3κ ≤ 2/5`) and 3 more `by linarith`; the +1/10 is *imported* in hypotheses `hlinearP` (`1+σ-3κ`) and `hlinearS` (`1+σ-4κ`) | OK, content imported |
| `waveStage_mean_gain` | :9665 | ✓ | one wave stage: pressure difference, cumulative bounds, both residuals in `1+σ−κ`, defect in `σ−κ`, and the derived request in `σ−κ` | delegates to `gaugeWaveStage_mean_from_covariance`; `show 9/10 ≤ (1+σ)-κ by linarith` (⟺ `κ ≤ 3/10`); closes with `simpa only [show 1+(σ-κ) = 1+σ-κ by ring]` and `show (1+σ-κ)-1 = σ-κ by ring` — both are *identities*, no strengthening | OK |
| `meanStages_constructed` | :8021 | ✓ | the temporal+rank stages produce: both increments in `1+σ−2κ`, pressure difference in `1+σ−2κ`, cumulative bounds, **defect in `σ+1/10`**, θ-residual in `1+(σ+1/10)`, axial residual (minus the temporal alias) in `1+(σ+1/10)` | 109 lines of plumbing; the *gain* enters at :8103 as `show 1 + (σ + 1/10) ≤ (1 + σ - 2*κ) + 9/10 - 2*κ by linarith` handed to `MovingMomentBounds.rankStage_defectBounds` | **UNCLEAR / E1** — the 1/10 per-cycle gain is a slice of a **9/10 gain asserted by an imported lemma**; this file only certifies `1/10 ≤ 9/10 − 4κ` |
| `finish_mean_stages` | :5417 | ✗ | earlier variant of the same composition | identical gain import at :5495 | UNCLEAR / E1 |
| `fourStage_mean_gain` | :8471 | ✗ | the whole cycle (2 wave stages + temporal inverse + rank solve) as one mean/debt gain: `DefectBounds G.slowStrip (σ+1/10)` | 125 lines; chains `gaugeWaveStage_mean_from_covariance` → `bandNativeSignedStage_mean_debt` → `meanStages_constructed`; final pressure step is `class_congr` + `change` + `ring` on a telescoping sum `(u₁−u)+(u₂−u₁)+(v−u₂)` | OK as composition; gain still traces to E1 |

### F. `ConstructedSignedLinear` (:3814-3982), sampled

| decl | line | cone | statement | mechanism | verdict |
|---|---|---|---|---|---|
| `contextRealBase` / `complexBase_eq_realLift` | :3818,:3822 | ✓ | the complexified base is the `realLift` of the real triple | `funext; fin_cases i <;> rfl` — definitional | OK |
| `WaveFrameMatch` | :3871 | ✓ | a 5-field record pinning `s.epsilon = c.operators.epsilon`, radius, radial/frequency/axial base equalities | structure | OK — this is the right way to force two frames to agree; no `Classical.choice`, no coercion |
| `WaveFrameMatch.base`,`.harmonicResidual` | :3885,:3894 | ✓ | consequences of the record | rewriting by the record's fields | OK |
| `linearBlockField_eq_real`,`linearBlockField_eq_modeResidual` | :3835,:3907 | ✓ | the linear block field equals the real/mode residual under the frame match | 36-line rewriting chains, each step a named linearity lemma | OK (spot-checked, not fully re-derived) |
| `SignedParameters.Control.full_bounds` | :3943 | ✓ | from a `Control` record and a request in `MeanClass … (B−1/2−κ)`, four wave-class bounds: amplitude `B−κ`, pressure `B+1/2−κ`, cutoff difference `B+1/2−2κ`, constructed-good `B+1/2−4κ` | single application of `SignedWaveUpdate.signed_bounds` with 14 fields of the record | OK — pass-through; the analytic content is in `SignedWaveUpdate` |
| `SignedParameters.goodBlock` | :3962 | ✓ | the good block is `coefficientBlock … (constructedGood …) 0` — **pressure coefficient literally `0`** | def | OK, note S4: the good block carries no pressure by construction |
| `SignedParameters.Control.good_bounds` | :3968 | ✓ | the good block satisfies `WaveBounds s P (B+1/2−4κ)` | takes `.2.2.2` of `full_bounds` (the `B+1/2−4κ` component — the right one), restricts from the product strip to the zero section via `class_zeroSection` + `sectionStrip_productStrip`, and discharges the pressure half with `MemClass.zero` (legitimate: the pressure *is* 0) | OK |

### G. Imported predicate definitions I verified (the meaning of every bound above)

* `MemClass` (`WeightedClasses.lean:110-114`): `bounds : ∀ m : ℕ, ∃ C ≥ 0, ∃ p : ℕ, ∀ n x ∈ domain, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (f n) x‖ ≤ C · ε_n^α · growth(n,x)^p · w n x`.
  **Quantifier order is the sound one**: `C` and `p` are chosen *before* the band `n` and the point
  `x` (they may depend on the jet order `m`, which is correct for an all-order class). This is
  pattern (B) and it passes. `UniformClass` (`LabelSumBounds.lean:34-40`) additionally puts the
  label `l` inside the `∀`, i.e. `C, p` are uniform in the label too — also the sound order.
* `growth n x = slow n · max 1 (delta x)⁻¹` (`:52`). So each class tolerates an arbitrary *fixed*
  power `p` of `slow n` and of the inverse edge distance. I checked the **concrete** instantiation:
  `slow := BaseContextAssembly.slowScale = max 1 (ChartScales.S n)` with `S n = n²`
  (`ChartScales.lean:28`), while `epsilon h n = Q n ^ h` (`ChartScales.lean:29`) with `Q n ≤ 1`
  decaying geometrically. Hence the gain `ε^α` is geometric in `n` and the tolerated loss
  `slow^p` is only polynomial in `n`: **the classes are not made vacuous by the `growth` factor.**
  This was my main vacuity worry and it is resolved *for the concrete strip*.
* `MemClass.mono_exponent` (`:191`): `MemClass s w α f → β ≤ α → MemClass s w β f`, proved with
  `Real.rpow_le_rpow_of_exponent_ge (epsilon_pos) (epsilon_le_one) hβα`. Sound, and it only ever
  *weakens*. All 41 `mono_exponent` uses in `CorrectionStep.lean` therefore go in the safe
  direction by typing.
* `UniformVelocity s P α a := ∀ i j, j ≠ 0 → UniformWaveClass … (a l).velocity n i j`
  (`UniformHarmonicInteraction.lean:24`): **the `j = 0` Fourier mode is excluded from every
  velocity bound in this file.** I checked that the companion hypothesis
  `hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l)` used at :9539 is
  `∀ n i, b.velocity n i 0 = 0` (`HarmonicWaveInteraction.lean:277`) — so where it is assumed, the
  excluded mode is *identically zero* and the exclusion is harmless. It is assumed for
  `v.blocks`; I did **not** verify it is assumed for every block appearing in every consumer.
* `CumulativeBounds` / `IncrementBounds` (`MeanIncrementBounds.lean:387-395`): the radial component
  always carries `+1` relative to angular/axial. Every `IncrementBounds`/`CumulativeBounds`
  statement in `CorrectionStep.lean` that I read respects that offset.
* `thetaResidual`/`axialResidual`/`gr` (`MeanIncrementBounds.lean:328,333,338`) and
  `Operators.radialDiv c f = dr f + c • (invRadius * f)`, `viscosity c f = ε·(∂_r² + r⁻¹∂_r + ∂_z² − c·r⁻²)`.

**Note S1 (a suspicion I resolved).** `radialCovarianceChange` (:76) carries the **opposite sign**
of `thetaCovarianceChange` (:70) and `axialCovarianceChange` (:73), plus an extra `+invRadius·X 1 1`.
That looks like a sign error until you read `MeanIncrementBounds.lean:338`: `gr` is defined as
`-( time m.radial + radialDiv 1 (rr + W 0 0) + dz (zr + W 2 0) − invRadius*(θθ + W 1 1) − viscosity 1 m.radial )`,
i.e. with an **overall negation**, while `thetaResidual`/`axialResidual` are not negated. Perturbing
`W 0 0, W 2 0, W 1 1` inside that expression gives exactly
`−radialDiv 1 (X 0 0) − dz (X 2 0) + invRadius·X 1 1` = :76, character for character. The three
weights (`radialDiv 1` radially and axially, `radialDiv 2` for θ) and the viscosity connection
parameters (1 radial, 1 angular, 0 axial) are the textbook cylindrical values for an axisymmetric
field. **Verdict: OK, and this is a real consistency check that could have failed.**

**Note S2.** `time = slowTime + fastTime = −(ε ∂_{eT}) + fastCoefficient·∂_{vT}`
(`MeanIncrementBounds.lean:56-63`) has a *minus* on the slow time derivative, and
`timeDirection` (:376) is `fastCoefficient•vT − ε•eT` — the same combination. The two conventions
agree inside this file; the absolute sign of `eT` is fixed elsewhere. Not a defect here, but a
place where an external sign convention is load-bearing.

**Note S4.** `goodBlock` (:3962) has literal pressure `0`, so its pressure bound in
`good_bounds` (:3968) is discharged by `MemClass.zero`. Honest, but it means "good block bounds"
say nothing about pressure; the pressure is carried by other blocks.

## Kernel-risk assessment

Full-file mechanical scan of `CorrectionStep.lean` (all 9,849 lines):

| token | hits |
|---|---|
| `decide`, `native_decide` | **0** |
| `macro` / `elab` / `syntax` / `notation`-decl / `macro_rules` at line start | **0** |
| `set_option`, `axiom`, `sorry`, `unsafe`, `partial`, `deriving`, `attribute` | **0** |
| `inductive` | **0** |
| `termination_by`, `Acc.rec`, any `.rec` application | **0** |
| `Nat.pow/div/mod/gcd/beq/ble` | **0** |
| numerals with ≥5 digits | 20, and **all 20 are the same real literal `1/100000`** in a hypothesis `κ ≤ 1/100000` (lines :2186, :2416, :2696, :3004, :4425, :5418, :7377, :7430, :7720, :8023, :8188, :8257, :8387, :8472, :8614, :8674, :9025, :9522, :9668, :9834) |
| `if … then … else` | **0** — so pattern (D) (junk `else 0`) is *absent from this file* |
| `nlinarith` / `calc` | 0 / 0 |
| `norm_num` | 1 (:7349) |
| `omega` | 2 (:6900, :6932) |
| `linarith` | 85 |
| `Classical.` | 0 |

**Vector (1) — recursors / inductives / well-founded recursion.** The file declares **no
inductive type**. It declares **23 structures** (all `Prop`-valued invariant records except
`CycleCoefficients` :4993, `CycleParameters` :5002, `CycleState` :6939,
`SignedParameters.Dynamics` :3982, which are data). The **only** recursive definition is
`CycleState.iterate` (:6952), structural recursion on `ℕ`, compiled to `Nat.rec`/`brecOn`. The
kernel must perform recursor reduction in exactly three places in this file: the two `rfl` proofs
`iterate_zero` (:6958) and `iterate_succ` (:6961), and the term proof `iterate_residual_band`
(:6984). Each is **one iota step at depth 1** on a symbolic `n` — the kernel never unfolds
`iterate` to a numeral depth, because no theorem in this file instantiates `n` with a literal. Three
further proofs (`iterate_representation` :6963, `iterate_bands` :6975 and, in consumers,
`ActualCycleResidualBounds.lean:884`) use the *induction principle* rather than reduction. Structure
eta is used pervasively (anonymous constructors `⟨…⟩`, projection-of-constructor `rfl`s such as
:5147, :6816) but only on small `Prop`/data structures with ≤ 10 fields; no nested or indexed
inductive family, no large elimination, no `Acc.rec`. **Kernel exposure on vector (1): minimal and
bounded — 3 single-step `Nat.rec` reductions.**

**Vector (2) — GMP / numeral arithmetic.** There is no `Nat` numeral arithmetic. All numerals are
small `ℝ` rationals (`1/5`, `9/10`, `17/25`, `19/10`, `1/100000`, `2`, `3`, `4`, `10`) appearing in
`linarith`/`norm_num` goals. `linarith` emits a rational-certificate proof term whose numerals are
of the size of the input literals (denominators ≤ 100000, i.e. ≤ 6 digits): the kernel checks
`ℝ`-field/`OrderedField` lemma applications with `Nat`/`Int` literals of at most a few digits. The
two `omega` calls (:6900, :6932) are on **symbolic** `max v.residualBand 1`, not literals. The one
`norm_num` (:7349) proves `9/10 + 1 = 19/10`. **Nothing here forces a large GMP computation; peak
kernel numeral work is ~6-digit rational arithmetic.** Note the one place where a *number* grows:
`residualBand := 2 * max v.residualBand 1` (:6830) doubles per cycle, but it stays symbolic — no
`decide`/`Nat.pow` ever evaluates it.

**Vector (3) — custom metaprogramming.** Zero hits in `CorrectionStep.lean`. The only non-standard
syntax is `local notation` inside proofs' surrounding sections
(`u₁`/`w₂`/`u₂` at :8464-8466, and `state` at `CorrectionAnalyticStep.lean:652` for the consumer).
`local notation` is *not* in the briefed "any instance is a finding" list (it is pure surface
abbreviation, elaborated away and invisible to the kernel), but I flag it because it makes the
`fourStage_mean_gain` statement (:8471-8520) much harder to read than it needs to be, and it is the
one place in my scope where the printed statement and the elaborated statement differ
substantially. Two `attribute`/`local instance` hits exist in **`InitialPhysicalData.lean:28`**
(`attribute [local instance] Classical.propDecidable`) — that file was delegated; see §Delegated.

**Bottom line for kernel trust:** for this file, all three vectors are essentially empty. If the
Lean kernel is being exploited anywhere in this artifact, it is not here. I confirmed this by scan
plus targeted reading and did not spend further budget on it, per the brief.

## Escalations

**E1 (highest). The per-cycle "gain" this file claims is a slice of a 9/10 gain asserted by an
imported lemma; `CorrectionStep.lean` only certifies `1/10 ≤ 9/10 − 4κ`.**
`CorrectionStep.lean:8103` (and the identical `:5495`) hands
`show 1 + (σ + 1/10) ≤ (1 + σ - 2*κ) + 9/10 - 2*κ by linarith` to
`MovingMomentBounds.rankStage_defectBounds`. Everything downstream — `meanStages_constructed`
(:8021), `fourStage_mean_gain` (:8471), and hence the σ ↦ σ+1/10 per-cycle improvement that the
whole scheme lives on — is that one imported inequality plus bookkeeping. Corroborating statistic:
**374 of 418 theorems in this file contain no arithmetic tactic at all**; the file proves almost no
estimate itself.
*Question for an expert:* does `MovingMomentBounds.rankStage_defectBounds` really deliver a `9/10`
improvement of the *defect* exponent for the rank stage, with constants uniform in the band, or is
its `9/10` an artifact of the `growth^p` slack in `MemClass`?
*What would settle it:* read `MovingMomentBounds.rankStage_defectBounds` end to end and identify
the analytic mechanism producing 9/10 (it should be a `radialMoment`/inverse-divergence estimate);
then check that the same `p` (polynomial degree) is not being silently increased at every cycle —
`MemClass` allows a *different* `p` at each application, and 1/10 per cycle × unboundedly many
cycles is only meaningful if `p` and `C` do not blow up with the cycle index.

**E2. `fullResidual` (:396) is the PDE residual *plus* `virtualDivergence` *plus* `errors.base`, and
the controlled object `fullGoodResidual` (:402) subtracts `errors.total` on top of that.**
So "the residual is small" in this file means "residual + virtual stress divergence + base error −
excluded total is small". `fullResidual_eq_good_add_excluded` (:414) is `simp [fullGoodResidual]`,
i.e. definitionally content-free — it cannot be used as evidence that the excluded terms are small.
*Question:* are `u.errors.base`, `u.errors.gaussian`, `u.errors.aliasError` and
`c.virtualTheta`/`c.virtualAxial` each bounded *independently*, in the same class and at an exponent
at least as good as the residual's, at the point where the headline theorem is assembled?
*What would settle it:* for the final candidate (`ActualCandidateConstruction.lean`), exhibit the
bound on each of the four excluded channels and check that `fullResidual` itself — not
`fullGoodResidual` — is what the blow-up argument consumes.

**E3. The representation invariant of the recursion is conditional on a same-carrier hypothesis
quantified over all cycles.** `iterate_representation` (:6963) requires
`hc : ∀ n l, SameCarrier ((iterate p c seed n).coefficients.blocks l) ((p n).signedBlock … l)`,
and `finalBlock_oscillation` (:6838) shows why: without it, `addBlock` is *not* field addition and
`CycleRepresentation` fails. `particular_carrier` (:6816) is `⟨rfl,rfl,rfl⟩` (free), but the signed
block's carrier match is assumed. It is consumed at
`ActualCandidateConstruction.lean:83` (and `CycleStateCoherence.lean:609` proves a per-`j` version).
*Question:* is `hc` discharged unconditionally there, or is it itself assumed / derived from a
`SameCarrier` field that the signed-block *constructor* only satisfies for the primary column?
*What would settle it:* trace the argument passed as `hc` at `ActualCandidateConstruction.lean:83`
to a closed proof, and check no hypothesis of the enclosing theorem re-introduces it.

**E4. The residual band doubles every cycle** (`nextCoefficients` :6830:
`residualBand := 2 * max v.residualBand 1`), so after `J` cycles the band is `2^J · max(b,1)` and
the number of active Fourier modes grows geometrically, while `labels` never grows (:6825).
*Question:* does any constant in the final assembly depend on the residual band (a mode count, a
Bernstein/Sobolev factor, a `Finset.sum` over the band)? If yes, a per-cycle constant that is
uniform in `n` but grows with `J` breaks the telescoping.
*What would settle it:* search the consumers of `CoefficientBands` for a bound whose constant is a
function of `v.residualBand`, and check the `J → ∞` limit in `ActualCandidateConstruction`.

**E5 (low, but cheap to settle). `GaugeSupported.directional` (:4503) has no differentiability
hypothesis**, so it also holds when `fderiv` returns its junk value 0. That is harmless for a
*support* conclusion, but the derived operators `.dr` (:4508), `.dz` (:4518), `.time` (:4523),
`.radialDiv` (:4529), `.viscosity` (:4534) are then support statements about expressions whose
*values* are junk unless smoothness is supplied separately.
*Question:* at every site where a `GaugeSupported (o.viscosity …)` fact is combined with an
*equation* about `o.viscosity …`, is the accompanying `SmoothOn`/`ContDiffOn` hypothesis present?
*What would settle it:* `state_gr_moving_regular` (:4574) is the model of doing it right (it returns
`SmoothOn ∧ GaugeSupported` as a pair); check that consumers always take the pair, never the support
half alone.

**E6 (presentational, but audit-relevant). Two lemma names claim more than their statements.**
`meanStages_residual_gain` (:8673) proves *no gain*: its conclusion exponent `1/2+(σ+1/10)` is its
hypothesis `hold`'s exponent `1/2+σ+1/10` modulo `add_assoc`. Likewise
`finalBlock_uniform_cumulative` (:8612) and `finalBlock_pressure_cumulative` (:9833) are
`mono_exponent` weakenings. None of these is false; but a reader (or a Comparator-style statement
check) that treats "…_gain" as evidence of an estimate will be misled.
*What would settle it:* nothing to verify — record it so the audit's coverage numbers are not read
as "264 estimates checked".

## Residue — what I could not check

1. **No build.** Every judgement is source-level. I did not confirm that these files compile, that
   the implicit-argument elaboration matches my reading, or that instance resolution picks the
   `StripData`/`Operators` I assumed. In particular, all statements involving
   `HarmonicWaveInteraction.productStrip`, `sectionStrip`, and `movingStripData` depend on strip
   *equalities* being definitional (`hs : movingStripData … = G.strip` at :8521 is proved by
   `simp only [Geometry.strip, G.inner_eq, G.outer_eq]`); I read those as plausible but did not
   re-elaborate them.
2. **~350 unread proof bodies** (the structural `simp only [<defs>]` congruence mass in
   `TemporalComposition` :579-731, `PhysicalRepresentation` :906-1012,
   `RankMeanComposition` :1014-1117, `CommonTemporalConstruction` :1728-2016,
   `SignedTensorRemainder` :2259-2445, `GaugeTemporalResidual` :2816-3034,
   `ConstructedSignedLinear` :3983-4219, `PeriodizedNativeBounds` :5503-5846,
   `NativeEquations` :5848-6215, `PeriodizedSignedLinear` :6217-6440,
   `ParticularLinear` :6442-6726, `PeriodizedCurl` :6996-7213, `CoherentReferenceParticular`
   :7896-7999, `UniformParticularGain` :8118-8242, `UniformSignedGain` :8324-8446,
   `ActualGaussianMeans` :8769-8955, `ActualMean` :8982-9106, `AnalyticInvariant` :9378-9506,
   `ActualWaveCycleGain` :9508-9635). A `simp only` with a list of definitions cannot prove a false
   equation, but it *can* hide which definition was unfolded; a defect of the "silently a different
   quantity" kind could live there. My sample covered every fingerprint class but not every
   instance.
3. **The imported analytic content.** `SignedWaveUpdate.signed_bounds`,
   `MovingMomentBounds.rankStage_defectBounds`, `HarmonicMeanInteraction.*`,
   `LabelSumBounds.*`, `GaugeDebtIncrement.temporalStage_debt_mem`,
   `gaugeWaveStage_mean_from_covariance` — all outside my scope and all where the actual estimates
   live (E1).
4. **Non-emptiness / non-vacuity of the concrete strip.** `StripData` (`WeightedClasses.lean:31`)
   permits `domain = ∅` (`isOpen_domain` holds for `∅`) and `zeta = 0`. A `∅` domain would make
   every class in this file vacuously true. Every theorem here takes the strip as a *parameter*, so
   this is not a defect of `CorrectionStep.lean`; it must be settled at the instantiation
   (`ActualInitialization.lean:651`, `ActualCycleGeometry.lean:40`). I did **not** verify that the
   final strip's domain is non-empty or that `zeta` is not identically zero. **This is the single
   cheapest possible total-collapse check for the whole Navier-Stokes half and I recommend someone
   do it explicitly.**
5. **`j = 0` mode coverage.** I verified the exclusion is harmless where `ZeroMode` is assumed
   (:9539), not that it is assumed everywhere it is needed.
6. **`CONE.csv` disagreements.** 14 of the 20 `κ ≤ 1/100000` payload theorems are marked
   `in_cone=False`, including `fourStage_mean_gain` (:8471) — the file's most substantial
   composition. Either the cone extraction misses them (they may be reached only through instance
   synthesis or `@[simp]`, the known blind spot named in `COVERAGE.md`), or the headline theorems
   genuinely do not use them. I did not resolve which.

## Delegated sub-audits (siblings spawned by this worker)

Two read-only children were spawned for the secondary files, each with the same threat model and
deliverable contract:

* `NavierStokes/InitialPhysicalData.lean` → `_sub-ns-initialphysicaldata.md`
  (specifically tasked with `attribute [local instance] Classical.propDecidable` at `:28` and the
  junk `else 0` branches near `:368`/`:376`, including a repo-wide consumer search for those
  branches).
* `NavierStokes/TerminalEdgeFactor.lean` → `_sub-ns-terminaledgefactor.md`.

### `TerminalEdgeFactor.lean` — child `tef-audit` verdict (report: `_sub-ns-terminaledgefactor.md`)

235 decls (62 `def` / 173 `theorem`); all 235 statements read, 188 proofs read in full.
Verdicts: **OK 233, UNCLEAR 1, KERNEL-RISK 0, SUSPICIOUS 0** (plus 3 "weak-but-true"). No false
statement found. Kernel: 0 `decide`/`native_decide`/`axiom`/`sorry`/`macro`/`inductive`/`.rec`/
`termination_by`, no numeral above 2 digits. Its three findings, which I am carrying up:

1. The 3 headline in-cone theorems (`TerminalEdgeFactor.lean:1467`, `:1562`, `:1659`) are
   unquantified-ε collar continuity and are **near-tautological**: `profileAxialStress_edge_jets`
   (`:1308`) kills *all* axial jets at `x = 0`, so the tilt is 0 and `coneGap(η,0) = 2` exactly.
   The cone conclusion holds because `Tz` is flat-zero, not because of any dynamics. Only consumer
   is `TerminalEdgePaper.lean:20`. The load-bearing quantitative statement is elsewhere:
   `TerminalCone.lean:398 profile_cone_margin` (`3/2 ≤ coneGap`, `δ ≤ 5/2`).
2. `normalizedParam` (`:1088`) is **junk exactly at the blow-up endpoint**: `η² = 1` gives
   `Real.log 0 = 0` hence `timeOf = 0` (the *first* time, not `t = 1`). All 18 dictionary lemmas
   (`:1090-1241`) carry a *strict* `η² < 1`, and every consumer (`TerminalCone.lean:204,215,225,
   234,247`) passes strict — so no error, **but the physical↔profile bridge does not exist at
   `|η| = 1`**, contrary to the docstring at `:692-698`.
3. The whole file is one inequality doubled: with `spatialExponent (1+h) = -1/2 - h`,
   `2(s·H − z·H') + H = -2hH − 2zH'`, so `profileCarrier_radial_gap` (`:1404`, `nlinarith`) is
   literally 2× `RadialHeatProfile.profile_h_logSlope_lt` (`:708`). Zero slack: `v > 2` and every
   cone conclusion die if that convention or that lemma shifts.

### `InitialPhysicalData.lean` — child `ipd-audit` verdict (report: `_sub-ns-initialphysicaldata.md`)

230 decls (177 `theorem` / 48 `def` / 5 `abbrev`; **zero** `structure`/`inductive`/`instance`/
`axiom`). Whole file displayed, ~1,400 lines re-derived; only two passages left statement-level
(`:1790-1832`, `:1909-1975`). Verdicts: **OK 230, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0**, where
"OK" = "follows from the cited imports by the shown mechanism". Its findings:

1. **The `else 0` junk branches at `:368`/`:376` are not a live bug, with a demonstrated reason.**
   The gate `0 < x.1.1` is exactly `t < 1`. Chain: `slowFast x = ((x.1.1,…),x.2)`
   (`PhysicalClassBounds.lean:623`) + `cylindricalMap` (ibid `:637`) make `(graph…w).2.1.1`
   defeq to `(commonLift…w).1.1`; `graph_time_pos` (`PhysicalMeanJetBounds.lean:226`) derives the
   gate from `w.1 < 1`; `preterminal = {w | w.1 < 1}` (`PhysicalWaveSum.lean:386`). Every
   value-reading lemma discharges the `if` with a *proof* (`ite_eq_left` at `:1069, :1078, :1200,
   :1212, :1517, :1526`); the support lemmas only use "amplitude ≠ 0 ⇒ info" (`:550` even
   *extracts* `0 < t`); `sourceStrip_time` (`:1060`) makes the branch unreachable on the chart
   domain. **Consequence to escalate:** the potential `B N0` is identically 0 for `t ≥ 1`, hence
   discontinuous at `t = 1`, and all regularity lives on the *open* set `preterminal` only.
2. Kernel risk nil by census, not assumption: 0 `decide`/`native_decide`/`axiom`/`macro`/
   `set_option`/`termination_by`/`Acc.rec`/`sorry`; **largest literal in the file is 4**; every `^`
   is `rpow` with a symbolic exponent. The `attribute [local instance] Classical.propDecidable` at
   `:28` is needed **only** by 4 `dite`s on `L ∈ active` (a `Set.range`, at `:268, :283, :599,
   :920`); since the file contains no `decide`, that instance can never reach the kernel as a
   computation, and `ite_eq_left`/`dite_eq_left` (Lean core `Init/Core:1179,1204`) hold for *any*
   instance.
3. Pattern-A/B traps checked and clean: quantifier order preserved (`∃C` pulled out before `intro`
   at `:125, :326, :951`); the `ℕ`-subtraction gap is discharged by `Nat.sub_sub_self` +
   `index_le_native` (`:1834`); `SignedLabel = Fin 2 × Label`, so every `(l.2,l.1)` swap
   (`:2377, :2406, :2533, :2772, :2808`) is sign-first *consistently*; pressure exponents cancel
   explicitly (`-(2*A*h) + (2*A*h) = 0` at `:2086`).

Its escalations: is any consumer's domain **not** contained in `preterminal`? Does
`piece_cartesian_velocity` really turn a `Q^(-h)` potential into a `Q^(A·h)` velocity under `curl`
(the one unverified exponent balance)? And — echoing my own residue item 4 — **nothing in that file
proves the fields are non-zero anywhere: all 177 theorems survive if `cartesianPotential ≡ 0.`**

Their verdicts are in those files; this report does not claim their coverage. For the record, my own
scan of the two files found: `InitialPhysicalData.lean` — 13 `norm_num`, 4 `nlinarith`, 2 `calc`,
3 `omega`, 6 `linarith`, 1 `attribute`, 1 `local instance`, 1 `if…then…else`, 1 `Classical.`,
1 `.choose`, 0 `decide`, 0 `inductive`, 0 metaprogramming; `TerminalEdgeFactor.lean` — 43
`norm_num`, 4 `nlinarith`, 4 `calc`, 9 `positivity`, 29 `linarith`, and **0** hits for every
token in the "any instance is a finding" list.
