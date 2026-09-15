# Deep audit worker report -- SUMMABILITY / CONVERGENCE behind `exists_scales`
Repo: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5). READ-ONLY; no build (no Mathlib on disk). All claims from source text.
Scope question: parent audit B/C -- is the `Nonempty (Scales c B)` instance behind
`EulerPacketInduction.constructionScales` (Euler/PacketInfiniteConstruction.lean:68) vacuous, and are its
"convergent series" trivially satisfiable?

## Scope

READ IN FULL (7 files, 84 declarations):
| file | lines | decls |
|---|---|---|
| Euler/PacketSourceScaleChoice.lean | 246 | 20 |
| Euler/PacketInductionScales.lean | 221 | 16 |
| Euler/PacketInfiniteConstruction.lean | 77 | 12 |
| Euler/PacketCommonScaleChoice.lean | 78 | 1 |
| Euler/PacketPressureSeries.lean | 129 | 8 |
| Euler/ParentRenewalPrefix.lean | 139 | 8 |
| Euler/ParentRenewalScaleCosts.lean | 256 | 19 |

READ TARGETED (statement + full proof of the cited decls only):
* Euler/EulerProof.lean:18983-19052 (`polynomial_over_growth_summable`, `exp_neg_le_reciprocal`,
  `exponential_decay_summable`, `exponential_decay_real_power_summable`), 19769-19782
  (`polynomial_source_scale_summable`), 20346-20406 (`source_exponential_geometric_majorant`,
  `source_exponential_tsum_bound`, `source_exponential_bound_tendsto_zero`), 20519-20539
  (`exists_uniform_stage_choice`), 20543-20598 (`uniform_source_exponent_bound`,
  `uniform_source_cost_tsum_bound`), 20603-20626 (`source_uniform_small_sum_choice`),
  20644-20691 (`finite_source_uniform_small_sum_choice`).
* Euler/PacketSourceScaleBounds.lean:16-95 (`monomialCost` + nonneg/eq_exp/theta bound/error bounds).
* Euler/PacketSourceScaleSequence.lean:18-60 (`shear`,`frequency`,`spike`,`supportScale`,
  `previousShear`,`previousFrequency`,`olderShear`,`timeWidth`).
* Euler/PacketSourceScaleActual.lean:20-45 and 217-247 (`epsilon`,`priorError`,`neighborError`,
  `geometryError`,`baseErrorCost`,`geometryErrorCost`, `structure ActualBounds`, `actual_uniform_choice`).
* Euler/PacketPressureScaleCosts.lean:18-46 (`badCoefficient`, `badCost`, `badCostSpec`).
* Euler/PacketSourceScaleFromCosts.lean:13-73 (`uniformBounds_of_costs`, `actualBounds_of_uniform`).
* Euler/PacketUniformFrequencyScales.lean:89-96 (`eventually_all_frequency`).
* Euler/PacketInductionStage.lean:23-56 (`structure Stage` field list -- consumer of the series).
* Euler/ParentNormalPacketParameters.lean:33-40 (`frequencySpec`).
* Euler/PacketInductionScaleBounds.lean:96,99 and Euler/StageDisplacementConfinement.lean:125 (consumers).

NOT read: the geometric/PDE layer (`Stage.forwardNext`, `joinedNext`, `S.firstStage`, `StageGuards`
internals, `LowBounds`, `ParentFrame`). Those are a different worker's scope; see Escalation 1.

## Headline verdict on question 1: DOES `SmallSeries` ASSERT CONVERGENCE? -- YES. LOUDLY YES.

Verbatim, Euler/PacketSourceScaleChoice.lean:121-124:

```lean
structure SmallSeries (f : ℕ → ℝ) (δ : ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ f n
  summable : Summable f
  total_le : (∑' n, f n) ≤ δ
```

The parent's hypothesis ("merely a pointwise `f n ≤ delta` bound dressed up with a name that claims
more") is FALSE. `SmallSeries f δ` demands three things: pointwise non-negativity, honest Mathlib
`Summable f` (which for ℝ is unconditional convergence of the net of finite partial sums, and is NOT
implied by any pointwise bound), and `tsum f ≤ δ`. The `tsum`-junk-value loophole (a non-summable ℝ
series has `∑' = 0`, so `tsum f ≤ δ` alone is vacuous for δ ≥ 0) is CLOSED here by the separate
`summable` field. This is the strongest of the three fields and it is a genuine field, not a derived
sugar.

`SmallSeries.term_le` (:126-127) is the CONVERSE direction of the parent's suspicion: it *derives* the
pointwise bound `f n ≤ δ` from `summable`+`nonneg`+`total_le` via `Summable.le_tsum`. Name matches
statement. Verdict [OK].

Load-bearing check (does anyone actually consume the convergence, or only `term_le`?): consumed.
`Euler/PacketInductionStage.lean:23` `structure Stage` carries n-indexed bounds of the form
`low.Be ≤ initialCoefficientCost + ∑ i ∈ range n, initialIncrement S.J S.X i` (:41), `core_bound` (:42),
`pressure_bound` (:43-45), and `coupling_error : |frame.a-1| ≤ 2*∑ i ∈ range n, renewalCost ... i` (:48).
These are collapsed to n-FREE constants by `finite_sum_le` / `partial_sum_le`, which need exactly
`summable`+`nonneg`+`total_le` (Euler/PacketInductionScaleBounds.lean:96,99;
Euler/StageDisplacementConfinement.lean:125; Euler/ParentRenewalPrefix.lean:30). So the summability is
not decoration.

## Question 2: is the decay PROVED or ASSUMED? -- PROVED, all the way down to Mathlib.

Chain, bottom-up (each arrow = "proved from", not "assumed"):

1. `Euler/PacketSourceScaleChoice.lean:226` `def scaleSequence J X : ℕ → ℝ | 0 => X | n+1 => ((J+n:ℕ):ℝ)^2 * scaleSequence J X n`.
   So `x n = X * ∏_{k<n} (J+k)^2` -- super-exponential (indeed factorial-squared) growth. This is a
   DEFINITION, not a hypothesis; `scaleSequence_succ` (:232) is `rfl`.
2. `Euler/EulerProof.lean:18984 polynomial_over_growth_summable`: `Summable (fun n => (J+n)^A / x n)`,
   proved by `summable_of_ratio_test_tendsto_lt_one` with ratio limit 0 (18997), using the recurrence.
   Real proof, no hypothesis of summability.
3. `Euler/EulerProof.lean:19020 exponential_decay_summable`: `Summable (exp (-b * x n/(J+n)^A))`, by
   `exp(-t) ≤ 1/t` (19014) majorization against step 2.
4. `Euler/EulerProof.lean:20348 source_exponential_geometric_majorant`: each term
   `≤ r * r^n` with `r = exp(-b*(x 0/J^A)) < 1`, i.e. GEOMETRIC decay, proved from
   `polynomial_scale_geometric_lower` + `stage_count_le_two_pow`.
   `20369 source_exponential_tsum_bound`: `∑' ≤ r/(1-r)` via `tsum_geometric_of_abs_lt_one` (20386).
   `20390 source_exponential_bound_tendsto_zero`: `r/(1-r) → 0` as `x 0 → ∞`.
5. `Euler/EulerProof.lean:20519 exists_uniform_stage_choice` picks J so that
   `c*((J+n)^a/(J-d+n)^B) ≤ b/4` for ALL n (needs `a < B`, supplied by the `CostSpec.a_lt_B` field);
   `20543/20578 uniform_source_exponent_bound` / `uniform_source_cost_tsum_bound` absorb the polynomial
   and log prefactors into half the exponent and conclude `∑' ≤ r/(1-r)`.
6. `Euler/EulerProof.lean:20644 finite_source_uniform_small_sum_choice` makes the choice UNIFORM over a
   `Fintype ι` of cost specs by `J := max 3 (Finset.univ.sup Ji)` (20656) plus an index-shift transport
   of `hcoeff` (20665-20673), and `X₀` by `eventually_all` (20680).
7. `Euler/PacketSourceScaleChoice.lean:40 finite_uniform_choice` converts that to
   `Summable ((s i).cost J x) ∧ tsum ≤ δ ∧ ∀ n, cost ≤ δ`, where the `Summable` half comes from
   `polynomial_source_scale_summable` (:59-62 -> EulerProof:19769) -- i.e. the summability is proved
   INDEPENDENTLY of the tsum bound, which is what closes the junk-value hole of step 5.

Nowhere in this chain is "summable" or "geometric decay" a hypothesis or structure field that the
caller must supply. `CostSpec` (:18-33) assumes only bare numeric side conditions
(`d ≤ 2`, `0 ≤ a`, `a < B`, `a ≤ N`, `0 < b`, `0 < C`) -- and `a < B` is exactly the inequality that
MAKES the exponent negative, so it is the right hypothesis, not a smuggled conclusion.
Every concrete spec discharges them by `norm_num`/`positivity` on literals
(`sourceCostSpec`, :84-119; `correctionCostSpec`, PacketInductionScales.lean:45-60;
`goodCostSpec`, PacketPressureSeries.lean:15-30; `badCostSpec`, PacketPressureScaleCosts.lean:29-46;
`activationCostSpec`, ParentRenewalScaleCosts.lean:194-209).

Junk-cost check (is a "cost" secretly 0, making SmallSeries trivial?): NO.
`monomialCost J d B a b c C p q x n = C*((J+n:ℕ):ℝ)^p*(x n)^q*exp(-b*(x n/(J+n)^a)+c*(x n/(J-d+n)^B))`
(PacketSourceScaleBounds.lean:16-19) with `0 < C` -- strictly positive for `x n > 0`. Same for
`goodCost` (PacketSourceScaleChoice.lean:147), `parentSquareRatio` (:144), `coefficientCost` (:137),
`extraTimeCost` (:140), `renewalCost` (ParentRenewalScaleCosts.lean:22), `frequency`/`shear`
(PacketSourceScaleSequence.lean:18-27, `exp` of positive things). No degenerate/zero envelope.

## Per-declaration findings

### Euler/PacketSourceScaleChoice.lean
* `CostSpec` :18-33 -- record of 9 numeric parameters + 6 side conditions. No analytic content assumed. [OK]
* `CostSpec.cost` :35 -- `= monomialCost J s.d s.B s.a s.b s.c s.C s.p s.q x`. Thin alias. [OK]
* `finite_uniform_choice` :40-74 -- for any Fintype family of specs: `∃ J ≥ 3, ∀ δ>0, ∃ X₀ ≥ 8`, and for
  every `x` with `x 0 ≥ X₀` and the quadratic recurrence: `Summable (cost)`, `tsum ≤ δ`, `∀ n, cost n ≤ δ`.
  Mechanism: `finite_source_uniform_small_sum_choice` for the tsum bound + `polynomial_source_scale_summable`
  for summability + `monomialCost_eq_exp` to identify the two shapes (`tsum_congr`, :65) + `Summable.le_tsum`
  for the pointwise part (:71). QUANTIFIER ORDER is honest: J first, then δ, then X₀ -- no circular
  "choose X₀ depending on the sequence it must control". [OK]
* `SourceCost` :76-82 -- 7-constructor enum + hand-written `Fintype` (`complete` by `cases c <;> simp`).
  `deriving DecidableEq` -- the only derived Decidable instance in scope; not used in a `decide`. [OK]
* `sourceCostSpec` :84-119 -- 7 literal specs; every side condition `by norm_num`/`positivity`.
  All literals small (≤ 128, plus `(2*C)^A` symbolic). [OK]
* `SmallSeries` :121-124 -- see headline. [OK]
* `SmallSeries.term_le` :126, `.weaken` :129, `.mono` :132-135 -- all three are correct and their names
  match: `mono` uses `Summable.of_nonneg_of_le` + `tsum_le_tsum` (needs the nonneg field: present). [OK]
* `coefficientCost`/`extraTimeCost`/`parentSquareRatio`/`goodCost` :137-149 -- explicit positive analytic
  expressions in `exp`, `sqrt`. `parentSquareRatio` is a quotient of two `exp`s (never 0 denominator). [OK]
* `UniformBounds` :151-157 -- five `SmallSeries` fields; `extraTime` is universally quantified over the
  frame coefficient `a` with `0 ≤ a n ≤ 2` (uniformity over the not-yet-built coupling). [OK]
* `source_uniform_choice` :162-223 -- builds `UniformBounds` from the 7 literal specs at `δ/3`, sums
  three of them (`Summable.tsum_add`, :189-191) and `mono`s each field down through the ACTUAL cost
  (`sourceCoefficientError_bound`, `sourceExtraTime_bound`, `sourceTimeRatio_bound`,
  `sourceParentSquareRatio_eq`, `sourceGoodCost_bound`). The `mono` direction is the safe one
  (actual ≤ envelope). [OK]
* `scaleSequence` :226-228 + `scaleSequence_zero/_succ` :230,:233 (`rfl`) -- structural ℕ recursion; see
  Kernel-risk. [OK]
* `explicit_sequence_uniform_choice` :237-244 -- instantiates the previous theorem at the concrete
  sequence, discharging the recurrence hypothesis by `scaleSequence_succ`. No new assumption. [OK]

### Euler/PacketCommonScaleChoice.lean
* `exists_common_guards` :18-76 -- THE aggregator. Statement: for a Fintype family `s` and constants,
  `∃ J ≥ 3, ∀ η>0, ∃ X₀ ≥ 8, δ` with `0 < δ ≤ min η (1/2)` such that for all `X ≥ X₀`:
  `ActualBounds J D C c X δ`, `∀ i, SmallSeries ((s i).cost J (scaleSequence J X)) δ`,
  `SmallSeries (badCost ...) δ`, `SmallSeries (2*CM*goodRatio*goodCost ...) δ`, and `∀ n, StageGuards ... n`.
  Mechanism: one call to `literal_uniform_choice` on the DISJOINT SUM `Sum SourceCost ι` (:34-38), so
  a single J/X₀ serves the source costs and the caller's extra costs -- this is the anti-circularity
  device and it is real. δ is defined BEFORE X is chosen (:41), the base scale is then pushed up twice
  (`max Y Z`, :53) where Z comes from `baseErrorCost_tendsto_zero ... .eventually_le_const` (:50-52).
  `ActualBounds` is then assembled by `uniformBounds_of_costs` + `actualBounds_of_uniform` (:62-70).
  No hypothesis of summability anywhere in the signature. [OK]
  NOTE (not a defect, but the place to look for the real content): the `∀ n, StageGuards` conjunct is
  produced by `stage_guards` (:75), which I did NOT read. Escalation 2.

### Euler/PacketPressureSeries.lean
* `goodCostSpec` :15-30 / `goodCost_le_spec` :32-43 -- envelope for `2*CM*goodRatio*goodCost`; the
  constant is `1+2*CM*goodRatio` and the bound goes through `sourceGoodCost_bound`. [OK]
* `add_series` :45-49 -- `SmallSeries f a → SmallSeries g b → SmallSeries (f+g) (a+b)`, via
  `Summable.add` + `Summable.tsum_add`. Correct; the `tsum_add` rewrite requires both summabilities and
  they are supplied. [OK]
* `finite_sum_le` :51-53 -- `∑ n ∈ range N, f n ≤ a` for EVERY N, from `Summable.sum_le_tsum` (needs
  nonneg on the complement: supplied by `hf.nonneg`) then `total_le`. The bound `a` is N-FREE. This is
  the exact "uniform over all n" chaining the parent asked about: YES it chains. [OK]
* `upper_increment_series` :55-62, `initial_increment_series` :64-69 -- combine `add_series`+`mono`; the
  increment is only assumed dominated pointwise, so the direction is safe. [OK]
* `uniform_choice` :73-104 -- adds good/bad costs to any finite family via `Sum ι Bool`. [OK]
* `literal_uniform_choice` :108-127 -- additionally delivers `X^1000 ≤ exp (X/(J-1)^7)` and
  `X^D ≤ exp (X/(J-1)^4)` from `eventually_pow_le_exp`, then `max Y Z`. This is what lets the
  n=0 exceptional stage (`previousShear 0 = X^1000`, `previousFrequency 0 = X^D`) join the same
  envelope. [OK]

### Euler/ParentRenewalPrefix.lean
* `relative_step_error` :14-21, `accumulate_step` :34-43 -- telescoping `|a(n+1)-1| ≤ 2∑_{i<n+1} e i`. [OK]
* `partial_sum_le` :23-25 -- same n-free uniform bound as `finite_sum_le`. [OK]
* `bounds_of_accumulated_error` :27-32 -- from `η ≤ 1/4` and the partial-sum bound, `a n ∈ [1/2,2]`
  for EVERY n. This is the payoff of convergence: the bound does not degrade with n. [OK]
* `coupling_prefix` :47-65, `coupling_and_tilt_prefix` :69-95 -- strong induction (`Nat.strong_induction_on`)
  where the step hypothesis may only use the already-bounded prefix (`∀ i ≤ n`). Statement is
  `∀ n ≤ N, ...` for an arbitrary N, so combined with n-free constants this is genuinely uniform.
  No `Acc.rec`/`termination_by`; `Nat.strong_induction_on` is a structural helper. [OK]
* `stage_congr_at` :97-112 -- field-wise transport of `StageGuards` along `a n = b n`, `β n = γ n`. [OK]
* `stage_guards_at` :117-137 -- SUBTLE and worth stating: to get a guard at a SINGLE stage n from the
  uniform theorem, it extends the two current scalars to artificial global sequences
  `b := fun _ => a n` and `γ i := β n * (scaleSequence J X n)^2 / (scaleSequence J X i)^2` (:125-126),
  applies `stage_guards`, then transports back. The `γ` trick works because `γ i * x i ^2` is
  CONSTANT (:129-131, `div_mul_cancel₀` with `pow_ne_zero` from `quadratic_growth_pos`). No division by
  zero, no future-stage hypothesis. Legitimate; not circular. [OK]

### Euler/ParentRenewalScaleCosts.lean
* `maximumError` :17-18 -- `geometryErrorCost` at the CONSTANT coupling `fun _ => 2` (the worst allowed
  value), so its summability does not presuppose the not-yet-built couplings. [OK]
* `errorConstant` :20 -- `30000000*neighborStabilityConstant*CF^2`; ℝ literal only. [OK]
* `renewalCost` :22-23 -- `3000/scaleSequence J X n + errorConstant CF * maximumError J D C c X n`.
  Division by `scaleSequence` -- non-zero whenever `0 < X`, and every consumer carries `0 < X`/`8 ≤ X`.
  [OK] (see Kernel/junk note K5)
* `maximumError_series` :29-31 -- instantiates `ActualBounds.coefficient` at `fun _ => 2` with
  `0 ≤ 2` and `2 ≤ 2`. [OK]
* `scaleSequence_double` :33-39, `reciprocal_geometric` :41-53, `reciprocal_series` :55-65 -- proves
  `1/x n ≤ (1/X)*(1/2)^n` by induction and hence `SmallSeries (1/x n) (2/X)` against
  `summable_geometric_two`. HONEST geometric series, computed constant `2/X`. [OK]
* `scale_series` :67-71 -- `SmallSeries f δ → SmallSeries (C*f) (C*δ)` for `0 ≤ C`, via `tsum_mul_left`. [OK]
* `renewal_series` :73-82 -- `SmallSeries (renewalCost) (6000/X + errorConstant CF * δ)`. [OK]
* `renewal_series_small` :86-93 -- weakens to any `η > 0` given `12000/η ≤ X` and
  `2*(1+errorConstant CF)*δ ≤ η`. The two smallness sources (base scale, δ) are separated correctly. [OK]
* `physical_error_le_maximum` :96-134 -- geometric-data error at the present stage ≤ `CF^2*maximumError`;
  uses `a ≤ 2`, `Θ ≤ sourceTheta`, `G ≤ CF(1+olderShear)`, `d ≤ prior+neighbor`. `Θ^40 ≤ sourceTheta^60`
  via `1 ≤ sourceTheta` (:130-131) -- exponent inflation in the SAFE direction. [OK]
* `coupling_polynomial_le` :136-150 -- `y^4+σ^2y^2+8σy^3 ≤ 10y` given `y ≤ 1`, `σ ≤ 1`. [OK]
* `actual_errors_le_cost` :152-190 -- couplingError and tiltError ≤ `renewalCost` at the SAME n. This is
  the bridge from geometry to the summable envelope. Hypotheses are all about stage n only. [OK]
* `activationCostSpec` :194-209, `activationCost_eq` :211-215 -- `cost = (2*CF+1)*parentSquareRatio`.
  Name and statement agree. [OK]
* `previousShear_one_le` :217-224, `activation_ratio_le` :226-246, `activation_smallness` :248-254 --
  `CF*(1+previousShear)+e ≤ ζ*shear` from `term_le` of the activation series. Uses only the POINTWISE
  consequence; correct usage of `term_le`. [OK]

### Euler/PacketInductionScales.lean
* `geometryConstant` :22 / `_one` :24-27, `activationMargin` :29 / `_pos` :32-34 / `_small` :36-43 --
  positive constants with `positivity`; `activationMargin = 1/(32*(activationConstant+1))`, denominator
  provably positive, so no `1/0` junk. [OK]
* `correctionCostSpec` :45-60 + `correctionCost_eq` :62-68 -- CHECKED BY HAND: with `a=2, b=1/4, c=0,
  C=1, p=q=0`, `monomialCost = exp(-(1/4)*(x n/(J+n)^2))`, and `frequency J X n = exp(x n/(J+n)^2)`
  (PacketSourceScaleSequence.lean:21), so `frequency^(-(1/4):ℝ) = exp(-(1/4)*x n/(J+n)^2)`. The claimed
  equality is TRUE, not a name-inflation. Proof is `simp only [...,← exp_mul, rpow_ofNat]; congr 1; ring`. [OK]
* `extraCost` :70-73 -- `Sum Unit Bool → CostSpec`: frequency spec, activation spec, correction spec.
  Exactly the three extra series in `Scales`. [OK]
* `initialIncrement` :75-77, `pressureIncrement` :79-81 -- explicit sums of `badCost`, `frequency^(-1/4)`,
  `goodCost`. Non-negative, non-degenerate. [OK]
* `Scales` :83-112 -- 22 fields. Numeric: `3 ≤ J`, `2000 ≤ D`, `8 ≤ X`, `0 < δ ≤ 1/16`,
  `δ ≤ activationMargin`, `1000000*geometryConstant*δ ≤ 1`. Analytic: `ActualBounds J D 4 c X δ`,
  `FirstScaleGuards J D X`, `∀ n, UniversalFrequency (frequency J X n)`,
  `∀ n, B ≤ previousFrequency J D X n`, SIX `SmallSeries` fields (frequency/activation/correction/bad/
  good at δ, renewal at 1/4), `baseHorizon J X ≤ 1`, `baseGuardCost ... ≤ 1/2`.
  NO field asserts the existence of a packet, a frame, or a future stage -- the docstring at :6-8 is
  accurate. So `Scales` is a pure parameter record. [OK]
* `exists_base_power` :114-121 -- `∃ D ≥ 2000` with `firstFrequencyPower < D*(theta/100)`, from
  `exists_nat_gt`. [OK]
* `exists_scales` :123-193 -- THE TARGET. `Nonempty (Scales c B)` for every `c ≥ 0` and every `B`.
  Mechanism, in order: (i) D from `exists_base_power`; (ii) J and the δ-parametrised choice from
  `exists_common_guards extraCost D _ 4 c geometryConstant gradientConstant gradientConstant
  hessianConstant 80` (:125-127); (iii) `η := min (1/16) (min activationMargin (min (1/(1000000*geometryConstant))
  (1/(8*(1+errorConstant frameConstant)))))`, `0 < η` by `positivity` (:128-132); (iv) `X₀, δ` from the
  choice at η (:140); (v) an `∀ᶠ X in atTop` conjunction of SEVEN eventual conditions (:150-171) and
  `hevent.exists` to pick ONE X (:172); (vi) the record is assembled field by field (:181-193).
  I checked the parameter alignment of every series field against `exists_common_guards`'s conclusion and
  against `extraCost`: `frequency_series = hdata.2.1 (Sum.inl ())`, `activation_series = ... (Sum.inr false)`,
  `correction_series` via `correctionCost_eq` (:175-180), `bad_series = hdata.2.2.1`,
  `good_series = hdata.2.2.2.1` (badCost J 4 gradientConstant gradientConstant hessianConstant 80 and
  2*gradientConstant*goodRatio*goodCost -- MATCHES the field types at :104-108), `renewal_series` from
  `renewal_series_small` with `12000/(1/4) = 48000 ≤ X` supplied by `hlarge` (:159,:191-192) and
  `2*(1+errorConstant frameConstant)*δ ≤ 1/4` from `hηrenew` (:145-149).
  NOT VACUOUS: the witness is explicit up to two `Eventually.exists`/`exists_nat_gt` choices, all six
  series are genuine `Summable`+`tsum ≤ δ` facts inherited from the proved geometric-majorant chain, and
  δ is chosen before X. `Eventually.exists` on `atTop` (ℝ) needs `NeBot`, which holds -- no vacuity there. [OK]
* `Scales.initial_series` :199-203, `Scales.pressure_series` :205-209 -- `SmallSeries (initialIncrement) (2δ)`
  and `(pressureIncrement) (3δ)` by `add_series`. [OK]
* `Scales.stage` :211-218 -- delivers `StageGuards ... n` from `stage_guards_at` for a single n given
  `a n ∈ [1/2,2]`, `β n * x n^2 ∈ [1/2,2]`. [OK]

### Euler/PacketInfiniteConstruction.lean
* `Stage.successor` :21-25 -- `cases n`: `forwardNext` for n=0, `joinedNext` for n+1. Produces a term of
  the INDEXED family `Stage S (n+1)`. Not read: the two successor constructions. [UNCLEAR -- out of scope]
* `Stage.successor_time` :27-32, `stages_time` :48-50 -- equational bookkeeping. [OK]
* `stages` :39-41 -- `def stages : (n : ℕ) → Stage S n | 0 => S.firstStage | n+1 => (stages n).successor hq hB`.
  Structural recursion into a Type-valued indexed family. THIS is the real existence engine, not
  `exists_scales`. [KERNEL-RISK (low) -- see K1]
* `stages_zero` :43, `stages_succ` :45-46 -- both `rfl`. [KERNEL-RISK (low) -- K1]
* `stages_initial_step` :52-59 -- velocity of stage n+1 = velocity of stage n + high + mean. Content is
  in `joinedNext_initial_velocity`. [UNCLEAR -- out of scope]
* `stages_gradient_atTop` :61-63, `packets_gradient_atTop` :74-75 -- `Tendsto ... atTop atTop` from
  `Stage.gradient_atTop`. Not read. [UNCLEAR -- out of scope]
* `ConstructionScales` :65-66 -- `abbrev` for `Scales requiredExponent (commonThreshold ...)`. [OK]
* `constructionScales` :68-70 -- `Classical.choice (exists_scales (requiredExponent : ℝ)
  (commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))`.
  The `Nonempty` is proved at EXACTLY these parameters (`exists_scales` is universally quantified over
  `c ≥ 0` and over `B` with NO further constraint on B, and `requiredExponent : ℕ` cast to ℝ is `≥ 0`).
  So this is NOT a `Classical.choose` of a subclass-only statement. Downstream code can only use
  `Scales` fields, so opacity of the witness is harmless. [OK]
* `packets` :72 -- `stages constructionScales le_rfl le_rfl n`; the two `le_rfl`s discharge
  `requiredExponent ≤ q` and `commonThreshold ≤ B` because q and B were instantiated AT those values.
  Slightly self-serving but sound: no hypothesis is being dodged, the parameters were simply chosen
  equal to their own thresholds. [OK]

## Question 3 -- do the partial-sum bounds chain to a UNIFORM bound over ALL n? YES.

`finite_sum_le` (PacketPressureSeries.lean:51) and `partial_sum_le` (ParentRenewalPrefix.lean:23) both
have the shape `∀ N, ∑ n ∈ range N, f n ≤ a` with `a` independent of N, derived from
`Summable.sum_le_tsum` (which needs `0 ≤ f` on the complement -- supplied) followed by `total_le`.
Concretely the constants delivered to the induction are: `2*S.δ` for `initialIncrement`
(PacketInductionScaleBounds.lean:96), `3*S.δ` for `pressureIncrement` (:99), `1/4` for `renewalCost`
(the `Scales.renewal_series` field, PacketInductionScales.lean:109), and `S.δ` for the correction series
(StageDisplacementConfinement.lean:125). Those n-free constants are what `bounds_of_accumulated_error`
(ParentRenewalPrefix.lean:27, needs `η ≤ 1/4`) converts into `a n ∈ [1/2,2]` for all n, and what keeps
`Stage.exterior_bound`/`core_bound`/`pressure_bound`/`coupling_error`
(PacketInductionStage.lean:41-48) from degrading as n grows. No "for each n there is a C_n" sleight of
hand: the quantifier order is `∃ J, ∀ δ, ∃ X₀, ∀ X, ∀ n`.

## Question 4 -- (a) subclass-`choose`, (b) limit interchange, (c) junk value?

(a) NO. The only `Classical.choice` in scope is PacketInfiniteConstruction.lean:69, and its argument is
`exists_scales` at exactly the instantiated parameters (see above). The other choices are
`Classical.choose`-style `choose` at EulerProof.lean:20654 (one stage index per element of a Fintype,
then `max`/`sup` with an explicit index-shift transport at 20665-20673 -- the transport is proved, not
assumed) and `Eventually.exists` at PacketInductionScales.lean:172 / PacketCommonScaleChoice.lean:50 /
PacketPressureSeries.lean:122 (`eventually_atTop.1`), all on `atTop` filters that are `NeBot`.

(b) NO limit/sum interchange. Every `tsum` manipulation is guarded by an explicit `Summable`:
`Summable.tsum_add` (PacketSourceScaleChoice.lean:189-191, PacketPressureSeries.lean:48),
`tsum_mul_left` (ParentRenewalScaleCosts.lean:70, EulerProof.lean:20386),
`Summable.tsum_le_tsum` (PacketSourceScaleChoice.lean:135, EulerProof.lean:20385,20595),
`Summable.sum_le_tsum` / `Summable.le_tsum` (PacketPressureSeries.lean:53, ParentRenewalPrefix.lean:25,
PacketSourceScaleChoice.lean:127,:71). `tsum_congr` at PacketSourceScaleChoice.lean:65 is pointwise.
No `Tendsto` of a series is used as a substitute for uniform control; the two `Tendsto` uses
(`baseErrorCost_tendsto_zero`, PacketCommonScaleChoice.lean:51; `source_exponential_bound_tendsto_zero`,
EulerProof.lean:20390) are immediately turned into `eventually_le_const`, i.e. a concrete threshold.

(c) One REAL junk-value hazard exists but is CLOSED at the use site, and I flag it as the single
name-vs-statement wart of the chain:
`EulerProof.lean:20603 source_uniform_small_sum_choice` and `:20644 finite_source_uniform_small_sum_choice`
conclude ONLY `(∑' n, exp (...)) ≤ δ` with NO `Summable` conjunct. Taken alone, such a statement is
satisfiable by a non-summable series (Mathlib's `tsum` of a non-summable ℝ family is `0 ≤ δ`). It is
nevertheless a true and non-vacuous statement here, because its proof goes through
`uniform_source_cost_tsum_bound` (:20578) which obtains the bound from
`hcost.tsum_le_tsum hmajor hsum` with a genuine `Summable` majorant (:20593-20595); and the caller
`finite_uniform_choice` (PacketSourceScaleChoice.lean:59-62) re-proves `Summable` independently. So:
[UNCLEAR->OK] statement is junk-vulnerable in isolation, repaired by construction and by the caller.
Other junk-value candidates checked and clean: ℕ truncated subtraction `(J-d+n : ℕ)`, `(J-1+n : ℕ)`,
`(J-1 : ℕ)` (PacketSourceScaleBounds.lean:16-19, PacketSourceScaleChoice.lean:141-149,
PacketPressureSeries.lean:111,:119-121) -- always guarded by `3 ≤ J` and `d ≤ 2` (CostSpec.d_le_two), and
`hp : (0:ℝ) < (J-1:ℕ)` is discharged by `omega` at PacketPressureSeries.lean:119;
divisions `3000/scaleSequence`, `12000/η`, `1/(32*(...+1))`, `1/(1000000*geometryConstant)`,
`β n * x n^2 / x i^2` -- all denominators proved non-zero (`quadratic_growth_pos`, `positivity`,
`pow_ne_zero`, ParentRenewalPrefix.lean:131,:137);
`rpow` with negative exponent (`frequency^(-(1/4))`, `previousFrequency^(-(1/4))`,
PacketInductionScales.lean:77, PacketSourceScaleActual.lean:22) -- bases are `exp _` or `X^D` with
`X ≥ 8`, so never the `0^(neg) = 0` junk branch. No `fderiv`/`deriv` junk-value in scope (the two
`fderiv` occurrences are in `Stage`'s hypotheses, PacketInductionStage.lean:33-39, out of scope).

## Kernel-risk

Repo-wide claim re-confirmed on my 7 files: ZERO `macro`/`elab`/`syntax`/`set_option`/`native_decide`/
`axiom`/`unsafe`/`partial`/`sorry`. (The `grep` hit for "partial" at PacketPressureSeries.lean:4 is the
English words "partial sums" inside a docstring.) So no custom metaprogramming finding here.

K1. Indexed-family recursor reduction, `rfl` on recursive data -- PacketInfiniteConstruction.lean:39
    (`stages`, structural recursion whose motive is the Type-valued indexed structure
    `Stage S : ℕ → Type`, PacketInductionStage.lean:23), with `stages_zero := rfl` (:43) and
    `stages_succ := rfl` (:46), plus `Stage.successor` (:21-25) and `successor_time` (:27-32) built by
    `cases n`. The kernel must whnf `Nat.rec`/`brecOn` applications at a dependent motive. Symbolic n,
    no numeral iteration, so cost is O(1) per unfolding. LOW risk, but it is the only place in scope
    where kernel defeq must reduce a recursor over an indexed family. [KERNEL-RISK low]
K2. `scaleSequence` (PacketSourceScaleChoice.lean:226-228) -- structural ℕ recursion on ℝ values with
    `scaleSequence_zero := rfl` (:230) and `scaleSequence_succ := rfl` (:233). Also
    `previousShear`/`previousFrequency`/`olderShear` (PacketSourceScaleSequence.lean:30-40) are
    non-recursive two-branch matches. No `termination_by`, no `WellFounded`, no `Acc.rec`, no
    `decreasing_by` in ANY of the 7 files. [KERNEL-RISK low]
K3. `decide`: ZERO occurrences in the 7 files. One nearby (`by decide : 4 ≤ 7`,
    PacketSourceScaleBounds.lean:73) -- two 1-digit ℕ literals; trivial for the kernel.
    `deriving DecidableEq` for `SourceCost` (PacketSourceScaleChoice.lean:78) is never fed to `decide`;
    the `Fintype` instance's `complete` is proved by `cases c <;> simp` (:82), 7 cases.
K4. `norm_num` census in scope: PacketSourceScaleChoice.lean 14 (lines 88,89,93,94,98,99,103,104,108,
    109,113,114,118,119 -- all `CostSpec` side conditions on 1-3 digit rationals);
    PacketInductionScales.lean 9 (55-59,117,127,192,217); PacketPressureSeries.lean 4 (25-28);
    ParentRenewalPrefix.lean 2 (57,85); ParentRenewalScaleCosts.lean 14 (31,52,76,121,138,139,148,149,
    181,182,204-207). All certificates are over ℚ with ≤ 8-digit numerators; the kernel's GMP `Nat`
    work is `Nat.ble`/`Nat.mul` on numbers below 10^8. Negligible.
K5. Big literals (all REAL, i.e. `(… : ℝ)` numerals inside inequalities, NOT ℕ literals the kernel must
    iterate): `1000000*geometryConstant*δ ≤ 1` (PacketInductionScales.lean:94,129,136,141,142;
    PacketCommonScaleChoice.lean:41,45,46,47), `48000` (PacketInductionScales.lean:151,159),
    `2000 ≤ D` (:89), `30000000` (ParentRenewalScaleCosts.lean:20,174,176), `3000`/`6000`/`12000`
    (ParentRenewalScaleCosts.lean:23,75,88), `X^1000` and `X^D` with `D ≥ 2000`
    (PacketSourceScaleSequence.lean:31,35; PacketPressureSeries.lean:111). The exponents 1000 and D are
    ℕ literals in `Monoid.npow` applied to a SYMBOLIC real X -- the kernel never unfolds them
    numerically (all lemmas used are `one_le_pow₀`, `pow_le_pow_right₀`, `pow_pos`, `eventually_pow_le_exp`).
    `2^(2*N+3)` at EulerProof.lean:20526,20531-20532 is symbolic in N and is handled by `omega` treating
    it as an atom. I found NO place where the kernel must compute a `Nat.pow`/`Nat.div`/`Nat.gcd` on a
    large numeral. [OK]
K6. `positivity` (44 uses) / `nlinarith` (14 uses) / `omega` (29 uses) in scope produce ordinary
    arithmetic certificates; `nlinarith only [...]` is always given an explicit hypothesis list, which
    bounds the certificate size. No `norm_num` extension, no `polyrith`. [OK]

## Escalations (ranked, with the exact expert question)

E1 (HIGH, and it is the correct target of the parent's worry -- the worry is simply in the wrong file).
   `exists_scales` is NOT the existence claim that can be empty: `Scales` (PacketInductionScales.lean:83)
   contains only numbers and series, and its `Nonempty` is honestly witnessed. The load-bearing existence
   is `Scales.firstStage : Stage S 0` and the two successors used by
   PacketInfiniteConstruction.lean:39-41 / :21-25.
   EXACT QUESTION for the Lean/PDE expert: "In `Euler/BaseInductionStage.lean`, is `Scales.firstStage`
   constructed from an explicit velocity field and an explicit `SmoothState`, or is it itself obtained
   from a `Classical.choice`/`Nonempty` whose proof only re-uses the `Scales` inequalities? And do
   `Stage.forwardNext` (Euler/PacketForwardSuccessor.lean) and `Stage.joinedNext`
   (Euler/PacketJoinedSuccessor.lean) return a `Stage S (n+1)` whose `parent`/`state` fields are built
   from an actual solution of the Euler system, or from a re-labelled copy of the previous stage
   (i.e. is `Stage` ever inhabited by a trivial/zero field)? Specifically: can
   `Stage.state.evolution.velocity` be identically 0 while all `Stage` fields still hold?"
E2 (MEDIUM). `exists_common_guards` (PacketCommonScaleChoice.lean:75) discharges
   `∀ n, StageGuards J D C c X K a β n` by `stage_guards` in `Euler/PacketSourceScaleGuards.lean`, and
   `StageGuards` itself (PacketSourceScaleGuards.lean:117) is a Prop-structure of 13 fields that I did
   not read. EXACT QUESTION: "Is any field of `StageGuards` (Euler/PacketSourceScaleGuards.lean:117-…)
   an inequality that is vacuously true for the chosen parameters -- in particular
   `compression`/`geometry_small`/`target_le_horizon` -- and does `stage_guards` derive them from
   `ActualBounds` or does it re-assume them?"
E3 (MEDIUM). Name-vs-statement wart, EulerProof.lean:20603 and :20644: the conclusion is a bare
   `∑' … ≤ δ` with no `Summable`. EXACT QUESTION: "Should
   `source_uniform_small_sum_choice`/`finite_source_uniform_small_sum_choice` be restated to carry
   `Summable`, so that no future caller can rely on a `tsum`-junk-value bound? (Today's only callers,
   `finite_uniform_choice` at Euler/PacketSourceScaleChoice.lean:40, re-prove summability, so this is a
   robustness question, not a soundness bug.)"
E4 (LOW). `Stage.gradient_atTop` (used at PacketInfiniteConstruction.lean:63,75) claims
   `Tendsto (fun n => (stages … n).activationGradient) atTop atTop`. That is the ONE unbounded-growth
   claim in this file. EXACT QUESTION: "Does `Stage.gradient_atTop` prove divergence from a per-stage
   multiplicative lower bound on `activationGradient`, or from a lower bound that is itself only
   `Eventually`? Does the blow-up statement of the paper depend on this `Tendsto` alone?"

## Residue

* NOT verified (no Mathlib build): that these files compile and that `#print axioms` shows only the
  three standard axioms. `Euler/BaseInductionStageNoOptions.lean:24` mentions `Quot.sound` in a
  docstring about axiom dependencies -- an author claim, not evidence.
* NOT read: `stage_guards` and `StageGuards` internals; `ActualBounds` consumers other than the ones
  cited; `Scales.firstStage`; `forwardNext`/`joinedNext`; `LowBounds`; `ParentFrame`; `EulerSmoothLimit`;
  `frequencyCostSpec`/`parameterEnvelope` (only `frequencySpec`'s call site checked);
  `sourceTheta_bounds`, `sourceCoefficientError_bound`'s own proof beyond its statement,
  `sourceExtraTime_bound`, `sourceTimeRatio_bound`, `sourceGoodCost_bound`,
  `baseErrorCost_tendsto_zero`, `eventually_firstScaleGuards`, `eventually_base_guards`,
  `universal_frequency_eventually`, `frequency_monotone`, `polynomial_scale_geometric_lower`,
  `stage_count_le_two_pow`, `polynomial_logs_uniformly_absorbed`.
* Verdict counts in scope: [OK] 62, [UNCLEAR] 4 (all four are "content lives in an unread file":
  `Stage.successor`, `stages_initial_step`, `stages_gradient_atTop`, plus the E3 wart which I resolve to
  OK at its use site), [KERNEL-RISK] 2 (both LOW: K1 indexed-family `rfl`/recursor, K2 `scaleSequence`
  structural recursion), [SUSPICIOUS] 0.
* Bottom line for the parent: the summability/convergence layer is REAL mathematics, honestly quantified,
  and non-vacuous. `SmallSeries` asserts `Summable` + `tsum ≤ δ`. Decay is PROVED from the explicit
  super-exponential `scaleSequence`, not assumed. If the Euler packet construction is empty, the
  emptiness is NOT here -- look at E1.
