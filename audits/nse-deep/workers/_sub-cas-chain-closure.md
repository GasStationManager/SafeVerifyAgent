# `StepData` chain-closure audit — does the NSE cycle induction chain?

READ-ONLY audit of `openai/NavierStokesAndEuler @ f9e8bc5`
(clone at `/home/gsm/.openclaw/workspace/repos/NSE`, no build run, no file modified).
All claims are source-level with `file:line`. Paths are relative to the repo root.

## 0. Verdict summary

| # | Question | Verdict |
|---|---|---|
| 0 | Does the induction chain on the live path? | **YES.** `ActualCyclePreservation.state_runInvariant` (`NavierStokes/ActualCyclePreservation.lean:826`) is a closed `theorem ∀ j`, with `StepData` *constructed*, not assumed. `CorrectionAnalyticStep.iterate_invariant` (`:657`) with its `data` hypothesis is the generic, unused-shaped version; the live path does not use it. |
| 1 | Any `WaveData` field bound that gets harder as σ grows? | **NO.** Every σ-carrying field is produced by a lemma that is *generic in the exponent* (`α : ℝ`, no bound), instantiated at `α = 1+σ-κ` / `1/2+σ`. Every σ-dependent side inequality either cancels σ exactly or is a *lower* bound on σ (so it gets easier). |
| 1b | `particularLinear` (1+σ-3κ), `signedLinear` (1+σ-4κ) | Proved per-cycle from the invariant alone; the loss is a **fixed** `-3κ` / `-4κ` shift, σ-free. The consuming inequalities are `1/2+σ+1/10 ≤ 1+σ-3κ` and `1/2+σ+1/10 ≤ 1+σ-4κ` — **σ cancels** (`NavierStokes/CorrectionStep.lean:9587`, `:9627`). |
| 2 | Is κ the same fixed number every cycle? | **YES.** `κ` is literally `ChartScales.kappa = 1/100000` (`NavierStokes/ChartScales.lean:24`), pinned by the local notation `local notation "κ" => ChartScales.kappa` (`ActualCyclePreservation.lean:38`) and `kappa_small : κ ≤ 1/100000` (`:74`). It never depends on `j`. |
| 3 | `primaryBand`, `tailStart`, `cells` per-cycle or uniform? | All three are **cycle-index-free constants**: `primaryBand := 1`, `cells := ActualCoreSupport.refinedCarrier`, `tailStart := (ActualPrimary.choice B N0).prepared.N + 1` (`ActualCyclePreservation.lean:579`, `:583`, `:596`). Nothing downstream needs more than that. |
| 4 | `cross_tail` — who proves it, σ-independent? | `ActualSignedMeanBinding.family_requested_cross_tail` (`NavierStokes/ActualSignedMeanBinding.lean:655`), reducing to the purely geometric `requested_cross_tail` (`:463`) via `partitionFactor_eq_one` / `physicalScale_tail`. Its statement is **fully generic in the family exponents `α δ β η`** and mentions no σ. **σ-independent.** |
| 5 | Invariant's σ-dependent fields | **CONFIRMED**: exactly `residual` (1/2+σ, `CorrectionStep.lean:9440`), `mean` (σ, `:9443`), `debt` (σ, `:9445`). Everything else in `CycleAnalyticInvariant` (`:9408-9461`) is σ-free, incl. `wave` 1/2 (`:9432`), `pressure` 1 (`:9434`), `difference` 17/25 (`:9436`). |
| 6 | Missing cycle-(n+1) input / wrongly-quantified growing constant? | **No missing input.** One honest caveat, stated loudly in §6: every class constant `C` is an existential *inside* each cycle's `Prop`, deliberately not uniform in the cycle index (`WeightedClasses.lean:37`, `:111`, and the comment `:125` "Stage constants are deliberately not uniform in the stage index"). The chain therefore delivers a *sequence of statements*, each with its own constants; it does not by itself deliver anything uniform in `j`. |

## 1. The live path is closed — no `data` hypothesis survives

```
ActualCyclePreservation.state_runInvariant (B N0 hN) (j)            :826   theorem, induction on j
  |- initial_runInvariant                                           :773
  |- next_runInvariant                                              :817
       |- particularData = ActualParticularCycleData.actual_data     :812  (R.analytic, R.periodic, hN, hσ)
       |- next_runInvariant_of_particular                            :800
            analytic := (stepResult_of_particular ...).invariant      :805
              |- stepResult_of_particular                             :742
                   = CorrectionAnalyticStep.step ... kappa_small (stepData_of_particular ...)   :752
              |- stepData_of_particular                               :730
                   = stepData_of_waves H hN hσ hl (waveData_of_particular H hN hσ P)            :740
            coherent := ActualCycleCoherence.step ...                 :806
            periodic := ActualCyclePeriodicity.step ...               :809
```

Inputs of the whole run: only `B N0 : ℕ` and `hN : ActualCarrierGeometry.geometricThreshold ≤ N0`
(`ActualCyclePreservation.lean:826-828`). `σ` is the ledger `ActualIterationLedger.sigma j`
(`NavierStokes/ActualIterationLedger.lean:22`), with `sigma_formula : sigma J = 1/5 + J/10`
(`:36`), `sigma_succ` (`:38`), `sigma_admissible : 1/5 ≤ sigma J` (`:41`),
`sigma_tendsto_atTop` (`:110`). The step's `hσ` argument is always
`ActualIterationLedger.sigma_admissible j` (`ActualCyclePreservation.lean:833`, `:879`, `:891`).

Consumption is also closed: `ActualCandidateAssembly.runData` (`NavierStokes/ActualCandidateAssembly.lean:476-481`)
packages `invariant`/`step`/`particular` for **all** `j` into `ActualStageEstimates.RunData`
(`NavierStokes/ActualStageEstimates.lean:97-102`). No `sorry` anywhere under `NavierStokes/`
(grep, 0 hits).

**No σ upper bound exists anywhere on the live path.** grep of `σ ≤ / < σ / ≤ σ` over
`CorrectionAnalyticStep.lean`, `ActualCyclePreservation.lean`, `ActualParticularCycleData.lean`,
`ActualSignedOutputBounds.lean`, `ActualSignedMeanBinding.lean`, `ActualCycleAssembly.lean`,
`ActualParticularMeanGain.lean` returns only `1/5 ≤ σ` and `κ ≤ 1/100000` forms
(`CorrectionAnalyticStep.lean:471,523,658`; `ActualCyclePreservation.lean:557,690,731,743,756,790,802,814,819`;
`ActualParticularCycleData.lean:800,815`; `ActualCycleAssembly.lean:1006`;
`ActualParticularMeanGain.lean:104,138`).

## 2. Per-field construction of `StepData` (`CorrectionAnalyticStep.lean:470-502`)

Built by `stepData_of_waves` (`ActualCyclePreservation.lean:556-600`).

| `StepData` field | live proof, file:line | σ-dependent? | re-derives every n? |
|---|---|---|---|
| `waves` | `waveData_of_particular` `ACP:689-728` | yes (see §3) | yes |
| `primaryBand := 1` | `ACP:579` | no | constant |
| `primary_band` | `ACP:76-78` `primary_band` (`tangentBlock l).BandLimited 1`) | no | constant, fixed primary family |
| `envelope_nonneg/le_one` | `ACP:567-570` from `ActualInitialization.envelope_nonneg/le_one` | no | constant |
| `cells := refinedCarrier` | `ACP:583` | no | constant |
| `carrier_closed` | `ActualCoreSupport.refinedCarrier_closed`, `ACP:584` | no | constant |
| `carrier_cells := Subset.rfl` | `ACP:585` | no | constant |
| `normal` | `core_normal H hN` `ACP:273-281` | no (uses only `H`) | yes |
| `frequency` | `core_frequency H hN` `ACP:283-289` | no | yes |
| `angular` | `core_angular H hN` `ACP:291-297` | no | yes |
| `assembly` | `ActualCycleAssembly.assembly` `ACP:571`, family `ActualCycleAssembly.family` `ActualCycleAssembly.lean:1024-1030` | σ enters as family exponents `(1/2, 17/25, 1/2+σ-κ, 1+σ-2κ)` | yes |
| `labels` | `assembly_supports.1` `ACP:573,590`; `hl` from `R.coherent.labels`/`state_labels` (`ACP:159-163`, `:805`) | no | yes |
| `old_support`, `particular_support` | `ACP:591-592` (from `H.inputSupport`) | no | yes |
| `primary_smooth/periodic` | `family_primary_smooth/periodic` `ACP:593-594` | no | yes |
| `rank_geometry` | `rank_geometry H` `ACP:91-96` | no | yes |
| `tailStart` | `ACP:596` = `(choice B N0).prepared.N + 1` | no | constant |
| `cross_tail` | `ACP:598-600` → `ActualSignedMeanBinding.family_requested_cross_tail:655` | **no** | yes |

## 3. `WaveData` (`CorrectionAnalyticStep.lean:30-95`), field by field

Built by `waveData_of_particular` (`ActualCyclePreservation.lean:689-728`) from
`P : ActualParticularCycleData.Data x σ` and
`first := ActualParticularMeanGain.postParticular_gain H d hσ` (`ACP:695`).

| `WaveData` field | exponent | live prover | σ-loss / constraint |
|---|---|---|---|
| `carrier` | – | `ActualCycleParameters.invariant_fixedParameters_signed_carrier H` `ACP:698` | none |
| `particular` | 1/2+σ | `P.amplitude` = `ActualParticularCycleData.amplitude_bounds H hN` `APC:577-591` → `ActualParticularStageControls.assembled_bounds ... (native_residual H)` | pure re-index of `H.residual` at 1/2+σ; **no** σ constraint |
| `tangent` | 1/2+σ-κ | `signed_block_bounds first .1` `ACP:428-444` → `ActualSignedOutputBounds.actual_block_bounds G rfl c post (1+σ-κ)` `ASOB:246-268` | `actual_block_bounds` is generic in `α : ℝ` with **no** bound on α; outputs `α-1/2`, `α`, `α-κ`, `α-3κ` |
| `curl` | 1+σ-2κ | same, `.2.2.2.1` (`α-κ` slot) | as above |
| `particularPressure` | 1+σ | `P.pressure` = `pressure_bounds H hN` `APC:593-608` | none |
| `signedPressure` | 1+σ-κ | `signed_block_bounds .2.2.1` | none |
| smoothness fields (8) | – | `P.coefficients/…` `APC:519,534,549`; `signed_*_smooth` `ACP:453-468` | σ-free |
| `particularSolenoidal` | – | `P.solenoidal` = `APC:640` | σ-free |
| `signedSolenoidal` | – | `signed_solenoidal first` `ACP:627-630` → `ActualSignedCommonDynamics.actual_modeSolenoidal ... (1+σ-κ)` `ASCD:496` | generic α |
| `particularSupport` | – | `ActualCycleAssembly.cycle_refined_particular_inputSupport hN x c H.inputSupport` `ACP:712` | σ-free |
| `signedSupport` | – | `signed_inputSupport` `ACP:648-651` | σ-free |
| `particularGaussian` / `signedGaussian` | **∀ β** | `P.gaussian` = `gaussian_bounds H hN` `APC:621-638`; `signed_gaussian_bounds` `ACP:446-451` | all-exponent ⇒ trivially fine for any σ |
| field regularity / periodicity / support (9) | – | `P.field/periodic/support` = `field_regular H T hN` `APC:424-441`; `signed_*` `ACP:453-...` | σ-free, need `T : Periodic x` (carried in `RunInvariant`) |
| **`particularLinear`** | 1+σ-3κ | `P.linear` = `ActualParticularCycleData.linear_bounds H hN` `APC:691-729` | `good_bounds H hN` at `1+σ-3κ` (`APC:610-619`) **+ exact identity** `field_cancellation H hN` (`APC:668-689`) via `linearGoodBlock_cancel_uniform`. Loss is a fixed `-3κ`; **no σ constraint at all** (`_hσ` is unused in `actual_data`, `APC:800`) |
| **`signedLinear`** | 1+σ-4κ | `signed_linear_bounds H first` `ACP:632-646` → `ActualSignedCommonDynamics.actual_linearGood_bounds G rfl post (1+σ-κ)` `ASCD:512-530`, then `(1+σ-κ)-3κ = 1+σ-4κ` (`ACP:645`) | generic α, no bound; loss fixed `-3κ` |

Both cancellation estimates are therefore **re-derived at every cycle from the invariant at σ n**;
neither is an input that must be supplied afresh, and neither carries a σ-dependent constant or loss.

## 4. Why growing σ never bites: the σ-cancelling inequalities

`majorant s w α C p n x = C * s.epsilon n ^ α * s.growth n x ^ p * w n x`
(`NavierStokes/WeightedClasses.lean:78`) with `epsilon n ≤ 1` (`:36`). So **larger exponent =
strictly stronger bound**, and `mono_exponent` only *weakens* (`:191-202`). Growing σ therefore
means the per-cycle demands are analytically sharper; the question is only whether the proof's
inequalities survive. They do, and here is why — every σ-carrying inequality on the live path is
either σ-cancelling or a lower bound on σ:

| where | inequality | after simplification |
|---|---|---|
| `CorrectionStep.lean:9587` | `1/2+σ+1/10 ≤ 1+σ-3κ` (particular linear) | `3κ ≤ 2/5`, **σ cancels** |
| `CorrectionStep.lean:9627` | `1/2+σ+1/10 ≤ 1+σ-4κ` (signed linear) | `4κ ≤ 2/5`, **σ cancels** |
| `CorrectionStep.lean:7283` `hγm` (both stages, via `:9588`, `:9628`) | `γ ≤ β+H-1/2` with `γ=1/2+σ+1/10`, `β=1/2+σ(-κ)`, `H=9/10` (`:9615`) | `3/5 ≤ 9/10 (-κ)`, **σ cancels** |
| `CorrectionStep.lean:7283` `hγc` | `γ ≤ α+β-κ` | `3/5 ≤ 1-κ`, **σ cancels** |
| `CorrectionStep.lean:7283` `hγs` | `γ ≤ 2β-κ` | `17/100+3κ ≤ σ` — lower bound, **easier as σ grows** |
| `SignedMeanGain.lean:427` `hγd` (via `signed_tensor_bounds:462`, remainder at `1+σ+17/100+κ`) | `γ ≤ δ+β` | `2κ ≤ 1/100`, **σ cancels** (tightest σ-free margin found) |
| `SignedMeanGain.lean:427` `hγs` | `γ ≤ 2β` | `17/100+3κ ≤ σ` — lower bound |
| `CorrectionStep.lean:7693` (`difference_bounds` of the signed family) | `17/25 ≤ 1/2+σ` | `σ ≥ 9/50`; margin `1/50` at σ=1/5, growing |
| `CorrectionStep.lean:8632` (`finalBlock_uniform_cumulative`, rebuilds `difference` at 17/25) | `17/25 ≤ 1/2+σ-κ` | `σ ≥ 9/50+κ`; satisfied, growing |
| `CorrectionStep.lean:9704` (`waveStage_mean_gain`) | `9/10 ≤ (1+σ)-κ` | `σ ≥ κ-1/10`; trivially true, growing |
| `CorrectionAnalyticStep.lean:619-620` | `1 ≤ 1+σ` and `1 ≤ 1+σ-κ` | trivial, growing |

So the σ-dependent margins are all "σ ≥ 17/100+3κ" or "σ ≥ 9/50(+κ)" type, i.e. **satisfied at the
seed σ₀ = 1/5 with margins 3/100 and 1/50 and monotonically improving**. Nothing needs `σ ≤ …`.

### The mechanism that makes the σ-growing demand affordable

`CorrectionAnalyticStep.step` needs the two cross defects at the *σ-growing* exponent
`1+σ+17/100+κ` (`CorrectionAnalyticStep.lean:600`). That is supplied by
`SignedCrossDefectClass.residual_defects_all_exponents_of_primitive`
(`NavierStokes/SignedCrossDefectClass.lean:173-198`), which returns **`∀ γ : ℝ`** with no bound,
using exactly `d.tailStart` and `d.cross_tail` (`CorrectionAnalyticStep.lean:582-583`).
The engine is `FiniteHeadClass.meanClass_all_exponents`
(`NavierStokes/FiniteHeadClass.lean:112-115`, `:97-104`): outside a finite head the defect is
*identically zero* by the exact tail identity, so the exponent can be raised at the price of the
constant factor `comparison s N α β = 1 + Σ_{n<N} ε_n^(α-β)` (`FiniteHeadClass.lean:23-24`).
Note `α - β = (1+σ-κ) - (1+σ+17/100+κ) = -(17/100+2κ)` is **σ-free**, so even this finite-head
constant is the *same* at every cycle. This is the single most load-bearing structural fact:
the exact identity `cross_tail` converts an unbounded-in-σ requirement into a cycle-uniform cost.

The same "all-exponent" trick appears twice more in the invariant and is re-derived each cycle:
`axisFlat : ∀ β` via `ActualCycleExcluded.nextAxisymmetricAlias_all_powers`
(`CorrectionAnalyticStep.lean:616-621`, stored `:433`), and `gaussianFlat : ∀ β`
(`:429-430`). If either had been a single-exponent field, the induction would have failed
at the first cycle where the ledger exponent overtook it; both are `∀ β`, so it does not.

## 5. Ledger bookkeeping (item 2 in full)

* `ChartScales.kappa = 1/100000` (`NavierStokes/ChartScales.lean:24`) — a `def` on a `ℝ` literal, no index.
* `ActualIterationLedger.kappa = 1/100000` (`ActualIterationLedger.lean:32`), `kappa_admissible` (`:115`), `kappa_pos` (`:117`).
* The step is always called with `κ := ChartScales.kappa` and `kappa_small` (`ActualCyclePreservation.lean:38,74,753`).
* Per-cycle margins for the whole ledger: `ActualIterationLedger.all_cycle_margins` (`:119-128`) — stated for *all* `n` with `κ ≤ 1/100000`, i.e. σ-uniform.
* `fixed_ledger` (`:418-428`) records `sigma 0 = 1/5`, `sigma (n+1) = sigma n + 1/10`, `kappa_admissible` together.

Gain accounting per cycle: residual `1/2+σ → 1/2+σ+1/10` (`CorrectionStep.lean:9568`),
debt `σ → σ+1/10` and mean `1+σ → 1+(σ+1/10)` (`CrossBasedMeanComposition.lean:594-597`),
against fixed κ-losses of at most `4κ = 4·10⁻⁵` per cycle. The `1/10` gain is bought from the
`17/100` remainder margin (`SignedMeanGain.lean:467`), which is σ-free.

## 6. DISAGREEMENTS / caveats, stated loudly

1. **No missing cycle-(n+1) input.** I looked for one specifically. Every field of
   `CycleAnalyticInvariant` at `σ+1/10` is constructed in `assemble`
   (`CorrectionAnalyticStep.lean:389-449`), and the three σ-free auxiliary invariants that the
   *constructor* needs beyond the analytic one — `Coherent` and `Periodic` (needed by
   `actual_data`, `ActualParticularCycleData.lean:799`, and by `stepData_of_particular`'s
   `hl`) — are carried in `RunInvariant` (`ActualCyclePreservation.lean:768-771`) and stepped
   at `:806` and `:809`. `hl` itself is also independently provable: `state_labels` (`:159-163`).
   So there is nothing the cycle-n output fails to deliver.

2. **`actual_data` does not even use `hσ`** (`ActualParticularCycleData.lean:800`, the argument is
   named `_hσ`). That is strong evidence for the σ-uniformity claim, not against it: the entire
   particular-wave data package is σ-agnostic, with σ appearing only as the exponent parameter
   inherited from `H.residual`.

3. **The one thing that does grow with the cycle index** is not an exponent condition but the
   *constants*: every `MemClass`/`UniformClass` bound is `∀ m, ∃ C ≥ 0, ∃ p, …`
   (`WeightedClasses.lean:111-113`, `LabelSumBounds.lean:37-39`), so each cycle's classes carry
   their own `C_j, p_j`. The file says so explicitly: "Stage constants are deliberately not
   uniform in the stage index" (`WeightedClasses.lean:125`, `def StageClasses` `:126-127`).
   Concretely, the exponent-raising step multiplies `C` by `comparison` (`FiniteHeadClass.lean:103`),
   and the class at exponent `1/2+σ_j` is a bound by `C_j · ε_n^(1/2+σ_j)` with `ε_n ≤ 1`.
   This is quantified in the *right* place for the induction (inside each cycle's `Prop`, so the
   induction chains), but it is quantified in the *wrong* place for anything that needs a limit in
   `j`: `ActualStageEstimates.RunData` (`ActualStageEstimates.lean:97-102`) is a `∀ j` family of
   independent statements, and nothing in it forces `sup_j C_j < ∞`. **If the final quantitative
   NS claim needs a `j`-uniform constant (e.g. summing increments to a limit field), it must be
   produced elsewhere — this induction does not supply it.** That is the place I would attack
   next, not `StepData` constructibility.

4. **Sharpest numeric margins** (all satisfied, none σ-shrinking, but they are the thin spots):
   `2κ ≤ 1/100` in `remainderTensor_mem`'s `hγd` (`SignedMeanGain.lean:427` with
   `δ=17/25, γ=1+σ+17/100+κ`), and `17/25 ≤ 1/2+σ-κ` i.e. `σ ≥ 9/50+κ`
   (`CorrectionStep.lean:8632`) — margin `1/50` at the seed, improving by `1/10` per cycle.

## 7. Files read

`NavierStokes/CorrectionAnalyticStep.lean` (:30-95, :260-320, :380-460, :460-530, :560-630, :657-686),
`NavierStokes/ActualCyclePreservation.lean` (:1-100, :149-165, :273-300, :428-470, :540-600, :606-680, :682-933),
`NavierStokes/ActualParticularCycleData.lean` (:41-95, :573-660, :668-730, :795-822),
`NavierStokes/ActualParticularMeanGain.lean` (:52-158),
`NavierStokes/ActualSignedOutputBounds.lean` (:246-276),
`NavierStokes/ActualSignedCommonDynamics.lean` (:496-531),
`NavierStokes/ActualSignedMeanBinding.lean` (:463-513, :644-697),
`NavierStokes/ActualCycleAssembly.lean` (:998-1060),
`NavierStokes/ActualIterationLedger.lean` (:22-130, :418-428),
`NavierStokes/ChartScales.lean` (:24),
`NavierStokes/CorrectionStep.lean` (:7253-7305, :7563-7603, :7645-7705, :8610-8660, :9395-9500, :9521-9630, :9665-9710),
`NavierStokes/WeightedClasses.lean` (:31-130, :191-203),
`NavierStokes/LabelSumBounds.lean` (:33-60, :101),
`NavierStokes/SignedCrossDefectClass.lean` (:28-200),
`NavierStokes/FiniteHeadClass.lean` (:23-129),
`NavierStokes/SignedMeanGain.lean` (:426-472),
`NavierStokes/CrossBasedMeanComposition.lean` (:546-616),
`NavierStokes/ActualStageEstimates.lean` (:97-127),
`NavierStokes/ActualCandidateAssembly.lean` (:455-500).
