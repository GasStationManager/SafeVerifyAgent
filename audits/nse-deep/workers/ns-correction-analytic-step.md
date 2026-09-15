# Worker report — `NavierStokes/CorrectionAnalyticStep.lean`: where the per-cycle `+1/10` is earned

Worker: `ns-analytic-step`. Read-only audit of `/home/gsm/.openclaw/workspace/repos/NSE`
@ `f9e8bc5` (openai/NavierStokesAndEuler). **Nothing under that path was modified.** No `lake build`
(no Mathlib on this box) — everything below is source-level reading of actual statements and actual
proof terms. All `file:line` are relative to the NSE repo root.

Predecessor: `workers/ns-stage-estimates.md`, which traced the whole NS residual-decay claim to
`CorrectionAnalyticStep.step` / `StepResult.invariant` and could not read it (its Escalation #1).
This report reads it.

---

## Headline

**The `+1/10` is a real estimate, not a relabeling — and I found the exact inequality that the whole
Navier–Stokes half is balanced on.** It is

```lean
-- NavierStokes/SignedMeanGain.lean:426-431
theorem remainderTensor_mem (f : SignedFamily s P α δ β η) (a : Assembly f) {γ : ℝ}
    (hβη : β ≤ η) (hγd : γ ≤ δ + β) (hγc : γ ≤ α + η) (hγs : γ ≤ 2 * β) :
    TensorClass s γ (remainderTensor f a)
-- NavierStokes/SignedMeanGain.lean:462-471
theorem signed_tensor_bounds {σ κ : ℝ} (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (f : SignedFamily s P (1 / 2) (17 / 25) (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f) :
    TensorClass s (1 + σ - κ) (incrementTensor f a) ∧
      TensorClass s (1 + σ + 17 / 100 + κ) (remainderTensor f a)
```

with `α = 1/2` (old wave), `δ = 17/25` (old-minus-primary *difference*), `β = 1/2+σ-κ` (signed
tangent), `η = 1+σ-2κ` (signed curl). The binding branch is `hγd : γ ≤ δ + β`, i.e.

    1 + σ + 17/100 + κ  ≤  17/25 + 1/2 + σ - κ  =  1 + σ + 9/50 - κ   ⟺   κ ≤ 1/200.

`9/50 = 18/100`, the step spends `17/100`, so **the entire per-cycle gain of the construction is
capped by `9/50 = 17/25 − 1/2 = 0.18`, of which `1/100 − 2κ` is left over as slack**, and `1/10` is
then a safe round-down of `17/100`. The repo says this out loud, in dead code:
`ExponentLedger.old_difference_bar_margin_iff` (`NavierStokes/ExponentLedger.lean:281-283`):
`17/100 < 9/50 - 2*κ ↔ κ < 1/200`.

Three consequences worth stating plainly:

1. **The gain does not degrade with the cycle index.** The cap `9/50` is `δ − α = 17/25 − 1/2`,
   built from two *σ-free* exponents of the invariant (`wave` at `1/2`, `difference` at `17/25`,
   `CorrectionStep.lean:9432,9436`). Nothing in the cap involves `σ`, so the same `1/10` is
   available at cycle 1 and at cycle 10^6. The only place `σ` enters the five margins is
   `σ − 3κ > 17/100`, which *improves* as `σ` grows.
2. **The nonlinear self-interaction is not swept under the rug.** It appears explicitly as the
   third branch `hγs : γ ≤ 2*β` of `remainderTensor_mem` and as `hγs : γ ≤ 2*β - κ` of
   `CorrectionStep.waveStage_residual_uniform:7283`.
3. **`ExponentLedger.lean`, the file that audits the manuscript's Proposition-10.3 arithmetic, is
   almost entirely dead code** (46 of 53 decls `in_cone=False`, including
   `signed_bar_gain_exceeds_seventeen_hundredths:178` and `all_stage_arithmetic:304`). The live
   proof re-derives every margin inline with `by linarith` at the point of use. That is fine for
   soundness but it means a reviewer who reads `ExponentLedger.lean` and is satisfied has read
   documentation, not the proof.

I did **not** find a break in the induction at this level, and the two questions I delegated both
came back closed in the reassuring direction (Cross-checks 1 and 2 at the end of this report):
the live induction is a *closed* theorem with no per-cycle `data` hypothesis
(`ActualCyclePreservation.state_runInvariant:826`, `StepData` constructed at `:730`), and the
per-cycle growth of the class constant `C` and degree `p` never reaches the exponent
(`PhysicalGraphBounds.slow_power_absorption:806` charges a fixed `+1` for any slow power).

**Verdict counts over the 45 declarations I examined statement-and-proof:**
`OK` **44** · `UNCLEAR` **1** (`ActualCycleExcluded.nextAxisymmetricAlias_all_powers:156` — mechanically
fine, its two `∀ β` inputs are delegated to unread `GaugeExcludedBounds` lemmas) ·
`KERNEL-RISK` **0** · `SUSPICIOUS` **0**. Of the 44 OK, **5 are off-cone dead code** that a reviewer
could mistake for the proof (`CorrectionAnalyticStep:632,657,674`, the `ExponentLedger` margin block,
`ActualIterationLedger.all_cycle_margins:119`).

---

## Scope

| file | lines | decls (CONE.csv, mark 4) | off-cone | how read |
|---|---|---|---|---|
| `NavierStokes/CorrectionAnalyticStep.lean` | 690 | 23 | 3 | **all 690 lines, line-by-line** |
| `NavierStokes/SignedCrossDefectClass.lean` | 200 | 10 | 1 | **all 200 lines, line-by-line** |
| `NavierStokes/FiniteHeadClass.lean` | 129 | 13 | 2 | **all 129 lines, line-by-line** |
| `NavierStokes/ExponentLedger.lean` | 322 | 53 | 46 | **all 322 lines, line-by-line** |
| `NavierStokes/CrossBasedMeanComposition.lean` | 703 | 14 | 4 | lines 1-340 and 376-703 read line-by-line (i.e. all but the `:337` off-cone twin) |
| `NavierStokes/WeightedClasses.lean` | 518 | — | — | lines 1-130 (`StripData`, `growth`, `majorant`, `MemClass`, `MeanClass`, `WaveClass`) line-by-line |
| `NavierStokes/CorrectionStep.lean` | 9849 | 559 | — | targeted: `:5414-5497` (`finish_mean_stages`), `:7240-7300` + `:7370-7470` (`waveStage_residual_uniform`, the two `residual_gain_local`s), `:8600-8710` (`finalBlock_uniform_cumulative`, `finalBlock_increment_bounds`, `meanStages_residual_gain`), `:9395-9505` (`CycleAnalyticInvariant`, `raw_mean_bounds`), `:9521-9635` (`waveStages_residual_gain`), `:9660-9710` (`waveStage_mean_gain`) — all line-by-line |
| `NavierStokes/SignedMeanGain.lean` | — | — | — | targeted: `:412-471` (`crossTensor`/`remainderTensor`/`incrementTensor`, `incrementTensor_split`, `remainderTensor_mem`, `incrementTensor_mem`, `signed_tensor_bounds`) line-by-line |
| `NavierStokes/ActualCycleExcluded.lean` | 226 | 10 | — | `:150-227` (`nextAxisymmetricAlias_all_powers`) line-by-line; rest skimmed |
| `NavierStokes/ActualIterationLedger.lean` | 433 | 68 | 35 | `:15-135` and `:264-290` line-by-line |

`CorrectionAnalyticStep.lean` kinds: 20 theorem (3 `private`), 4 structure, 1 abbrev. I read
**every** declaration of it, statement *and* proof term. Total read line-by-line ≈ 2,700 lines.

---

## A. What exactly improves by `1/10`

### A1. `StepResult` and its `invariant` field, verbatim (`CorrectionAnalyticStep.lean:504-516`)

```lean
/-- In addition to preservation, keep the actual increments needed by
the physical-stage estimates. -/
structure StepResult : Prop where
  invariant : CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x)
  temporal : IncrementBounds G.strip (1+σ-2*κ) ((p).temporalIncrement v c u)
  rank : IncrementBounds G.strip (1+σ-2*κ) ((p).rankIncrement v c u)
  pressure : MeanClass G.strip (1+σ-2*κ) (((p).next v c u).pressure - (u).pressure)
  velocityCoefficients : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2+σ-κ)
    (fun l n z => ((p).finalBlock v c u l).velocity n i j z - ((v).blocks l).velocity n i j z)
  pressureCoefficients : ∀ j, LabelSumBounds.UniformWaveClass G.strip P (1+σ-κ)
    (fun l n z => ((p).finalBlock v c u l).pressure n j z - ((v).blocks l).pressure n j z)
  afterSignedTheta : MeanClass G.strip (1+σ-2*κ) (((p).afterSigned v c u).thetaResidual c)
  afterSignedAxial : MeanClass G.strip (1+σ-2*κ) (((p).afterSigned v c u).axialResidual c)
```

### A2. `step`'s statement, verbatim (`CorrectionAnalyticStep.lean:521-525`)

```lean
theorem step (D : StaticData G h index axial r c κ)
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (hσ : 1/5 ≤ σ) (hκsmall : κ ≤ 1/100000)
    (d : StepData G h index axial particular signed r c x primary P S D H hσ) :
    StepResult G h index axial particular signed r c x primary P S (σ := σ) (κ := κ)
```

### A3. **Which quantity, which norm, which region**

`σ` is *not* a spatial decay rate. It is the power of the **band parameter** `s.epsilon n` in the
weighted class (`WeightedClasses.lean:78-79,107-113`):

```lean
def majorant (s : StripData D) (w : ℕ → D → ℝ) (α C : ℝ) (p n : ℕ) (x : D) : ℝ :=
  C * s.epsilon n ^ α * s.growth n x ^ p * w n x          -- :78
structure MemClass (s : StripData D) (w : ℕ → D → ℝ) (α : ℝ) (f : ℕ → D → E) : Prop where
  weight_nonneg : ∀ n x, x ∈ s.domain → 0 ≤ w n x
  smooth : ∀ n, ContDiffOn ℝ ∞ (f n) s.domain
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n x, x ∈ s.domain → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s w α C p n x        -- :111-113
```

with `epsilon_pos`, `epsilon_le_one` (`:35-36`) and
`growth n x = s.slow n * max 1 (s.delta x)⁻¹`, `1 ≤ growth` (`:50-55`). Since `epsilon n ≤ 1`, a
**larger** exponent is a **stronger** bound; `MemClass.mono_exponent` is used everywhere in the
weakening direction (e.g. `CorrectionStep.lean:9587` weakens a `1+σ-3κ` bound down to
`1/2+σ+1/10`). Region: `s.domain`, the similarity strip `G.strip.domain` (for the debt,
`G.slowStrip`). Weight: `w = zeta` for `MeanClass` (`:115`), `w = sqrt zeta * P` for `WaveClass`
(`:118`). Order: **all** derivative orders, with `C` and the polynomial degree `p` re-chosen for
each finite order `m` (this is the `∀ m, ∃ C, ∃ p` quantifier order — see §C2).

`CycleAnalyticInvariant` (`CorrectionStep.lean:9408-9461`) has **exactly three σ-dependent
fields** — I checked all 40 fields one at a time:

```lean
  residual : UniformHarmonicInteraction.UniformVelocity G.strip P (1/2+σ)      -- :9440
    (fun l => HarmonicResidual.residualBlock c x.state (x.coefficients.blocks l) …)
  mean : MeanResidualBounds G.strip σ c x.state                                -- :9443
  debt : DefectBounds G.slowStrip σ c x.state                                  -- :9445
```

Everything else is σ-free: `wave` at `1/2` (`:9432`), `pressure` at `1` (`:9434`),
`difference` at `17/25` (`:9436`), `covariance` at `1` (`:9439`), `axisFlat : ∀ β` (`:9459`),
`gaussianFlat : ∀ β` (`:9454`), plus ~30 structural/regularity/support fields. **So "gain `1/10`"
means: the harmonic residual of every label block, the mean residual, and the pressure/rank debt
all pick up one more factor `epsilon n ^ (1/10)` per cycle, in all derivative orders, on the whole
similarity strip, with per-cycle constants.**

Hypotheses under which it holds: a *fixed* geometry record `StaticData` (`:152-177`, whose fields
are equalities identifying `G`'s region/strip/gauge with the similarity data, plus
`OperatorBounds … κ` and `BaseBounds`), the invariant at `σ`, `1/5 ≤ σ`, `κ ≤ 1/100000`, and a
`StepData` (`:470-502`) carrying this cycle's `WaveData` (`:30-95`) — 30 fields of estimates on the
two *constructed* increments — plus a mode assembly, envelope bounds, a rank geometry, and one
**tail identity** `cross_tail` (`:500-502`).

---

## B. Walk of the proof — earned estimate, or accounting?

**Verdict: an earned estimate.** The chain has four genuinely quantitative links and two exact
algebraic identities. I list them in the order `step` uses them.

### B1. The exact algebraic splittings (these are the "accounting", and they are honest)

* `SignedMeanGain.incrementTensor_split:419` — `incrementTensor = crossTensor + remainderTensor`,
  proved by `covariance_increment_split` (a bilinearity identity), where
  `crossTensor = symmetricCovariance (primaryField) (tangentField)` and `remainderTensor` is
  everything else (`:412-417`).
* `CrossBasedMeanComposition.meanBar_eq_sigma_add_defect:30-34` —
  `meanBar X = physicalSigma G e f + crossDefect G e f X`, by `unfold; abel`. `crossDefect` is
  *defined* as the difference (`:26-28`), so this is a definition unfolding, not a claim.
* `CorrectionStep.waveStage_residual_uniform`'s core: `residualBlock_wave_update_split` (used at
  `:7295`) splits the new residual exactly into (old source + linear good block) + (nonlinear
  interaction block). The proof then bounds the two pieces separately and closes with `.congr`.
* `CrossBasedMeanComposition.averaged_residual_decomposition_with_defect:78-136` — the angular mean
  of the new θ/axial residual **equals** `removedBump + meanBar(remainderField) + radialDiv(crossDefect)`
  on `G.strip.domain`. Proved by `average_congr` on `H.theta_split` plus
  `cross_cancels_with_defect:58` and two `linarith`s. *This is the cancellation that pays for the
  cycle*: the designed cross covariance kills the requested stress, and only the **defect** and the
  **remainder** survive.

### B2. Link 1 — the tensor estimate that caps everything (`SignedMeanGain.lean:426-471`)

Quoted in the Headline. `remainderTensor_mem` needs `γ ≤ min(δ+β, α+η, 2β)`:

| branch | value at `α=1/2, δ=17/25, β=1/2+σ-κ, η=1+σ-2κ` | meaning |
|---|---|---|
| `δ + β` | `1+σ+9/50-κ` | (actual − primary) × new tangent — **binding** |
| `α + η` | `1+σ+1/2-2κ` | old wave × new curl |
| `2β` | `1+2σ-2κ` | **new wave squared (nonlinear self-interaction)** |

`signed_tensor_bounds:462` instantiates `γ = 1+σ+17/100+κ`; the three `by linarith` side goals at
`:471` are exactly `17/100+2κ ≤ 9/50`, `17/100+κ ≤ 1/2-2κ`, `17/100+κ ≤ σ-2κ` (the last needs
`σ ≥ 1/5`). I re-derived all three by hand: they hold with slack `1/100-2κ`, `33/100-3κ`,
`3/100-3κ`. **The first is the tightest inequality in the Navier–Stokes half of this artifact.**

### B3. Link 2 — the `17/100` bar-residual gain (`CrossBasedMeanComposition.lean:140-265`)

`signed_mean_gain_of_cross_defects:140` concludes, from the cross defects at `1+σ+17/100+κ`:

```lean
    MeanClass G.strip (1 + σ - 2 * κ) (v.thetaResidual c) ∧ …                     -- :160-161
    MeanClass G.strip (1 + σ + 17 / 100) (StateMomentBalances.meanBar (v.thetaResidual c)) ∧ … -- :162-163
```

i.e. **the full new mean residual gains nothing (`1+σ-2κ`), but its angular mean gains `17/100`.**
The three summands of the bar bound are visible at `:264`:
`(hbθ.mono_exponent …).add (G.average_mem hRestθs hRestθ) .add hdθ`, matched to the identity
`hbar.1` by `class_congr` — respectively the removed bump (from the *measured debt*, `:243-244`),
the remainder field (`hRestθ:216-221`, which is `thetaCovarianceChange_mem ho hEi` — i.e. **the
`hEi` of B2**), and the radial divergence of the defect (`hdθ:247-250`). Nothing is dropped: each
`convert! … using 1; ring` is an exponent normalisation, and I checked each `ring` target.

### B4. Link 3 — the wave residual gain (`CorrectionStep.lean:7253-7301`, `9521-9633`)

```lean
theorem waveStage_residual_uniform … (hγm : γ ≤ β + H - 1/2) (hγc : γ ≤ α + β - κ)
    (hγs : γ ≤ 2*β - κ) :                                                        -- :7283
    UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c v
      (HarmonicWaveInteraction.addBlock (a l) (b l)) (G l + g l) (A₁ l))          -- :7284-7285
```

`waveStages_residual_gain:9521` applies it **twice** (particular stage `:9580`, signed stage
`:9618`) with target `γ = 1/2+σ+1/10` (`:9568`), `α = 1/2`, `β = 1/2+σ` resp. `1/2+σ-κ`,
`H = 9/10` (`hmean:9615`, the cumulative mean increment bound). The six `(by linarith)` at
`:9588,9628` are:

| side condition | instance | slack |
|---|---|---|
| `γ ≤ β+H-1/2` | `1/2+σ+1/10 ≤ σ+9/10` | `3/10` |
| `γ ≤ α+β-κ` | `1/2+σ+1/10 ≤ 1+σ-κ` | `4/10-κ` |
| `γ ≤ 2β-κ` | `1/2+σ+1/10 ≤ 1+2σ-κ` (needs `σ≥1/5`) | `σ-1/10-κ ≥ 1/10` |

plus the two linear-cancellation inputs `hlinearP` at `1+σ-3κ` and `hlinearS` at `1+σ-4κ`, weakened
to `1/2+σ+1/10` at `:9587,9627` (`1/10+3κ ≤ 1/2`). So the wave gain is limited by `2/5`, not by
`1/10` — the `1/10` is a deliberate round-down. `ParticularParameters.residual_gain_local:7370`
and `PeriodizedSignedParameters.NativeDynamics.residual_gain_local:7429` show the same hard-coded
`+1/10` at the single-block level, with `hα : 7/10 ≤ α` matching `1/2+σ, σ ≥ 1/5`.

### B5. Link 4 — the temporal + rank solve converts the bar gain into a full gain (`CorrectionStep.lean:5417-5496`)

`finish_mean_stages` takes the full residual only at `1+σ-2κ` (`hcθ,hcz:5440-5441`) but the **bar**
at `1+σ+17/100` (`hbarθ,hbarz:5442-5443`), and returns the debt at `σ+1/10` and the θ/axial mean at
`1+(σ+1/10)` (`:5450-5453`). The three exponent inequalities are stated inline:

```lean
  have hH : 9 / 10 ≤ 1 + σ - 2 * κ := by linarith                                        -- :5455
  have hβ : 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 1 - 2 * κ := by linarith                -- :5457
  … MovingMomentBounds.rankStage_defectBounds … hH
    (show 1 + (σ + 1 / 10) ≤ (1 + σ - 2 * κ) + 9 / 10 - 2 * κ by linarith)               -- :5495
```

i.e. the temporal inverse buys a full `+1 − 2κ` and the rank solve `+9/10 − 2κ` **on the
non-mean part**, which is why only the bar matters. Slack again large (`8/10-4κ`).

### B6. Link 5 — the defect is `∀ γ` because it is supported in finitely many bands

`SignedCrossDefectClass.residual_defects_all_exponents_of_primitive:173` gives
`∀ γ, MeanClass G.strip γ (meanBar (crossTensor …) − physicalSigma …)` from a *baseline* bound at
`1+σ-κ` (`residual_defects_mem:118`, itself `crossTensor_mem:37` giving `α+β = 1+σ-κ`, minus
`physicalSigma_mem:64`) plus the **tail identity** `htail` (`:183-185`). The promotion is
`FiniteHeadClass.meanClass_all_exponents:112`, which I read in full and re-derived:

```lean
def comparison (s : StripData D) (N : ℕ) (α β : ℝ) : ℝ :=
  1 + ∑ n ∈ Finset.range N, s.epsilon n ^ (α - β)                                  -- :23-24
theorem jet_bound … : ‖iteratedFDeriv ℝ j (f n) x‖ ≤ majorant s w β (C * comparison s N α β) p n x
```

For `n < N` it is `ε_n^α ≤ comparison · ε_n^β` (finite sum of positive terms, `:34-50`); for
`n ≥ N` the function vanishes on the *open* domain, hence every jet vanishes
(`jet_eq_zero:67-74`, via `iteratedFDerivWithin_of_isOpen` — correct, and openness is a real
hypothesis `s.isOpen_domain`). **Degree `p` unchanged**, weight unchanged. This is sound and is
*not* a junk-value trick: it is the standard "finitely many bands cost only a constant". Its price
is that the whole scheme now depends on the tail identity `cross_tail` being genuinely available
(see Escalation 2).

### B7. Where `step` puts it together (`CorrectionAnalyticStep.lean:521-629`)

Order of operations, all verified line-by-line:

1. `hCov₀/hCovP:538-549` — particular covariance increment at `1/2+(1/2+σ) = 1+σ`
   (`assembledCovarianceIncrement_mem`, exponents matched by `show (1:ℝ)/2+(1/2+σ) = 1+σ by ring`).
2. `hCovS:557-561` — signed covariance at `1+σ-κ` from `signed_tensor_bounds` (B2).
3. `hθ,hz := H.raw_mean_bounds:576` (`CorrectionStep.lean:9470`) — the invariant's `mean` at `σ`
   plus the all-powers axis alias give the *raw* residuals at `1+σ`.
4. `hθ₁,hz₁:577` — `waveStage_mean_gain` (`CorrectionStep.lean:9666-9687`) gives the
   after-particular residuals at `1+σ-κ`.
5. `hDefects:582` — the `∀ γ` cross defects (B6), instantiated at `1+σ+17/100+κ` at `:600`.
6. `hMean:593-603` — `mean_gain_from_waves_of_cross_defects`
   (`CrossBasedMeanComposition.lean:546`) → `hDebt` at `σ+1/10`, `hTheta`/`hAxial` at `1+(σ+1/10)`.
7. `hAxis:616` — the axis alias stays all-powers (`ActualCycleExcluded.nextAxisymmetricAlias_all_powers:156`).
8. `hFull := assemble …:622` — the 40-field invariant at `σ+1/10`.

`assemble` (`:265-449`) is where the `+1/10` lands in the *stored* invariant. Note carefully: it
**receives** `hDebt : DefectBounds G.slowStrip (σ+1/10)`, `hTheta`/`hAxial` at `1+(σ+1/10)` and
`hAxis : ∀ β` as hypotheses (`:295-300`) — so `assemble` itself is bookkeeping — while the
*residual* field at `1/2+(σ+1/10)` is produced inside it, at `:322`
(`meanStages_residual_gain`, `CorrectionStep.lean:8673`, fed by `waveStages_residual_gain` at
`:312`). **The quantitative content is entirely in `step`'s calls 4-6 and in `assemble`'s call at
`:312/:322`; the rest of `assemble` is 40 fields of structural transport.** I checked each of the
40 fields against the invariant's declaration and none of them silently drops a `σ`.

---

## C. The three failure modes

### C1. (i) Does the induction chain? — no break found

The invariant at `σ+1/10` must be a valid *input* for the next cycle. Field by field:

| invariant field | needed at cycle n+1 | delivered by cycle n | verdict |
|---|---|---|---|
| `residual` at `1/2+σ'` | `σ' = σ+1/10` | `assemble:416` ← `meanStages_residual_gain` at `1/2+(σ+1/10)` (`CorrectionStep.lean:8693`) | OK |
| `mean` at `σ'` | ditto | `assemble:417` ← `next_meanResidualBounds` fed by `hTheta/hAxial` at `1+(σ+1/10)` | OK |
| `debt` at `σ'` | ditto | `assemble:419` = `hDebt` at `σ+1/10` | OK |
| `wave` at `1/2` (σ-free) | same number every cycle | `assemble:410` ← `finalBlock_uniform_cumulative` (`CorrectionStep.lean:8612`), `(hold.add hpart.mono).add hsigned.mono`, needs `1/2 ≤ 1/2+σ-κ` | OK |
| `difference` at `17/25` (σ-free) | same number every cycle | same lemma `:8625-8639`; needs **`17/25 ≤ 1/2+σ-κ`**, i.e. `0.68 ≤ 0.7-κ` | OK, **margin only `0.02-κ`** |
| `covariance` at `1` | σ-free | `assemble:414` ← `next_covariance_mem` with `1 ≤ 1+σ` and `1 ≤ 1+σ-κ` | OK |
| `axisFlat : ∀ β` | σ-free | `assemble:433` = `hAxis` ← `nextAxisymmetricAlias_all_powers:156` | OK (delegated, see Esc. 1) |
| `gaussianMean = 0` | exact identity | `assemble:444` `(next_gaussian_angularMean …).trans H.gaussianMean` | OK |
| `carrier`, `phase`, `frequency`, `angular` | unchanged | `assemble:397-400`, from `H.*` alone (the constructed blocks share the carrier by `WaveData.carrier`) | OK |
| `reconstructed`, `primitives`, `masses` | re-established | `assemble:420-422` ← `next_primitive`, `next_zeroMassesOn` | OK |
| `1/5 ≤ σ'` | needed by next `step` | `1/5 ≤ σ+1/10` trivially | OK |
| `κ ≤ 1/100000` | same `κ` | `κ` is a *parameter of `StaticData`*, not indexed by the cycle; the live instantiation is `ChartScales.kappa = 1/100000` (`ActualIterationLedger.lean:32`, `ActualCyclePreservation.lean:74`) | OK |

**The one number that could have broken this is `17/25`.** It is the *only* invariant exponent that
must be re-established from increments that are themselves only `1/2+σ-κ`-small, and the margin is
`1/2+σ-κ-17/25 = 0.02-κ` at `σ = 1/5`. It is positive, and it grows with `σ`; the repo states the
same fact in dead code (`ExponentLedger.signed_increment_above_cumulative_difference:233`,
`17/25 < waveExponent σ - κ`). **If `σ₀` had been `< 18/100 + κ` instead of `1/5`, the difference
field would not be maintainable and the whole scheme would collapse.** That is the tightest
structural coupling I found, and it is exactly the same `9/50` that caps the gain in B2 — the
construction is balanced on one number used twice.

The remaining chaining question — whether a full `StepData` (30 `WaveData` fields, the mode
`assembly`, and the `cross_tail` identity) can actually be *built* at every cycle from the
invariant at `σ n` — lives in `ActualCyclePreservation.lean` / `ActualParticularCycleData.lean`
and was delegated to child `cas-chain-closure` (report:
`workers/_sub-cas-chain-closure.md`). At my level I can confirm the *shape* is right:
`CorrectionAnalyticStep.iterate_invariant:657` takes exactly
`data : ∀ n (H : invariant at σ n (state n)), StepData … H (hσ n)`, i.e. the per-cycle data is
allowed to be *rebuilt* from the invariant at each `n` — the induction hypothesis is not asked to
carry it. (And note `iterate_invariant` is itself **off-cone**; the live induction is
`ActualCyclePreservation.state_runInvariant:826`, which does the same thing with `sigma_succ`.)

### C2. (ii) A constant that grows with the cycle index — the real residual risk

`MemClass.bounds` is `∀ m, ∃ C, ∃ p, …` (`WeightedClasses.lean:111`). Every `.add`,
`.mono_exponent`, `class_congr`, and `FiniteHeadClass` promotion re-chooses `C` (and `.add`
re-chooses `p`). Concretely, `finalBlock_uniform_cumulative:8629` is
`((hold.add (hpart.mono)).add (hsigned.mono))`, so `C_{J+1} ≈ C_J + c_J` and `p_{J+1} ≈ max/sum` —
**both may grow with the cycle index `J`, and nothing in this file bounds their growth.** So the
`+1/10` improves the *exponent* while the *constant and degree of the class* degrade.

Why I believe (but did not fully verify here) that this is harmless:

* the consumer's quantifier order permits it. `StageEstimates.finite_residual`
  (`MixedCandidateAssembly.lean:62`) is `∀ J m, JetRate … (gain J - residualLoss m)` and
  `JetRate l q f m r := ∃ C ≥ 0, ∀ᶠ x in l, ‖∇^m f x‖ ≤ C * q x ^ r`
  (`DiagonalResidual.lean:33`) — the `∃ C` is *inside* `∀ J m`, so a `J`-dependent constant is
  allowed by the type. What is **not** allowed is a `J`-dependent *exponent loss*: `residualLoss`
  takes only `m`, and the live instantiation is `fixedLoss m = physicalLoss h (2h) m`
  (`ActualCycleResidualBounds.lean:1145`), which is `J`-free.
* the exponent slack is a fixed `0.7h`: the ledger only claims `gain h J = h·J/10`
  (`ActualIterationLedger.lean:29`) while the invariant delivers `h·(1/2+σ_J)` with
  `σ_J = 1/5+J/10` (`gain_le_residualWave:264`, `sigma_formula:36`), i.e. a permanent surplus of
  `h·(1/2+1/5) = 0.7h`. A `growth n x ^ p = (slow n · max 1 δ(x)⁻¹)^p` factor with `slow n`
  polynomial in the band index is swallowed by any *fixed* positive exponent surplus, at the price
  of a `p`-dependent (hence `J`-dependent) constant — which the previous bullet permits.

Because this is the parent's sharpened worry, I delegated the verification of *where `growth^p`
actually goes* in the class→`JetRate` conversion to child `cas-class-degree`
(`workers/_sub-cas-class-degree.md`). I flagged it as the one place where "+1/10 per cycle" could
still have been made vacuous. **It is now CLOSED in the reassuring direction — see Cross-check 2:**
`PhysicalGraphBounds.slow_power_absorption:806` charges a *fixed* `+1` in the band exponent for
**any** real slow power (only the constant depends on the power), the loss functions are `J`-free by
type (`ActualCycleResidualBounds.lean:1145`, degree discarded at `:926`), and the spatial factor
`(max 1 (delta x)⁻¹)^p` is absorbed by the Gaussian-flat weight `zeta = exp(-c/x²)`
(`PhysicalClassBounds.lean:55-74`). `delta` is **not** bounded below, and does not need to be.

### C3. (iii) Is the gain in the same quantity the ledger sums? — yes

The ledger sums `sigma J` (`ActualIterationLedger.lean:22`, `= ExponentLedger.stageParameter J`)
and converts it to a physical rate through `gain_le_residualWave:264` →
`Invariant.residual_jetRate` (`ActualCycleResidualBounds.lean:1158`) → `finite_residual_rates:1190`.
The exponent it consumes is `h·(1/2+σ)`, i.e. exactly the `ε`-power of the invariant's `residual`
field (`1/2+σ`, `CorrectionStep.lean:9440`) with `ε_n = Q n ^ h` (`StaticData.fast:169` fixes
`fastCoefficient n = Tg^index n * Q n^(1+h)`; `ActualCycleResidualBounds.native_residual:845`
carries `h*(1/2+σ)`). The `mean`/`debt` fields at `σ` feed the same residual bound via the
term-by-term decomposition the predecessor worker verified. **So the improved quantity and the
summed quantity are the same exponent, up to the `0.7h` surplus.** I looked specifically for a
bait-and-switch here (gain in the *bar* residual, ledger summing the *full* residual) and the
bar/full distinction is resolved *inside* `finish_mean_stages` (B5) before the invariant is
rebuilt — the invariant's `mean`/`debt` fields are the full ones.

---

## D. Kernel-risk assessment

Regex census over my scope (`CorrectionAnalyticStep`, `CrossBasedMeanComposition`,
`SignedCrossDefectClass`, `FiniteHeadClass`, `ExponentLedger`, `WeightedClasses`,
`CycleMeanEquation`, `ActualCycleExcluded`, `ActualIterationLedger` — 3,849 lines):

| token | count |
|---|---|
| `decide` / `native_decide` | **0 / 0** |
| `sorry` / `axiom` | **0 / 0** |
| `macro` / `elab` / `syntax` / `set_option` | **0 / 0 / 0 / 0** |
| `unsafe` / `partial` / `deriving` | **0 / 0 / 0** |
| `termination_by` / `WellFounded` / `Acc.rec` / explicit `.rec` | **0 / 0 / 0 / 0** |
| new `inductive` | **0** (4 non-recursive `structure`s in `CorrectionAnalyticStep`: `WaveData:30`, `StaticData:152`, `StepData:470`, `StepResult:506`; `StepResult` and `WaveData` are `Prop`-valued records) |
| `induction` | 2 in `CorrectionAnalyticStep` (`:665` in `iterate_invariant`, plus its docstring), 2 in `WeightedClasses`, 1 in `CycleMeanEquation` |
| `norm_num` | 2 (`ExponentLedger:273,289`), 2 (`CrossBasedMeanComposition:123,134`, both `norm_num only [Nat.cast_ofNat]`), 5 (`ActualIterationLedger`) |
| `linarith` / `nlinarith` | 8 / 0 in `CorrectionAnalyticStep`; 19/0 in `CrossBasedMeanComposition`; 29/0 in `ExponentLedger`; 12/**2** in `ActualIterationLedger` (`:105`, `:...`) |
| `rfl` | 5 in `CorrectionAnalyticStep` (`:197, 246, 541, 583, 591`) |
| largest numeral anywhere in scope | `1000000` (`ExponentLedger.lean:276`, off-cone), then `100000` (50 sites), `69999` (`ExponentLedger:229`, off-cone) |

**(1) Recursive inductives / recursors.** One `Nat` induction in my scope,
`CorrectionAnalyticStep.iterate_invariant:665-670` (`zero => hseed`,
`succ n ih => … simpa only [CycleState.iterate_succ, hσstep]`), and it is **off-cone**. The kernel
type-checks a `Nat.rec` application; it does not iterate it (the motive is a `Prop` and the
recursion is not reduced at a literal). `Finset.range` sums appear in `FiniteHeadClass.comparison:24`
but over an abstract `N`, so nothing is unfolded. No indexed families, no large elimination, no
`Acc.rec`, no structure recursion. **Risk: LOW, depth 1.**

**(2) GMP / numerals.** No `decide`, no `Nat.pow`/`div`/`mod`/`gcd`, no numeral of more than 7
digits, and the 7-digit one is in off-cone documentation. Everything the kernel must recompute is
a `linarith`/`norm_num` certificate over rationals with denominators `10, 25, 50, 100, 200,
100000` — e.g. `17/100+2κ ≤ 9/50` with `κ ≤ 1/100000`. `Real.rpow` is used for
`epsilon n ^ α` with **real** exponents (`WeightedClasses.majorant:79`), so those are not numeral
computations at all: the kernel never evaluates them, it only transports lemmas
(`Real.rpow_add`, `rpow_le_rpow_of_exponent_ge`). **Risk: NEGLIGIBLE.** Concretely: to accept
`CorrectionAnalyticStep.lean` the kernel performs no `Nat` arithmetic beyond `Nat.ble`-style
comparisons on ≤6-digit literals inside `linarith` certificates, and reduces no recursor at a
numeral.

**(3) Metaprogramming.** Zero occurrences of every token in scope. Two things I record as
*not* findings but as the only non-standard elaboration in the file: (a) `local notation "p"/"v"/"u"`
(`CorrectionAnalyticStep.lean:258-260, 463-465, 651-652`) — notation only, no new elaborator, but it
makes the file materially harder to audit (every `(p).next v c u` must be expanded mentally to
`(CycleParameters.ofGeometry G h index axial particular signed r).next x.coefficients c x.state`);
(b) `include W` / `include D` (`:104, 185`) — the standard Lean 4 variable-inclusion command.

### Cone status of everything I audited (`CONE.csv`, mark 4)

**In-cone (live):** all of `CorrectionAnalyticStep` except `:632, 657, 674`; `crossDefect:26`,
`meanBar_eq_sigma_add_defect:30`, `cross_cancels_with_defect:58`,
`averaged_residual_decomposition_with_defect:78`, `signed_mean_gain_of_cross_defects:140`,
`bandSignedStage_mean_debt_of_cross_defects:271`, `fourStage_mean_gain_of_cross_defects:392`,
`mean_gain_from_waves_of_cross_defects:546`; `SignedCrossDefectClass` `:28,37,64,73,102,118,136,173`;
`FiniteHeadClass` `:23,26,31,34,42,53,67,79,97,106,112`; `ExponentLedger` only
`:24,27,30,286,288,291,297`; `ActualIterationLedger.sigma_succ:38`, `gain_tendsto_atTop:107`,
`gain_le_residualWave:264`.

**Off-cone (dead) — and two of these matter for how the artifact reads:**

* `CorrectionAnalyticStep.step_preserves:632`, `iterate_invariant:657`, `iterate_results:674` —
  the file's own iteration theorems are **not used**. The live consumer is
  `ActualCyclePreservation.stepResult_of_particular:742` → `.invariant` in
  `next_runInvariant_of_particular:800`, with the induction at `state_runInvariant:826`.
* **46 of 53 `ExponentLedger` decls**, including `particularGain:33`, `signedGain:38`,
  `signedBarGain:44`, all five `*_bar_margin` lemmas, `signed_bar_gain_exceeds_seventeen_hundredths:178`,
  `completed_mean_margin:208`, `completed_defect_margin:220`, `old_difference_bar_margin_iff:281`,
  `all_stage_arithmetic:304` — and `ActualIterationLedger.all_cycle_margins:119` which wraps it.
  The "arithmetic audit of Proposition 10.3" is therefore *documentation*: sound, checkable, and
  not part of the proof. The live proof re-derives each margin with an inline `by linarith`
  (`SignedMeanGain.lean:471`, `CorrectionStep.lean:5455-5457, 5495, 9587-9588, 9627-9628`).
* `CrossBasedMeanComposition.crossDefect_mem_of_cross:36`, `crossDefect_all_exponents_of_tail:46`,
  `bandSignedStage_mean_debt_of_cross:337`, `mean_gain_from_waves_of_finite_head:630`;
  `SignedCrossDefectClass.defect_all_exponents:86`; `FiniteHeadClass.waveClass_all_exponents:119`,
  `unweightedClass_all_exponents:124`. All are the *exact-cancellation* or generic twins of live
  lemmas — consistent with the live path going through the `_of_primitive` / `_of_cross_defects`
  versions, i.e. the weaker hypotheses. That is the honest direction.

---

## Per-declaration findings

`CorrectionAnalyticStep.lean` — **all 23 declarations, read statement and proof**.

| decl | line | cone | statement (my words) | mechanism | verdict |
|---|---|---|---|---|---|
| `Point` | 25 | T | `= CorrectionStep.CyclePoint` | abbrev | OK |
| `WaveData` | 30 | T | 30 fields of estimates/regularity on *this cycle's two constructed increments*: particular at `1/2+σ`, tangent `1/2+σ-κ`, curl `1+σ-2κ`, particular pressure `1+σ`, signed pressure `1+σ-κ`, gaussians at every `β`, plus smoothness/solenoidality/support/periodicity, and the two linear-cancellation fields `particularLinear` `1+σ-3κ` (`:88`) and `signedLinear` `1+σ-4κ` (`:93`) | structure (hypotheses) | OK as a spec. The docstring's claim "No complete updated residual or mean estimate is an input" is **true**: every field is about `particularBlock`/`signedBlock`/`signedTangent`/`signedCurl`, never about `next` |
| `WaveData.signed` | 108 | T | signed block itself is `1/2+σ-κ` | `(tangent.add (curl.mono_exponent)).congr` + `ring`; needs `κ ≤ 1/2` | OK — `curl` at `1+σ-2κ` is weakened to `1/2+σ-κ`, legitimate direction |
| `.particular_zero_germ` | 118 | T | outside its carrier the particular block vanishes near `z` (`j ≠ 0`) | `block_velocity_zero_germ_of_inputSupport` + `particularBlock_real` | OK |
| `.signed_zero_germ` | 125 | T | same for the signed block | ditto | OK |
| `.covariance_moving` | 134 | T | both covariance increments are `MovingField` | `covarianceIncrement_moving` twice; second uses `(hu.add W.particularField)` — i.e. the *accumulated* field | OK — the `add` is the right accumulation, I checked the argument order |
| `StaticData` | 152 | T | the fixed geometry: 20 fields identifying `G` with `aliasData` (`coord = 2h`, `HEq region`, `strip`, `gauge`, `index`), `OperatorBounds … κ`, `BaseBounds`, `fast n = Tg^index n * Q n^(1+h)`, rank parameters | structure | OK. `HEq G.region aliasData.region` (`:157`) is a heterogeneous equality over the `coord`-indexed `SlowRegion` — handled by the three `private` transport lemmas below, not by `cast` abuse |
| `.radius_pos` | 187 | T | radius `> 0` on the strip | `rw [D.operators_eq]; G.strip_radius_pos` | OK |
| `.graph` | 191 | T | the operators are graph operators | `refine ⟨(G.time,0), G.temporal, ?_⟩; rw …; rfl` | OK — a **`rfl` on a 6-field record**; definitional, unverifiable without elaboration (see Residue 3) |
| `.time_nonneg` | 199 | T | `0 ≤ h` | `D.time` + `aliasData.h_pos.le` | OK |
| `.slow_scale` | 203 | T | `S n ≤ G.slow n` | `congrArg (·.slow) D.strip` then `aliasData.slow_scale` | OK |
| `.index_lower` | 208 | T | `nativeIndex h n ≤ index n + gap` | `simpa only [D.time, D.index_eq]` | OK |
| `.compatible` | 211 | T | the cycle parameters are `Compatible` with the similarity data | 6-field anonymous constructor + `funext` on `fast` | OK |
| `primitive_region_transport` | 221 | T | transport `PrimitiveData` along `coord = coord'`, `HEq U V` | `subst; eq_of_heq; subst; exact` | OK — the *only* sound way to use that `HEq`; no `cast` |
| `moving_region_transport` | 231 | T | same for `MovingField` | ditto | OK |
| `region_carrier_eq` | 241 | T | carriers agree | ditto + `rfl` | OK |
| `assemble` | 265 | T | **from the invariant at `σ`, the wave data, and 9 quantitative inputs (`hCovP`, `hCovS`, `hTemporal`, `hRank`, `hCumulative`, `hDebt` at `σ+1/10`, `hTheta`/`hAxial` at `1+(σ+1/10)`, `hAxis : ∀β`), build the invariant at `σ+1/10`** | 40-field `refine`; the only *new* quantitative work is `waveStages_residual_gain` (`:312`) and `meanStages_residual_gain` (`:322`); four goals deferred to `:435-449` (primitives, oscillatory pressure smoothness, gaussian mean, base angular continuity) | OK — and I want it on record that the mean/debt gain is **assumed** here and **proved** in `step`; reading `assemble` alone would give the false impression that `+1/10` is free |
| `StepData` | 470 | T | per-cycle inputs: `waves`, `primaryBand`, envelope bounds, `cells`, carrier closedness/inclusion, three `LocalUnweighted` bounds, the mode `assembly` + `labels`, two `SupportedOscillations`, primary smoothness/periodicity, `rank_geometry`, `tailStart`, and **`cross_tail`** (`:500-502`): for all `n ≥ tailStart`, `meanBar (crossTensor … 0 i.succ) n z = requestedStress … n z i` | structure | OK as a spec — but `cross_tail` is the hinge of B6 (Escalation 2) |
| `StepResult` | 506 | T | invariant at `σ+1/10` plus 7 increment/class bounds at `1+σ-2κ` / `1/2+σ-κ` / `1+σ-κ` | structure | OK. Note the 7 extra fields are at the **old** `σ`; they are the per-stage increments the physical estimates consume, not gains |
| `step` | 521 | T | the whole analytic step | see §B7 | **OK — this is the load-bearing theorem and it is a real proof**, ~110 lines, no `sorry`, no `decide`; every quantitative input traced to `signed_tensor_bounds` / `waveStage_residual_uniform` / `finish_mean_stages` |
| `step_preserves` | 632 | **F** | projection to the invariant | `(step …).invariant` | OK (dead) |
| `iterate_invariant` | 657 | **F** | `∀ n, invariant (σ n) (state n)` given `σ(n+1) = σ n + 1/10` and per-`n` `StepData` | `induction n`; `simpa only [CycleState.iterate_succ, hσstep]` | OK (dead) — the live twin is `ActualCyclePreservation.state_runInvariant:826` |
| `iterate_results` | 674 | **F** | same plus the per-stage `StepResult`s | `⟨hi, fun n => step … (hi n) …⟩` | OK (dead) |

Selected supporting declarations (read line-by-line, outside `CorrectionAnalyticStep.lean`):

| decl | file:line | cone | statement | mechanism | verdict |
|---|---|---|---|---|---|
| `CycleAnalyticInvariant` | `CorrectionStep.lean:9408` | T | 40-field invariant; only `residual:9440`, `mean:9443`, `debt:9445` depend on `σ` | structure | OK |
| `CycleAnalyticInvariant.raw_mean_bounds` | `CorrectionStep.lean:9470` | T | raw θ/axial residuals at `1+σ` | `H.mean.angular.add (axisFlat (1+σ)).map proj` + `meanGoodResidual_at`, closed by `ring` | OK — the axis alias is *added back*, not ignored |
| `waveStage_residual_uniform` | `CorrectionStep.lean:7253` | T | new residual at `γ ≤ min(β+H-1/2, α+β-κ, 2β-κ)` | exact `residualBlock_wave_update_split` + `interactionBlock_uniform`, `.mono_exponent (le_min …)` | OK — **the nonlinear term is the third branch** |
| `waveStages_residual_gain` | `CorrectionStep.lean:9521` | T | after both wave stages, residual at `1/2+σ+1/10` | the above, applied twice (`:9580`, `:9618`) | OK, slack `≥ 3/10` |
| `finalBlock_uniform_cumulative` | `CorrectionStep.lean:8612` | T | new block still `1/2`, new difference still `17/25` | `.add` + `.mono_exponent` + `congr`/`ring` | OK — **the σ-free budget, margin `0.02-κ`** |
| `finish_mean_stages` | `CorrectionStep.lean:5417` | T | temporal+rank stages give debt `σ+1/10`, means `1+(σ+1/10)` | `gaugeTemporalStage_constructed`, `gaugeRankStage_constructed`, `rankStage_defectBounds`; three inline exponent inequalities `:5455,5457,5495` | OK |
| `meanStages_residual_gain` | `CorrectionStep.lean:8673` | T | the mean update preserves the wave-residual gain `1/2+(σ+1/10)` | `meanStage_residual_uniform` + `incrementBounds_updated` | OK |
| `remainderTensor_mem` | `SignedMeanGain.lean:426` | T | remainder tensor at `min(δ+β, α+η, 2β)` | `f.remainder_sum_mem` | OK — **the cap** |
| `signed_tensor_bounds` | `SignedMeanGain.lean:462` | T | increment tensor `1+σ-κ`, remainder tensor `1+σ+17/100+κ` | `incrementTensor_mem`, `remainderTensor_mem`, four `by linarith` | OK — the `17/100` is *chosen here*, `9/50-κ` was available |
| `signed_mean_gain_of_cross_defects` | `CrossBasedMeanComposition.lean:140` | T | new full mean residual `1+σ-2κ`; new **bar** residual `1+σ+17/100` | `averaged_residual_decomposition_with_defect` + 3 summand bounds | OK — the actual gain step |
| `averaged_residual_decomposition_with_defect` | `CrossBasedMeanComposition.lean:78` | T | exact identity for the bar of the new residual | `average_congr` on `theta_split`, `cross_cancels_with_defect`, `linarith` | OK — an identity, so the term-by-term bounding after it is legitimate |
| `fourStage_mean_gain_of_cross_defects` | `CrossBasedMeanComposition.lean:392` | T | 4 stages (particular wave, signed wave, temporal, rank) → debt `σ+1/10`, means `1+(σ+1/10)` | `gaugeWaveStage_mean_from_covariance`, `bandSignedStage_mean_debt_of_cross_defects`, `meanStages_constructed`; pressure telescoped by `class_congr … ring` | OK |
| `mean_gain_from_waves_of_cross_defects` | `CrossBasedMeanComposition.lean:546` | T | the same, phrased on `CycleParameters.next` | `assembledCovarianceIncrement_mem` + the above; two `erw [hw₂]` | OK (see Residue 4 on `erw`) |
| `crossTensor_mem` | `SignedCrossDefectClass.lean:37` | T | cross tensor at `α+β` | `harmonic_covariance_sum_mem` + `bilinearCovariance_comm` | OK |
| `residual_defects_all_exponents_of_primitive` | `SignedCrossDefectClass.lean:173` | T | `∀ γ`, both cross defects are in class `γ` | baseline `1+σ-κ` + tail identity + `FiniteHeadClass` | OK — **conditional on `cross_tail`** |
| `FiniteHeadClass.jet_bound` / `memClass_of_finite_bands` / `meanClass_all_exponents` | `FiniteHeadClass.lean:79,97,112` | T | finite-head support ⇒ every exponent, same weight and degree | `comparison` = `1 + Σ_{n<N} ε_n^{α-β}`; `jet_eq_zero` via openness | OK — re-derived by hand, sound |
| `nextAxisymmetricAlias_all_powers` | `ActualCycleExcluded.lean:156` | T | the axis alias stays all-powers | old alias (IH) + temporal alias + (new − old) pressure alias, each `∀β` from `GaugeExcludedBounds` | OK mechanically; the `∀β` inputs are delegated (Esc. 1) |
| `ExponentLedger.*` margins | `ExponentLedger.lean:80-317` | **F** | the five gains all exceed `1/10`/`17/100`, at every stage | `linarith`/`min` algebra | OK arithmetically, **dead code** |
| `ActualIterationLedger.all_cycle_margins` | `ActualIterationLedger.lean:119` | **F** | ditto, at `sigma n` | `ExponentLedger.all_stage_arithmetic` | OK, dead |
| `ActualIterationLedger.gain_le_residualWave` | `ActualIterationLedger.lean:264` | T | `gain h J ≤ h * residualWave J` | `residual_physical_gap` + `linarith` | OK — this is the `0.7h` surplus of §C2 |

---

## Escalations

**1. The three `∀ β` ("beyond all orders") delegated claims.**
`ActualCycleExcluded.nextAxisymmetricAlias_all_powers:205-220` obtains
`MeanClass d.strip β` for *every real* `β` from
`GaugeExcludedBounds.temporalAliasState_mean_bounds` and
`GaugeExcludedBounds.pressureAliasState_mean_bounds` (two calls). Since `epsilon n → 0`, a
non-trivial field in class `β` for all `β` must decay faster than every power of the band scale.
*Question for an expert:* are those two lemmas honest (the alias errors really are
beyond-all-orders, e.g. Gaussian tails / exact mode exclusion), or is one of them vacuous /
supported on finitely many bands in a way that hides a `q = 0` degeneracy?
*What would settle it:* read `GaugeExcludedBounds.temporalAliasState_mean_bounds` and
`pressureAliasState_mean_bounds` and check whether their `∀β` conclusion comes from a
`FiniteHeadClass`-style finite-support argument (fine) or from an unbounded `exp(-c/ε)` estimate
(fine but needs its own audit) — and whether either is actually `0` by construction (then the
"alias" bookkeeping is decoration). Note a sibling already flagged
`ActualCycleResidualBounds.current_pressureAlias_class:175` as UNCLEAR for the same reason.

**2. `StepData.cross_tail` — the tail identity that buys the `∀γ` defect.**
`CorrectionAnalyticStep.lean:500-502`. Everything in B6 (and hence the `17/100` input in B3)
is conditional on: for all `n ≥ tailStart`, the band-averaged cross covariance **equals** the
requested physical stress, exactly, on all of `G.strip.domain`.
*Question:* is that identity proved for the actual construction, for a `tailStart` that does not
depend on `σ` or on the cycle index — and is `requestedStress` the *same* object the mean
machinery consumes (`LocalSignedRequest.requestedStress G.patch G.coord c ((p).afterParticular v c u)`,
note the **after-particular** state)?
*What would settle it:* the live discharge of `cross_tail` in
`ActualCyclePreservation.stepData_of_waves:556` / `ActualSignedMeanBinding.lean:673-692`; delegated
to child `cas-chain-closure`.

**3. `κ ≤ 1/200` is the true admissibility threshold, and it is only `2×10²` away from the
tightest inequality of the scheme.** `SignedMeanGain.lean:471` needs
`17/100 + 2κ ≤ 9/50` (⟺ `κ ≤ 1/200`), and the whole construction fixes `κ = 10⁻⁵`
(`ChartScales.kappa`, `ActualIterationLedger.lean:32`).
*Question:* is `κ` really only used as an *upper* bound everywhere, or is there a place that needs
`κ` bounded **below** (e.g. an operator/aliasing estimate that costs `κ` and would fail at
`κ = 0`)? If both, the admissible window is an interval and the audit should confirm `10⁻⁵` is in
it. Also: does any *single* estimate need `9/50` rather than `17/100`, i.e. is the `1/100 - 2κ`
slack real everywhere or is it consumed elsewhere?
*What would settle it:* grep every `OperatorBounds`/`BaseBounds` field for a lower bound on `κ`,
and re-derive the five `signedBarGain` branches against the live call sites rather than against
the (dead) `ExponentLedger`.

**4. `σ₀ = 1/5` and the `17/25` difference budget are coupled, with margin `0.02 − κ`.**
`CorrectionStep.lean:8625-8639` needs `17/25 ≤ 1/2+σ-κ`; `SignedMeanGain.lean:471` needs
`17/100+2κ ≤ 17/25-1/2`. So `17/25` is simultaneously the *cheapest* thing the increments must beat
and the *cap* on the gain.
*Question:* where is `difference` at `17/25` first established for the initial state, and is the
number `17/25` forced by the initialization (`ActualInitialization.lean:1083-1093` shows
`17/25 ≤ 1 - ChartScales.kappa` by `norm_num`, i.e. the initial difference is much better) or
chosen to make the cap come out above `17/100`? If the latter, an expert should confirm no other
estimate degrades when `δ` is raised.
*What would settle it:* read `ActualInitialization.lean:1060-1100` and
`CorrectionInitialization.lean:1789` (`differenceBlock` at `17/25`).

**5. Dead scaffolding that a reviewer will mistake for the proof.**
`ExponentLedger.lean` (46/53 off-cone, including every margin theorem and
`all_stage_arithmetic:304`), `ActualIterationLedger.all_cycle_margins:119`, and
`CorrectionAnalyticStep.{step_preserves:632, iterate_invariant:657, iterate_results:674}`.
*Question:* is that intentional (documentation) or a sign of a refactor that left the live path
using a different, unaudited set of inequalities? I checked the live inline `linarith`s against
the ledger's statements and they agree numerically, so I believe it is documentation.
*What would settle it:* confirm the cone extraction, then either delete or mark those files.

**6. ~~The class-degree question~~ (parent's sharpened target) — RESOLVED, kept for the record.**
`MemClass` re-chooses `C` and `p` at every application and `finalBlock_uniform_cumulative:8629`
makes both grow with the cycle index, but the conversion to the physical jet bound charges a fixed
`+1` for all slow-power growth (`PhysicalGraphBounds.slow_power_absorption:806`) and the exponent
losses are `J`-free by type. See Cross-check 2. **The residual form of the worry, worth one expert
sentence:** nothing on the live path proves `sup_J C_J < ∞`, so any statement that needs a
*stage-uniform* constant (e.g. a genuine `J → ∞` limit rather than a per-`J` bound) does not follow.
`WeightedClasses.lean:125` says this deliberately: *"Stage constants are deliberately not uniform in
the stage index."* Both children independently landed on this as the remaining attack surface
(`ActualStageEstimates.RunData:97`).

---

## Residue — what I could not check

1. **Anything below `signed_tensor_bounds`.** `remainderTensor_mem` delegates to
   `f.remainder_sum_mem` (a `SignedFamily` field/lemma in `LabelSumBounds`), and
   `crossTensor_mem` to `harmonic_covariance_sum_mem`. I verified the *exponent algebra* of the
   three branches but not the harmonic-sum estimates behind them. Likewise
   `interactionBlock_uniform` (the nonlinear block), `gaugeTemporalStage_constructed`,
   `gaugeRankStage_constructed`, `MovingMomentBounds.rankStage_defectBounds`,
   `GaugeDebtIncrement.*`, `MeanStageRegularity.*`, `GaugeExcludedBounds.*`,
   `SignedMeanGain.Assembly`/`signedFamily` and `LabelSumBounds.SignedFamily` itself.
2. **The construction of `StepData` at every cycle** (delegated, child `cas-chain-closure`) and
   **the class→`JetRate` conversion** (delegated, child `cas-class-degree`).
3. **Definitional claims discharged by `rfl`** that I cannot verify without elaboration:
   `CorrectionAnalyticStep.lean:197` (`c.operators = graphOperators …`), `:246`,
   `:541` (`fun _ => ⟨rfl,rfl,rfl⟩`, a `SameCarrier`), **`:583`** (the `hfixed` argument
   `(reconstructState G.gauge c (afterParticular …)).pressure = (afterParticular …).pressure`),
   `:591`, and `ActualCycleExcluded.lean:177,183,186,198-201`. `:583` is the one I would check
   first: the analogous fact is elsewhere proved by a lemma
   (`GaugeMomentBalances.reconstructState_idempotent`, used at
   `CrossBasedMeanComposition.lean:467`), so `rfl` here is plausible but load-bearing.
4. **Two `erw`** at `CrossBasedMeanComposition.lean:621-622` (`by erw [hw₂]; exact hg` and
   `erw [hw₂] at hgain`). `erw` unfolds reducible definitions to make `rw` succeed; it is where a
   "same up to defeq" mismatch would be papered over. Cannot check without elaboration.
5. **No elaboration or kernel check at all.** I report what the source claims. A `linarith`,
   `simpa only`, `convert! … using 1; ring`, or `class_congr` could fail to elaborate; the
   parent's premise (Comparator passed) is what licenses ignoring that. Conversely I cannot rule
   out that a `simp only` closes a goal differently from what its surrounding `have` name suggests.
6. **`CycleMeanEquation.lean`** (623 lines) was only skimmed: `step` uses it via
   `hStep : CycleMeanEquation.StepData` (`:345-366`) and `hStep.next_meanHypotheses` (`:418`).
   Its 16 fields are all supplied from `H.*`/`W.*` and I checked the supply, not the consumer.
7. **`WeightedClasses.lean:130-518`** — I read only the definitions and `mono_exponent`'s use
   sites, not the ~40 closure lemmas (`add`, `sub`, `map`, `dz`, `radialDiv`, `class_congr`,
   `MemClass.zero`). If e.g. `MemClass.add` silently weakened the weight, many of my "OK"s would
   need revisiting; the definitions are simple enough that I consider this low risk.

---

## Cross-check 1 — chain closure (child `cas-chain-closure`, `workers/_sub-cas-chain-closure.md`)

Independent read of the *live* constructors. Summary of what it reports, with its `file:line`:

* **The induction chains, and the live path is even cleaner than the generic one.**
  `ActualCyclePreservation.state_runInvariant:826` is a *closed* theorem `∀ j` in `B, N0, hN` — it
  has **no `data` hypothesis at all**; `StepData` is *constructed* at
  `ActualCyclePreservation.lean:730` out of the `RunInvariant` record (`:768`, analytic + coherent +
  periodic). `CorrectionAnalyticStep.iterate_invariant:657`, which does take a `data` argument, is
  the unused generic form (consistent with my cone finding).
* **No upper bound on `σ` exists anywhere.** A grep for `σ ≤` / `≤ σ` finds only `1/5 ≤ σ` and
  `κ ≤ 1/100000`. So nothing forbids `σ → ∞`.
* **The two cancellation estimates are σ-free after cancellation.** At
  `CorrectionStep.lean:9587,9627` they are consumed as `1/2+σ+1/10 ≤ 1+σ-3κ` and `≤ 1+σ-4κ`: `σ`
  cancels, the requirement is the *fixed* `1/10+3κ ≤ 1/2`. Their provers are
  `ActualParticularCycleData.linear_bounds:691` (from `good_bounds:610` plus an **exact identity**
  `field_cancellation:668`) and `ActualSignedCommonDynamics:512`, both generic in the exponent with
  no upper bound on it. Notably `ActualParticularCycleData.actual_data:800` **does not use `hσ`**
  (the binder is `_hσ`), i.e. the per-cycle wave construction is indifferent to how large `σ` has
  become — which is exactly what makes the induction chain.
* **The finite-head cost is σ-free.** In the promotion at `SignedCrossDefectClass:173` the baseline
  exponent is `1+σ-κ` and the target `1+σ+17/100+κ`, so
  `α-β = -(17/100+2κ)` — independent of `σ`, hence `FiniteHeadClass.comparison:23`
  (`1 + Σ_{n<N} ε_n^{α-β}`) is a *fixed* constant, not one that degrades per cycle. `cross_tail`
  itself is discharged by `ActualSignedMeanBinding:655` (generic in `α δ β η`, geometric argument at
  `:463`) — this closes my Escalation 2 in the reassuring direction.
* **Confirms my §A3 reading** of `CorrectionStep.lean:9408-9461` (σ only in `residual:9440`,
  `mean:9443`, `debt:9445`) and my §C1 margin: `17/25 ≤ 1/2+σ-κ` at `:8632`, margin `1/50` at
  `σ = 1/5` and growing.
* **Cycle-index-free:** `κ = ChartScales.kappa = 1/100000` fixed (`ActualCyclePreservation:38,74`);
  `primaryBand`, `cells`, `tailStart` are cycle-free (`ActualCyclePreservation:579,583,596`).
* **What does grow: the class constants `C_j`** — the existential is *inside* each cycle's `Prop`
  (`WeightedClasses.lean:111`, `LabelSumBounds:37`), and `WeightedClasses.lean:125` says so in a
  docstring: *"Stage constants are deliberately not uniform in the stage index."* Child A's verdict:
  harmless for the induction, and the place to attack is any statement that needs
  `sup_j C_j < ∞` — it names `ActualStageEstimates.RunData:97` (a `∀ j` record with no such
  supremum). That is the same seam as my §C2, from the other side.

---

## Cross-check 2 — the class degree/constant question (child `cas-class-degree`, `workers/_sub-cas-class-degree.md`)

This closes §C2 and Escalation 6 (the parent's sharpened worry: *"is `+1/10` per cycle empty because
`p` and `C` may grow with the cycle index?"*). **Verdict: NOT vacuous.** The mechanism it found, with
its `file:line`:

1. **`PhysicalGraphBounds.slow_power_absorption:806`** —
   `(a : ℝ) : ∃ C > 0, ∀ n, S n ^ a ≤ C * Q n ^ (-1)`. **Any** real power of the slow scale costs
   exactly **1** in the band exponent, and only the constant depends on `a`. It is charged once, in
   `stripped_class_physical_bound:824-861`, whose conclusion exponent is
   `g − (graphLoss m + 1)` — *independent of `a`* (hence of `p`, hence of the cycle index). The
   loss is named at `PhysicalMeanJetBounds.lean:132`: `loss degree m = graphLoss m + 1 + degree`.
   This works only because `slow n = max 1 n^2` is polynomial while `Q n = 2^{-n}` is geometric
   (`ActualInitialization.lean:651`, `BaseContextAssembly.lean:31`, `ChartScales.lean:28`,
   `ActualMeanPhysicalData.slowScale_le_S:246`).
2. **The exponent loss is `J`-free by type, not by accident:** `NativeBounds.loss : ℕ → ℝ`
   (`PhysicalResidualJetBounds.lean:377`), `RawStageBounds.L : ℕ → ℝ`
   (`CutStageEstimates.lean:199`), and
   `fixedLoss m = m(m+2) + 1 + (2·A h + 1/2) + 2h·m` (`ActualCycleResidualBounds.lean:1145`).
   The degree `p` is destructured and *discarded* at `ActualCycleResidualBounds.lean:926`
   (`obtain ⟨A, hA, e, hb⟩ := hf.bounds m`) and does not appear in the exponent computation at
   `:951`.
3. **The spatial factor `(max 1 (delta x)⁻¹)^p` is absorbed by the weight, not by a lower bound on
   `delta`** (which does not exist): `zeta` is Gaussian-flat, `exp(-c/x²)`
   (`PhysicalClassBounds.lean:55-74`, `FlatCutoff.lean:26`), so `K(p,c)` finite for every `p`.
   Per-`J` constants are then absorbed because the cutoff schedule is chosen **after** them
   (`CutStageEstimates.lean:362-368`, at the price `g j / 2` — the halving my predecessor worker
   already validated).
4. The `0.7h` surplus is real (`ActualIterationLedger.lean:252`) but is used only at
   `:1203-1206`; the `+1` of `slow_power_absorption` is paid separately. **No `J`-uniform `p` or `C`
   is needed anywhere on the live path.**

So the exponent bookkeeping is: per-cycle `p` and `C` grow freely; the conversion to the physical
`JetRate` charges a **fixed** `+1` for all of the `slow`-power growth and puts everything else in the
constant, which the consumer (`∀ J m, ∃ C, …`) permits. **The `+1/10` gain therefore survives
intact.**
