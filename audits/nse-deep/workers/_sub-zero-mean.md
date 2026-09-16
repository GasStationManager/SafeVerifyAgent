
# Sub-audit: is the mean EVER nonzero on the live NSE chain?
Repo /home/gsm/.openclaw/workspace/repos/NSE @ f9e8bc5. READ-ONLY. No `lake build` (0 .olean, pinned v4.34.0-rc2). Grep+read only.
Started 2026-09-16T18:48:06

## Q1. seed.mean / ranked.mean / initialized.mean

**Type facts.** `CorrectionState.State` carries `mean : Triple D` (NavierStokes/CorrectionState.lean:65-70);
`MeanIncrementBounds.Triple` = 3 `Field D = ℕ → D → ℝ` (NavierStokes/MeanIncrementBounds.lean:26-29);
`updated m h = ⟨m.radial+h.radial, m.angular+h.angular, m.axial+h.axial⟩` (MeanIncrementBounds.lean:31-32);
`State.addIncrement s m .. = { mean := updated s.mean m, ... }` (CorrectionState.lean:150-156).

**(a) `(seed B N0).mean` = SYNTACTICALLY ZERO.**
`ActualInitialMean.seed B N0 := bandSeed (activeLabels ...) primaryPiece (baseError B)` (NavierStokes/ActualInitialMean.lean:43-44).
`CorrectionInitialization.bandSeed ... : State D where mean := ⟨0, 0, 0⟩` (NavierStokes/CorrectionInitialization.lean:1106-1112, mean at :1108).
Independently confirmed by an `rfl` lemma: `ActualInitialization.sourceState_mean (B N0) : (sourceState B N0).mean = ⟨0,0,0⟩ := rfl` (NavierStokes/ActualInitialization.lean:266).
Same for the sibling `seed` in ActualInitialCoherence.lean:34-35 (also `bandSeed`).

**(b) `(ranked B N0).mean` = NOT zero; it carries the TEMPORAL + RANK increments.**
Chain (all definitional):
- `primary B N0 := VariableGaugeMean.reconstructState commonGauge (commonContext B) (seed B N0)` (ActualInitialMean.lean:48-49).
  `reconstructState g c u := { u with pressure := meanPressure ... }` (NavierStokes/VariableGaugeMean.lean:517-523) — **mean PRESERVED** (record update touches only `pressure`).
- `temporal B N0 := VariableGaugeMean.temporalStageState commonGauge h index axial (commonContext B) (primary B N0)` (ActualInitialMean.lean:51-53).
  `temporalStageState g h index axial c u := reconstructState g c (u.addIncrement (temporalIncrementState g h index axial c u) 0 0 0 ⟨0,0,temporalAliasState ...⟩)` (VariableGaugeMean.lean:559-563).
  So `temporal.mean = updated ⟨0,0,0⟩ (temporalIncrementState ...)` — **mean ADDED TO**.
  `temporalIncrementState` (VariableGaugeMean.lean:538-545): radial = `PressureStream.streamBeta (ε n • axial) (temporalPotential g h index c u n)`,
  angular = `MeanChartCompatibility.temporalAtIndex h n (index n) (u.thetaResidual c n)`,
  axial = `PressureStream.streamGamma (physicalSpeed ...) (0, radialDirection) (temporalPotential ...)`. These are real analytic fields built from `u.thetaResidual` / `u.axialResidual`, not `0`.
- `ranked B N0 := VariableGaugeMean.rankStageState commonGauge rankData axial (commonContext B) (temporal B N0)` (ActualInitialMean.lean:55-57).
  `rankStageState g r axial c u := reconstructState g c (u.addIncrement (rankIncrementState g r axial c u) 0 0 0 ExcludedErrors.zero)` (VariableGaugeMean.lean:580-583) — **mean ADDED TO again**, by `rankIncrementState` (VariableGaugeMean.lean:571-578, built from `rankDesiredAxial` / `rankAngular`).
  Hence `ranked.mean = updated (updated ⟨0,0,0⟩ temporalIncrement) rankIncrement`.

**(c) `(initialized B N0).mean` = NOT zero, and there is an EXPLICIT THEOREM saying so.**
`initialized B N0 := GaugeInitialization.initializedBands commonGauge rankData h index axial (commonContext B) (activeLabels ...) primaryPiece (baseError B)` (ActualInitialMean.lean:59-62)
= `retainPressureAlias g c (rankBands ...)` (CorrectionInitialization.lean:1359-1363), where `rankBands = rankStageState .. (temporalBands ..)` (:1353-1357) and `temporalBands = temporalStageState .. (primaryBands ..)` (:1347-1351), `primaryBands = reconstructState g c (bandSeed ..)` (:1342-1345) — i.e. the same 4-step chain as (b).
**`ActualMeanPotentialRealization.initializedBands_mean` (NavierStokes/ActualMeanPotentialRealization.lean:589-604):**
`(initializedBands g r h index axial c labels pieces baseError).mean = MeanIncrementBounds.updated (VariableGaugeMean.temporalIncrementState g h index axial c (primaryBands ...)) (VariableGaugeMean.rankIncrementState g r axial c (temporalBands ...))`,
proved by `change updated (updated ⟨0,0,0⟩ temporalIncrement) rankIncrement = _ ; simp only [updated, zero_add]` (:599-604).
**=> The literal initialized mean is exactly `temporalIncrement + rankIncrement`. It is NOT the zero triple.**

### Q1 verdict
`seed.mean` is literally `⟨0,0,0⟩`. `ranked.mean` and `initialized.mean` are NOT zero: they are the sum of the temporal-stage and rank-stage mean increments. The zero only sits at the seed, as the base case of the induction.


## Q2. Census of every stage that can change `u.mean` (all `*_mean` / `.mean =` lemmas)

Only THREE primitive constructors ever touch `mean`, and exactly ONE of them writes a nonzero triple:

| # | stage / constructor | file:line | effect on `u.mean` |
|---|---|---|---|
| 1 | `reconstructState g c u = {u with pressure := ...}` | VariableGaugeMean.lean:517-523 | **PRESERVED** (record update, `mean` untouched) |
| 2 | `retainPressureAlias g c u = {u with errors := ...}` | CorrectionInitialization.lean:1281-1284 | **PRESERVED** |
| 3 | `gaugeRefreshPressureAlias g c old current = {current with errors := ...}` | CorrectionStep.lean:3042-3046 | **PRESERVED** |
| 4 | `SignedMeanGain.waveStage g c u w q gaussian = reconstructState g c (u.addIncrement zeroTriple 0 w q ...)` | SignedMeanGain.lean:168-172 | **PRESERVED**: `waveStage_mean : (waveStage ...).mean = u.mean := updated_zeroTriple u.mean` (SignedMeanGain.lean:180-184); `zeroTriple := ⟨0,0,0⟩` (:143), `updated_zeroTriple : updated m zeroTriple = m` (:146-148) |
| 5 | `CorrectionStep.gaugeWaveStage` (cycle wave stage) | CorrectionStep.lean:3328-3333 | **PRESERVED**: `gaugeWaveStage_mean : (gaugeWaveStage g c u w q e).mean = u.mean := updated_zeroTriple u.mean` (CorrectionStep.lean:3339-3342) |
| 6 | `temporalStageState g h index axial c u = reconstructState g c (u.addIncrement (temporalIncrementState g h index axial c u) 0 0 0 ⟨0,0,temporalAliasState ...⟩)` | VariableGaugeMean.lean:559-563 | **ADDED TO**: `GaugeDebtIncrement.temporalStage_mean : (temporalStageState ...).mean = updated u.mean (temporalIncrementState g h index axial c u) := rfl` (GaugeDebtIncrement.lean:448-450) |
| 7 | `rankStageState g r axial c u = reconstructState g c (u.addIncrement (rankIncrementState g r axial c u) 0 0 0 ExcludedErrors.zero)` | VariableGaugeMean.lean:580-583 | **ADDED TO** (by `rankIncrementState`, VariableGaugeMean.lean:571-578) |

Nothing anywhere REPLACES the mean; `addIncrement` only ever does `mean := updated s.mean m` (CorrectionState.lean:150-152) and `updated` is componentwise `+` (MeanIncrementBounds.lean:31-32).

**Cycle level.** `CycleParameters.next u = gaugeRefreshPressureAlias (afterRank (afterTemporal (afterSigned (afterParticular u))))` (CorrectionStep.lean:5042-5085), with `afterParticular`/`afterSigned` = `gaugeWaveStage` (:5042-5044, :5066-5068), `afterTemporal` = `temporalStageState` (:5073-5074), `afterRank` = `rankStageState` (:5079-5080). The mean bookkeeping is stated exactly:
- `afterParticular_mean : (p.afterParticular v c u).mean = u.mean` (CorrectionStep.lean:5314-5315)
- `afterSigned_mean : (p.afterSigned v c u).mean = u.mean` (CorrectionStep.lean:5317-5318)
- **`next_mean : (p.next v c u).mean = updated (updated u.mean (p.temporalIncrement v c u)) (p.rankIncrement v c u)`** (CorrectionStep.lean:5115-5122)
So EVERY cycle adds the two increments to the mean; the wave/particular/signed/gauge stages do not.

### FIRST place the mean provably becomes non-(syntactically)-zero
**`VariableGaugeMean.temporalStageState`, at NavierStokes/VariableGaugeMean.lean:562** — the `u.addIncrement (temporalIncrementState g h index axial c u) ...` in the temporal stage. On the LIVE initial chain this is instantiated at **NavierStokes/ActualInitialMean.lean:51-53** (`temporal B N0`), and the resulting mean is pinned by an explicit theorem at **NavierStokes/ActualMeanPotentialRealization.lean:589-604** (`initializedBands_mean`), which states the live `initialized` mean equals `temporalIncrement + rankIncrement`.

**Is that increment provably nonzero (not merely non-syntactically-zero)?** Its angular component is `MeanChartCompatibility.temporalAtIndex h n (index n) (u.thetaResidual c n)` (VariableGaugeMean.lean:542) and its radial/axial components are `streamBeta`/`streamGamma` of `temporalPotential`, which is `streamPotential ... (temporalAtIndex h n (index n) (u.axialResidual c n))` (VariableGaugeMean.lean:532-536). At the seed, where the mean IS zero, the residuals are NOT zero — they reduce to the primary-wave covariance divergences:
- `zeroMean_gr (hm : u.mean = ⟨0,0,0⟩) : u.gr c = -(radialDiv 1 (W 0 0) + dz (W 2 0) - invRadius * W 1 1)` (CorrectionInitialization.lean:1825-1830)
- `zeroMean_theta : u.thetaResidual c = radialDiv 2 (W 0 1) + dz (W 2 1) - radialDiv 2 c.virtualTheta` (:1832-1837)
- `zeroMean_axial : u.axialResidual c = radialDiv 1 (W 0 2) + dz (W 2 2 + u.pressure) - radialDiv 1 c.virtualAxial` (:1839-1844)
with `W = u.covariance = bilinearCovariance (seed oscillation) (seed oscillation)` (CorrectionState.lean:98-99; `bandSeed_covariance`, CorrectionInitialization.lean:1114-1118) — i.e. the genuine Reynolds stress of the primary wave packet. So the increment is DRIVEN by the wave covariance, not by the (zero) seed mean. I found NO theorem in the repo asserting a pointwise nonvanishing / lower bound on `mean` itself, so "nonzero" here means *structurally nonzero and residual-driven*, not *proved `≠ 0`*.

