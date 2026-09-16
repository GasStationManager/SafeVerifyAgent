
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

