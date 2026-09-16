# NSE deep audit — HEADLINE CHAIN vs. wave-label inhabitance

Repo: /home/gsm/.openclaw/workspace/repos/NSE @ f9e8bc5. READ-ONLY. No file modified, no `lake build` run
(no `.olean`, toolchain mismatch). All findings are from source reading + grep, with file:line.
Method note: I also built an *import-respecting* identifier reference graph over the 609 modules in the
transitive import closure of `NavierStokes/ComparatorSolution.lean` (in a scratch Python session, nothing
written to the repo) to find candidate dependency paths, then **verified every hop by hand** against the
literal source line. Every hop quoted below was checked in the source.

--------------------------------------------------------------------------------
## 1. Top-level / headline results

### Declared headline results (README.md + formalization.yaml)
`formalization.yaml:55,64` (+ alignment rows `:112,116`) name the two Navier–Stokes headline declarations;
`:75,87` (+ `:120,124`) name the two Euler ones. The label machinery under audit lives in `NavierStokes/`, so the NS pair is the
relevant headline.

| # | declaration | file:line |
|---|---|---|
| 1 | `NavierStokes.Comparator.navier_stokes_breakdown_R3` | `NavierStokes/ComparatorSolution.lean:16` |
| 2 | `NavierStokes.Comparator.navier_stokes_breakdown_periodic` | `NavierStokes/ComparatorSolution.lean:23` |
| — | `#print axioms` for both | `NavierStokes/ComparatorSolution.lean:31,32` |
| 3 | `Euler.euler_breakdown_R3` | `Euler/Solution.lean:33` |
| 4 | `Euler.exists_compact_smooth_euler_singularity` | `Euler/Solution.lean:43` |
| ref | Comparator reference statement (challenge module, NOT imported by the solution) | `ComparatorChallenges/NavierStokes.lean:273` |
| cfg | comparator config listing the two NS names | `ComparatorChallenges/NavierStokes.json:6` |

### Adapters and the spine below headline #1
* `NavierStokes.ComparatorBridge.navier_stokes_breakdown_R3` — `NavierStokes/ComparatorR3Theorem.lean:38`
  (proof at `:43` `obtain ... := NavierStokesR3.theorem_1_1 ν hν`; also `option_C_of_compact_candidate` at
  `ComparatorR3Theorem.lean:21`, which picks the **zero** initial datum `fun _ => 0` at `:33`).
* `NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic` — `NavierStokes/ComparatorTheorem.lean:47`
  (proof at `:52` via `PeriodicPaper.periodic_corollary`; that corollary in turn consumes
  `NavierStokesR3.theorem_1_1_with_initial_rest` at `NavierStokes/PeriodicPaperTheorem.lean:158`, i.e. the
  **same** spine).

### `theorem_1_1` family
| declaration | file:line |
|---|---|
| `NavierStokesR3.theorem_1_1_with_initial_rest` | `NavierStokes/R3/Theorem.lean:26` |
| `NavierStokesR3.theorem_1_1` | `NavierStokes/R3/Theorem.lean:46` |
| `NavierStokesR3.candidateStatement` | `NavierStokes/R3/Theorem.lean:53` |
| `NavierStokesR3.coreBreakdownStatement` | `NavierStokes/R3/Theorem.lean:61` |
| `NavierStokesR3.breakdownStatement` | `NavierStokes/R3/Theorem.lean:62` |
| `NavierStokesR3.theorem_1_1_with_dissipation` | `NavierStokes/R3/Theorem.lean:66` |
| `NavierStokesR3.theorem_1_1_with_maximalH3` | `NavierStokes/R3/H3MaximalLifespan.lean:109` |

### `witness` / `selected_witness`
| declaration | file:line |
|---|---|
| `NavierStokes.ActualCandidateAssembly.Witness` (a `Prop`, the packaged goal) | `NavierStokes/ActualCandidateAssembly.lean:1121` |
| `NavierStokes.ActualCandidateAssembly.witness` | `NavierStokes/ActualCandidateAssembly.lean:1153` |
| `NavierStokes.ActualCandidateAssembly.selected_witness` | `NavierStokes/ActualCandidateAssembly.lean:1177` (`= witness selectedBudget selectedThreshold ...` at `:1180`) |
| `NavierStokes.ActualCandidateAssembly.selected_candidate` | `NavierStokes/ActualCandidateAssembly.lean:1183` |
| bottom producer | `GermCandidateAssembly.exists_candidate_witness_of_finite_stages` — `NavierStokes/GermCandidateAssembly.lean:164`, invoked at `ActualCandidateAssembly.lean:1155` |
| consumers of `selected_witness` | `NavierStokes/R3/ActualCandidate.lean:132`, `:149`; `NavierStokes/R3ActualCandidate.lean:20`; `NavierStokes/LocalAngularGrowth.lean:243` |

### `CandidateProperties` and its FIELDS
Two structures with this name are in play.

A. Periodic/base version — `NavierStokes/ProblemStatement.lean:101`. Fields:
`velocity_smooth :103`, `pressure_smooth :104`, `force_smooth :105`, `velocity_periodic :106`,
`pressure_periodic :107`, `force_periodic :108`, `zero_initial_velocity :109`, `force_time_support :110`,
`divergence_free :111`, `navier_stokes :112`, **`speed_unbounded :114`**.

B. Whole-space (ν-parameterised, used by `theorem_1_1`) — `NavierStokes/R3/ProblemStatement.lean:92`. Fields:
`velocity_smooth :94`, `pressure_smooth :95`, `support_compact :96`, `velocity_support :97`,
`pressure_support :99`, `force_smooth :101`, `force_support :102`, `zero_initial_velocity :103`,
`divergence_free :104`, `navier_stokes :106`, `energy_bounded :108`, **`speed_unbounded :109`**.
Related: `Candidate :112`, `GlobalFiniteEnergySolution :125`, `candidateStatement :138`,
`coreBreakdownStatement :143`, `breakdownStatement :150`.

### `speed_unbounded` (the blow-up field) and `SpeedUnboundedAtOne`
* `def SpeedUnboundedAtOne` — `NavierStokes/ProblemStatement.lean:94-96`:
  `∀ M > 0, ∀ δ > 0, ∃ t x, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖`. `abbrev` re-export at
  `NavierStokes/R3/ProblemStatement.lean:88`.
* Field occurrences: `ProblemStatement.lean:114`, `R3/ProblemStatement.lean:109`,
  `R3CompactCandidate.lean:37`, `PeriodicPaperTheorem.lean:47`.
* Where it is actually *produced* in the audited chain:
  `FinalSlowBase.speedUnbounded` — `NavierStokes/FinalSlowBase.lean:380`, from
  `FinalSlowBase.axis_tendsto` — `NavierStokes/FinalSlowBase.lean:372`, from
  `BaseResidual.baseVelocity_axis_tendsto_atTop` — `NavierStokes/BaseResidual.lean:104`.
  This is a **closed formula** blow-up: `FinalSlowBase.origin` (`FinalSlowBase.lean:361-363`) gives
  `velocity H v upper B (t,0) = ((1-t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • coordinateVector 2`,
  and the only positivity input is the scalar `W.axis.small.j_pos` (`FinalSlowBase.lean:378`).
  **No label type appears anywhere in this blow-up argument.**

--------------------------------------------------------------------------------
## 2. Does the headline statement / its near dependencies mention `Nonempty`, `IsEmpty`, `Fintype`, or a label type?

Headline statement verbatim (`NavierStokes/ComparatorSolution.lean:16-21`):

```
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu
```

* **Fully closed.** The statement quantifies only over `nu : ℝ`, two function fields, and (negatively) a
  solution pair. It is **not** quantified over any label type, and mentions no label type, no `Nonempty`,
  no `IsEmpty`, no `Fintype`, no `Finset`.
* Its statement vocabulary is entirely from `NavierStokes/ComparatorDefinitions.lean`:
  `InitialVelocityConditionDecay :124`, `ForceConditionDecay :159`, `NavierStokesExistenceAndSmoothness :191`,
  `NavierStokesExistenceAndSmoothnessRn :219`. None of these mention labels/`Nonempty`/`Fintype`.
* Depth walked: **6+ levels** on the spine (headline → bridge → `theorem_1_1` → `theorem_1_1_with_initial_rest`
  → `ActualCandidate.selected_candidate_one_with_initial_rest` → `ActualCandidateAssembly.selected_witness`
  → `witness` → `estimates` / `GermCandidateAssembly.exists_candidate_witness_of_finite_stages`), plus
  6–8 further levels down each of the six branches in §3.
* `Nonempty` **does** occur on the spine, but never of a label type:
  - `¬ Nonempty (GlobalFiniteEnergySolution ν f)` — `NavierStokes/R3/Theorem.lean:29`, `:70`;
    `R3/ProblemStatement.lean:153` (`breakdownStatement`), structure at `R3/ProblemStatement.lean:125`.
  - `candidateStatement_iff_nonempty` — `R3/ProblemStatement.lean:157` (`Nonempty (Candidate ν)`).
  - `Nonempty (OneSidedExtension …)` — `GermCandidateAssembly.lean:180,183,186,232,236,242` (extension
    germs of *velocity fields*, not labels).
  - `NavierStokes.ActualPrimary.choice_nonempty : Nonempty (Choice B N0)` — `CorrectionInitialization.lean:3923`,
    used at `:3929` `choice B N0 := Classical.choice (choice_nonempty B N0)`. **This is inhabitance of the
    parameter record `Choice` (`:3907`), NOT of the index type.** The label type is then *defined* from it:
    `abbrev Label (B N0 : ℕ) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N`
    (`CorrectionInitialization.lean:3931`).
* Also on the spine, statement-level: `ActualCandidateAssembly.Witness` (`:1121-1151`) is stated purely in
  terms of `VelocityField`/`PressureField`/`ℕ → ℕ` — label types have already been summed away
  (`SolenoidalDiagonal.potentialSum …`), so no label type is visible in the spine statements at all.

**Answer to 2: the headline statement is fully closed and label-free; no `Nonempty`/`IsEmpty`/`Fintype`
hypothesis about any label type occurs in it or in any spine statement above the estimate layer.**

--------------------------------------------------------------------------------
## 3. Does the headline chain pass through the six case-split sites? YES — all six.

Enclosing declarations (line of the `theorem` keyword) and consumers:

| # | split site | enclosing decl (file:line of `theorem`) | fully-qualified name | consumers (grep of bare name) |
|---|---|---|---|---|
| 1 | `ActualInitialMean.lean:318` `rcases isEmpty_or_nonempty (Index B N0)` | `ActualInitialMean.lean:309` | `NavierStokes.ActualInitialMean.covariance_bounds_of_curl` | `ActualInitialMean.lean:558` (inside `covariance_bounds`, `:554`) — only consumer |
| 2 | `ActualSignedUnmaskedBounds.lean:161` `cases isEmpty_or_nonempty (Label B N0)` | `ActualSignedUnmaskedBounds.lean:150` | `NavierStokes.ActualSignedUnmaskedBounds.raw_jets` | `ActualSignedUnmaskedBounds.lean:204`, `:205` (inside `localized_jets`, `:185`) |
| 3 | `ActualSignedUnmaskedBounds.lean:196` same split | `ActualSignedUnmaskedBounds.lean:185` | `NavierStokes.ActualSignedUnmaskedBounds.localized_jets` | `ActualSignedUnmaskedBounds.lean:217` (`potential_jets`, `:207`), `:369` (`own_potential_pressure_class`, `:357`) |
| 4 | `ActualSignedStageControls.lean:1132` `cases isEmpty_or_nonempty (SignedLabel B N0)` | `ActualSignedStageControls.lean:1121` | `NavierStokes.ActualSignedStageControls.raw_coefficients_jets` | `ActualSignedGaussian.lean:175`, `ActualSignedOutputBounds.lean:161`, `ActualSignedCommonDynamics.lean:115`, `ActualSignedStageControls.lean:1183` |
| 5 | `ActualParticularStageControls.lean:941` `by_cases hne : Nonempty (ActivePair B N0)` | `ActualParticularStageControls.lean:924` | `NavierStokes.ActualParticularStageControls.raw_jets` | `ActualCurrentParticularBounds.lean:161`, `ActualParticularDynamics.lean:878`, `:1088`, `ActualParticularGaussian.lean:218`, `ActualParticularStageControls.lean:1371` |
| 6 | `ActualParticularStageControls.lean:1214` same split | `ActualParticularStageControls.lean:1209` | `NavierStokes.ActualParticularStageControls.cutoff_jets` | `ActualCurrentParticularBounds.lean:169`, `ActualParticularGaussian.lean:218`, `ActualParticularStageControls.lean:1375` |

### Shared spine (verified hop-by-hop, literal lines)
```
NavierStokes.Comparator.navier_stokes_breakdown_R3        ComparatorSolution.lean:16
  -> ComparatorSolution.lean:20   exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu
ComparatorBridge.navier_stokes_breakdown_R3               ComparatorR3Theorem.lean:38
  -> ComparatorR3Theorem.lean:43  obtain ... := NavierStokesR3.theorem_1_1 ν hν
NavierStokesR3.theorem_1_1                                R3/Theorem.lean:46
  -> R3/Theorem.lean:48           obtain ... := theorem_1_1_with_initial_rest ν hν
NavierStokesR3.theorem_1_1_with_initial_rest              R3/Theorem.lean:26
  -> R3/Theorem.lean:32           obtain ... := ActualCandidate.selected_candidate_one_with_initial_rest
...ActualCandidate.selected_candidate_one_with_initial_rest  R3/ActualCandidate.lean:143
  -> R3/ActualCandidate.lean:149  ActualCandidateAssembly.selected_witness
ActualCandidateAssembly.selected_witness                  ActualCandidateAssembly.lean:1177
  -> ActualCandidateAssembly.lean:1180   witness selectedBudget selectedThreshold ...
ActualCandidateAssembly.witness                           ActualCandidateAssembly.lean:1153
  -> ActualCandidateAssembly.lean:1157   ... (estimates B N0 hN)
  -> ActualCandidateAssembly.lean:1158   ... (directStages_support B N0 hN)
ActualCandidateAssembly.estimates                         ActualCandidateAssembly.lean:1090
  -> ActualCandidateAssembly.lean:1094   GluedStageEstimates.actualStageEstimates ...
  -> ActualCandidateAssembly.lean:1095   ... (ActualSignedWaveData.signedInputs B N0 hN)
```

### Branch to sites 5 and 6
```
GluedStageEstimates.actualStageEstimates          GluedStageEstimates.lean:684
  -> :700   (current_potential_bound R C hGeom hN hq)
GluedStageEstimates.current_potential_bound       GluedStageEstimates.lean:627
  -> :634   ActualCurrentParticularBounds.current_potential_mode_bound
ActualCurrentParticularBounds.current_potential_mode_bound   :873
  -> :886   obtain ... := actual_native_potential_bound y hcar hin hN j hj hsrc m
ActualCurrentParticularBounds.actual_native_potential_bound  :543
  -> :554   have hb := native_modulated_bound (actual_potential_coefficient_class x hx hs hN j hj H)
ActualCurrentParticularBounds.actual_potential_coefficient_class :152
  -> :161   have hr := ActualParticularStageControls.raw_jets x        <-- SITE 5
  -> :169   (ActualParticularStageControls.cutoff_jets x j)            <-- SITE 6
```

### Branch to site 1
```
GluedStageEstimates.actualStageEstimates          :684
  -> :695   let E := stageEstimates_of_component_bounds R M hN W ...
GluedStageEstimates.stageEstimates_of_component_bounds  :379
  -> :431-434  simpa only [actualInitialTemporalInput, actualInitialRankInput, ...] using
               represented_initial_rate ... (actualInitialRankInput B N0 N hN) ...
ActualPhysicalStageBounds.actualInitialRankInput  ActualPhysicalStageBounds.lean:850
  -> :854   (initialRank_moving B N0) (initialRank_nativeJets B N0 N (by omega))
ActualMeanPhysicalData.initialRank_nativeJets     ActualMeanPhysicalData.lean:568
  -> :571   initial_nativeJets_of_class (initialRank_moving B N0) (initialRank_class B N0) N hN
ActualMeanPhysicalData.initialRank_class          ActualMeanPhysicalData.lean:550
  -> :552   have HD := (ActualInitialMean.primary_mean_data B N0).temporal_debt_bounds
ActualInitialMean.primary_mean_data               ActualInitialMean.lean:561
  -> :562   primaryData_of_covariance B N0 (covariance_bounds B N0).1
ActualInitialMean.covariance_bounds               ActualInitialMean.lean:554
  -> :558   covariance_bounds_of_curl B N0 curl_amplitude_uniform                <-- SITE 1
```
(Independent second route into the same file: `ActualMeanPhysicalData.lean:287`
`initialPressure_nativeJets` → `ActualInitialMean.initial_cumulative_bounds` `ActualInitialMean.lean:644` →
`initial_bounds :636` → `primary_mean_data :561`.)

### Branch to sites 2 and 3
```
ActualCandidateAssembly.estimates                 :1095  ActualSignedWaveData.signedInputs B N0 hN
ActualSignedWaveData.signedInputs                 ActualSignedWaveData.lean:657
  -> :661   pressure j := cyclePressureData (ActualCyclePreservation.state B N0 j) (stageResult B N0 hN j)
ActualSignedWaveData.cyclePressureData            :574
  -> :577   pressureFromResiduals (N0 := N0) (ActualParticularMeanGain.postParticular x) R.primitive
ActualSignedWaveData.pressureFromResiduals        :531
  -> :536   (ActualSignedNativeRegularity.nativeRegular_from_residuals u H hp α hfixed hθ hz)
ActualSignedNativeRegularity.nativeRegular_from_residuals  :477
  -> nativeRegular :441 -> :444  potential I n := (native_potential_smooth_and_flat ... ).1
ActualSignedNativeRegularity.native_potential_smooth_and_flat :411
  -> potential_smooth_and_flat :309 -> :315  exact own_native_smooth (own_potential_pressure_class hR).1
ActualSignedUnmaskedBounds.own_potential_pressure_class    :357
  -> :369   ownField_uniform hw (localized_jets hR).2                    <-- SITE 3
ActualSignedUnmaskedBounds.localized_jets         :185
  -> :204   SignedCopyBounds.uniform_smul cutoff_local_jets (raw_jets hR).1 hw   <-- SITE 2
```

### Branch to site 4
```
ActualCandidateAssembly.witness                   :1158  (directStages_support B N0 hN)
ActualCandidateAssembly.directStages_support      :673
  -> :678   ActualCandidateConstruction.angularMeanStages_shrinkingSupport (meanCycleInput B N0 hN) j
ActualCandidateAssembly.meanCycleInput            :483
  -> :489   (ActualCyclePreservation.state_waveData B N0 hN)
ActualCyclePreservation.state_waveData            ActualCyclePreservation.lean:860
  -> :866   waveData_of_particular (state_invariant B N0 hN j) hN
ActualCyclePreservation.waveData_of_particular    :689
  -> :709   signedGaussianSmooth := signed_gaussian_coefficients_smooth first
ActualCyclePreservation.signed_gaussian_coefficients_smooth :465
  -> :469   ((ActualSignedGaussian.globalGaussian_all_gains (signed_request_jets first) 0).each l) n i
ActualSignedGaussian.globalGaussian_all_gains     ActualSignedGaussian.lean:224
  -> :240   (localGaussian_all_gains hR β)
ActualSignedGaussian.localGaussian_all_gains      :189
  -> :199   (localGaussian_wave_jets hR) bandScales
ActualSignedGaussian.localGaussian_wave_jets      :161
  -> :175   (raw_coefficients_jets hR).1                                 <-- SITE 4
```
(Independent second consumer: `ActualSignedOutputBounds.lean:161` inside `native_inputs` `:154`.)

**All six enclosing declarations are consumed, and all six lie on a verified reference path from
`NavierStokes.Comparator.navier_stokes_breakdown_R3`. The label case-splits are therefore inside the
headline chain, not dead code.**

### How each empty branch is discharged (this is the load-bearing observation)
Every empty branch closes the goal with `isEmptyElim` / a `False` derivation and the **zero constant**:
* `ActualSignedUnmaskedBounds.lean:162-164`:
  `constructor <;> refine ⟨fun l => isEmptyElim l, fun _ => ⟨0, le_rfl, 0, fun l => isEmptyElim l⟩⟩`
* identical at `ActualSignedUnmaskedBounds.lean:197-199` and `ActualSignedStageControls.lean:1133-1135`.
* `ActualParticularStageControls.lean:977-987` and `:1230-1233`: `hempty … : False := hne ⟨⟨(l,n),hz.1⟩⟩`,
  then `⟨0, le_rfl, 0, …⟩`.
* `ActualInitialMean.lean:319-339`: with `IsEmpty (Index B N0)`, `activeLabels … = ∅` (`:320-321`),
  hence `(seed B N0).oscillation = 0` (`:322`) and `tangentSum = 0` (`:325`), and the mean-class bounds
  are supplied by `MemClass.zero` (`:328-329`).

So in the empty world every one of these six obligations is a *true* statement with constant `0`, i.e. all
label-indexed obligations here are **upper bounds** and are vacuously satisfiable.

### Repo-wide inhabitance search (adversarial)
* `grep -F 'Nonempty (Label' / 'Nonempty (Index' / 'Nonempty (SignedLabel' / 'Nonempty (ActivePair' /
  'Nonempty (CellIndex'` over all `*.lean`: the **only** hits are the two `by_cases` lines and their
  immediate `let`s — `ActualParticularStageControls.lean:941,942,1214,1215` — plus one section instance
  variable `variable [Countable Λ] [Nonempty (ActivePair H v a reference chart)]` at
  `ActualSignedGeometry.lean:1275` (used by `activeEnumeration` `:1277` / `activeEnumeration_surjective`
  `:1280`). That instance is supplied **only inside the nonempty branch** of the case split
  (`ActualParticularStageControls.lean:942-944`, `:1215-1217`, via
  `Classical.choose (exists_surjective_nat (ActivePair B N0))`).
* `grep -F 'IsEmpty (Label' / 'IsEmpty (Index' / …`: **no hits** (only the `isEmpty_or_nonempty` splits).
* `grep -E 'instance.*CellIndex|Fintype.*CellIndex|Nonempty.*CellIndex'`: **no hits**. There is no
  `Nonempty`, `Inhabited`, or `Fintype` instance for `BaseChartJets.CellIndex` (`BaseChartJets.lean:825`),
  `PrimaryGeometryAssembly.Index` (`PrimaryGeometryAssembly.lean:137-138`), or
  `ActualPrimary.Label` (`CorrectionInitialization.lean:3931`) anywhere in the repo.
* `grep -E 'activeLabels.*(Nonempty|nonempty|≠ ∅|card)'` and
  `grep -E '(Nonempty|nonempty|≠ ∅|0 < .*card).*(CommonWindow.labels|activeLabels)'`: **no hits**. The
  `Finset` of active labels (`CorrectionInitialization.lean:5179-5183`, membership lemma `:5185`) is never
  shown nonempty either. Note site 5/6 split on `ActivePair B N0` — a *subtype* of `Label × ℕ` cut by
  `ActivePairCondition` (`ActualSignedGeometry.lean:1269`, `:1264-1267`) — so even a nonempty `Label`
  would not by itself populate it.

--------------------------------------------------------------------------------
## 4. If `Label B N0` were EMPTY, is the headline still provable, or vacuous/false?

**Plainly: the headline stays exactly as strong, is NOT vacuous, and NO inhabitance obligation for a
wave-label type ever reaches it.**

Justification:

1. **The headline asserts existence of concrete analytic objects, not a property of a label-indexed
   object.** `ComparatorSolution.lean:16-20`: `∃ u₀ f, InitialVelocityConditionDecay u₀ ∧
   ForceConditionDecay f ∧ ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)`. No label type,
   no index type, no `Nonempty`/`IsEmpty`/`Fintype` occurs. Emptiness of a label type cannot make this
   statement vacuous — there is nothing to quantify vacuously over. (Even the witnesses are label-free:
   `u₀ = fun _ => 0` at `ComparatorR3Theorem.lean:33`.)
2. **The blow-up content does not use labels.** The only `speed_unbounded` producer in this chain is
   `FinalSlowBase.axis_tendsto` (`FinalSlowBase.lean:372`) → `BaseResidual.baseVelocity_axis_tendsto_atTop`
   (`BaseResidual.lean:104`), driven by the closed formula in `FinalSlowBase.origin`
   (`FinalSlowBase.lean:361-363`) and the single scalar positivity `W.axis.small.j_pos`
   (`FinalSlowBase.lean:378`). Furthermore the correction stages are *required to vanish* near the axis:
   `GermCandidateAssembly.origin_eventually_base` (`GermCandidateAssembly.lean:109-120`) proves the mixed
   diagonal **equals the base** at the origin near `t → 1⁻`, under `AxisZeroOn` hypotheses
   (`:112-113`), and `origin_blowup` (`:146-159`) transports the base blow-up through that equality
   (`:157` `apply (FinalSlowBase.axis_tendsto H v upper B).congr'`). The germ assembly consumes it at
   `GermCandidateAssembly.lean:264` (`haxis := origin_blowup …`) and hands it to
   `CandidateConsequences.mixed_exists_force_with_consequences` (`:266-271`).
3. **All label-indexed obligations in the chain are upper bounds**, hence trivially true when the index is
   empty — see the six empty branches quoted in §3 (`⟨0, le_rfl, 0, …⟩`, `MemClass.zero`).
4. Consequently, **no declaration on the headline chain ever needs, assumes, or proves inhabitance of a
   wave-label type**; the only `Nonempty` inhabitance actually proved nearby is of the *parameter record*
   `Choice` (`CorrectionInitialization.lean:3923`, used at `:3929`), which is what *defines* the index type
   (`:3931`) rather than populating it.

### GAPS / risks to report loudly
* **G1 (fidelity, not soundness).** Because nothing anywhere assumes or proves label inhabitance, every
  theorem on the chain is proved *uniformly in the possibility that the wave index is empty*. So the
  formal artifact does not certify that the paper's wave-correction apparatus contributes anything: if
  `Label B N0` (or merely `activeLabels …`, `CorrectionInitialization.lean:5179`, or `ActivePair B N0`,
  `ActualSignedGeometry.lean:1269`) is in fact empty, all corrections are the zero field and the whole
  `Actual*Bounds`/`*StageControls` layer is decoration. The headline would still be "proved" — from
  `FinalSlowBase`/`BaseResidual` alone.
* **G2 (where a lower bound *should* have been needed).** The one spine obligation that *ought* to force
  the corrections to be present is `MixedCandidateAssembly.StageEstimates.finite_residual`
  (`MixedCandidateAssembly.lean:62-65`): the residual jets of the `J`-prefix must decay at rate
  `gain J - residualLoss m` with `gain_top : Tendsto gain atTop atTop` (`:38`). Zero corrections give a
  `J`-independent residual, so this field should be unsatisfiable in the degenerate world. In the artifact
  it is discharged by `ActualCycleResidualBounds.finite_residual_rates`
  (`GluedStageEstimates.lean:436-440`), fed by the `PhysicalData` realizations
  (`GluedStageEstimates.lean:385-388`, `:690-693`). I could not resolve, by reading alone and with no
  build available, whether that discharge secretly tolerates the empty-index case. This is the single
  highest-value follow-up: if `finite_residual` is provable with an empty index, some definition in the
  residual ledger is degenerate; if it is not, then the artifact silently depends on an unproved
  inhabitance fact — yet §3's grep shows no such fact is ever stated. **Either way it is a defect
  candidate, and it cannot be seen from the six case-split sites, because those are all upper bounds.**
* **G3 (method limit).** No build was possible (no `.olean`, toolchain mismatch), so all of the above is
  source-level: the reference paths were found by an import-respecting identifier graph and then each hop
  was verified against the literal source line quoted here. Elaboration-level dependencies (instance
  resolution, structure-projection defaults, `simp` set usage) are not covered by grep and could add
  further edges, but cannot *remove* the quoted ones.
