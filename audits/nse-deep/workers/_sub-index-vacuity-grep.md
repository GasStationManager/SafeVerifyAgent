# Index-vacuity grep survey — NSE repo @ f9e8bc5 (READ-ONLY, no build)

Scope: `NavierStokes/` (816 .lean files). No file was modified; no `lake build` was run.

## 1. Pattern counts (`grep -rn ... NavierStokes/ | wc -l`)

| pattern | hits | files |
|---|---|---|
| `activeLabels` | 172 | 20 |
| `unsignedLabels` | 14 | 2 |
| `signedLabels` | 14 | 2 |
| `fieldSum` | 235 | 22 |
| `tangentSum` | 12 | 3 |
| `partitionFactor` | 18 | 2 |
| `LabelSumBounds.fieldSum` | 122 | 21 |
| `isEmpty_or_nonempty` | 4 | 3 |

Caveat: every `signedLabels` hit is a substring of `unsignedLabels` (all 14 hits are in
`NavierStokes/ActualPrimaryCovariance.lean` 216-500 and `NavierStokes/ActualSignedMeanBinding.lean:284`).
There is **no identifier `signedLabels`** in the repo.

Top `activeLabels` files: InitialPhysicalData 26, ActualPrimaryCovariance 25, ActualSignedCurrentSupport 22,
ActualSignedMeanBinding 15, ActualCyclePreservation 12, ActualSignedPhysicalCoherence 10,
ActualInitialCoherence 10, ActualInitialMeanEquation 9, ActualInitialMean 9,
CorrectionInitialization(+NoOptions) 7+7, ActualCycleParameters 4, ActualInitialExcluded 3,
ActualCycleCoherence 3, InitialHarmonicContinuation 3, GluedStageEstimates 2, ActualCandidateAssembly 2,
ActualCandidateConstruction 1, ActualInitialization 1, ActualMeanPhysicalData 1.

The 4 `isEmpty_or_nonempty` sites (the ONLY explicit emptiness case splits in the repo):
- `NavierStokes/ActualInitialMean.lean:318`  `rcases isEmpty_or_nonempty (Index B N0)`
- `NavierStokes/ActualSignedUnmaskedBounds.lean:161`  `cases isEmpty_or_nonempty (Label B N0)`
- `NavierStokes/ActualSignedUnmaskedBounds.lean:196`  `cases isEmpty_or_nonempty (Label B N0)`
- `NavierStokes/ActualSignedStageControls.lean:1132`  `cases isEmpty_or_nonempty (SignedLabel B N0)`
In all four the empty branch is discharged by `isEmptyElim` / constant `0` (e.g.
ActualSignedUnmaskedBounds.lean:164, ActualSignedStageControls.lean:1135), i.e. the split exists only
because the downstream library lemma (`SignedCopyBounds.uniform_*`, `UniformPrimaryWeights.*`)
carries a `[Nonempty ι]` instance argument. The repo therefore *knows* the label type may be empty
and never supplies a nonemptiness witness at those points.

## 2. Key definitions: where the wave field is a Finset.sum over labels

### 2a. The generic sum operator
`NavierStokes/LabelSumBounds.lean:499-500`
```lean
noncomputable def fieldSum (labels : ℕ → Finset ι) (u : ι → Oscillation D) : Oscillation D :=
  fun n p i => ∑ l ∈ labels n, u l n p i
```
`labels n = ∅` ⟹ `fieldSum labels u = 0` (by `Finset.sum_empty`), for every `u`.

### 2b. The state seed built from it
`NavierStokes/CorrectionInitialization.lean:1106-1112` (comment at 1104-1105 explicitly says
"The active labels may depend on the chart band. No bound on their total cardinality is inserted…")
```lean
noncomputable def bandSeed (labels : ℕ → Finset ι) (pieces : ι → PrimaryPiece (D × ℝ))
    (baseError : Oscillation D) : State D where
  mean := ⟨0, 0, 0⟩
  pressure := 0
  oscillation := LabelSumBounds.fieldSum labels (fun l => (pieces l).velocity)
  oscillatoryPressure := fun n p => ∑ l ∈ labels n, (pieces l).pressure n p
  errors := ⟨baseError, LabelSumBounds.fieldSum labels (fun l => (pieces l).excluded), 0⟩
```
and the non-band variant `seed` at `CorrectionInitialization.lean:1096-1102`
(`oscillation := ∑ l ∈ labels, (pieces l).velocity`).
Mirrored verbatim in `CorrectionInitializationNoOptions.lean:1107` / `:1117`.

### 2c. The concrete label Finsets
`NavierStokes/CorrectionInitialization.lean:5179-5183`
```lean
noncomputable def activeLabels (U : LocalSignedRequest.SlowRegion (2 * h)) (B N0 n : ℕ) :
    Finset (Label B N0 × Fin 2) := by
  classical
  exact ((CommonWindow.labels (CoordinateAlgebra.D h) (BaseContextAssembly.geometryBound nominal U) n).preimage
    (PrimaryGeometryAssembly.label nominal) (PrimaryGeometryAssembly.label_injective nominal).injOn).product Finset.univ
```
`NavierStokes/ActualPrimaryCovariance.lean:216-220`
```lean
noncomputable def unsignedLabels (B N0 n : ℕ) : Finset (Label B N0) := by
  classical
  exact (CorrectionInitialization.CommonWindow.labels (CoordinateAlgebra.D h)
    (BaseContextAssembly.geometryBound nominal standardRegion) n).preimage
      (PrimaryGeometryAssembly.label nominal) (PrimaryGeometryAssembly.label_injective nominal).injOn
```
with `activeLabels standardRegion B N0 n = (unsignedLabels B N0 n).product Finset.univ`
(`ActualPrimaryCovariance.lean:222-223`, by `rfl`).
Both are **preimage** Finsets, so emptiness is a priori possible: it needs a
`CommonWindow.labels` element that pulls back along `PrimaryGeometryAssembly.label`.

### 2d. Label TYPE chain (all subtypes; nothing constructs an element unconditionally)
- `CorrectionInitialization.lean:3931` `abbrev ActualPrimary.Label (B N0) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N`
- `PrimaryGeometryAssembly.lean:137-139` `abbrev Index (N) := BaseChartJets.CellIndex F.data.h (activeLeft W) (activeRight W) N`
- `BaseChartJets.lean:825-827` `def CellIndex (h lo hi) (N) := {L : PositiveRepresentatives.ActiveLabel (PrimaryRepresentatives.referenceCompact h lo hi) // N ≤ L.val.1}`
- `PositiveRepresentatives.lean:25` `def ActiveLabel (K) := PrimaryRepresentatives.ActiveLabel (positivePart K)`
- `PrimaryRepresentatives.lean:91-92` `def ActiveLabel (K : Set Slow) := {L : Label // 1 ≤ L.1 ∧ (K ∩ tsupport (nativeMask L.1 L.2)).Nonempty}`
- derived: `ActualPrimaryBounds.lean:33` `SignedLabel := Fin 2 × ActualPrimary.Label`,
  `ActualInitialization.lean:27` `Index (B N0) := ActualPrimary.Label B N0 × Fin 2`,
  `ActualSignedStageControls.lean:35` `SignedLabel := ActualPrimary.Label × Fin 2`.
So `Index/Label/SignedLabel` are all empty as soon as `ActualPrimary.Label B N0` is.

### 2e. Other label sums
- `ActualPrimaryCovariance.lean:381-382` `partitionFactor B N0 n x = ∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2`
- `ActualPrimaryCovariance.lean:539-541` `tangentSum B N0 = fun n z i => ∑ l ∈ activeLabels standardRegion B N0 n, (piece standardRegion l.2 l.1).tangentVelocity n z i`
- `ActualSignedMeanBinding.lean:332-339` `actualPrimaryField` / `actualSignedField` = `LabelSumBounds.fieldSum (activeLabels standardRegion B N0) …`
- `ActualCyclePreservation.lean:167-169` `primaryField = fieldSum (ActualPrimary.activeLabels standardRegion B N0) …`
- `CorrectionStep.lean:5033/5039/5057/5063` `particularVelocity`, `particularGaussian`, `signedVelocity`, `signedGaussian` = `fieldSum v.labels …`; `:5037/5061` the pressures as raw `∑ l ∈ v.labels n`
- `ActualInitialExcluded.lean:1153` `initialGaussian` also via `fieldSum`.

## 3. Top-level theorems that degenerate to statements about the identically-zero field
(no `isEmpty_or_nonempty` in any of these proofs; all `activeLabels`/`v.labels`-indexed)

1. `NavierStokes/ActualCandidateAssembly.lean:1183` **`selected_candidate : ProblemStatement.candidateStatement`**
   The terminal producer of the blow-up candidate (feeds `Comparator.navier_stokes_breakdown_R3`).
   Its state's oscillation is the label sum: `ActualCandidateAssembly.lean:261-267`
   (`(cycle B N0 0).state.oscillation n x i = ∑ l ∈ activeLabels standardRegion B N0 n, (piece …).velocity n x i`)
   and `:269-272` for the pressure. Labels empty ⟹ the "candidate" has oscillation ≡ 0 and
   pressure ≡ 0; every wave estimate in the chain is an estimate on 0. Degenerates without any split.
2. `NavierStokes/ActualCandidateAssembly.lean:1153` **`witness (B N0) (hN …) : Witness B N0 hN`** and
   `:1177` `selected_witness`. Same object, one level down: bundles all stage bounds for the
   label-sum state; each component becomes a bound on the zero field.
3. `NavierStokes/ActualSignedMeanBinding.lean:655` **`family_requested_cross_tail`**
   `meanBar (SignedMeanGain.crossTensor f a 0 i.succ) n x = requestedStress … n x i` where
   `crossTensor` is the symmetric covariance of two `fieldSum` fields with
   `hlabels : a.labels = activeLabels standardRegion B N0`. Labels empty ⟹ LHS ≡ 0, so the theorem
   only asserts `requestedStress … = 0`: the cancellation content vanishes.
4. `NavierStokes/ActualSignedMeanBinding.lean:621` **`literal_requested_cross_tail`**
   (and `:590` `cycle_requested_cross_tail`, `:605` `fixed_requested_cross_tail`). Statements are
   literally `meanBar (symmetricCovariance (fieldSum state.coefficients.labels …) (fieldSum … )) = requestedStress`.
   With `hlabels : state.coefficients.labels = activeLabels standardRegion B N0` both `fieldSum`s are 0.
5. `NavierStokes/ActualSignedMeanBinding.lean:672` **`family_defects_all_exponents`**
   "∀ γ, …" all-exponent class bounds for the defects of the signed family whose labels are
   `activeLabels standardRegion B N0`. Empty labels ⟹ every field involved is 0 and all-exponent
   membership is the trivial `MemClass … 0`.
6. `NavierStokes/ActualInitialMean.lean:647` **`initial_mean_bounds : MeanResidualBounds strip (1/5) … (initialized B N0)`**
   and `:651` `initial_debt_bounds`, `:655` `initial_zeroMasses`, `:659` `initial_mean_smooth`,
   `:664` `initial_mean_support`. `initialized B N0` is `GaugeInitialization.initializedBands …
   (ActualPrimary.activeLabels standardRegion B N0) primaryPiece (baseError B)`
   (`ActualInitialMean.lean:60-62`, `:670` `initialized_formula`), whose oscillation is `bandSeed`'s
   `fieldSum`. Labels empty ⟹ the oscillatory part is 0 and only `baseError` survives.
   (NB the *sibling* lemma `covariance_bounds_of_curl` at `:309` DOES split at `:318` — it is the
   exception, not the rule.)
7. `NavierStokes/ActualCyclePreservation.lean:179` **`primaryField_smooth`** and `:184`
   `primaryField_periodic` (with `:171` `primaryField_eq : primaryField = tangentSum`).
   Regularity/periodicity asserted for `fieldSum (activeLabels …)`; on empty labels this is the
   smoothness and periodicity of the zero field.
8. `NavierStokes/ActualCyclePreservation.lean:894` **`state_afterTemporal_debt`**, `:904`
   `state_wave_transport`, `:914` `state_covariance_moving` — the per-cycle preservation package for
   `state B N0 j`, whose coefficient labels are pinned to `activeLabels` by
   `ActualCyclePreservation.lean:160` (`(state B N0 n).coefficients.labels = ActualPrimary.activeLabels …`).
   Every wave-transport / covariance-increment claim becomes a claim about 0.
9. (bonus) `NavierStokes/ActualInitialExcluded.lean:1366` `initializedErrors_all_gains` and `:1371`
   `initializedErrors_vector_all_gains`: all-exponent unweighted class for `(initialized B N0).errors.total`,
   again a `fieldSum`-based object (`initialGaussian` at `:1153`).
10. (bonus) `NavierStokes/ActualWaveRegularity.lean:792` `SignedData.regular` and `:808` `next_regular`:
   smoothness/periodicity/support of `p.signedVelocity v c u = fieldSum v.labels …`
   (`CorrectionStep.lean:5057`). Vacuous-tolerant, no split.
11. (bonus) `NavierStokes/ActualParticularMeanGain.lean:138` `postParticular_gain` and `:104`
   `covariance_class`: gain estimates for `particularVelocity` = `fieldSum v.labels …`.

## 4. THE CRUCIAL QUESTION: does anything assert the label type / Finset is nonempty?

### 4a. Direct assertions — NONE
- `grep -rn "Nonempty (Label\|Nonempty (Index\|Nonempty (SignedLabel\|Nonempty (ActiveLabel\|Nonempty (CellIndex\|Nonempty (ActualPrimary.Label\|Nonempty (PrimaryGeometryAssembly.Index\|Nonempty (UnsignedLabel" NavierStokes/` → **0 hits**.
- `grep -rn ".*activeLabels.*Nonempty" / "unsignedLabels.*Nonempty"` (both orders) → **0 hits**.
- `grep -rn "Finset.Nonempty" NavierStokes/` → **0 hits**.
- `grep -rn "card_pos" NavierStokes/` → **0 hits**. `grep -rn "Inhabited" NavierStokes/` → **0 hits**.
- `.card` appears 96× but **never** applied to `activeLabels` / `unsignedLabels`
  (`grep -rn "activeLabels\|unsignedLabels\|signedLabels" NavierStokes/ | grep card` → 0 hits).
  Compare the design comment at `CorrectionInitialization.lean:1104-1105`: no cardinality bound
  (upper *or* lower) is inserted anywhere.
- The only `Nonempty` facts about *some* index type are:
  * `NavierStokes/ActualParticularPhysicalData.lean:615` `instance sourceIndex_nonempty (N) : Nonempty (SourceIndex N) := ⟨(0, (⟨(4,0,false), le_rfl⟩, ⟨0, by simp⟩))⟩`
    where `SourceIndex N := Copy × PhysicalWaveSum.WaveIndex N` (`:613`). This is a *raw*
    band-label index, NOT `Label/Index/SignedLabel B N0`; and the field built from it is gated by
    `if hL : I.2.1 ∈ F.active then … else 0` (`:621-624`), so the supplied witness contributes 0
    unless it lies in `F.active` — the instance says nothing about `F.active` being inhabited.
  * `[Nonempty Label]` / `[Nonempty ι]` / `[Nonempty Λ]` / `[Nonempty L]` are *hypotheses* on
    generic type variables: `ParticularCopyBounds.lean:453,480` (`variable {Label : Type}` at `:359`),
    `ActualGaussianCoverage.lean:730,801,1251` (`variable {Label P : Type}` at `:71`),
    `ActualSignedControl.lean:379,444,571,683`, `UniformPrimaryWeights.lean:84,87,154,238,255,327,393,436,453,596,625,675,705`,
    `SignedCopyBounds.lean:697,756`, `CorrectionInitialization.lean:2720`,
    `ActualParticularPhysicalData.lean:252`, `LocalizedMeanInteraction.lean:298`.
    These are exactly the instances that force the 4 `isEmpty_or_nonempty` splits in §1.
  * `ActualParticularStageControls.lean:941-942` and `:1214-1215` do `by_cases hne : Nonempty (ActivePair B N0)`
    — again a case split, i.e. the opposite of an assertion.
  * All other 200-ish `Nonempty` hits are about witness/solution structures
    (`Nonempty (NominalProfile.Witness F)` `MatchingDebtBounds.lean:930`, `choice_nonempty`
    `CorrectionInitialization.lean:3923`, `Nonempty (Prepared …)` `PrimaryGeometryAssembly.lean:394`,
    `OneSidedExtension`, `GlobalFiniteEnergySolution`, …), not about label sets.

### 4b. CONDITIONAL existence only (`∃ (a label)` gated on a nonzero mask/field)
- `PrimaryRepresentatives.lean:159-162` `physicalMask_active … (hm : mask D L q x ≠ 0) : ∃ A : ActiveLabel K, A.val = L`
- `PrimaryRepresentatives.lean:542-547` `physicalMask_has_representative` (same, packaged)
- `PositiveRepresentatives.lean:61-66` `physicalMask_has_positive_representative` (same, positive time)
- `PositiveRepresentatives.lean:66`, `PrimaryRepresentatives.lean:162/547` are the only `∃ … : ActiveLabel …` in the repo.
- `InitialPhysicalData.lean:535-540` `sourceFamily_nonzero`, `:550-553` `potential_amplitude_data`,
  `:572-575` `pressure_amplitude_data` — `∃ l : SignedLabel B N0, …` but each needs a
  `≠ 0` hypothesis on the assembled family.
- `InitialPhysicalData.lean:2398-2402` `potential_periodized_index`, `:2408-2412`
  `pressure_periodized_index` — `∃ l : ActualPrimary.Label B N0 × Fin 2, primaryIndex l = I`,
  again from `… periodized … I w ≠ 0`.
All of these are **vacuously satisfiable** if the field is identically zero: they are
"if something is nonzero then a label exists", never "a label exists".
Also note `BaseChartJets.CellIndex` adds `N ≤ L.val.1`, and `N = (choice B N0).prepared.N` is
opaque, so even a produced `ActiveLabel` need not land in `Index W N`.

### 4c. HOWEVER: non-vacuity IS derivable from two existing theorems (no new axiom needed)
This is the one real counterweight to the vacuity hypothesis. It is *not* stated as a declaration,
but it follows from declarations that exist:

1. `NavierStokes/ActualSignedMeanBinding.lean:54-67`
   `theorem actual_strip_nonempty : ActualInitialization.geometry.strip.domain.Nonempty`
   with the *explicit witness* `((G.patch.a + G.patch.b) / 2, ((1, 0), (0, 0)))` (line 56).
   And `ActualInitialization.lean:665` `geometry_strip : geometry.strip = strip := rfl`,
   `ActualInitialization.lean:383-384` `strip := BaseContextAssembly.nativeStrip nominal standardRegion`
   — i.e. exactly the domain used by the covariance lemmas (compare
   `ActualSignedMeanBinding.lean:110-113`, which feeds `hx : x ∈ geometry.strip.domain`
   straight into `BaseContextAssembly.nativeStrip_time nominal standardRegion`).
2. `NavierStokes/ActualPrimaryCovariance.lean:508-513`
   ```lean
   theorem partitionFactor_eq_one (B N0 n : ℕ) {x : Point}
       (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
       (hq : physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N) :
       partitionFactor B N0 n x = 1
   ```
   whose proof runs through `partitionFactor_eq_tail` (`:464-506`, a
   `finsum_eq_sum_of_support_subset` onto `(unsignedLabels B N0 n).image (relativeLabel B N0)`)
   and `PartitionedCovariance.physical_mask_tail_sum_sq` (`:766-768`, value **= 1**).
3. The scale hypothesis is satisfiable on that same domain:
   `ActualPrimaryCovariance.lean:527-529` `physicalScale_tail (hn : (choice B N0).prepared.N + 1 ≤ n)
   (hx : x ∈ (nativeStrip nominal standardRegion).domain) : physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N`.

Chaining 1+3+2: for every `B N0` and every `n ≥ (choice B N0).prepared.N + 1`,
`∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x₀ L) ^ 2 = 1`
at the explicit point `x₀`. A sum over `∅` is `0 ≠ 1`, therefore
`unsignedLabels B N0 n ≠ ∅`, therefore `activeLabels standardRegion B N0 n ≠ ∅`
(`ActualPrimaryCovariance.lean:222-223`) and `Label/Index/SignedLabel B N0` is inhabited.

Consequences / caveats for the audit:
- The blanket claim "all wave-label types could be empty, so the whole surface is vacuous"
  is **refutable inside the repo** for band indices `n > prepared.N`, using only
  `actual_strip_nonempty` + `partitionFactor_eq_one` + `physicalScale_tail`.
- What is still genuinely absent: (a) any *declaration* stating nonemptiness or positive
  cardinality of a label type/Finset; (b) any statement for the *low* bands `n ≤ prepared.N`
  (there `partitionFactor` is only `1 - missingWeight …`, `ActualPrimaryCovariance.lean:730-735`,
  which may be 0); (c) any lower bound on `#activeLabels`. So the §3 theorems remain formally
  vacuity-tolerant as written; the vacuity is excluded only indirectly, and only via the
  partition-of-unity route.
