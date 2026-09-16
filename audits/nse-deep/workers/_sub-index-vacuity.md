# `ns-index-nonempty` — worker B: the VACUITY SURFACE of an empty wave-label set

Artifact: /home/gsm/.openclaw/workspace/repos/NSE @ f9e8bc5. READ-ONLY. No `lake build` attempted
(0 `.olean`, pinned `leanprover/lean4:v4.34.0-rc2` + mathlib `85e3a25e006c`, box has v4.33.0).
All claims below are source-read + grep, each with `file:line`.

## 0. The one type that matters

All four split sites reduce to nonemptiness of ONE type:

* `CorrectionInitialization.ActualPrimary.Label B N0`
  := `PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N`   — CorrectionInitialization.lean:3931
* `PrimaryGeometryAssembly.Index W N` := `BaseChartJets.CellIndex F.data.h (activeLeft W) (activeRight W) N`
  — PrimaryGeometryAssembly.lean:137-139
* `BaseChartJets.CellIndex h lo hi N` := `{L : PositiveRepresentatives.ActiveLabel (referenceCompact h lo hi) // N ≤ L.val.1}`
  — BaseChartJets.lean:825-827
* `PositiveRepresentatives.ActiveLabel K` := `PrimaryRepresentatives.ActiveLabel (positivePart K)` — PositiveRepresentatives.lean:25
* `PrimaryRepresentatives.ActiveLabel K` := `{L : Label // 1 ≤ L.1 ∧ (K ∩ tsupport (nativeMask L.1 L.2)).Nonempty}`
  — PrimaryRepresentatives.lean:91-92

So a wave label is a `(band, gridcell)` pair with `band ≥ max 1 ((choice B N0).prepared.N)` whose closed native-mask
support meets the positive-time part of the reference compact set. Only a `Countable` instance is registered for it
(PrimaryGeometryAssembly.lean:141); **there is no `Nonempty`/`Inhabited` instance and no `card_pos` lemma anywhere**.

Type identity of the four split sites:
* `ActualInitialMean.Index B N0 = ActualPrimary.Label B N0 × Fin 2` — ActualInitialMean.lean:25
* `ActualSignedUnmaskedBounds.Label B N0 = ActualSignedStageControls.SignedLabel B N0` — ActualSignedUnmaskedBounds.lean:23
* `ActualSignedStageControls.SignedLabel B N0 = ActualPrimary.Label B N0 × Fin 2` — ActualSignedStageControls.lean:35
* (`ActualPrimaryBounds.SignedLabel B N0 = Fin 2 × ActualPrimary.Label B N0` — ActualPrimaryBounds.lean:33)

All are `Fin 2`-products of the same base type ⇒ empty iff `ActualPrimary.Label B N0` is empty. One question, four sites.

## 1. The four explicit split sites — per-site verdict

### Site 1. `ActualInitialMean.covariance_bounds_of_curl` — ActualInitialMean.lean:309, split at :318
Statement (:314-316): `(∀ i j, MeanClass strip 1 ((seed B N0).covariance i j)) ∧ (∀ i j, MeanClass strip (3/2 - kappa) ((seed B N0).covariance i j - tangentCovariance B N0 i j))`.

Empty branch :319-339 does exactly:
* `hl : activeLabels standardRegion B N0 n = ∅` (:320-321, by `isEmptyElim`)
* `hs : (seed B N0).oscillation = 0` (:322-324, `simp [seed, bandSeed, LabelSumBounds.fieldSum, hl]`)
* `ht : ActualPrimaryCovariance.tangentSum B N0 = 0` (:325-327)
* `hz alpha : MeanClass strip alpha 0` (:328-329) and then `class_congr` for both halves (:330-339).

Why it collapses: `seed B N0 = bandSeed (activeLabels ...) primaryPiece (baseError B)` — ActualInitialMean.lean:43-44,
and `bandSeed.oscillation = LabelSumBounds.fieldSum labels (fun l => (pieces l).velocity)` —
CorrectionInitialization.lean:1110, with `fieldSum labels u = fun n p i => ∑ l ∈ labels n, u l n p i` —
LabelSumBounds.lean:499-500. Empty `labels n` ⇒ `oscillation ≡ 0`, `oscillatoryPressure ≡ 0` (:1111),
`errors.excluded ≡ 0` (:1112). `(seed).covariance i j` is `bilinearCovariance oscillation oscillation i j`
(CorrectionInitialization.lean:1114-1118) ⇒ `≡ 0`.

**VERDICT: STILL-TRUE-BUT-EMPTY (zero content).** Both conclusions are genuinely provable; they are statements
`MeanClass strip alpha 0`, i.e. about the identically-zero field. Nothing false; nothing about waves either.
Note the one survivor: `bandSeed.errors` first component is `baseError B`, NOT a label sum
(CorrectionInitialization.lean:1112) — so the base error is untouched by emptiness.

### Site 2. `ActualSignedUnmaskedBounds.raw_jets` — ActualSignedUnmaskedBounds.lean:150, split at :161
### Site 3. `ActualSignedUnmaskedBounds.localized_jets` — ActualSignedUnmaskedBounds.lean:185, split at :196
### Site 4. `ActualSignedStageControls.raw_coefficients_jets` — ActualSignedStageControls.lean:1121, split at :1132

All three have the SAME empty branch, one line each, byte-identical up to whitespace:
`constructor <;> refine ⟨fun l => isEmptyElim l, fun _ => ⟨0, le_rfl, 0, fun l => isEmptyElim l⟩⟩`
(:164, :199, :1135).

The conclusions are conjunctions of `PeriodizedWaveBounds.UniformLocalJets s w alpha K f`, whose definition is
purely universally quantified over the label:
```
structure UniformLocalJets (s) (w : L → ℕ → D → ℝ) (α) (K : L → ℕ → I → Set D) (f : L → ℕ → I → D → E) : Prop where
  smooth : ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ContDiffAt ℝ ∞ (f l n i) x
  bounds : ∀ m, ∃ C, 0 ≤ C ∧ ∃ p, ∀ l n i x, x ∈ s.domain → x ∈ K l n i → ∀ j ≤ m, ‖iteratedFDeriv ...‖ ≤ majorant ...
```
— PeriodizedWaveBounds.lean:254-259. With `L` empty both fields are vacuous quantifications; the `bounds` witness is
literally `C = 0, p = 0`.

**VERDICT (sites 2, 3, 4): FULLY VACUOUS (no content whatsoever).** These are not statements about a zero field —
they are empty ∀-statements. `raw_jets`/`localized_jets`/`raw_coefficients_jets` are the *amplitude and pressure jet
bounds* of the signed correction — i.e. the core "the wave coefficients are controlled at exponent β+1/2, β+1"
estimates. With an empty label type they say nothing, and their entire proof (the `inr` branches at
:165-183, :200-205, :1136-1155, which cite `SignedCopyBounds.uniform_coefficients_jets`, Cramer/normal-floor
positivity, etc.) is unreachable. Their `C = 0` witness is the honest signal: constant 0 for zero waves.

Summary table:

| # | site | enclosing decl | empty-branch content | verdict |
|---|------|----------------|----------------------|---------|
| 1 | ActualInitialMean.lean:318 | `covariance_bounds_of_curl` :309 | `activeLabels = ∅`, `(seed).oscillation = 0`, `tangentSum = 0`, then `MeanClass strip α 0` | STILL-TRUE-BUT-EMPTY (bound on 0) |
| 2 | ActualSignedUnmaskedBounds.lean:161 | `raw_jets` :150 | `isEmptyElim`, `C = 0`, `p = 0` | FULLY VACUOUS (empty ∀) |
| 3 | ActualSignedUnmaskedBounds.lean:196 | `localized_jets` :185 | `isEmptyElim`, `C = 0`, `p = 0` | FULLY VACUOUS (empty ∀) |
| 4 | ActualSignedStageControls.lean:1132 | `raw_coefficients_jets` :1121 | `isEmptyElim`, `C = 0`, `p = 0` | FULLY VACUOUS (empty ∀) |

Neither branch is FALSE at these four sites. The splits are honest defensive plumbing; they hide nothing.

## 2. SILENT trivialisation — no split, statement degenerates

Machine survey (own parse of all 707 `NavierStokes/*.lean`, 34 998 declarations): 36 `theorem`s whose *statement*
mentions a label sum (`activeLabels` / `unsignedLabels` / `fieldSum` / `tangentSum` / `partitionFactor` /
`tangentCovariance` / `seed B N0`) AND contains an estimate/equation keyword AND whose proof body contains **no**
`isEmpty_or_nonempty`. Top by importance:

### (S1) `ActualSignedMeanBinding.requested_cross_tail` — ActualSignedMeanBinding.lean:463-471  ★ FALSE
```
meanBar (actualCross B N0 c u 0 i.succ) n x
  = LocalSignedRequest.requestedStress geometry.patch geometry.coord c u n x i
```
for all `c u`, all `n ≥ (choice B N0).prepared.N + 1`, all `x ∈ geometry.strip.domain`.
LHS is built from `actualCross = symmetricCovariance (actualPrimaryField) (actualSignedField)` (:341-343) and
`actualSignedField = LabelSumBounds.fieldSum (activeLabels standardRegion B N0) ...` (:336-339) ⇒ **LHS ≡ 0** when
labels are empty. So emptiness forces `requestedStress c u n x i = 0` for EVERY state `u`. By
`theta_cross_tail` :487-493 / `axial_cross_tail` :495-501 that is `physicalSigma geometry 2 (u.thetaResidual c) = 0`
for every `u` — plainly false (the theorem is universally quantified over `u`, so pick a state with nonzero theta
residual). Proof route: `requested_cross_factor` :442-459 then `partitionFactor_eq_one` :471. **This is the closing
identity of the gain mechanism and it becomes FALSE under emptiness, with no split anywhere.**
Downstream, same fate, still no split: `requested_cross_tail_jets` :503, `cycle_requested_cross_tail` :590,
`fixed_requested_cross_tail` :605, `literal_requested_cross_tail` :621, `family_requested_cross_tail` :655,
`family_defects_all_exponents` :672.

### (S2) `ActualPrimaryCovariance.partitionFactor_eq_one` — ActualPrimaryCovariance.lean:508-513  ★ FALSE (0 = 1)
`partitionFactor B N0 n x = ∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2` (:381-382)
⇒ `= 0` when the label type is empty (`unsignedLabels` is a `Finset.preimage` of the label type, :216-220).
The theorem asserts `= 1` for `x ∈ (nativeStrip nominal standardRegion).domain` and
`physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N`. The `= 1` half comes from
`PartitionedCovariance.physical_mask_tail_sum_sq` (PartitionedCovariance.lean:766-785), which is **unconditional**
(hypotheses: only `0 < q` and `q ≤ Q N`), and the label-side bridge is `partitionFactor_eq_tail` :464-506, which
manufactures an index from a nonvanishing mask via `PrimaryGeometryAssembly.physicalMask_has_index` :484.
No `Nonempty` variable is in scope in that file (only `variable {B N0 : ℕ}`, ActualPrimaryCovariance.lean:92).
**Cleanest contradiction: 0 = 1 needs no auxiliary nonvanishing fact.**
Same for `partitionFactor_eq_one_sub_missing` (used at :745, :484 of ActualSignedMeanBinding).

### (S3) `ActualPrimaryCovariance.mean_tangentCovariance_eq_leading` — :614-619  ★ FALSE unless `leadingStress ≡ 0`
`meanBar (tangentCovariance B N0 0 i.succ) n x = leadingStress i n x` for `n ≥ N+1`, `x ∈ strip`.
`tangentSum B N0 = fun n z i => ∑ l ∈ activeLabels ..., (piece ...).tangentVelocity n z i` (:539-541),
`tangentCovariance = bilinearCovariance tangentSum tangentSum` (:543-545) ⇒ LHS ≡ 0 ⇒ forces `leadingStress ≡ 0`
on the strip tail. Jet version `mean_tangentCovariance_jets` :621-628 likewise.

### (S4) `ActualPrimaryCovariance.averagedDefect_meanClass` — :847-851 (with `averagedDefect_zero_tail` :748-752)
`averagedDefect B N0 i := meanBar (tangentCovariance B N0 0 i.succ) - leadingStress i` (:737-738).
`averagedDefect_zero_tail` proves it vanishes identically for `n ≥ N+1`; `averagedDefect_meanClass` then upgrades to
**every exponent `beta`** via `memClass_of_finite_bands`. This "arbitrary exponent for free" is *entirely* powered by
tail vanishing. Under emptiness `averagedDefect = -leadingStress i`, so the theorem asserts `-leadingStress` lies in
every mean class and vanishes on the tail — **FALSE unless `leadingStress ≡ 0`**. Consumers, no split:
`averagedDefect_derivative_meanClass` :856, `averagedDefect_radialDiv_meanClass` :861,
`tangent_virtual_bar_meanClass` :893-922.

### (S5) `ActualPrimaryCovariance.tangent_virtual_bar_meanClass` :893 → `ActualInitialMean.matched_fluxes` :583
Under emptiness `tangentCovariance ≡ 0` and `(seed).covariance ≡ 0`, so
`MeanClass ... 2 (meanBar 0 - meanBar (commonContext B).virtualTheta)` = a claim about the BASE virtual stress alone.
The wave content is fully displaced onto `virtualTheta`/`virtualAxial`, which are not label sums
(`meanBar_virtualTheta` :882, `meanBar_virtualAxial` :886). Same in
`ActualInitialMean.matched_fluxes_of_covariance` :368-394 and `matched_fluxes` :583-591.
**Verdict: silently re-targeted — uninformative about waves, and false-or-implausibly-strong about the base.**

### (S6) The whole ActualInitialMean initialization tower — all about `seed B N0`, no split
`covariance_bounds` :554-558 (exported, unconditional) → `primary_mean_data` :561 → `primary_bounds` :565-581 →
`initial_bounds_of_primaryData` :503-532 (`CumulativeBounds` / `MeanResidualBounds (1/5)` / `DefectBounds` /
`ZeroMassesOn`) → `temporal_bounds` :593-610 → `rank_bounds` :612. Also `seed_covariance_smooth` :224,
`tangent_covariance_smooth` :242, `primaryData_of_covariance` :434-475, `curl_amplitude_uniform` :536-552.
Every one of these is a bound on a field whose oscillatory part is `fieldSum activeLabels ...`.
**Verdict: STILL-TRUE-BUT-EMPTY en bloc — the entire quantitative initialization becomes a set of estimates on 0.**

### (S7) generic library layer — safe but empty
`LabelSumBounds.supported_covariance_fieldSum_eq` :563, `supported_covariance_sum_mem` :599,
`harmonic_covariance_sum_mem` :624, `SignedFamily.remainder_sum_mem` :1004,
`harmonic_covariance_increment_sum_mem` :1064; `CorrectionInitialization.covariance_bounds_of_blocks` :2844,
`covariance_bounds` :2897; `CorrectionStep.assembledSigned_stateTensor_mem` :3214,
`assembledCovarianceIncrement_mem` :7491. These are generic in the index type `ι`, so with `ι` empty they are
STILL-TRUE-BUT-EMPTY (bounds on 0). No falsity here.

## 3. Crisp answers

**Q: if the tower is empty, which wave estimates carry no information?**
Everything downstream of `activeLabels`/`unsignedLabels`/`fieldSum`/`tangentSum`:
* the amplitude/pressure/potential jet bounds (`raw_jets` :150, `localized_jets` :185, `potential_jets` :207,
  `raw_coefficients_jets` :1121, `actual_raw_coefficients_jets` ActualSignedStageControls.lean:1159) — **vacuous**;
* the seed covariance class bounds and the whole initialization tower (S6) — **estimates on 0**;
* the generic label-sum library estimates (S7) — **bounds on 0**.
None of the artifact's wave estimates would carry ANY information about a wave.

**Q: does anything become FALSE?**
**YES — three independent falsities, none of them protected by a split:**
1. `ActualPrimaryCovariance.partitionFactor_eq_one` :508 becomes `0 = 1` (the RHS `= 1` comes from the
   label-free `PartitionedCovariance.physical_mask_tail_sum_sq`, PartitionedCovariance.lean:766).
2. `ActualSignedMeanBinding.requested_cross_tail` :463 becomes `0 = requestedStress c u n x i` for **every** state.
3. `ActualPrimaryCovariance.mean_tangentCovariance_eq_leading` :614 becomes `0 = leadingStress i n x`, and
   `averagedDefect_meanClass` :847 becomes an all-exponent bound on `-leadingStress`.

Both (1) and (2) fire on the SAME hypothesis pair that the artifact already discharges unconditionally:
* a strip point: `ActualSignedMeanBinding.actual_strip_nonempty` :54-67, witness
  `((G.patch.a + G.patch.b)/2, ((1,0),(0,0)))`, hypothesis-free, on `ActualInitialization.geometry.strip.domain`;
  bridged by `ActualInitialization.geometry_strip : geometry.strip = strip := rfl` :665 and
  `ActualInitialization.strip := BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion` :383
  — i.e. *exactly* the domain in `partitionFactor_eq_one`'s hypothesis, by `rfl`;
* a band: take `n := (choice B N0).prepared.N + 1`, then
  `ActualPrimaryCovariance.physicalScale_tail` :527-535 supplies `physicalScale n x ≤ Q ((choice B N0).prepared.N)`.

**Therefore emptiness is not merely uninformative — it is REFUTED by the artifact's own unconditional theorems,
for every `B N0`.** W25's five-line argument is SOUND; I found no gap in it. I also found two strictly better routes:

* **Shortest route (no 0 = 1 needed):** `PrimaryGeometryAssembly.physicalMask_has_index`
  (PrimaryGeometryAssembly.lean:198-209) *already* concludes `∃ i : Index W N, label W i = L` from a nonvanishing
  physical mask at a positive-time strip-admissible point. This is a direct `Nonempty (Label B N0)` producer; the
  nonvanishing mask itself follows from `physical_mask_tail_sum_sq = 1` (PartitionedCovariance.lean:766). This is the
  natural place to state `ns_index_nonempty`, and it needs no reductio.
* **Strongest route:** `requested_cross_tail` :463 is false for every nonzero-residual state, so the entire signed
  gain mechanism, not just one normalisation, is inconsistent with emptiness.

**Residual worry (the honest one):** the refutation is a THEOREM the artifact never states. Grep confirms **zero**
declarations assert `Nonempty (ActualPrimary.Label B N0)`, `0 < (unsignedLabels ...).card`, or `(activeLabels ...).Nonempty`;
the only instance registered on the label type is `PrimaryGeometryAssembly.indexCountable` :141. So a reader cannot
see that the four `isEmpty` branches are dead code, and the four empty branches (which prove `C = 0` bounds and
`MeanClass strip α 0`) look like real estimates on paper. The correct fix is one lemma
`Nonempty (ActualPrimary.Label B N0)` (five lines, from :508 + :54 + :527, or two lines from
PrimaryGeometryAssembly.lean:198) plus deletion of the four `isEmpty` branches — a documentation/rigour defect, not a
soundness defect.

## 4. Addendum — corroboration by an independent grep worker (same commit, disjoint method)

Counts in `NavierStokes/` (hits/files): `activeLabels` 172/20, `unsignedLabels` 14/2, `fieldSum` 235/22
(`LabelSumBounds.fieldSum` 122/21), `tangentSum` 12/3, `partitionFactor` 18/2, `isEmpty_or_nonempty` **4/3**
— i.e. the four sites above and no others. The identifier `signedLabels` does not exist (all 14 hits are substrings
of `unsignedLabels`).

Independent confirmation of §0: **no declaration anywhere asserts nonemptiness** — 0 hits for
`Nonempty (Label/Index/SignedLabel/ActiveLabel/CellIndex)`, `Finset.Nonempty` on a label Finset, `Finset.card_pos`,
`Inhabited`; `.card` is never applied to `activeLabels`. The only existence lemmas are *conditional* on a nonvanishing
field (PrimaryRepresentatives.lean:159, :542; PositiveRepresentatives.lean:61; InitialPhysicalData.lean:535, :550,
:572, :2398, :2408) and are vacuous at 0.

Extra silent-trivialisation consumers found by that worker (verified present):
* `ActualCandidateAssembly.selected_candidate` — ActualCandidateAssembly.lean:1183 (`ProblemStatement.candidateStatement`),
  via `selected_witness` :1177 and the candidate assembly at :1153; the candidate's oscillation *is* the label sum
  (ActualCandidateAssembly.lean:261, :269). **This is the top-level consumer**: an empty tower would make the exhibited
  blow-up candidate a base-only field.
* `ActualInitialMean.lean:647` `initial_cumulative_bounds`, :651 `initial_mean_bounds`, :655 `initial_debt_bounds`,
  :659 `initial_zeroMasses`, :664 `initial_mean_smooth` — the exported face of (S6), all projections of
  `initial_bounds` :640.
* `ActualCyclePreservation.lean:179`, :184, :894, :904, :914 (labels pinned at :160);
  `ActualWaveRegularity.lean:792`, :808; `ActualParticularMeanGain.lean:138`.

Two residual gaps that the reductio does NOT close, and that a stated lemma should record:
* the contradiction only fires for `n ≥ (choice B N0).prepared.N + 1`; for `n ≤ prepared.N` the artifact has only
  `partitionFactor_eq_one_sub_missing` (ActualPrimaryCovariance.lean around :730), i.e. `= 1 - missingWeight`, which
  can legitimately be 0 — so the argument gives nonemptiness of the *type* (enough, since the type does not depend on
  `n`), but says nothing about `unsignedLabels B N0 n` being nonempty at low bands;
* there is no lower bound on `(activeLabels ...).card` anywhere, so no statement of the form "at least one active label
  per band" exists.
