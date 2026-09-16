# Worker C — in-cone MATERIAL dependence on wave-label inhabitance (`ns-index-nonempty`)

Repo `/home/gsm/.openclaw/workspace/repos/NSE` @ f9e8bc5. READ-ONLY. No build attempted
(0 `.olean`, pinned `leanprover/lean4:v4.34.0-rc2` + mathlib 85e3a25e006c vs box Mathlib v4.33.0).
All claims are source claims with file:line.

## 0. Cone-ledger schema (learned, not guessed)

`audits/nse-deep/CONE.csv`, 52,516 rows, header
`file,line,kind,name,in_cone,in_import_closure` (`head -3` of the file).
Semantics from the audit's own notes: `in_cone` = "there is a named reference chain from the headline
theorems" (`FINDINGS.md:238`, `:220`, instrument `audits/cone.py`, mark 4 at `FINDINGS.md:614-634`);
`in_import_closure` = the declaration's FILE is inside the import closure of the headline modules
(`FINDINGS.md:391-420`). Counts: `in_cone` True 38,369 / False 14,147; `in_import_closure`
True 48,900 / False 3,616. `in_cone=True` is an OVER-approximation (last-component/contiguous-run
token matching, `FINDINGS.md:475-476`, `:507-514`), so `in_cone=False` is the strong signal.

## 1. The label type, precisely

* `CorrectionInitialization.lean:3931` `abbrev Label (B N0) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N`
* `PrimaryGeometryAssembly.lean:137` `abbrev Index (N) := BaseChartJets.CellIndex F.data.h (activeLeft W) (activeRight W) N`
* `BaseChartJets.lean:825-827` `def CellIndex h lo hi N := {L : PositiveRepresentatives.ActiveLabel (referenceCompact h lo hi) // N ≤ L.val.1}`
* `PositiveRepresentatives.lean:25` `ActiveLabel K := PrimaryRepresentatives.ActiveLabel (positivePart K)`
* `PrimaryRepresentatives.lean:91-92` `ActiveLabel K := {L : Label // 1 ≤ L.1 ∧ (K ∩ tsupport (nativeMask L.1 L.2)).Nonempty}`

So inhabitance = "some unsigned label of band `≥ N` (and `≥ 1`) has mask support meeting the
positive-time part of the reference compact set". Everything else is a wrapper:
`ActualInitialization.lean:27` / `ActualInitialMean.lean:25` `Index B N0 = ActualPrimary.Label B N0 × Fin 2`;
`ActualSignedStageControls.lean:35` `SignedLabel B N0 = ActualPrimary.Label B N0 × Fin 2`;
`ActualSignedUnmaskedBounds.lean:23` `Label B N0 = ActualSignedStageControls.SignedLabel B N0`;
`ActualParticularStageControls.lean:35` `Label B N0 = Fin 2 × ActualPrimary.Label B N0`;
`ActualParticularStageControls.lean:445` `ActivePair B N0 = {i : Label B N0 × ℕ // Active i.1 i.2}` with
`:442-443` `Active l n := 1 ≤ n ∧ BaseChartJets.cellBand l.2 ∈ CommonWindow.levels n`.

## 2. WHY the case splits exist: the enumeration hypothesis (mechanism, not decoration)

`UniformPrimaryWeights.lean:84` `def enumeration (ι) [Countable ι] [Nonempty ι] : ℕ → ℕ × ι` and
`:87 enumeration_surjective` are the *only* reason a `[Nonempty _]` binder exists in the wave layer.
Every "uniform over labels" lemma pulls along that surjection:
`SignedCopyBounds.lean:697 uniform_smul [Countable L] [Nonempty L]` (uses it at `:702-705`),
`ParticularCopyBounds.lean:453 UniformModalControl.localJets [Countable Label] [Nonempty Label]`
(`:460-462`), `ActualSignedControl.lean:379 uniform_band_smul [Countable Λ] [Nonempty Λ]` (`:385-386`),
`CorrectionInitialization.lean:2720-2725`, `UniformPrimaryWeights.lean:154-175,238-299,393-400`.
`ActualSignedGeometry.lean:1275` `variable [Countable Λ] [Nonempty (ActivePair H v a reference chart)]`
serves the same purpose for the active-pair enumeration `:1277 activeEnumeration`, `:1280 …_surjective`.

The concrete instantiation sites therefore need `[Nonempty <concrete label type>]`, and each of them
obtains it from a CASE HYPOTHESIS, never from a proof:

| site | enclosing decl (name, `theorem` line) | in_cone | empty branch | what the nonempty branch buys |
|---|---|---|---|---|
| `ActualInitialMean.lean:318` `rcases isEmpty_or_nonempty (Index B N0)` | `ActualInitialMean.covariance_bounds_of_curl` :309 | True | :319-338 | `hs : (seed B N0).oscillation = 0`, `ht : tangentSum B N0 = 0` then `MemClass.zero` |
| `ActualSignedUnmaskedBounds.lean:161` | `ActualSignedUnmaskedBounds.raw_jets` :150 | True | :162-164 (`isEmptyElim`, `⟨0, le_rfl, 0, …⟩`) | `SignedCopyBounds.uniform_coefficients_jets` :167-181 |
| `ActualSignedUnmaskedBounds.lean:196` | `ActualSignedUnmaskedBounds.localized_jets` :185 | True | :197-199 | `SignedCopyBounds.uniform_smul` :204-205 |
| `ActualSignedStageControls.lean:1132` | `ActualSignedStageControls.raw_coefficients_jets` :1121 | True | :1133-1135 | `SignedCopyBounds.uniform_coefficients_jets` :1138-1152 |
| `ActualParticularStageControls.lean:941` `by_cases hne : Nonempty (ActivePair B N0)` | `…StageControls.raw_jets` :924 | True | :983-994 (`hempty … : False`) | `Classical.choose (exists_surjective_nat (ActivePair B N0))` :942-943 |
| `ActualParticularStageControls.lean:1214` same | `…StageControls.cutoff_jets` :1209 | True | :1245-1248 | same :1215-1217 |

**Two sites the parent brief did not list** — `ActualParticularStageControls.lean:941` and `:1214`
(`by_cases hne : Nonempty (ActivePair B N0)`, `let : Nonempty (ActivePair B N0) := hne` at `:942`/`:1215`).
So the artifact case-splits at **six** sites, not four, and the sixth type (`ActivePair`) is *not* one of
the four the brief names.

In every branch the conclusion is either a `∀ l, …`/`UniformLocalJets` (vacuous when the index is empty,
discharged by `isEmptyElim`) or a `MeanClass` bound on a label SUM (which is literally `0` when empty,
`ActualInitialMean.lean:325-331`). **Hence none of the six is materially dependent: each statement is TRUE
either way, and the artifact proves both branches.** The case split is sound and, as shown in §5, redundant.

## 3. Exhaustive `Nonempty` census (hypothesis vs conclusion)

`grep -rn 'Nonempty' NavierStokes Euler ComparatorChallenges --include=*.lean` = **305 lines**; of these
**37** are typeclass binders `[Nonempty …]` / `variable [Nonempty …]` / `omit [Nonempty …]`, 18 are
`Set.Nonempty`/`Finset.Nonempty`-shaped, the rest are `Nonempty (SomeStructure …)` existence packets
(Euler `Forcing`, `Choice`, `Witness`, …) unrelated to wave labels.

**Refutation of the prior claim's arithmetic.** The claim "all five known occurrences
(ParticularCopyBounds.lean:453,480; ActualGaussianCoverage.lean:730,801,1251)" undercounts by ~7x.
Full `[Nonempty …]` binder list (all HYPOTHESES, none a conclusion):
`ActualSignedControl.lean:379,444,516,543,571,683`; `ParticularCopyBounds.lean:453,480`;
`CorrectionInitialization.lean:2720,2764,2842`; `ActualGaussianCoverage.lean:730,801,1251`;
`UniformPrimaryWeights.lean:84,87,154,238,255,327,393,436,453,596,625,675,705`;
`CorrectionInitializationNoOptions.lean:2731,2775,2853`; `LocalizedMeanInteraction.lean:298`;
`ActualParticularPhysicalData.lean:252`; `SignedCopyBounds.lean:697,756`;
`ActualSignedGeometry.lean:1275`; `Euler/EulerProof.lean:19186,19211`.
Every one of them is on an ABSTRACT type variable (`Λ`, `ι`, `L`, `J`, `Label`, `X`) except
`ActualSignedGeometry.lean:1275`, whose type `ActivePair H v a reference chart` is a defined subtype of
section variables (still generic in `H v a reference chart`).

**Exhaustive concrete-type grep** — `Nonempty (Label | Index | SignedLabel | ActiveLabel | CellIndex |
UnsignedLabel | ActivePair | PrimaryGeometryAssembly… | BaseChartJets… | ActualPrimary…` — returns
exactly five lines, all in the two `by_cases` sites plus the `:1275` binder:
`ActualParticularStageControls.lean:941,942,1214,1215`, `ActualSignedGeometry.lean:1275`.
And `grep 'Nonempty' NavierStokes/{PrimaryGeometryAssembly,BaseChartJets,PositiveRepresentatives,PrimaryRepresentatives}.lean`
returns only `PrimaryGeometryAssembly.lean:394` (`Nonempty (Prepared …)`, a different type) and
`PrimaryRepresentatives.lean:92` (the `Set.Nonempty` inside `ActiveLabel`'s own predicate).

**CONFIRMED:** no declaration anywhere in the artifact states or concludes
`Nonempty (Label/Index/SignedLabel/CellIndex/ActiveLabel/UnsignedLabel …)`.

**One inhabitance CONCLUSION does exist, for a different type — and it is out of cone:**
`ActualParticularPhysicalData.lean:615` `instance sourceIndex_nonempty (N) : Nonempty (SourceIndex N) := ⟨(0, (⟨(4,0,false), le_rfl⟩, ⟨0, by simp⟩))⟩`
with `:613 abbrev SourceIndex (N) := Copy × PhysicalWaveSum.WaveIndex N` and
`PhysicalWaveSum.lean:344 abbrev WaveIndex (H) := BandLabel × Harmonic H`. That type carries NO activity
predicate, which is exactly why an explicit witness is available. CONE rows: `potential_class` :252,
`SourceIndex` :613, `sourceIndex_nonempty` :615, `nativePotential_bounds` :695 are all
`in_cone=False, in_import_closure=False`. So the single place the artifact discharges a `[Nonempty ι]`
hypothesis *by a proof* (`:705 potential_class hN …`, instance found at `:615`) is out of the cone and
about a trivially-inhabited band/copy index — NOT about the cell-index label type.

**Is a `[Nonempty …]`-carrying lemma in-cone AND applied with the hypothesis discharged?** Yes, and only
in one way: from the case hypothesis of §2. In-cone rows: `UniformPrimaryWeights.enumeration` :84 True,
`enumeration_surjective` :87 True, `SignedCopyBounds.uniform_smul` :697 True,
`ParticularCopyBounds.UniformModalControl.localJets` :453 True,
`ActualSignedControl.uniform_band_smul` :379 True. Their concrete consumers are the six in-cone
case-split theorems in §2's table. Out-of-cone `[Nonempty …]` carriers:
`ActualParticularPhysicalData.potential_class` :252 (False/False),
`LocalizedMeanInteraction.local_iUnion` :298 (False/True),
`ActualSignedGeometry.activeEnumeration` :1277, `activeEnumeration_surjective` :1280,
`activeCopyChart` :1301 (all `in_cone=False, in_import_closure=True`).

## 4a. Blowup lower bound is LABEL-FREE (child `blowup-lb`, `workers/_sub-index-incone-blowup.md`)

Independent trace by child `blowup-lb`, verdict **label-free**, i.e. an empty label type would NOT
falsify the headline. Chain it reports: `Witness` `ActualCandidateAssembly.lean:1121-1163` ->
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` :1155, whose ONLY blowup input is
`haxis` :298 -> `CandidateConsequences.lean:185-215` -> `MixedPeriodicAssembly.lean:366`
`periodicVelocity_speed_unbounded`; the divergence itself is `GermCandidateAssembly.lean:147-159`
`origin_blowup` = `FinalSlowBase.axis_tendsto` + `origin_eventually_base` :107-145, closed at
`FinalSlowBase.lean:372-379` by `rw [leading_origin]; exact W.axis.small.j_pos`, with
`BaseResidual.lean:90-116` giving `‖base (t,0)‖ = (1-t)^(-(1/2+h)) * d.axial 0 (0,0)`.
The bounded-below object is the leading SLOW-order axial coefficient at the axis,
`d.axial 0 (0,0) = W.axis.j` (`FinalSlowBase.lean:356-360`, `EntranceAlignedBase.lean:861`), positive by
`NaturalAxisData.lean:44` with `j := min (jcap/2) (1/2000)` (`MatchingConeBounds.lean:982-988`).
No `fieldSum` / `activeLabels` / `tangentSum` enters it. Moreover labels are switched OFF at the axis:
`ActualCandidateAssembly.lean:643-648 axis_not_active` (`profileRadius = 0 < leftRadius`), the
`axisZeroOn` family (`:592`, `:649`, `:466`, `:680`, `:144`), and `DirectAngularDiagonal.lean:315
angularSum_axis` kills `BSum` on the axis.

**Inverse finding worth more than the original worry:** the singularity is PRESCRIBED by the label-free
slow base, so the entire wave/label layer is not load-bearing for the blowup. Audit weight belongs on the
force side (`navier_stokes: residual = f`) and on `VanishingJointJets` / `boundaryLimits` at `t = 1`.
Child's own gaps: no compile (defeq read only); `localDomain :448/458` origin membership unexpanded;
residual/force layer unaudited.

## 4. Counter-direction (does anything NEED an inhabitant?)

Delegated in parallel to two independent children whose findings are filed at
`workers/_sub-index-incone-counter.md` (label-indexed suprema / `partitionFactor` consumers /
`Finset.max'`-style witnesses; includes the flagged
`MixedCandidateAssembly.lean:29-65 → ActualCandidateAssembly.lean:1090-1098,1152 →
ActualCycleResidualBounds.lean:1158-1172,1190-1206` chain) and
`workers/_sub-index-incone-blowup.md` (the `speed_unbounded` divergence chain), plus
`workers/_sub-index-incone-headline.md` for the headline trace. My own reading of the headline statement:

`ActualCandidateAssembly.lean:1123-1158` `def Witness (B N0) (hN) : Prop := ∃ a : ℕ → ℕ, SelectedSchedule … ∧ …
∃ ea eb ep, ∃ forcing, CandidateProperties (activatedVelocity (periodicVelocity ASum BSum)) … ∧ …`, proven at
`:1161 theorem witness` and specialized at `:1177 theorem selected_witness` (in_cone=True),
`:1183-1186 selected_candidate : ProblemStatement.candidateStatement`.
**No wave-label type occurs in that statement**: it quantifies over `ℕ → ℕ`, `VelocityField`,
`PressureField` and `SolenoidalDiagonal.potentialSum` of stage fields (`:1126-1131`). The
`CandidateProperties` field that could bite is `speed_unbounded : SpeedUnboundedAtOne u`
(`R3CompactCandidate.lean:37`, def `ProblemStatement.lean:94`), because `ProblemStatement.lean:151`
proves `¬ SpeedUnboundedAtOne (fun _ => 0)`; and the artifact itself proves that an empty label type
forces the oscillation to vanish (`ActualInitialMean.lean:325-328`). The divergence is produced from
`haxis : Tendsto (fun t => ‖velocity A v (t,0)‖) (𝓝[<] 1) atTop`
(`MixedPeriodicAssembly.lean:322-324`; sibling `PeriodicResidualLimits.lean:444-446`), i.e. from an axis
LOWER bound on the stage sums, not from the label bookkeeping directly — see the child file for the
full hop-by-hop trace. Note the asymmetry that matters for this audit: an inhabitant is *needed* nowhere
to STATE or PROVE the wave-layer estimates (§2), whereas the blowup lower bound is the only place where
non-triviality of the construction is at stake.

## 4b. Counter-direction result (child `counter-dir`, `workers/_sub-index-incone-counter.md`)

Child `counter-dir` reports (and I re-verified the load-bearing citation myself):
* The flagged chain is **NOT** a counter-witness. `MixedCandidateAssembly.lean:29-65 StageEstimates` has
  no label type at all (its index is the stage `N`); the content is `JetRate` =
  `∃ C ≥ 0, eventually ‖jet‖ ≤ C * q ^ r` (`DiagonalResidual.lean:33-34`), an UPPER bound satisfied by `0`.
  Same for `ActualCycleResidualBounds.lean:1158 residual_jetRate` and `:1190 finite_residual_rates`
  (`∀ J m`, upper bound; the label type appears only in the `CycleState (Index B N0)` parameter).
  Not vacuous, zero-satisfiable, no inhabitant needed.
* **Zero** uses of `Finset.max'/min'/sup'/inf'` over a label Finset anywhere in `NavierStokes`
  (`min'` occurs only over `levels n : Finset ℕ`, `CorrectionInitialization.lean:3776`).
* The real (and only) obligation is `[Nonempty Label]` via `UniformPrimaryWeights.lean:84-85`,
  discharged only at the case splits — same conclusion as my §2/§3.
* **Its strongest find, which I verified verbatim:** `ActualSignedMeanBinding.lean:463-472
  requested_cross_tail` (`in_cone=True`) applies `partitionFactor_eq_one B N0 n hx (physicalScale_tail B N0 hn hx)`
  at `:471`, with `hx : x ∈ ActualInitialization.geometry.strip.domain` and `hn : (choice B N0).prepared.N + 1 ≤ n`.
  So an in-cone theorem rewrites `partitionFactor = 1` under hypotheses that
  `actual_strip_nonempty` (`:54`) satisfies unconditionally. Reported in-cone chain upward:
  `:508 -> ActualSignedMeanBinding:463 -> :667 -> ActualCyclePreservation:599/740/878 ->
  ActualCandidateAssembly:480 -> estimates:1090 -> witness:1153 -> :1177 -> ComparatorSolution:17/24`.

**Consequence, stated sharply.** In the "needs an inhabitant as a HYPOTHESIS" sense the answer is NO
(§2, §4a). In the "would be FALSE without an inhabitant" sense the answer is **YES for exactly one
in-cone family**: `ActualPrimaryCovariance.lean:508 partitionFactor_eq_one` (and its in-cone consumer
`ActualSignedMeanBinding.lean:471`) is false when the label type is empty, because its hypotheses are
satisfiable. Since it is proven, emptiness is refuted rather than tolerated.

## 4c. Headline spine (child `hl-chain`) and the closure of its flagged gap G2

Child `hl-chain` (`workers/_sub-index-incone-headline.md`) reports the headline as
`NavierStokes.Comparator.navier_stokes_breakdown_R3`, `ComparatorSolution.lean:16` (periodic twin :23),
spine `:20 -> ComparatorR3Theorem.lean:38/:43 -> R3/Theorem.lean:46/:48 -> :26/:32 ->
R3/ActualCandidate.lean:143/:149 -> ActualCandidateAssembly.lean:1177/:1180 -> witness :1153 ->
estimates :1090`. Verdicts: the headline statement is closed and label-free
(`ComparatorSolution.lean:16-21`), no inhabitance obligation reaches it, and it is not weakened by an
empty label type; the only `Nonempty` facts on the spine are for SOLUTION types
(`R3/Theorem.lean:29`, `R3/ProblemStatement.lean:125,153`) and for the PARAMETER record
`Choice` (`CorrectionInitialization.lean:3923`), which DEFINES the index at `:3931` rather than
populating it. All six split sites are on the chain (consumers e.g.
`ActualCurrentParticularBounds.lean:161,169`, `ActualSignedGaussian.lean:175`,
`ActualInitialMean.lean:558`), each empty branch closing with constant `0`.

Its top gap G2 — `StageEstimates.finite_residual` (`MixedCandidateAssembly.lean:62-65`), with
`gain_top` (`:38`), discharged at `GluedStageEstimates.lean:436-440` — **I close by reading the
definitions**: `finite_residual : ∀ J m, JetRate … m (gain J - residualLoss m)` and
`DiagonalResidual.lean:33-34 def JetRate l q f m r := ∃ C, 0 ≤ C ∧ ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r`
— a pure UPPER bound, satisfied by `C = 0` for the zero field, whatever the sign of the exponent.
`gain` is label-free arithmetic: `GluedStageEstimates.lean:402 gain := ActualIterationLedger.gain h`
with `ActualIterationLedger.lean:29 gain h j := h * j / 10`, `gain_top` from
`GluedStageEstimates.lean:406`. So `finite_residual` tolerates an empty index; G2 is **not** a defect
candidate. The residual-decay ladder is therefore NOT the index-uniform counter-witness W25 looked for —
consistent with `counter-dir`'s reading of `ActualCycleResidualBounds.lean:1158,1190`.

## 5. Adversarial test of W25's five-line refutation — it SURVIVES, and extends further

I re-derived W25's argument from the sources, independently, and it holds:

1. `ActualPrimaryCovariance.lean:381-382`
   `def partitionFactor (B N0 n) (x) : ℝ := ∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2`
   — a `Finset.sum` over `unsignedLabels B N0 n : Finset (Label B N0)`
   (`:216-220`, a `Finset.preimage` under `PrimaryGeometryAssembly.label nominal`). If the TYPE is empty,
   that Finset is empty and the sum is `0`.
2. `ActualPrimaryCovariance.lean:508-513`
   `theorem partitionFactor_eq_one (B N0 n) {x} (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
   (hq : physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N) : partitionFactor B N0 n x = 1`.
3. `ActualPrimaryCovariance.lean:527-536 physicalScale_tail` supplies `hq` for **every** `n` with
   `(choice B N0).prepared.N + 1 ≤ n`, from the SAME `hx`. So only `hx` must be satisfiable.
4. `hx` is satisfiable with NO hypotheses: `ActualSignedMeanBinding.lean:54-67 actual_strip_nonempty :
   ActualInitialization.geometry.strip.domain.Nonempty`, witness `((G.patch.a + G.patch.b)/2, ((1,0),(0,0)))`,
   closed proof (`normalized_axis_scale` :48, `movingStrip_domain`).
   Bridge, checked by me: `ActualInitialization.lean:665 geometry_strip : geometry.strip = strip := rfl`
   and `ActualInitialization.lean:383-384 def strip := BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion`,
   while `ActualPrimaryCovariance.lean:18` does `open CorrectionInitialization.ActualPrimary`, so the
   `nominal`/`standardRegion` in `partitionFactor_eq_one`'s hypothesis are *the same terms*. The bridge is
   syntactic, not up to unfolding an opaque definition.
5. Therefore `0 = 1` unless `Label B N0` is inhabited ⇒ `Nonempty (ActualPrimary.Label B N0)` is a
   consequence of in-cone theorems (`partitionFactor_eq_one` :508 in_cone=True, `physicalScale_tail`
   :527 in_cone=True). Wrappers follow: `Index B N0`, `SignedLabel B N0` are `… × Fin 2`
   (`ActualInitialMean.lean:25`, `ActualSignedStageControls.lean:35`) and `Fin 2` is inhabited.

**Extension W25 missed (needed for the two sites W25 never saw).** `ActivePair B N0`
(`ActualParticularStageControls.lean:445`) needs an ACTIVE pair, which mere inhabitance of `Label` does
not obviously give. It does, though: `Active l n := 1 ≤ n ∧ cellBand l.2 ∈ CommonWindow.levels n`
(`:442-443`), `CommonWindow.self_mem (n) : n ∈ levels n` (`CorrectionInitialization.lean:3760`), and every
label satisfies `1 ≤ L.1` by construction (`PrimaryRepresentatives.lean:92`, `cellBand` =
`L.val.val.1`, `BaseChartJets.lean:829`). Take `n := cellBand l.2`: `Active l n` holds. So all SIX
case-split sites are on types that the artifact's own in-cone theorems entail are inhabited.

**Caveats I am obliged to state loudly, since they are the residue of the worry:**
* This is a META-theorem about the sources. **No Lean declaration in the artifact states it**
  (§3 exhaustive grep). The artifact still never proves its wave-label set inhabited, and the six case
  splits remain in the source as evidence that the author did not have the fact available.
* The witness theorem `actual_strip_nonempty` is `in_cone=False` (`in_import_closure=True`) in
  `CONE.csv` — i.e. the headline chain never references it. The derivation is available to an auditor,
  not used by the proof.
* The derivation is only as good as `partitionFactor_eq_one`'s own proof
  (`:512-513`, via `partitionFactor_eq_tail` :459-508 and `physical_mask_tail_sum_sq`), which I read but
  did not machine-check (no build possible). If that proof were vacuous or wrong, the inhabitance
  corollary evaporates — but then a *headline-relevant* covariance identity is wrong, which is a strictly
  worse defect than the original worry.

## 6. VERDICT

* **Material dependence: NO.** No in-cone theorem's TRUTH depends on the wave-label type being inhabited
  at the six case-split sites: each empty branch is proven inside the artifact
  (`ActualInitialMean.lean:319-338`; `ActualSignedUnmaskedBounds.lean:162-164`, `:197-199`;
  `ActualSignedStageControls.lean:1133-1135`; `ActualParticularStageControls.lean:983-994`, `:1245-1248`).
  The only thing inhabitance buys is the `enumeration` device (`UniformPrimaryWeights.lean:84`), i.e. a
  PROOF convenience, not statement content.
* **Census: all 37 `[Nonempty …]` binders are hypotheses**; the single inhabitance conclusion is
  `ActualParticularPhysicalData.lean:615` for `SourceIndex` (out of cone, activity-free type).
  In-cone hypothesis carriers are discharged only from the six case hypotheses, never by a proof.
* **Headline: no inhabitance obligation reaches it.** `ActualCandidateAssembly.lean:1123-1158,1177`
  mentions no label type; the residual risk is confined to the `speed_unbounded` axis lower bound
  (`MixedPeriodicAssembly.lean:322`), tracked in `workers/_sub-index-incone-blowup.md`.
* **W25's conclusion: not refuted — corroborated on an independent re-derivation, and extended to
  `ActivePair`.** Its status is "in-cone theorems entail it", not "the artifact proves it".
