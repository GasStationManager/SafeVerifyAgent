# NSE deep audit - IN-CONE counter-direction: does any in-cone theorem NEED an inhabited wave label?

Repo `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`. READ-ONLY. No `lake build` (impossible here);
every claim below is from source reading + grep, with file:line. Compile-level claims (definitional
equality, elaboration) are marked as INFERRED where they rest on the file type-checking as committed.

## 0. Verdict (short)

**YES - one real counter-witness exists, and it is not merely "needs an inhabitant": it *proves* one.**

`NavierStokes/ActualPrimaryCovariance.lean:508` `partitionFactor_eq_one` asserts
`partitionFactor B N0 n x = 1` where `partitionFactor` is *literally a `Finset.sum` over
`unsignedLabels B N0 n : Finset (Label B N0)`* (`:381-382`). If `Label B N0` were empty the sum is `0`,
so the statement would read `0 = 1`. Its two hypotheses are **satisfiable, unconditionally, inside the
artifact**: `NavierStokes/ActualSignedMeanBinding.lean:54 actual_strip_nonempty` exhibits an *explicit*
point of the very same strip domain, and `NavierStokes/ActualPrimaryCovariance.lean:527
physicalScale_tail` supplies the second hypothesis for every `n >= (choice B N0).prepared.N + 1`.
Hence `Nonempty (ActualPrimary.Label B N0)` is *derivable* from in-cone material for every `B N0`.
The four `isEmpty_or_nonempty` case splits are therefore defensive/robustness, not necessity.

The flagged `MixedCandidateAssembly` chain is **not** a counter-witness: it is an upper-bound
(`JetRate`) ladder over `N`-indexed stages, satisfiable by zero fields; it never mentions a label type.

## 1. The flagged "index-uniform, never case-splits" chain: verdict per site

### 1a. `MixedCandidateAssembly.lean:29-65` `structure StageEstimates`

```
NavierStokes/MixedCandidateAssembly.lean:29: structure StageEstimates (h qbig : R) (A B : N -> VelocityField)
NavierStokes/MixedCandidateAssembly.lean:30:     (P : N -> PressureField) where
...
NavierStokes/MixedCandidateAssembly.lean:36:   gain_pos : forall j, 1 <= j -> 0 < gain j
NavierStokes/MixedCandidateAssembly.lean:59:   finite_background : forall J m,
NavierStokes/MixedCandidateAssembly.lean:60:     JetRate (N[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
NavierStokes/MixedCandidateAssembly.lean:61:       (MixedDiagonalResidual.uncutVelocity A B J) m (-backgroundLoss m)
NavierStokes/MixedCandidateAssembly.lean:62:   finite_residual : forall J m,
NavierStokes/MixedCandidateAssembly.lean:64:       (fun z => navierStokesResidual (MixedDiagonalResidual.uncutVelocity A B J)
NavierStokes/MixedCandidateAssembly.lean:65:         (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (gain J - residualLoss m)
```

VERDICT: **no label type occurs in this structure at all**. The only index is the *stage* `j`/`J : N`
(always inhabited). "Index-uniform" here means uniform in the stage number, not in a wave label.
The quantitative fields are:
* `gain_pos` (`:36`): positivity of a *real sequence* `gain : N -> R`, not of any label-indexed sum.
* `finite_background` / `finite_residual` (`:59`, `:62`): `forall J m, JetRate ...`.

`JetRate` is a pure UPPER bound:
```
NavierStokes/DiagonalResidual.lean:33: def JetRate (l : Filter D) (q : D -> R) (f : D -> V) (m : N) (r : R) : Prop :=
NavierStokes/DiagonalResidual.lean:34:   exists C : R, 0 <= C and forall^f x in l, ||iteratedFDeriv R m f x|| <= C * (q x) ^ r
```
So `JetRate` is satisfied by the zero field with `C = 0`. If the wave-label type were empty, all label
sums collapse to `0`, the stage fields degenerate to their label-free (base) parts, and every field of
`StageEstimates` remains a *true but weaker* statement. Not "vacuously true" in the `forall`-over-an-
empty-type sense, but trivially satisfiable and **needing no inhabitant**. NO counter-witness here.

### 1b. `ActualCandidateAssembly.lean:1090-1098` `estimates`

```
NavierStokes/ActualCandidateAssembly.lean:1090: noncomputable def estimates (B N0 : N)
NavierStokes/ActualCandidateAssembly.lean:1091:     (hN : ActualCarrierGeometry.geometricThreshold <= N0) :
NavierStokes/ActualCandidateAssembly.lean:1092:     MixedCandidateAssembly.StageEstimates h (ActualCandidateConstruction.qbig B N0)
NavierStokes/ActualCandidateAssembly.lean:1093:       (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) :=
NavierStokes/ActualCandidateAssembly.lean:1094:   GluedStageEstimates.actualStageEstimates (runData B N0 hN) (meanCycleInput B N0 hN)
...
NavierStokes/ActualCandidateAssembly.lean:1098:     (representations B N0 hN) (physicalData B N0 hN)
```
VERDICT: this is a **`def` (data), not a claim**; it carries no content that emptiness can destroy.
It is the transit point through which `partitionFactor_eq_one` reaches the main theorem
(`runData` at `:1094`; see section 3.4), but by itself it needs no inhabitant.

### 1c. `ActualCandidateAssembly.lean:1121-1151` `Witness` / `:1153 witness`

This one *does* contain positive content - a divergence claim:
```
NavierStokes/ActualCandidateAssembly.lean:1142:       Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
NavierStokes/ActualCandidateAssembly.lean:1143:         TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum) (t, x)))
NavierStokes/ActualCandidateAssembly.lean:1144:         (N[<] (1 : R)) atTop and
```
I tested it as a candidate and it FAILS to be one. The H3 divergence is produced from an *axis speed*
blow-up:
```
NavierStokes/CandidateConsequences.lean:153: theorem h3_tendsto_of_speed_tendsto ... (x : R -> Space)
NavierStokes/CandidateConsequences.lean:155:     (hx : Tendsto (fun t => ||u (t, x t)||) (N[<] (1 : R)) atTop) :
NavierStokes/CandidateConsequences.lean:214:     h3_tendsto_of_speed_tendsto hc (fun _ => 0) (mixed_activated_speed_tendsto haxis),
```
i.e. evaluated on the trajectory `fun _ => 0` (the axis), with input
`haxis : Tendsto (fun t => ||MixedPeriodicAssembly.velocity A v (t, 0)||) (N[<] 1) atTop`
(`NavierStokes/CandidateConsequences.lean:194`). And the artifact *separately proves that the
label-indexed wave stages vanish on the axis*:
```
NavierStokes/ActualCandidateAssembly.lean:144: theorem initialPotential_axisZeroOn (B N0 : N) :
NavierStokes/ActualCandidateAssembly.lean:680: theorem positivePotential_axisZeroOn (B N0 : N)
NavierStokes/ActualCandidateAssembly.lean:1161:     (initialPotential_axisZeroOn B N0) (positivePotential_axisZeroOn B N0 hN)
```
So the divergence is carried by the label-free base/direct part, and an empty label type would not
destroy it. NO counter-witness here.

### 1d. `ActualCycleResidualBounds.lean:1158-1172` `residual_jetRate`

```
NavierStokes/ActualCycleResidualBounds.lean:1152: variable {B N0 N : N} {sigma : R} {x : CycleState (Index B N0)} (H : Invariant sigma x)
NavierStokes/ActualCycleResidualBounds.lean:1158: theorem residual_jetRate {u : VelocityField} {P : PressureField}
NavierStokes/ActualCycleResidualBounds.lean:1159:     (hGeom : ActualCarrierGeometry.geometricThreshold <= N0) (hN : 4 <= N)
NavierStokes/ActualCycleResidualBounds.lean:1160:     (hbase : x.state.errors.base = ActualInitialization.baseError B)
NavierStokes/ActualCycleResidualBounds.lean:1161:     (d : PhysicalData B N x.state u P) (m : N) :
NavierStokes/ActualCycleResidualBounds.lean:1162:     DiagonalResidual.JetRate GlobalBaseError.originPast (physicalQ ActualPrimary.h) (residual u P) m
NavierStokes/ActualCycleResidualBounds.lean:1163:       (ActualPrimary.h * (1/2 + sigma) - fixedLoss m) := by
```
VERDICT: the label type appears only in *parameter positions* (`x : CycleState (Index B N0)`), and the
conclusion is again a `JetRate` UPPER bound (see 1a). Non-vacuous when the label type is empty (it
still constrains `u`,`P`), but zero-satisfiable and needing no inhabitant. NO counter-witness.

### 1e. `ActualCycleResidualBounds.lean:1190-1206` `finite_residual_rates`

```
NavierStokes/ActualCycleResidualBounds.lean:1190: theorem finite_residual_rates {B N0 N : N}
NavierStokes/ActualCycleResidualBounds.lean:1192:     (p : N -> CycleParameters (Index B N0)) (u : N -> VelocityField) (P : N -> PressureField)
NavierStokes/ActualCycleResidualBounds.lean:1193:     (H : forall J, Invariant (ActualIterationLedger.sigma J) (CycleState.iterate p ...))
NavierStokes/ActualCycleResidualBounds.lean:1195:     (d : forall J, PhysicalData B N (...) (u J) (P J)) :
NavierStokes/ActualCycleResidualBounds.lean:1198:     forall J m, DiagonalResidual.JetRate GlobalBaseError.originPast (physicalQ ActualPrimary.h)
NavierStokes/ActualCycleResidualBounds.lean:1199:       (fun w => navierStokesResidual (u J) (P J) w.1 w.2) m
NavierStokes/ActualCycleResidualBounds.lean:1200:       (ActualIterationLedger.gain ActualPrimary.h J - fixedLoss m) := by
```
VERDICT: same shape - `forall J m, <upper bound>`; the quantification is over `N`, not over labels.
The `gain J` in the exponent is a real sequence (`ActualIterationLedger.gain`), not a label sum.
NO counter-witness. **Summary for the flagged chain: it never needs, and never proves, an inhabitant;
it is an upper-bound ladder that survives emptiness with weakened content.**

## 2. Census of label-indexed suprema / choices / positive lower bounds (`NavierStokes/*.lean`)

* `iSup`/`sSup`/`sup over a label type`: only two real hits, neither label-indexed:
  * `NavierStokes/AnalyticCoefficientBounds.lean:281: sSup ((fun z => (F z).re) '' K)` - sup over a
    compact set of complex points, bddAbove supplied at `:286`; no labels.
  * `NavierStokes/ClosedIntervalCkOperators.lean:256,270: ... = (sup) x : I, ||B x||` - operator norm
    over the interval `I`; no labels.
* `Classical.choice` / `Classical.choose`: 30+ hits, all on *data/geometry* existentials, not on a
  label. The most relevant ones:
  * `NavierStokes/CorrectionInitialization.lean:3929: noncomputable def choice (B N0 : N) : Choice B N0 := Classical.choice (choice_nonempty B N0)`
    with `choice_nonempty` proved at `:3923-3927` from `PrimaryTargetBounds.exists_constructed_bounds`.
    This chooses the *geometry/covariance package*, not a label; the label type is then
    `abbrev Label (B N0 : N) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N` (`:3931`).
  * `NavierStokes/PrimaryRepresentatives.lean:95: Classical.choose L.property.2` - choice *from* a
    label's own witness field (see the label definition in section 5), i.e. it consumes an inhabitant,
    it does not create one.
  * `NavierStokes/UniformPrimaryWeights.lean:85: Classical.choose (exists_surjective_nat (N x i))` -
    THIS is the one that forces `[Nonempty i]`; see section 4.
* Positive lower bounds on label-indexed quantities: I scanned all 182 lines mentioning
  `activeLabels|unsignedLabels|signedLabels`; **none** carries a `0 <`, `Nonempty`, or `!= empty`
  claim - except the `= 1` claim of section 3. The one positivity constant that *is* fed into the
  label-uniform machinery is label-free:
  `NavierStokes/ActualPrimaryBounds.lean:1243-1251 normalFloor (B N0) = normalLower * min (phases B N0 0).b (phases B N0 1).b`,
  `normalFloor_pos` - a `min` over `Fin 2` phase constructions, not over labels.

## 3. `partitionFactor_eq_one` - THE counter-witness (full detail)

### 3.1 The statement, with all hypotheses

```
NavierStokes/ActualPrimaryCovariance.lean:508: theorem partitionFactor_eq_one (B N0 n : N) {x : Point}
NavierStokes/ActualPrimaryCovariance.lean:509:     (hx : x in (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
NavierStokes/ActualPrimaryCovariance.lean:510:     (hq : physicalScale n x <= ChartScales.Q (choice B N0).prepared.N) :
NavierStokes/ActualPrimaryCovariance.lean:511:     partitionFactor B N0 n x = 1 := by
NavierStokes/ActualPrimaryCovariance.lean:512:   rw [partitionFactor_eq_tail B N0 n hx]
NavierStokes/ActualPrimaryCovariance.lean:513:   exact physical_mask_tail_sum_sq _ _ (physicalScale_pos n hx) hq _
```
Exactly two hypotheses: `hx` (a point of the native strip domain) and `hq` (the point's physical scale
is at or below the chosen threshold band).

### 3.2 The definitions that make emptiness fatal

```
NavierStokes/ActualPrimaryCovariance.lean:381: noncomputable def partitionFactor (B N0 n : N) (x : Point) : R :=
NavierStokes/ActualPrimaryCovariance.lean:382:   sum L in unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2
```
```
NavierStokes/ActualPrimaryCovariance.lean:216: noncomputable def unsignedLabels (B N0 n : N) : Finset (Label B N0) := by
NavierStokes/ActualPrimaryCovariance.lean:217:   classical
NavierStokes/ActualPrimaryCovariance.lean:218:   exact (CorrectionInitialization.CommonWindow.labels (CoordinateAlgebra.D h)
NavierStokes/ActualPrimaryCovariance.lean:219:     (BaseContextAssembly.geometryBound nominal standardRegion) n).preimage
NavierStokes/ActualPrimaryCovariance.lean:220:       (PrimaryGeometryAssembly.label nominal) (PrimaryGeometryAssembly.label_injective nominal).injOn
```
`unsignedLabels B N0 n : Finset (Label B N0)`, and `Label B N0 = ActualPrimary.Label B N0`
(`CorrectionInitialization.lean:3931`). If `Label B N0` is empty then *every* `Finset (Label B N0)` is
`empty`, so `partitionFactor B N0 n x = 0` for all `n, x`, and the conclusion `= 1` is FALSE.
So `partitionFactor_eq_one` is a genuine `Finset.sum-over-labels = positive constant` claim -
exactly the shape the audit asked for. It does NOT case-split on `isEmpty_or_nonempty`.

The value `1` comes from a partition-of-unity over the FULL (label-type-independent) tail index:
```
NavierStokes/PartitionedCovariance.lean:766: theorem physical_mask_tail_sum_sq (D : R) (N : N) {q : R} (hq : 0 < q)
NavierStokes/PartitionedCovariance.lean:767:     (hqN : q <= ChartScales.Q N) (x : SlotColoring.Position) :
NavierStokes/PartitionedCovariance.lean:768:     (finsum U : UnsignedLabel, mask D (tailLabel N U) q x ^ 2) = 1 := by
```
and the finite-vs-total identification is
```
NavierStokes/ActualPrimaryCovariance.lean:464: theorem partitionFactor_eq_tail (B N0 n : N) {x : Point}
NavierStokes/ActualPrimaryCovariance.lean:465:     (hx : x in (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
NavierStokes/ActualPrimaryCovariance.lean:466:     partitionFactor B N0 n x =
NavierStokes/ActualPrimaryCovariance.lean:467:       finsum U : UnsignedLabel, mask (CoordinateAlgebra.D h)
NavierStokes/ActualPrimaryCovariance.lean:468:         (tailLabel (choice B N0).prepared.N U) (physicalScale n x) (physicalPosition n x) ^ 2 := by
```
whose proof *manufactures a label from a nonzero mask*:
```
NavierStokes/ActualPrimaryCovariance.lean:484:     obtain <L, hL> := PrimaryGeometryAssembly.physicalMask_has_index nominal
NavierStokes/ActualPrimaryCovariance.lean:500:     refine Finset.mem_image.mpr <L, (mem_unsignedLabels n L).mpr hactive, ?_>
```
i.e. the inhabitance *producer* is
```
NavierStokes/PrimaryGeometryAssembly.lean:198: theorem physicalMask_has_index {N : N} (L : PartitionedCovariance.UnsignedLabel)
NavierStokes/PrimaryGeometryAssembly.lean:199:     (hL : 1 <= L.1) (hN : N <= L.1) {q : R} {x : SlotColoring.Position}
NavierStokes/PrimaryGeometryAssembly.lean:200:     (hq : 0 < q) (hR : 0 <= x 0) (hT : 0 < x 2)
NavierStokes/PrimaryGeometryAssembly.lean:204:     (hm : PartitionedCovariance.mask (CoordinateAlgebra.D F.data.h) L q x != 0) :
NavierStokes/PrimaryGeometryAssembly.lean:205:     exists i : Index W N, label W i = L := by
```
`exists i : Index W N` - a literal existence statement over the wave-label type, discharged from a
nonzero mask (via `PositiveRepresentatives.physicalMask_has_positive_representative`, `:206-207`).

### 3.3 Are the hypotheses satisfiable? YES, unconditionally

```
NavierStokes/ActualSignedMeanBinding.lean:54: theorem actual_strip_nonempty : ActualInitialization.geometry.strip.domain.Nonempty := by
NavierStokes/ActualSignedMeanBinding.lean:55:   let G := ActualInitialization.geometry
NavierStokes/ActualSignedMeanBinding.lean:56:   refine <((G.patch.a + G.patch.b) / 2, ((1, 0), (0, 0))), ?_>
```
No hypotheses; an explicit point. And that domain is *the same* domain
`partitionFactor_eq_one` wants:
```
NavierStokes/ActualInitialization.lean:383: noncomputable def strip : StripData Point :=
NavierStokes/ActualInitialization.lean:384:   BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion
NavierStokes/ActualInitialization.lean:665: theorem geometry_strip : geometry.strip = strip := rfl
```
(Independently corroborated by the fact that `ActualSignedMeanBinding.lean:471` passes an
`hx : x in ActualInitialization.geometry.strip.domain` *directly* as the `hx` argument of
`partitionFactor_eq_one`; that only elaborates if the two are definitionally equal - INFERRED from the
committed file type-checking.)

Second hypothesis is free for high bands:
```
NavierStokes/ActualPrimaryCovariance.lean:527: theorem physicalScale_tail (B N0 : N) {n : N} (hn : (choice B N0).prepared.N + 1 <= n)
NavierStokes/ActualPrimaryCovariance.lean:528:     {x : Point} (hx : x in (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
NavierStokes/ActualPrimaryCovariance.lean:529:     physicalScale n x <= ChartScales.Q (choice B N0).prepared.N := by
```

**Derivation (4 lines, all in-cone, no case split):** take `x0` from `actual_strip_nonempty`
(`ActualSignedMeanBinding.lean:54`); set `n := (choice B N0).prepared.N + 1`; then
`partitionFactor_eq_one B N0 n hx0 (physicalScale_tail B N0 le_rfl hx0)` gives
`sum over unsignedLabels B N0 n of (spatialMask ...)^2 = 1`. If `IsEmpty (Label B N0)` the sum is `0`,
so `0 = 1`. Hence **`Nonempty (ActualPrimary.Label B N0)` for every `B N0`**.
=> the "labels might be empty, so the estimates are vacuous" worry is not merely *avoided* by the
artifact, it is *refutable inside* the artifact. (I could not run this derivation - no build - so it is
a source-level argument, not a checked Lean term.)

### 3.4 Consumers of `partitionFactor_eq_one`, and the in-cone path

Direct consumers (only two):
```
NavierStokes/ActualPrimaryCovariance.lean:619 | in NavierStokes.ActualPrimaryCovariance.mean_tangentCovariance_eq_leading (:614)
NavierStokes/ActualSignedMeanBinding.lean:471 | in NavierStokes.ActualSignedMeanBinding.requested_cross_tail (:463)
```
Chain to the two main results (each link verified by name-occurrence inside the named declaration):
```
partitionFactor_eq_one            ActualPrimaryCovariance.lean:508
 -> requested_cross_tail          ActualSignedMeanBinding.lean:463 (used at :471)
 -> family_requested_cross_tail   ActualSignedMeanBinding.lean:667
 -> stepData_of_waves             ActualCyclePreservation.lean:599
 -> stepData_of_particular        ActualCyclePreservation.lean:740
 -> state_stepData                ActualCyclePreservation.lean:878
 -> runData                       ActualCandidateAssembly.lean:480
 -> estimates                     ActualCandidateAssembly.lean:1090 (uses runData at :1094)
 -> witness                       ActualCandidateAssembly.lean:1153 (uses estimates at :1157)
 -> selected_witness              ActualCandidateAssembly.lean:1177
 -> ... ComparatorBridge          ComparatorTheorem.lean:47 / ComparatorR3Theorem.lean
 -> navier_stokes_breakdown_{R3,periodic}  ComparatorSolution.lean:17, :24
```
The second consumer branch (`mean_tangentCovariance_eq_leading` -> `mean_tangentCovariance_jets`,
`ActualPrimaryCovariance.lean:614,621`) feeds the same initialization/mean machinery.
So `partitionFactor_eq_one` is IN-CONE.

Related same-shape siblings (also no case split):
```
NavierStokes/ActualPrimaryCovariance.lean:730: theorem partitionFactor_eq_one_sub_missing (B N0 n : N) {x : Point}
NavierStokes/ActualPrimaryCovariance.lean:732:     partitionFactor B N0 n x = 1 - missingWeight (choice B N0).prepared.N (physicalScale n x)
```
This one is weaker as a counter-witness: `1 - missingWeight` could in principle be `0`. Only the
`= 1` version at `:508` is outright inconsistent with emptiness.

## 4. `Finset.max'/min'/sup'/inf'` over label Finsets: NONE. But `[Nonempty Label]` obligations EXIST

Complete census over all 817 `.lean` files (817 files / 429281 lines scanned):
* `Finset.max'` : 0 hits. `Finset.inf'` : 0 hits.
* `.min'` : 6 hits, all in the `CommonWindow` band-window code, over a `Finset N` of *scale levels*:
```
NavierStokes/CorrectionInitialization.lean:3757: noncomputable def levels (n : N) : Finset N :=
NavierStokes/CorrectionInitialization.lean:3758:   insert n (Finset.Icc (max 1 (n - 2)) (n + 2))
NavierStokes/CorrectionInitialization.lean:3762: theorem levels_nonempty (n : N) : (levels n).Nonempty := <n, self_mem n>
NavierStokes/CorrectionInitialization.lean:3775: noncomputable def index (h : R) (n : N) : N :=
NavierStokes/CorrectionInitialization.lean:3776:   ((levels n).image (ChartScales.nativeIndex h)).min' ((levels_nonempty n).image _)
NavierStokes/CorrectionInitialization.lean:3779:   exact Finset.min'_le _ _ (Finset.mem_image.mpr <m, hm, rfl>)
NavierStokes/CorrectionInitialization.lean:3790:   (Finset.min'_mem ((levels n).image (ChartScales.nativeIndex h)) ((levels_nonempty n).image _))
```
  plus the duplicate file `CorrectionInitializationNoOptions.lean:3787,3790,3801`.
  The nonemptiness argument is `levels_nonempty n = <n, self_mem n>` - a *natural number* witness
  (`n in levels n`), nothing to do with the wave-label type.
* `.sup'` : 3 hits, all over `Finset.range (M + 1)` (never empty):
```
NavierStokes/DiagonalJetBounds.lean:142:   let B : R := (Finset.range (M + 1)).sup'
NavierStokes/DiagonalJetBoundsNoOptions.lean:156:   let B : R := (Finset.range (M + 1)).sup'
NavierStokes/DiagonalResidual.lean:107:   max 0 ((Finset.range (M + 1)).sup'
```
=> **no extremum over a label Finset anywhere.** The "most valuable find" the brief hoped for does not
exist in that form.

What DOES exist is a typeclass-level inhabitance obligation on the label type:
```
NavierStokes/UniformPrimaryWeights.lean:84: noncomputable def enumeration (i : Type*) [Countable i] [Nonempty i] : N -> N x i :=
NavierStokes/UniformPrimaryWeights.lean:85:   Classical.choose (exists_surjective_nat (N x i))
NavierStokes/UniformPrimaryWeights.lean:87: theorem enumeration_surjective (i : Type*) [Countable i] [Nonempty i] :
NavierStokes/UniformPrimaryWeights.lean:88:     Surjective (enumeration i) := Classical.choose_spec (exists_surjective_nat (N x i))
```
consumed by the label-uniform jet machinery, which therefore carries `[Nonempty Label]`:
```
NavierStokes/ParticularCopyBounds.lean:453: theorem localJets [Countable Label] [Nonempty Label]
NavierStokes/ParticularCopyBounds.lean:460:   let e := UniformPrimaryWeights.enumeration Label
NavierStokes/ParticularCopyBounds.lean:461:   apply SignedCopyBounds.uniform_local_of_pull (UniformPrimaryWeights.enumeration_surjective Label)
NavierStokes/ParticularCopyBounds.lean:480: variable [Countable Label] [Nonempty Label]
NavierStokes/ActualGaussianCoverage.lean:730:   [Countable Label] [Nonempty Label]
NavierStokes/ActualGaussianCoverage.lean:801: variable [Countable Label] [Nonempty Label]
NavierStokes/ActualGaussianCoverage.lean:1251: variable [Countable Label] [Nonempty Label]
```
And THIS is precisely what the four `isEmpty_or_nonempty` sites discharge - by case split, not by
proof. Each supplies the instance in the `inr` branch with `let := h` and kills the `inl` branch with
`isEmptyElim`:
```
NavierStokes/ActualSignedUnmaskedBounds.lean:161:   cases isEmpty_or_nonempty (Label B N0) with
NavierStokes/ActualSignedUnmaskedBounds.lean:163:       let := h
NavierStokes/ActualSignedUnmaskedBounds.lean:164:       constructor <;> refine <fun l => isEmptyElim l, fun _ => <0, le_rfl, 0, fun l => isEmptyElim l>>
NavierStokes/ActualSignedUnmaskedBounds.lean:166:       let := h    (nonempty branch -> SignedCopyBounds.uniform_coefficients_jets at :169)
NavierStokes/ActualSignedUnmaskedBounds.lean:196:   cases isEmpty_or_nonempty (Label B N0) with        (same pattern, :199 / :201)
NavierStokes/ActualSignedStageControls.lean:1132:   cases isEmpty_or_nonempty (SignedLabel B N0) with  (same pattern, :1135 / :1137)
NavierStokes/ActualInitialMean.lean:318:   rcases isEmpty_or_nonempty (Index B N0) with he | he
NavierStokes/ActualInitialMean.lean:320:     have hl (n : N) : ActualPrimary.activeLabels ... n = empty := ... (fun l => isEmptyElim l)
NavierStokes/ActualInitialMean.lean:322:     have hs : (seed B N0).oscillation = 0 := ...
NavierStokes/ActualInitialMean.lean:340:   . let := he ; exact AssembledPrimary.covariance_bounds ...
```
Note the empty branches are all *conclusion-preserving*: the estimate targets are `UniformLocalJets`
(an upper bound, `<0, le_rfl, 0, ...>`) or a `MeanClass` of the zero field (`ActualInitialMean.lean:328
MemClass.zero`). This is exactly consistent with section 1: the estimate ladder is upper-bound shaped.

## 5. Why inhabitance is not trivial for this label type (context)

```
NavierStokes/CorrectionInitialization.lean:3931: abbrev Label (B N0 : N) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N
NavierStokes/PrimaryGeometryAssembly.lean:137: abbrev Index (N : N) :=
NavierStokes/PrimaryGeometryAssembly.lean:138:   BaseChartJets.CellIndex F.data.h (NominalConeAssembly.activeLeft W)
NavierStokes/PrimaryGeometryAssembly.lean:139:     (NominalConeAssembly.activeRight W) N
NavierStokes/BaseChartJets.lean:825: noncomputable def CellIndex (h lo hi : R) (N : N) :=
NavierStokes/BaseChartJets.lean:826:   {L : PositiveRepresentatives.ActiveLabel (PrimaryRepresentatives.referenceCompact h lo hi) //
NavierStokes/BaseChartJets.lean:827:     N <= L.val.1}
NavierStokes/PositiveRepresentatives.lean:25: noncomputable def ActiveLabel (K : Set Slow) := PrimaryRepresentatives.ActiveLabel (positivePart K)
NavierStokes/PrimaryRepresentatives.lean:91: noncomputable def ActiveLabel (K : Set Slow) :=
NavierStokes/PrimaryRepresentatives.lean:92:   {L : Label // 1 <= L.1 and (K int tsupport (nativeMask L.1 L.2)).Nonempty}
```
So a label is a *subtype* carrying a proof that its mask support meets the reference compact, with band
at least `N`. Only `Countable` is registered as an instance
(`PrimaryGeometryAssembly.lean:141 instance indexCountable`); **no `Nonempty`/`Inhabited` instance for
`Index`/`Label`/`CellIndex` is declared anywhere** (grep: 0 hits). That is why the four case splits are
needed to feed `[Nonempty Label]`, and it is why the section-3 derivation is interesting: the
inhabitant is available (via `physicalMask_has_index`), it just was never packaged as an instance.

## 6. Caveats

* No compilation was performed (no `.olean`s, toolchain mismatch), as instructed. Statements are read
  from source. Two places rely on the committed file elaborating as written:
  the strip definitional equality in 3.3, and the chain links in 3.4 (name occurrence inside the
  named declaration, which does not by itself prove a *proof-term* dependency - it is a strong
  indication, not a `#print axioms`-grade fact).
* The chain in 3.4 was found with an automated inverted-index walk over declaration bodies; the four
  weakest links (`family_requested_cross_tail`, `stepData_of_waves`, `stepData_of_particular`,
  `state_stepData`, `runData`) were each re-checked by hand as occurring inside the named enclosing
  declaration.
