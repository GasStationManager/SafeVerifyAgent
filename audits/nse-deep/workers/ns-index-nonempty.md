# Worker report — `Index B N0`: is the wave tower's label set ever proved nonempty?

Worker `ns-index-nonempty`. Read-only audit of `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`.
**Nothing under that path was modified.** No `lake build` (no Mathlib on box); source-level reading only.
Follow-up to E1 of `workers/ns-nondegeneracy.md` §A5.

## Headline

**The literal claim is CONFIRMED, and the substantive worry behind it is REFUTED.**

* There is **no** `Nonempty (Index …)` / `Nonempty (Label …)` / `Nonempty (SignedLabel …)` /
  `Nonempty (CellIndex …)` theorem or instance anywhere in the repository (full grep printed in §A1).
  The only `Nonempty Label` occurrences are *instance-argument hypotheses* on lemmas, never conclusions.
  So the artifact indeed never records that its own wave tower is inhabited, and it case-splits on
  emptiness at four sites.
* **But emptiness is refutable in ~5 lines from the artifact's own theorems**, all but one of them
  `in_cone = True`. The partition-of-unity identity
  `partitionFactor_eq_one` (`NavierStokes/ActualPrimaryCovariance.lean:508`) says a **`Finset.sum` over
  `unsignedLabels B N0 n : Finset (ActualPrimary.Label B N0)` equals `1`** at every strip point with
  `n ≥ (choice B N0).prepared.N + 1`. An empty index type forces that Finset to be `∅` and the sum to
  be `0`. Combined with the explicit strip witness `actual_strip_nonempty`
  (`NavierStokes/ActualSignedMeanBinding.lean:54-67`) this gives `0 = 1`. Hence
  `Nonempty (ActualPrimary.Label B N0)`, hence `Nonempty (Index B N0)`.
* Verdict: **structural gap, not a defect.** The four `isEmpty_or_nonempty` branches are *dead code*
  (unreachable but harmlessly proved). The wave tower is **not** void. Downgrade E1/E2 from
  `SUSPICIOUS` to `OK (unrecorded)`.

## Scope

Files read for this question (declaration counts from `audits/nse-deep/CONE.csv`):

| file | decls | in_cone True/False | read line-by-line | skimmed/grepped |
|---|---|---|---|---|
| `NavierStokes/PrimaryRepresentatives.lean` | 96 | 87/9 | 60-120, 150-200, 535-550 | rest |
| `NavierStokes/PositiveRepresentatives.lean` | 89 | 75/14 | 18-80 | rest |
| `NavierStokes/PrimaryGeometryAssembly.lean` | 83 | 56/27 | 130-230 | rest |
| `NavierStokes/BaseChartJets.lean` | 69 | 61/8 | 810-880 | rest |
| `NavierStokes/ActualPrimaryCovariance.lean` | 116 | 105/11 | 210-235, 370-400, 455-545, 590-625 | rest |
| `NavierStokes/PartitionedCovariance.lean` | 110 | 85/25 | 755-800 | rest |
| `NavierStokes/ActualInitialMean.lean` | 63 | 60/3 | 300-350 | rest |
| `NavierStokes/ActualSignedUnmaskedBounds.lean` | 36 | 33/3 | 150-210 | rest |
| `NavierStokes/ActualSignedStageControls.lean` | 126 | 119/7 | 1120-1150 | rest |
| `NavierStokes/ActualSignedMeanBinding.lean` | 65 | 37/28 | 40-75 | rest |
| `NavierStokes/CorrectionInitialization.lean` | 393 | 334/59 | 3881-3960 (namespace `ActualPrimary`) | rest |

**Total decls in scope files: 1246.** Read line-by-line: **≈ 46 declarations** in the ranges above.
Everything else was reached by targeted grep (all greps printed below verbatim), because the question
is a *reachability* question about one type, not a proof-by-proof audit of these files.
Parts B and C were delegated to two read-only children (`_sub-index-headline.md`,
`_sub-index-force-divfree.md`); their verdicts are folded in at §B and §C with attribution.

## A. Is `Index B N0` ever proved nonempty?

### A0. The type chain (verbatim)

```lean
-- NavierStokes/ActualInitialMean.lean:25
abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2
-- NavierStokes/CorrectionInitialization.lean:3931   (inside `namespace ActualPrimary`, opened :3881)
abbrev Label (B N0 : ℕ) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N
-- NavierStokes/PrimaryGeometryAssembly.lean:137-139
abbrev Index (N : ℕ) :=
  BaseChartJets.CellIndex F.data.h (NominalConeAssembly.activeLeft W)
    (NominalConeAssembly.activeRight W) N
-- NavierStokes/BaseChartJets.lean:825-827
noncomputable def CellIndex (h lo hi : ℝ) (N : ℕ) :=
  {L : PositiveRepresentatives.ActiveLabel (PrimaryRepresentatives.referenceCompact h lo hi) //
    N ≤ L.val.1}
-- NavierStokes/PositiveRepresentatives.lean:25
noncomputable def ActiveLabel (K : Set Slow) := PrimaryRepresentatives.ActiveLabel (positivePart K)
-- NavierStokes/PrimaryRepresentatives.lean:91-92
noncomputable def ActiveLabel (K : Set Slow) :=
  {L : Label // 1 ≤ L.1 ∧ (K ∩ tsupport (nativeMask L.1 L.2)).Nonempty}
-- NavierStokes/PrimaryRepresentatives.lean:24
abbrev Label := PartitionedCovariance.UnsignedLabel     -- = ℕ × Grid (SlotColoring.lean:31 shape)
```
Also the same type under other names:
`ActualSignedStageControls.lean:35 abbrev SignedLabel (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2`;
`ActualSignedUnmaskedBounds.lean:23 abbrev Label (B N0 : ℕ) := ActualSignedStageControls.SignedLabel B N0`;
`ActualPrimaryBounds.lean:33 abbrev SignedLabel (B N0 : ℕ) := Fin 2 × ActualPrimary.Label B N0`.
So a single nonemptiness fact about `ActualPrimary.Label B N0` settles all four split sites.

To inhabit `Index B N0` one must exhibit a grid label `L = (n, k)` with (a) `1 ≤ n`,
(b) `N ≤ n` where `N = (choice B N0).prepared.N` is **`Classical.choice`-selected**
(`CorrectionInitialization.lean:3929`), and (c) `referenceCompact h lo hi ∩ positiveTime ∩
tsupport (nativeMask n k) ≠ ∅`. (c) is the nontrivial part: it is a *geometric* claim about the mask
grid at an arbitrarily fine, non-explicit band `N`.

### A1. Full grep output — no `Nonempty` conclusion anywhere

`grep -rn -E 'Nonempty \((Index|Label|SignedLabel|ActiveLabel|CellIndex)|Nonempty (Index|Label|SignedLabel|ActiveLabel|CellIndex)' --include=*.lean .`

```
./NavierStokes/ParticularCopyBounds.lean:453:theorem localJets [Countable Label] [Nonempty Label]
./NavierStokes/ParticularCopyBounds.lean:480:variable [Countable Label] [Nonempty Label]
./NavierStokes/ActualGaussianCoverage.lean:730:  [Countable Label] [Nonempty Label]
./NavierStokes/ActualGaussianCoverage.lean:801:variable [Countable Label] [Nonempty Label]
./NavierStokes/ActualGaussianCoverage.lean:1251:variable [Countable Label] [Nonempty Label]
```
All five are **hypotheses** (instance binders), not conclusions. Widening to any `Nonempty` whose line
mentions label/index/cell:
```
NavierStokes/ParticularCopyBounds.lean:453,480         (hypotheses, as above)
NavierStokes/ActualGaussianCoverage.lean:730,801,1251  (hypotheses, as above)
NavierStokes/PrimaryRepresentatives.lean:92:  {L : Label // 1 ≤ L.1 ∧ (K ∩ tsupport (nativeMask L.1 L.2)).Nonempty}
NavierStokes/LabelCounting.lean:29:  {L | L.1 = n ∧ (normalizedBox A L ∩ B).Nonempty}
NavierStokes/ActualParticularPhysicalData.lean:615:instance sourceIndex_nonempty (N : ℕ) : Nonempty (SourceIndex N)
```
Lines 92 and 29 are `Set.Nonempty` *inside the subtype predicate* (not nonemptiness of the label type);
`:615` is a different type (`SourceIndex`). **Confirmed: no declaration in the repo has
`Nonempty (Index/Label/SignedLabel/ActiveLabel/CellIndex …)` as its conclusion.**

The only existence statements about these types are **conditional upgrades**:
```
./NavierStokes/PrimaryRepresentatives.lean:159-166
theorem physicalMask_active (K : Set Slow) (D : ℝ) (L : Label)
    (hL : 1 ≤ L.1) {q : ℝ} {x : Position}
    (hx : normalizedSlow D L.1 x ∈ K) (hm : PartitionedCovariance.mask D L q x ≠ 0) :
    ∃ A : ActiveLabel K, A.val = L := by
  refine ⟨⟨L, hL, normalizedSlow D L.1 x, hx, ?_⟩, rfl⟩ …
./NavierStokes/PrimaryRepresentatives.lean:542   physicalMask_has_representative           (same, + coords)
./NavierStokes/PositiveRepresentatives.lean:61   physicalMask_has_positive_representative  (same, + 0 < x 2)
./NavierStokes/PrimaryGeometryAssembly.lean:198-209
theorem physicalMask_has_index {N : ℕ} (L : PartitionedCovariance.UnsignedLabel)
    (hL : 1 ≤ L.1) (hN : N ≤ L.1) … (hm : PartitionedCovariance.mask (CoordinateAlgebra.D F.data.h) L q x ≠ 0) :
    ∃ i : Index W N, label W i = L
```
i.e. *"if some physical mask is nonzero at a point of the reference region, that label is active."*
Every one needs a point `x` with `mask ≠ 0` handed in. Sole consumer:
```
./NavierStokes/ActualPrimaryCovariance.lean:484: obtain ⟨L, hL⟩ := PrimaryGeometryAssembly.physicalMask_has_index nominal …
```
and there the `mask ≠ 0` comes from `hU : U ∈ support (…)` inside a support-shrinking argument — still
conditional. So **§A5 of `ns-nondegeneracy` is correct as stated.**

### A2. …but emptiness contradicts an in-cone identity the artifact already proves

The refutation goes through the partition of unity, not through the label lemmas.

```lean
-- NavierStokes/ActualPrimaryCovariance.lean:216-223
noncomputable def unsignedLabels (B N0 n : ℕ) : Finset (Label B N0) := by
  classical
  exact (CorrectionInitialization.CommonWindow.labels (CoordinateAlgebra.D h)
    (BaseContextAssembly.geometryBound nominal standardRegion) n).preimage
      (PrimaryGeometryAssembly.label nominal) (PrimaryGeometryAssembly.label_injective nominal).injOn

theorem activeLabels_product (B N0 n : ℕ) :
    activeLabels standardRegion B N0 n = (unsignedLabels B N0 n).product Finset.univ := rfl

-- NavierStokes/ActualPrimaryCovariance.lean:381-382
noncomputable def partitionFactor (B N0 n : ℕ) (x : Point) : ℝ :=
  ∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2

-- NavierStokes/ActualPrimaryCovariance.lean:508-513          [in_cone = True]
theorem partitionFactor_eq_one (B N0 n : ℕ) {x : Point}
    (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain)
    (hq : physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N) :
    partitionFactor B N0 n x = 1 := by
  rw [partitionFactor_eq_tail B N0 n hx]
  exact physical_mask_tail_sum_sq _ _ (physicalScale_pos n hx) hq _

-- NavierStokes/ActualPrimaryCovariance.lean:527-535          [in_cone = True]
theorem physicalScale_tail (B N0 : ℕ) {n : ℕ} (hn : (choice B N0).prepared.N + 1 ≤ n)
    {x : Point} (hx : x ∈ (BaseContextAssembly.nativeStrip nominal standardRegion).domain) :
    physicalScale n x ≤ ChartScales.Q (choice B N0).prepared.N

-- NavierStokes/PartitionedCovariance.lean:766-768            [in_cone = True]
theorem physical_mask_tail_sum_sq (D : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q)
    (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position) :
    (∑ᶠ U : UnsignedLabel, mask D (tailLabel N U) q x ^ 2) = 1
```

and the strip point exists, with an explicit witness (no choice, no hypothesis):

```lean
-- NavierStokes/ActualSignedMeanBinding.lean:54-67             [in_cone = False, in_import_closure = True]
theorem actual_strip_nonempty : ActualInitialization.geometry.strip.domain.Nonempty := by
  let G := ActualInitialization.geometry
  refine ⟨((G.patch.a + G.patch.b) / 2, ((1, 0), (0, 0))), ?_⟩ …
-- NavierStokes/ActualInitialization.lean:665
theorem geometry_strip : geometry.strip = strip := rfl
-- NavierStokes/ActualInitialization.lean:383-384
noncomputable def strip : StripData Point :=
  BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion
```
`geometry.strip.domain` and `(BaseContextAssembly.nativeStrip nominal standardRegion).domain` are the
**same set, definitionally** (`:665` is `rfl` onto `:383`), and `:383` is exactly the set
`partitionFactor_eq_one` quantifies over. So the derivation is:

1. `obtain ⟨x, hx⟩ := actual_strip_nonempty` — a concrete point of the strip domain.
2. put `n := (choice B N0).prepared.N + 1`; `physicalScale_tail B N0 le_rfl hx` gives `hq`.
3. `partitionFactor_eq_one B N0 n hx hq : ∑ L ∈ unsignedLabels B N0 n, spatialMask L (…) ^ 2 = 1`.
4. If `IsEmpty (ActualPrimary.Label B N0)` then `unsignedLabels B N0 n = ∅` (a `Finset` of an empty
   type) and the sum is `0` by `Finset.sum_empty`. So `(0 : ℝ) = 1`, absurd.
5. Therefore `(unsignedLabels B N0 n).Nonempty`, so `Nonempty (ActualPrimary.Label B N0)`, so
   `Nonempty (Index B N0)` (`= Label × Fin 2`, `Fin 2` inhabited) and likewise
   `Nonempty (SignedLabel B N0)`.

Three of the four inputs are `in_cone = True`; only the strip witness is `in_cone = False` (it is
proved, imported, and its proof is a closed term — cone status affects *who cites it*, not whether it
holds). **Consequence: for every `(B, N0)` the label set is inhabited at every band
`n ≥ (choice B N0).prepared.N + 1`, so the four `isEmpty` branches are unreachable.**

This is a *checkable* claim, and the cheapest way to settle it is to add the five lines above to the
artifact and build. I could not build (no Mathlib), so I flag it as **HIGH-CONFIDENCE, UNBUILT**.

Sanity cross-check that the argument is not circular: `partitionFactor_eq_one` does **not** assume the
label set nonempty; its proof (`:512-513`) rewrites through `partitionFactor_eq_tail` (`:464-506`),
which converts the `Finset` sum into the *unrestricted* `finsum` over all `UnsignedLabel`s and then
applies the dyadic partition-of-unity `physical_mask_tail_sum_sq`. The `finsum` is over the full label
type, whose emptiness is not at issue; the content of `:464-506` is exactly that the full sum's support
lands inside `unsignedLabels`, and *that* step is where `physicalMask_has_index` is used
(`:484-495`) — so the artifact already knows "nonzero mask ⇒ active label"; it simply never runs the
argument in the other direction to conclude inhabitedness.

### A3. The four emptiness case-splits, quoted, and what each empty branch proves

| site | type split on | empty branch proves |
|---|---|---|
| `ActualInitialMean.lean:318-339` | `Index B N0` | `activeLabels … = ∅` (`:320`), `(seed B N0).oscillation = 0` (`:322`), `tangentSum = 0` (`:325`), then both `MeanClass` goals by `MemClass.zero` |
| `ActualSignedUnmaskedBounds.lean:161-164` | `Label B N0` | both `UniformLocalJets` by `⟨fun l => isEmptyElim l, fun _ => ⟨0, le_rfl, 0, fun l => isEmptyElim l⟩⟩` — constant `0` |
| `ActualSignedUnmaskedBounds.lean:196-199` | `Label B N0` | identical |
| `ActualSignedStageControls.lean:1132-1135` | `SignedLabel B N0` | identical |

```lean
-- ActualInitialMean.lean:317-327 (verbatim)
  rcases isEmpty_or_nonempty (Index B N0) with he | he
  · let := he
    have hl (n : ℕ) : ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun l => isEmptyElim l)
    have hs : (seed B N0).oscillation = 0 := by
      funext n x i
      simp [seed, bandSeed, LabelSumBounds.fieldSum, hl]
```
Both branches are proved, so nothing is vacuous *as a matter of logic*; and by §A2 the first branch is
mathematically unreachable. Note the direct tension worth recording: `:320` proves
`activeLabels … n = ∅` **for all `n`**, while `partitionFactor_eq_one` forces
`unsignedLabels B N0 n ≠ ∅` for `n` large — i.e. the two together are the contradiction of §A2, in the
artifact's own vocabulary.

### A4. For contrast: where the artifact *does* prove a `Nonempty`

`CorrectionInitialization.lean:3929`: `noncomputable def choice (B N0 : ℕ) : Choice B N0 :=
Classical.choice (choice_nonempty B N0)`, and `choice_nonempty` **is** discharged
(`:3920-3927`, ending `exact ⟨⟨a, dg, eb, il, hdg, heb, hil, hb⟩⟩`). So the author does prove
`Nonempty` where a `Classical.choice` forces the issue; the label set is not forced, which is a
plausible and innocent explanation of the gap.

## B. Would the headline still be proved if `Index B N0` were empty?

**Delegated to child `index-headline`** (report `workers/_sub-index-headline.md`). Its verdict is
folded in below; see §Escalations for the part I could not corroborate myself.

**Child verdict (`index-headline`, report `workers/_sub-index-headline.md`): (a) — the headline is still
PROVED with an empty index.** Its evidence, which I spot-checked at every `file:line` it cites:

* The headline is `theorem_1_1` (`NavierStokes/R3/Theorem.lean:46`) → `breakdownStatement`
  (`R3/ProblemStatement.lean:150`) → the 12 `CandidateProperties` fields (`:92-109`). Field by field
  (child's §2), **none** takes an inhabitant of `Index`/`Label`/`SignedLabel`/`CellIndex` and none
  carries an unresolved `[Nonempty …]` for them: `navier_stokes` is *definitional* (the force IS the
  traced residual, `CandidateFromLimits.lean:82` vs `:181-182`), the supports come from the two
  cutoffs, `energy_bounded` from compact support + smoothness.
* The only non-trivial field, `speed_unbounded`, is carried by **one index-free positive constant**:
  `FinalSlowBase.axis_tendsto` (`:372-378`) closes on `W.axis.small.j_pos`
  (`NaturalAxisData.lean:41-45`), through `BaseResidual.baseVelocity_axis_tendsto_atTop`
  (`:104-114`), whose only inputs are `0 < d.axial 0 (0,0)` and vanishing of the higher axial modes.
  The profile carrying it (`FinalSlowBase.actualProfile`, `:619-634`) is index-free, and the wave
  index is built **on top** of it (`CorrectionInitialization.lean:3886` then `:3931`), never the
  reverse — so there is no hidden loop back into the tower.
* **The loudest part, and it is the artifact's own theorem:** the correction tower is *proved
  identically zero on a neighbourhood of every axis point* — which is exactly where the blow-up is
  read off. `AxisZeroOn` (`GermCandidateAssembly.lean:24-25`),
  `positivePotential_axisZeroOn` (`ActualCandidateAssembly.lean:680-686`) assembled from
  `particular`/`signed`/`stream` (`:649-655`), the signed one via `axis_not_active` (`:642-647`:
  the axis is never in the active carrier because `PrimaryTargetBounds.leftRadius_pos`), and these
  are handed to the assembly at `:1161-1162`. So even with a **nonempty** index the waves
  contribute exactly `0` to `speed_unbounded`.
* Its emptiness census matches mine independently: 4 `isEmpty_or_nonempty` sites, each empty branch
  proving the same statement; the `[Nonempty Λ]` binders (`ActualSignedControl.lean:379,444,571,683`,
  `ParticularCopyBounds.lean:453,480`, `ActualGaussianCoverage.lean:730,801,1251`) are all
  discharged *inside* the nonempty branch (`let := h` at `ActualSignedUnmaskedBounds.lean:166,201`,
  `ActualInitialMean.lean:340`), so **no `Nonempty` obligation propagates up to
  `witness`/`selected_witness`/`theorem_1_1`**.

**Its one honest residue, which I am promoting to my E4.** The tower *is* in the chain of the
residual decay ladder: `StageEstimates.gain_top`/`finite_residual`
(`MixedCandidateAssembly.lean:29-65`) → `ActualCandidateAssembly.estimates:1090-1098` →
`GluedStageEstimates.actualStageEstimates:684` → `ActualCycleResidualBounds.finite_residual_rates`
(`:1190-1206`) / `Invariant.residual_jetRate` (`:1158-1172`), where the state is
`x : CycleState (Index B N0)` (`:1152`). That ladder yields `VanishingJointJets`
(`JointResidualLimits.lean:84-86`) and hence smoothness of the force across `t = 1`. None of
`ActualCycleResidualBounds`/`ActualCyclePreservation`/`GluedStageEstimates` case-splits on
emptiness, so those proofs are index-*uniform* — the child could not tell from source whether they
stay true for a zero tower or whether their active-annulus geometry tacitly forces inhabitedness.
By my §A2 the question is **moot for soundness** (the index is inhabited), but it is the one place
where an empty tower would have had to be checked rather than shrugged at.

**Where I part company with the child, mildly:** it calls the tower "decoration". That is right for
the *conclusion* `speed_unbounded` and wrong for the *hypotheses* of the assembly it is fed to — the
tower is what makes the residual small enough for the glue, and W12/W16 already found that ladder to
be real work. The accurate sentence is: the tower is not load-bearing for the **blow-up**, and it is
load-bearing for the **smoothness of the force**.

Independent of the child, one thing I can state from §A2: the question is now **moot for soundness** —
the index is inhabited, so no headline theorem can be silently resting on a vacuous wave tower.
It remains interesting for *structure*, and the sibling's §A6 answer stands on its own evidence:
`speed_unbounded` (`NavierStokes/R3/ProblemStatement.lean:109`) is discharged from the explicit
self-similar base on the axis (`NavierStokes/BaseResidual.lean:104-114`, `FinalSlowBase.lean:372-382`,
`h₀` from `W.axis.small.j_pos`, `NaturalAxisData.lean:44`) and does not route through the wave tower.

## C. Does the force's support/smoothness, or divergence-freeness, need a wave?

**Delegated to child `index-force-divfree`** (report `workers/_sub-index-force-divfree.md`).

**Child verdict (`index-force-divfree`, report `workers/_sub-index-force-divfree.md`): both clauses are
WAVE-INDEPENDENT.** Quoting its cited `file:line`s, which I spot-checked below:

*(i) Force compact spatial support is IMPOSED by fixed cutoffs, not derived from field content.*
- `NavierStokes/R3/PositiveTimeForce.lean:46` — `def force f := fun z => timeCutoff z.1 • f z`; the
  support theorem at `:72-80` takes as hypotheses only `IsCompact K` and
  `∀ t x, x ∉ K → f (t,x) = 0`. That file's imports are `R3.ProblemStatement` + `SmoothCutoffs` only, so
  it cannot touch the wave tower.
- `NavierStokes/R3CompactCandidate.lean:88` — `compactForce f := fun z => outerCutoff z.2 • f z`, with
  `:94` closed by `simp [outerCutoff_zero_outside]`. Wired into the actual candidate at
  `NavierStokes/R3/ActualCandidate.lean:88-89, 109-110`.
- Smoothness through `t = 1` is a Whitney/Borel glue: `NavierStokes/CandidateFromLimits.lean:82-87` →
  `NavierStokes/SpacetimeGluing.lean:344`, whose only hypothesis is `ContDiffOn ℝ ∞ f (past T)`, fed by
  *vanishing* residual jets (`NavierStokes/JointResidualLimits.lean:84`).
- Consequence the child states plainly and I agree with: **`f ≡ 0` satisfies both clauses verbatim.**
  So neither clause can detect an empty tower.

*(ii) Divergence-freeness is structural + termwise.* `NavierStokes/SpatialLocalization.lean:258-262`
gives `div (curl …) = 0`; `NavierStokes/DirectAngularDiagonal.lean:291-313` closes the sum with
`Finset.sum_eq_zero` over `Finset.range N`, each term by the rotation-field identity at `:175-179`. An
empty or zero tower is therefore trivially divergence free.

*Force non-triviality is never assumed* — it is **derived** from `speed_unbounded`
(`NavierStokes/MaximalLifespan.lean:275-290`, `NavierStokes/R3/CandidateBreakdown.lean:53-62`), which by
the sibling's §A6 comes from the base profile on the axis, not from the tower.

**My reading of this:** answer to C is *no* on both counts — emptiness would not bite at the force or at
divergence-freeness. Combined with §A2 the point is moot for soundness, but it does sharpen the
structural picture: the force clauses are *imposed by construction* (two multiplicative cutoffs plus a
gluing lemma with a vanishing-jet hypothesis), so they carry no information about whether the
constructed field is non-trivial. The only clause that carries that information is `speed_unbounded`.

## D. Kernel-risk assessment for this scope

Vectors from the brief, checked over the 11 scope files with
`grep -nE 'macro|elab |syntax|set_option|native_decide|^axiom|unsafe |partial def|sorry|decide|Nat\.pow|Nat\.gcd|Nat\.div|Nat\.mod|termination_by|\.rec |Acc\.rec|inductive |deriving '`:

**(1) Recursive inductives / recursors / `Acc.rec` / large elimination — ABSENT.**
Zero `inductive`, zero `termination_by`, zero `.rec`/`Acc.rec`, zero `deriving` in all 11 files. The
only type constructions in scope are `Subtype` (`ActiveLabel`, `CellIndex`), `Prod` (`Index`,
`SignedLabel`, `UnsignedLabel`), `Fin 2`, and `Finset`. `CellIndex`/`ActiveLabel` are **`def`s that
unfold to `Subtype`**, and the kernel only needs `Subtype` eta / projection, not a recursor
reduction — visible in `PrimaryGeometryAssembly.lean:141-144`, where `Countable (Index W N)` is got by
`dsimp only [Index, BaseChartJets.CellIndex, PositiveRepresentatives.ActiveLabel,
PrimaryRepresentatives.ActiveLabel]; infer_instance`, i.e. by *delta-unfolding to `Subtype`* and reusing
Mathlib's instance. `label_injective` (`:148-149`) is `fun _ _ he => Subtype.ext (Subtype.ext he)` —
two `Subtype.ext` applications, no recursion. `Finset.sum` over `unsignedLabels` is the one place a
`Multiset`/`Quot` recursor is involved, and only through Mathlib's `Finset.sum_empty`/`sum_congr`
lemmas, never by kernel unfolding of a concrete list.
**Verdict: no recursor reduction is required of the kernel here.**

**(2) GMP / numeral arithmetic — TWO trivial sites, nothing else.**
```
NavierStokes/ActualPrimaryCovariance.lean:330:  … zero_pow (by decide : (2 : ℕ) ≠ 0) …
NavierStokes/ActualSignedMeanBinding.lean:295:  … zero_pow (by decide : (2 : ℕ) ≠ 0) …
```
Each is `Nat.decEq 2 0` at literals `2` and `0`: one `Nat.ble`/`beq` step on 1-digit numerals, closing
in constant time. No `Nat.pow`/`div`/`mod`/`gcd`, no literal above 4, no `norm_num` certificate over
big numerals in scope. The exponent `2` in `spatialMask … ^ 2` and `mask … ^ 2` is a `ℕ` literal in a
**real-valued** `Monoid.npow`, so the kernel never computes it as a numeral; and `Q_succ`
(`ActualPrimaryCovariance.lean:521-525`) is `Real.rpow` algebra closed by `norm_num; ring`, not integer
arithmetic. **Verdict: negligible; peak kernel numeral work is `2 ≠ 0`.**

**(3) Custom metaprogramming — ZERO.** No `macro`, `elab`, `syntax`, `set_option`, `native_decide`,
`axiom`, `unsafe`, `partial` in any of the 11 scope files. Consistent with the repo-wide scan.

**Non-kernel risk actually present in scope: classical choice.** `Classical.choose` is the *definition*
of `representative` (`PrimaryRepresentatives.lean:94-95`), and `(choice B N0).prepared.N` is
`Classical.choice`-selected (`CorrectionInitialization.lean:3929`). This is sound (both choices are
over types proved nonempty at `:97-102` / `:3920-3927`) but it is exactly why `N` is not an explicit
numeral, and therefore why an explicit label witness cannot be written down — the reason the gap in §A1
exists at all. `classical` appears at `ActualInitialMean.lean:317`,
`ActualSignedUnmaskedBounds.lean:160,195`, `ActualSignedStageControls.lean:1131`,
`ActualPrimaryCovariance.lean:217,227,469` — all `Decidable`-instance bridging, no `Decidable` instance
is ever *evaluated*.

**Cone status (mark 4).** From `audits/nse-deep/CONE.csv`:

| decl | file:line | in_cone | in_import_closure |
|---|---|---|---|
| `ActualInitialMean.Index` | `ActualInitialMean.lean:25` | True | True |
| `ActualPrimary.Label` | `CorrectionInitialization.lean:3931` | True | True |
| `BaseChartJets.CellIndex` | `BaseChartJets.lean:825` | True | True |
| `PositiveRepresentatives.ActiveLabel` | `PositiveRepresentatives.lean:25` | True | True |
| `PrimaryRepresentatives.ActiveLabel` | `PrimaryRepresentatives.lean:91` | True | True |
| `PrimaryRepresentatives.physicalMask_active` | `PrimaryRepresentatives.lean:159` | True | True |
| `PositiveRepresentatives.physicalMask_has_positive_representative` | `PositiveRepresentatives.lean:61` | True | True |
| `PrimaryGeometryAssembly.physicalMask_has_index` | `PrimaryGeometryAssembly.lean:198` | True | True |
| `ActualPrimaryCovariance.unsignedLabels` | `ActualPrimaryCovariance.lean:216` | True | True |
| `ActualPrimaryCovariance.activeLabels_product` | `ActualPrimaryCovariance.lean:222` | True | True |
| `ActualPrimaryCovariance.partitionFactor_eq_one` | `ActualPrimaryCovariance.lean:508` | True | True |
| `ActualPrimaryCovariance.physicalScale_tail` | `ActualPrimaryCovariance.lean:527` | True | True |
| `ActualPrimaryCovariance.mean_tangentCovariance_eq_leading` | `ActualPrimaryCovariance.lean:614` | True | True |
| `PartitionedCovariance.physical_mask_tail_sum_sq` | `PartitionedCovariance.lean:766` | True | True |
| `ActualInitialMean.covariance_bounds_of_curl` | `ActualInitialMean.lean:309` | True | True |
| `ActualSignedMeanBinding.actual_strip_nonempty` | `ActualSignedMeanBinding.lean:54` | **False** | True |
| `CorrectionInitializationNoOptions.ActualPrimary.Label` | `…NoOptions.lean:3942` | False | False |

The whole nonemptiness derivation is in-cone except the strip witness. Note also that the
emptiness-split theorems themselves are in-cone (`covariance_bounds_of_curl`, `ActualInitialMean.lean:309`,
`in_cone = True`), so the dead branch *is* part of the shipped proof — dead, but shipped.

## Per-declaration findings

| # | declaration | file:line | statement, in my words | mechanism | verdict |
|---|---|---|---|---|---|
| 1 | `ActualInitialMean.Index` | `ActualInitialMean.lean:25` | wave label type `= ActualPrimary.Label B N0 × Fin 2` | `abbrev`, no content | OK |
| 2 | `ActualPrimary.Label` | `CorrectionInitialization.lean:3931` | `= PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N`; the band floor is `Classical.choice`-selected | `abbrev` over a choice-selected `ℕ` | OK (opaque `N`) |
| 3 | `BaseChartJets.CellIndex` | `BaseChartJets.lean:825-827` | active positive labels with band `≥ N` | `Subtype` of `ActiveLabel` | OK |
| 4 | `PrimaryRepresentatives.ActiveLabel` | `PrimaryRepresentatives.lean:91-92` | labels with band `≥ 1` whose closed mask support meets `K` | `Subtype`, predicate is `Set.Nonempty` of an intersection | OK |
| 5 | `PositiveRepresentatives.ActiveLabel` | `PositiveRepresentatives.lean:25` | same with `K` replaced by `K ∩ {0 < time}` | `def` composition | OK |
| 6 | `representative` | `PrimaryRepresentatives.lean:94-95` | picks a point of `K ∩ tsupport (nativeMask …)` | `Classical.choose` of the subtype's own witness | OK |
| 7 | `representative_mem` / `_mem_tsupport` | `PrimaryRepresentatives.lean:97,100` | that point is in `K` / in the mask support | `Classical.choose_spec` projections | OK |
| 8 | `physicalMask_active` | `PrimaryRepresentatives.lean:159-166` | nonzero physical mask at a point of `K` ⇒ that label is active | builds the `Subtype` from the given point; `subset_closure` + `mul_ne_zero_iff` | OK (conditional) |
| 9 | `physicalMask_has_representative` | `PrimaryRepresentatives.lean:542-549` | same in reference coordinates | direct application of #8 | OK (conditional) |
| 10 | `physicalMask_has_positive_representative` | `PositiveRepresentatives.lean:61-72` | same, upgrading `0 ≤ x 2` to `0 < x 2` so the time coordinate is positive | #8 with `div_pos` for the time component | OK (conditional) |
| 11 | `physicalMask_has_index` | `PrimaryGeometryAssembly.lean:198-209` | nonzero mask + `N ≤ L.1` ⇒ `∃ i : Index W N, label W i = L` | #10 then `refine ⟨⟨A, ?_⟩, hA⟩`; `simpa only [hA] using hN` | OK (conditional) — **not an unconditional witness** |
| 12 | `indexCountable` | `PrimaryGeometryAssembly.lean:141-144` | `Countable (Index W N)` | `dsimp only` delta-unfold to `Subtype`, `infer_instance` — no recursor | OK |
| 13 | `label_injective` | `PrimaryGeometryAssembly.lean:148-149` | the underlying-label map is injective | `Subtype.ext ∘ Subtype.ext` | OK |
| 14 | `unsignedLabels` | `ActualPrimaryCovariance.lean:216-220` | `Finset (Label B N0)`: preimage of the `CommonWindow` label window under `label`, along an injection | `Finset.preimage` with `label_injective … .injOn` | OK |
| 15 | `activeLabels_product` | `ActualPrimaryCovariance.lean:222-223` | `activeLabels … = unsignedLabels ×ˢ univ` | `rfl` | OK (definitional, checkable) |
| 16 | `partitionFactor` | `ActualPrimaryCovariance.lean:381-382` | `∑ L ∈ unsignedLabels B N0 n, spatialMask L (nativePoint n x L) ^ 2` | `def`, a `Finset.sum` | OK |
| 17 | `partitionFactor_eq_tail` | `ActualPrimaryCovariance.lean:464-506` | that sum equals the unrestricted `finsum` over all tail labels | `finsum_eq_sum_of_support_subset`, with support control via `physicalMask_has_index` + `activeLabels_cover` (`:484-500`) | OK — the crux of §A2 |
| 18 | `partitionFactor_eq_one` | `ActualPrimaryCovariance.lean:508-513` | `partitionFactor B N0 n x = 1` when `x` in the native strip and `physicalScale n x ≤ Q N` | #17 then `physical_mask_tail_sum_sq` | **OK, and it refutes emptiness** |
| 19 | `physicalScale_tail` | `ActualPrimaryCovariance.lean:527-535` | `n ≥ N+1` ⇒ `physicalScale n x ≤ Q N` on the strip | `Q_antitone` + `Q_succ` + `q ≤ 2` from the region, `linarith` | OK |
| 20 | `physical_mask_tail_sum_sq` | `PartitionedCovariance.lean:766-785` | `∑ᶠ U, mask D (tailLabel N U) q x ^ 2 = 1` for `0 < q ≤ Q N` | `finsum_pair_eq` + per-row `physicalSlowMask_sum_sq` + `dyadicMask_tail_sum_sq` | OK — a genuine partition of unity |
| 21 | `mean_tangentCovariance_eq_leading` | `ActualPrimaryCovariance.lean:614-619` | for `n ≥ N+1`, the mean tangent covariance equals the leading stress exactly | `mean_tangentCovariance_factor` then `partitionFactor_eq_one … one_mul` | OK — an in-cone consumer of #18, so #18 is load-bearing |
| 22 | `covariance_bounds_of_curl` | `ActualInitialMean.lean:309-350` | two `MeanClass` bounds for the seed covariance | `isEmpty_or_nonempty (Index B N0)`: empty ⇒ `oscillation = 0` and `MemClass.zero`; nonempty ⇒ `AssembledPrimary.covariance_bounds` | OK (empty branch now known dead) |
| 23 | `raw_jets` | `ActualSignedUnmaskedBounds.lean:150-183` | uniform local jet bounds for raw signed coefficients | same split; empty ⇒ constants `0`; nonempty ⇒ `SignedCopyBounds.uniform_coefficients_jets` | OK (dead branch) |
| 24 | `localized_jets` | `ActualSignedUnmaskedBounds.lean:185-205` | same after cutoff | same split; nonempty ⇒ `uniform_smul` of `raw_jets` | OK (dead branch) |
| 25 | `raw_coefficients_jets` | `ActualSignedStageControls.lean:1121-1150+` | same for the stage-controls copy | same split | OK (dead branch) |
| 26 | `actual_strip_nonempty` | `ActualSignedMeanBinding.lean:54-67` | the native strip domain is nonempty | explicit witness `((a+b)/2, ((1,0),(0,0)))`, `normalized_axis_scale` + `norm_num` + `linarith` | OK — **the missing ingredient of §A2** |
| 27 | `geometry_strip` | `ActualInitialization.lean:665` | `geometry.strip = strip` | `rfl` | OK (definitional bridge) |
| 28 | `ActualInitialization.strip` | `ActualInitialization.lean:383-384` | `= BaseContextAssembly.nativeStrip nominal standardRegion` | `def` | OK |
| 29 | `choice` / `choice_nonempty` | `CorrectionInitialization.lean:3929` / `:3920-3927` | the prepared-data choice, and that its type is nonempty | `Classical.choice` of a proved `Nonempty` (`exact ⟨⟨a, dg, eb, il, …⟩⟩`) | OK — shows the author proves `Nonempty` when forced |
| 30 | `sourceIndex_nonempty` | `ActualParticularPhysicalData.lean:615` | `Nonempty (SourceIndex N)` | the repo's only label-flavoured `Nonempty` instance — **different type**, not `Index` | OK (irrelevant to E1) |

Verdict counts over the 30 examined declarations: **OK 30**, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0
— with the one structural note that §A1's gap is real (the artifact does not state what §A2 proves).

## Escalations

**E1 (was `ns-nondegeneracy` E1/E2) — DOWNGRADE, do not chase.**
`NavierStokes/ActualInitialMean.lean:318`, `ActualSignedUnmaskedBounds.lean:161`, `:196`,
`ActualSignedStageControls.lean:1132`.
Question for an expert: *does the five-line derivation in §A2 compile?* i.e. add
```lean
theorem index_nonempty (B N0 : ℕ) : Nonempty (ActualInitialMean.Index B N0) := by
  obtain ⟨x, hx⟩ := ActualSignedMeanBinding.actual_strip_nonempty
  have hq := ActualPrimaryCovariance.physicalScale_tail B N0 (le_refl _) hx
  have h1 := ActualPrimaryCovariance.partitionFactor_eq_one B N0 _ hx hq
  -- `partitionFactor` is `∑ L ∈ unsignedLabels …`; if the type were empty this is `0 = 1`
  …
```
What would settle it: a successful `lake build` of that snippet against the artifact. If it compiles,
the wave tower is provably inhabited and the item closes as `OK`. If it does **not** compile, the
interesting failure mode is a coercion/`rfl` mismatch between `geometry.strip.domain` and
`(nativeStrip nominal standardRegion).domain`; `ActualInitialization.lean:665` says they are `rfl`, so
I expect it to go through. **Rank 1 only because it is cheap and it closes a whole audit item.**

**E2 — the derivation's one out-of-cone link.**
`NavierStokes/ActualSignedMeanBinding.lean:54` is `in_cone = False`. Question: is there an in-cone
theorem exhibiting a point of `(nativeStrip nominal standardRegion).domain`? What would settle it: a
grep of in-cone decls whose statement is `… .domain.Nonempty` or `∃ x, x ∈ … .domain`. This matters
only for the *bookkeeping* claim "the headline depends on inhabitedness", not for the mathematics.

**E3 — dead code shipped in-cone.** `ActualInitialMean.lean:309` is `in_cone = True` and contains a
branch (`:318-339`) that §A2 shows is unreachable. Question: is there any *other* in-cone theorem whose
**only** proof path is through an `isEmpty` branch (i.e. a bound that is proved *only* vacuously)? What
would settle it: an automated pass listing in-cone theorems whose proof text contains
`isEmptyElim` outside a `cases`/`rcases` that also proves the nonempty branch. My four sites all prove
both branches, so none of them is such a case; the pass is to confirm there is no fifth site.

**E4 (promoted from the child's §5) — the one place emptiness would have bitten.**
`NavierStokes/MixedCandidateAssembly.lean:29-65`, `ActualCandidateAssembly.lean:1090-1098,1152`,
`ActualCycleResidualBounds.lean:1158-1172,1190-1206`, `GluedStageEstimates.lean:684`.
Question for an expert: the residual-decay ladder (`gain_top`, `finite_residual`) is stated over
`CycleState (Index B N0)` and never case-splits on emptiness, so it is index-uniform — does its
active-annulus geometry *require* an inhabitant, or would `gain J → ∞` survive a zero tower? What
would settle it: whether any step of `Invariant.residual_jetRate` consumes a lower bound that is a
sum over a nonempty label set. Moot for soundness given §A2; rank 3, structural only.

## Residue — what I could not check

1. **No build.** Every claim here is source-level. §A2 in particular is an argument I constructed from
   the artifact's lemmas; I could not elaborate it. If a hidden universe/instance mismatch blocks step 4
   (`Finset` over an empty type ⇒ `∅`), my headline weakens back to §A1's "never proved".
2. **`(choice B N0).prepared.N` is opaque.** I cannot exhibit a *concrete* label `(n, k)`; the
   derivation is by contradiction and gives no witness. So I cannot say *how many* waves there are, only
   that there is at least one at every band above the threshold. Whether the tower is *rich* enough
   (e.g. infinitely many labels, or labels at every band) is untouched.
3. **`spatialMask` positivity not audited.** I took `partitionFactor_eq_one` at its word for the value
   `1`; I read its proof one level deep (`partitionFactor_eq_tail` + `physical_mask_tail_sum_sq`) but not
   the `SquaredPartition.dyadicMask_tail_sum_sq` / `physicalSlowMask_sum_sq` leaves.
4. **`CommonWindow.labels`** (`CorrectionInitialization.lean:3753-3879`) — the actual `Finset` behind
   `unsignedLabels` — I did not read. If that window were empty for all `n` the artifact would be
   inconsistent with `partitionFactor_eq_one`, which is exactly §A2; I did not audit it directly.
5. **Parts B and C are children's work**, corroborated only by cross-reading their cited `file:line`s;
   I did not independently re-derive their dependency traces.
6. **`ActualGaussianCoverage` / `ParticularCopyBounds` `[Nonempty Label]` consumers** — I confirmed the
   five binder sites but did not trace which concrete instantiation supplies the instance at each call
   site. Given §A2 this is now a hygiene question, not a soundness one.
