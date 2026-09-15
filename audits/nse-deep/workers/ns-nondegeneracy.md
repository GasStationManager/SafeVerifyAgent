# Worker report — two collapse checks: `StripData` non-degeneracy and `SameCarrier`

Worker `ns-nondegeneracy`. Read-only audit of `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`.
**Nothing under that path was modified.** No `lake build` was run (no Mathlib on box); everything
below is source-level reading of actual statements and actual proof terms. Every `file:line` was
re-derived from the ORIGINAL (non-comment-stripped) file.

Handed up by sibling `ns-correction-step` (`workers/ns-correction-step.md`, residue items 4 and E3)
as "the single cheapest possible total-collapse check for the whole Navier-Stokes half".

## Headline

Both collapse checks come back **NEGATIVE — no collapse**, and in the `StripData` case the
sibling's characterisation of the collapse is **wrong in two independent ways**. I disagree loudly
below (§A0). One *new* degeneracy is real but is not a soundness defect: the label index type is
never proved nonempty and the artifact proves both branches (§A5, E2).

## Scope

I did not audit a file; I audited two *questions* across the tower, so the scope is a set of
passages, not a set of files. The 26 files I opened contain **2,227 decls** (1,703 `theorem`,
501 `def`/`abbrev`, 23 `structure`) over 26,396 lines; in-cone counts per file from `CONE.csv` are
in the table below. I read **41 declarations line-by-line, statement and proof term** (listed in
§Per-declaration findings, every one of them re-typed from the file, not from a docstring), plus a
mechanical token/numeral scan of **all 26 files in full** (§Kernel-risk). I did **not** read the
other ~2,186 decls of those files; that was not the assignment and I do not claim it.

| file | lines | decls | in-cone decls (CONE.csv) |
|---|---|---|---|
| `NavierStokes/WeightedClasses.lean` | 518 | 44 | 35 |
| `NavierStokes/WeightedRadialPrimitive.lean` | 1,106 | 72 | 60 |
| `NavierStokes/PhysicalMeanDomain.lean` | 1,762 | 114 | 99 |
| `NavierStokes/LocalSignedRequest.lean` | 1,026 | 67 | 70 |
| `NavierStokes/SignedMeanGain.lean` | 1,365 | 97 | 79 |
| `NavierStokes/ActualInitialization.lean` | 1,518 | 154 | 135 |
| `NavierStokes/ActualSignedMeanBinding.lean` | 700 | 65 | 37 |
| `NavierStokes/ActualSignedGeometry.lean` | 1,495 | 120 | 98 |
| `NavierStokes/BaseContextAssembly.lean` | 905 | 93 | 85 |
| `NavierStokes/NativeBandExtension.lean` | 1,016 | 76 | 70 |
| `NavierStokes/ActualSignedStageControls.lean` | 1,353 | 126 | 119 |
| `NavierStokes/R3CompactCandidate.lean` | 282 | 30 | 28 |
| `NavierStokes/R3/ProblemStatement.lean` | 223 | 24 | 19 |
| `NavierStokes/R3/Theorem.lean` | 82 | 6 | 3 |
| `NavierStokes/ProblemStatement.lean` | 169 | 24 | 21 |
| `NavierStokes/BaseResidual.lean` | 2,808 | 202 | 192 |
| `NavierStokes/FinalSlowBase.lean` | 713 | 91 | 70 |
| `NavierStokes/PrimaryRepresentatives.lean` | 787 | 93 | 87 |
| `NavierStokes/BaseChartJets.lean` | 935 | 68 | 61 |
| `NavierStokes/ActualInitialMean.lean` | 678 | 63 | 60 |
| `NavierStokes/HarmonicWaveInteraction.lean` | 1,136 | 87 | 61 |
| `NavierStokes/PrimaryTargetBounds.lean` | 1,036 | 81 | 79 |
| `NavierStokes/SignedStressPrimitive.lean` | 1,254 | 136 | 73 |
| `NavierStokes/ActualPrimaryBounds.lean` | 1,754 | 142 | 138 |
| `NavierStokes/ActualPrimaryCovariance.lean` | 1,317 | 116 | 105 |
| `NavierStokes/ActualSignedUnmaskedBounds.lean` | 458 | 36 | 33 |

(The per-file "in-cone decls" column is `CONE.csv`'s own count for that file and can exceed my
decl parse where `CONE.csv` counts `instance`/`lemma` separately; the two disagree by ≤ 9 on any
file and by 0 on 6 files. Neither number is load-bearing below.)

Task B (`SameCarrier`) and task C (the `t ≥ 1` regime of the potential) were delegated to two
read-only children on the same brief; their reports are `_sub-samecarrier.md` and
`_sub-potential-terminal.md`. §B and §C below carry their verdicts and say what I checked myself.

---

## A. `StripData` — is the class tower vacuous?

### A0. Where the briefing is wrong (disagreement, stated first)

The sibling wrote: *"`StripData` permits `domain = ∅`, `zeta = 0`, so every class is vacuous …
settled at `ActualInitialization.lean:651`."* Three claims; **one is right, two are wrong.**

1. **RIGHT:** the *record* permits `domain = ∅`. `StripData`
   (`NavierStokes/WeightedClasses.lean:31-43`) has 12 fields and **not one of them asserts
   `domain.Nonempty`**:
   ```lean
   structure StripData (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] where
     domain : Set D
     isOpen_domain : IsOpen domain
     epsilon : ℕ → ℝ ;  epsilon_pos ;  epsilon_le_one
     slow : ℕ → ℝ ;  one_le_slow
     delta : D → ℝ ;  delta_pos : ∀ x ∈ domain, 0 < delta x
     zeta : D → ℝ ;  zeta_smooth : ContDiffOn ℝ ∞ zeta domain
     zeta_nonneg : ∀ x ∈ domain, 0 ≤ zeta x
   ```
   `⟨∅, isOpen_empty, 1, …, 0, …, 0, …⟩` is a legal `StripData`, and with `domain = ∅` every field
   of `MemClass` (`:107-114`) is vacuous: `weight_nonneg` and `bounds` are guarded by
   `x ∈ s.domain`, and `smooth : ∀ n, ContDiffOn ℝ ∞ (f n) s.domain` is `ContDiffOn … ∅`, which is
   trivially true. So `MemClass`/`MeanClass`/`WaveClass`/`UniformClass` over an empty strip are
   **all** vacuous. The structural observation is correct and worth having.

2. **WRONG:** `zeta = 0` does **not** make the classes vacuous — it makes them **strictly
   stronger**. `majorant s w α C p n x = C * s.epsilon n ^ α * s.growth n x ^ p * w n x`
   (`WeightedClasses.lean:78-79`) and `MeanClass s α f = MemClass s (fun _ x => s.zeta x) α f`
   (`:115-116`), so with `zeta ≡ 0` the majorant is identically `0` and `MeanClass s α f` says
   `‖iteratedFDeriv ℝ j (f n) x‖ ≤ 0` for every order `j` and every `x ∈ domain` — i.e. *`f` and
   all its derivatives vanish on the domain*. A degenerate `zeta` therefore cannot hide a false
   estimate; it can only make the estimates unsatisfiable (or force the field to be 0). The
   collapse direction for `zeta` is the opposite of the one the briefing names.

3. **WRONG:** `ActualInitialization.lean:651` settles nothing. That line is
   `slow := BaseContextAssembly.slowScale`, the 10th field of the `geometry` structure instance at
   `:642-663`. There is no non-degeneracy content there or anywhere in `:640-670`. The question is
   actually settled 700 lines away in a different file — see A3.

### A1. Which strip do the headline theorems actually use?

One strip, reachable by two names that are *definitionally* equal:

* `ActualInitialization.strip = BaseContextAssembly.nativeStrip ActualPrimary.nominal
  ActualPrimary.standardRegion` (`ActualInitialization.lean:383-384`, in-cone).
* `ActualInitialization.geometry.strip` (`SignedMeanGain.lean:560-563` unfolds `Geometry.strip` to
  `LocalSignedRequest.movingStripData G.region G.patch.a G.patch.b …`).
* `theorem geometry_strip : geometry.strip = strip := rfl` (`ActualInitialization.lean:665`) — a
  bare `rfl`, so the two are the same term up to unfolding.
* `ActualPrimaryBounds.strip` (`:29`) is the same `nativeStrip nominal region` with
  `region = ActualSignedGeometry.standardSlowRegion …` (`:27`), i.e. the same strip again.
* The product/full strips are pullbacks of it: `ActualSignedCoherence.fullStrip =
  HarmonicWaveInteraction.productStrip ActualInitialization.geometry.strip` (`:29-30`),
  `ActualPrimaryBounds.fullStrip = productStrip strip` (`:930`),
  `ActualSignedStageControls.fullStrip = ActualPrimaryBounds.fullStrip` (`:545`), and
  `productStrip s = pullbackStrip s projection` (`HarmonicWaveInteraction.lean:76`), whose domain is
  the preimage of `s.domain` under `Prod.fst`. So *all* of them are nonempty iff the one strip is.

Its domain is characterised exactly, twice:

```lean
-- LocalSignedRequest.lean:191-198
theorem movingStrip_domain … (x : Point) :
    x ∈ (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).domain ↔
      x.2.1 ∈ U.carrier ∧ (profileMap coord x).1 ∈ Ioo a b := by
  change (x.2.1 ∈ U.carrier ∧ ((profileMap coord x).1 ∈ Ioo a b ∧ x.2.1 ∈ U.carrier)) ↔ _
  tauto
-- BaseContextAssembly.lean:236-245
theorem nativeStrip_mem (U) (x) :
    x ∈ (nativeStrip W U).domain ↔ x.2.1 ∈ U.carrier ∧
      PrimaryTargetBounds.profileRadius F.data.h (slowCoordinates x) ∈
        Ioo (PrimaryTargetBounds.leftRadius W) (PrimaryTargetBounds.rightRadius W)
```

So non-emptiness needs (i) `U.carrier ≠ ∅` and (ii) `a < b`. `SlowRegion`
(`LocalSignedRequest.lean:111-120`) also has **no** `carrier.Nonempty` field, so the same
structural gap exists one level down; and `a < b` is free from the patch:
`Patch.a_lt_b (P) : P.a < P.b := P.a_lt_left.trans (P.left_lt_right.trans P.right_lt_b)`
(`SignedStressPrimitive.lean:33-34`).

### A2. The concrete `zeta` is strictly positive, and that is proved in-cone

`zeta` on this strip is not an abstract weight, it is the explicit two-sided log-edge weight:
`logStripData` (`WeightedRadialPrimitive.lean:1005-1025`) sets
`zeta := fun z => zeta cL cR (logLength a b) (logPosition a z.1)` with
`zeta cL cR L x = edge cL x * edge cR (L - x)` (`:33`), and

```lean
theorem zeta_pos (cL cR : ℝ) {L x : ℝ} (hx : x ∈ Ioo 0 L) : 0 < zeta cL cR L x :=
  mul_pos (edge_pos cL hx.1) (edge_pos cR (sub_pos.mpr hx.2))     -- :46-47, in-cone
```

Both restrictions of it discharge `zeta_nonneg` *from strict positivity*, not from a `0 ≤ 0`:
`localStripData … zeta_nonneg := fun _ hp => (zeta_pos cL cR (logPosition_mem ha hp.1)).le`
(`PhysicalMeanDomain.lean:55`), same at `WeightedRadialPrimitive.lean:1025`. And strict positivity
is available *in-cone* as a statement, not only as a proof step:

* `NativeBandExtension.radialInterior_spec` (`:372-377`, in-cone) concludes, among four things,
  `0 < PrimaryTargetBounds.movingWeight W x.1`;
* `ActualSignedStageControls.fullStrip_zeta_pos` (`:764-775`, in-cone):
  `{x : FullPoint} (hx : x ∈ fullStrip.domain) : 0 < fullStrip.zeta x`, proved by rewriting
  `fullStrip.zeta` to `movingWeight` (`ActualSignedGeometry.viewStrip_zeta`, in-cone) and applying
  the previous item;
* `ActualSignedStageControls.covariance_margins` (`:777-784`, in-cone) *uses* `zeta` as a **lower**
  bound: `(coefficientLower ^ 2 * (choice B N0).inverseLower) * fullStrip.zeta x ≤
  SmoothCovariance.weights (matrix l k n x) (target l k n x) j`, with
  `coefficientLower_pos` (`:405`, in-cone).

So the `zeta`-degenerate instance is not merely harmless (A0.2), it is **excluded** for this strip.

### A3. The domain is nonempty, and it is proved with an explicit witness

This is the answer to the sibling's residue item 4, and it is not where the briefing said it is:

```lean
-- NavierStokes/ActualSignedMeanBinding.lean:48-52
theorem normalized_axis_scale : SimilarityCoordinates.coordinateQ (2 * h) (1, 0) = 1 := by
  symm
  exact SimilarityCoordinates.eq_coordinateQ (by linarith [outgoing.data.h_pos])
    (by linarith [outgoing.data.h_lt_half]) (by norm_num) (by norm_num)
    (by simp [SimilarityCoordinates.forwardScalar])

-- NavierStokes/ActualSignedMeanBinding.lean:54-67
theorem actual_strip_nonempty : ActualInitialization.geometry.strip.domain.Nonempty := by
  let G := ActualInitialization.geometry
  refine ⟨((G.patch.a + G.patch.b) / 2, ((1, 0), (0, 0))), ?_⟩
  apply (LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b
    G.leftWeight G.rightWeight G.patch.a_pos G.left_pos G.right_pos
    G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one _).mpr
  constructor
  · change 0 < (1 : ℝ) ∧ SimilarityCoordinates.coordinateQ (2 * h) (1, 0) ∈ Ioo (1 / 2 : ℝ) 2
    rw [normalized_axis_scale]
    norm_num
  · change ((G.patch.a + G.patch.b) / 2) /
      Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (1, 0)) ∈ Ioo G.patch.a G.patch.b
    rw [normalized_axis_scale, Real.sqrt_one, div_one]
    constructor <;> linarith [G.patch.a_lt_b]
```

Walk it: the witness is the point `x = ((a+b)/2, ((1,0),(0,0)))` — radial coordinate at the
mid-annulus, slow coordinate `(1,0)`. First bullet: membership in
`standardSlowRegion.carrier = {z | 0 < z.1 ∧ coordinateQ (2h) z ∈ Ioo (1/2) 2}`
(`ActualSignedGeometry.lean:30-46`) reduces by `change` to `0 < (1:ℝ) ∧ 1 ∈ Ioo (1/2) 2` after
rewriting with `normalized_axis_scale`, then `norm_num`. Second bullet: the profile radius is
`((a+b)/2)/√1 = (a+b)/2 ∈ Ioo a b` by `a < b`. No hypothesis, no `Classical.choice`, no
`Nonempty` instance argument. **The strip is nonempty. The class tower over it is not vacuous.**

Two honest caveats, both checkable:

* `actual_strip_nonempty` is **`in_cone = False`** in `CONE.csv`; its only consumer is
  `no_legacy_nativeData` (`:69-71`, also out of cone), which uses it to show
  `IsEmpty (SignedMeanGain.NativeData ActualInitialization.geometry)`. So no headline theorem
  *needs* the strip to be nonempty. That does not weaken the conclusion: emptiness is excluded as a
  **fact** about the concrete instance, and vacuity is a property of the instance, not of who cites
  it. It does mean the *audit* cannot say "the artifact relies on non-emptiness"; it relies on
  nothing here.
* The witness's slow time coordinate is `1`, not a physical time. On this chart the slow time is
  `const * (1 - t)` (`ActualSignedPhysicalGeometry.lean:140-155`, `commonGraph_slow`), so
  `0 < s.1 ⟺ t < 1`; the witness is an interior point of the pre-terminal region, consistent with
  §C.

### A4. What *would* have been vacuous (so the check is not empty of consequence)

Had the domain been empty, everything the tower states pointwise on it would be vacuous. Concretely,
in-cone examples I read: `MemClass`/`MeanClass`/`WaveClass`/`UnweightedClass`
(`WeightedClasses.lean:107-124`) and hence every `…_mem` / `…_class` estimate of
`CorrectionStep.lean` (264 in-cone theorems there per `COVERAGE.md`); `LabelSumBounds.UniformClass`
(`:33`); `SignedMeanGain.SmoothTriple/…` predicates at `SignedMeanGain.lean:823-827`;
`OperatorBounds`/`TensorClass` hypotheses at `:867-869`; `covariance_margins` (`:777`, in-cone) and
`fullStrip_zeta_pos` (`:764`, in-cone), which are quantified over `x ∈ fullStrip.domain`. So the
question was worth asking; the answer is that it is closed.

### A5. A *different* degeneracy that is real: the label index type is never proved nonempty

While closing A3 I found the collapse the briefing should have asked about. The wave/correction
machinery is indexed by

```lean
abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2     -- ActualInitialization.lean:27
abbrev Index (N : ℕ) := BaseChartJets.CellIndex F.data.h (activeLeft W) (activeRight W) N
                                                                -- PrimaryGeometryAssembly.lean:137
noncomputable def CellIndex (h lo hi : ℝ) (N : ℕ) :=
  {L : PositiveRepresentatives.ActiveLabel (PrimaryRepresentatives.referenceCompact h lo hi) //
    N ≤ L.val.1}                                                -- BaseChartJets.lean:825-827
noncomputable def ActiveLabel (K : Set Slow) :=
  {L : Label // 1 ≤ L.1 ∧ (K ∩ tsupport (nativeMask L.1 L.2)).Nonempty}
                                                                -- PrimaryRepresentatives.lean:91-92
```

A repo-wide grep finds **no** `Nonempty (Index …)`, `Nonempty (Label …)`, `Nonempty (SignedLabel …)`
or `Nonempty (CellIndex …)` anywhere (`NavierStokes/` has exactly one such instance, and it is for a
different type: `ActualParticularPhysicalData.lean:615 instance sourceIndex_nonempty`). Instead the
artifact **case-splits on emptiness** at four sites and proves the degenerate branch by hand:

```lean
-- ActualInitialMean.lean:318-324
  rcases isEmpty_or_nonempty (Index B N0) with he | he
  · let := he
    have hl (n : ℕ) : ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun l => isEmptyElim l)
    have hs : (seed B N0).oscillation = 0 := by
      funext n x i; simp [seed, bandSeed, LabelSumBounds.fieldSum, hl]
```
also `ActualSignedUnmaskedBounds.lean:161`, `:196`, `ActualSignedStageControls.lean:1132`. In the
nonempty branch they insert `he` as a local instance (`let := he`), which is how the many
`[Countable Λ] [Nonempty Λ]` lemmas (`ActualSignedControl.lean:379, 444, 571, 683`,
`ParticularCopyBounds.lean:453`, `ActualGaussianCoverage.lean:730`) are ever applied.

This is **honest and sound** — both branches are proved, so nothing is vacuous — but it means the
artifact does **not** know that its own oscillatory correction is present. If
`Index B N0 = ∅` for the selected `(B, N0)`, then `(seed B N0).oscillation = 0` by the artifact's
own lemma, every wave estimate is trivially true, and the entire signed/wave tower is void. Verdict
`SUSPICIOUS` (not `KERNEL-RISK`, not false). Escalation E2.

### A6. The zero field cannot satisfy the headline (so "everything survives if the field ≡ 0" is false)

The sibling carried up from `ipd-audit`: *"nothing in that file proves the fields are non-zero
anywhere: all 177 theorems survive if `cartesianPotential ≡ 0`."* True of that file, and
**false of the tower**. The top-level record demands blow-up as a field:

```lean
-- NavierStokes/R3/ProblemStatement.lean:92-109
structure CandidateProperties (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) : Prop where
  …
  energy_bounded : UniformFiniteEnergy (Ico 0 1) u
  speed_unbounded : SpeedUnboundedAtOne u
-- NavierStokes/ProblemStatement.lean:94-96
def SpeedUnboundedAtOne (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖
```

`theorem_1_1 : ProblemStatement.breakdownStatement` (`R3/Theorem.lean:46-49`, in-cone) produces
`CandidateProperties ν u p f K`; `u ≡ 0` fails `speed_unbounded` at `M = 1`. The same field appears
in the whole-space candidate record `R3CompactCandidate.Properties`
(`:24-37`, in-cone; `speed_unbounded : SpeedUnboundedAtOne u` at `:37`). Its mechanism is explicit
and quantitative:

```lean
-- NavierStokes/BaseResidual.lean:90-114
theorem baseVelocity_norm_at_origin … (hz : ∀ j, 0 < j → d.axial j (0,0) = 0)
    (h0 : 0 < d.axial 0 (0, 0)) {t : ℝ} (ht : t < 1) :
    ‖baseVelocity a h C d (t, 0)‖ = (1 - t) ^ (-CoordinateAlgebra.A h) * d.axial 0 (0, 0)
theorem baseVelocity_axis_tendsto_atTop … (h0 : 0 < d.axial 0 (0, 0)) :
    Tendsto (fun t : ℝ => ‖baseVelocity a h C d (t, 0)‖) (𝓝[<] 1) atTop
```
(both in-cone), discharged for the actual profile at `FinalSlowBase.lean:372-382`
(`axis_tendsto`, in-cone) with `h0` supplied by `W.axis.small.j_pos` (`:378`), where
`j_pos : 0 < j` is a **field** of the axis witness structure (`NaturalAxisData.lean:44`).

So: the non-degeneracy of the *solution* is asserted in-cone (`R3/ProblemStatement.lean:109`) and
comes from a strictly positive leading axial coefficient, on the axis `x = 0`, from the explicit
self-similar base — **not** from the correction tower. Structural consequence worth stating: a
vacuous correction tower would not damage `speed_unbounded`; it would damage `navier_stokes`,
`force_smooth`, `force_support` and `energy_bounded`, which is where the content of Theorem 1.1
actually lives.

---

## B. `SameCarrier` — delegated to child `samecarrier` (report `_sub-samecarrier.md`)

**Verdict: `hc` is discharged unconditionally. No collapse.** Its result, which I carry up and did
not re-derive myself:

* `SameCarrier` (`CorrectionStep.lean:2027`) is three genuine function equalities (frequency, phase,
  angular), not a vacuous predicate; when it fails, `addBlock` performs a *carrier substitution*, so
  the failure mode is **wrong value**, not vacuity
  (`HarmonicWaveInteraction.lean:440`: `(addBlock a b).osc = a.osc + (withCarrier a b).osc`,
  unconditional).
* `ActualCandidateConstruction.lean:80` `cycle_representation (B N0 j : ℕ)` has **no hypotheses** and
  passes `hc := cycle_signed_carrier B N0` (`:74`, no hypotheses) →
  `ActualCycleParameters.fixedParameters_signed_carrier` (`:499`) → `cycle_carrier` (`:62`), which is
  a `Nat.rec` on the cycle index `j`: base case `ActualInitialization.primary_tangent_carrier`
  (`:843`) `= ⟨rfl, rfl, rfl⟩`, step case `⟨ih.frequency, ih.phase, ih.angular⟩` (pure defeq —
  `addBlock` is `{a with velocity := …, pressure := …}`, the carrier fields are never touched); the
  signed leg is three `rfl`s (`ActualCycleParameters.lean:327, 332, 337`).
* Uniform in `n` and `j`, for arbitrary state and context. Not re-assumed by the enclosing theorem.
  `CycleStateCoherence.lean:601/609` is a *consumer*, not the discharge, and is out of cone.
  `invariant_*_signed_carrier` (`ActualCycleParameters.lean:398, 508`) do re-import the hypothesis
  through `CycleAnalyticInvariant.carrier` (`ActualCyclePreservation.lean:640, 698`), but
  `cycle_representation` does not use that path.
* Cone: `iterate_representation` (`CorrectionStep.lean:6963`), `ActualCandidateConstruction.lean:80`
  and the whole discharge chain are `in_cone = True`.
* Kernel: 0 `.rec`/`decide`/`Acc.rec`/`termination_by`/metaprogramming in that chain; `iterate` is
  structural `Nat.rec` with `iterate_succ := rfl`; largest numeral is the symbolic `2^(j+1)`.
* Child verdicts: OK 11, UNCLEAR 1, KERNEL-RISK 0, SUSPICIOUS 0.
* The child's own escalation is exactly my §A5: `hc`'s `∀ l : Index B N0` is vacuous if that type is
  empty — in which case `CycleRepresentation` forces `oscillation = 0` (degenerate, and *stronger*,
  not weaker). Same conclusion, independently reached.

---

## C. The `t ≥ 1` regime of the potential — delegated to child `potential-terminal`

Delegated to child `potential-terminal` (report `_sub-potential-terminal.md`) with the specific
questions: are the `else 0` branches at `InitialPhysicalData.lean:368, 376` live; is any in-cone
consumer's domain outside `preterminal = {w | w.1 < 1}`; and is there any nonvanishing/lower-bound
statement in the Navier-Stokes half. **See §Addendum for its verdict** (this section was written
before its reply; the addendum is appended verbatim when it lands).

What I can already say from my own reading, which bears directly on it:

1. The gate pattern is not confined to `InitialPhysicalData.lean`. The same
   `if 0 < <slow time> then <formula> else 0` shape occurs at `BaseContextAssembly.lean:454`
   (`if 0 < x.1 then rawStress H v upper B n x else 0`) and `:697`. On the strip it is never
   reached: `BaseContextAssembly.nativeStrip_time` (`:254-256`) gives
   `0 < x.2.1.1` for every `x ∈ (nativeStrip W U).domain`, from `U.time_pos`
   (`LocalSignedRequest.lean:119`), and `standardSlowRegion.carrier` requires `0 < z.1` by
   construction (`ActualSignedGeometry.lean:32`). So the `else 0` branch is off-domain by the same
   mechanism the sibling verified for `:368/:376`, and this is *structural*, not incidental.
2. The `t ≥ 1` regime cannot matter to the headline, because the headline never mentions it: every
   field of `CandidateProperties` (`R3/ProblemStatement.lean:94-109`) is quantified over
   `Ico (0:ℝ) 1`, `Ioo (0:ℝ) 1`, `preSingularDomain`, or (for `speed_unbounded`) `t ∈ Ioo 0 1` with
   `1 - δ < t`. There is no statement at or after `t = 1` to be made cheap by the `else 0` branch.
   The only thing that *would* have needed `t ≥ 1` is a continuation/uniqueness claim, and the
   artifact makes none: `R3CompactCandidate.lean:13` says so, and the competitor record
   `GlobalFiniteEnergySolution` (`R3/ProblemStatement.lean:125-135`) is the *hypothesis* of a
   refutation, not something the construction must extend to.
3. The nonvanishing question is answered in §A6 and it is answered in the artifact's favour:
   `speed_unbounded` (`R3/ProblemStatement.lean:109`) with the in-cone
   `Tendsto … atTop` at `BaseResidual.lean:104` and `FinalSlowBase.lean:372`.

---

## Per-declaration findings

41 declarations read line-by-line (statement **and** proof term). Cone column from `CONE.csv`
(`in_cone`). Verdict tags: `OK` = statement matches its name and the shown mechanism establishes it;
`SUSPICIOUS` = true but the surrounding claim is weaker/other than a reader would assume.

| # | decl | file:line | cone | what the statement says (my words) | mechanism (actual) | verdict |
|---|---|---|---|---|---|---|
| 1 | `WeightedClasses.StripData` | `WeightedClasses.lean:31` | ✓ | 12-field record: an open `domain`, positive band scales `epsilon ≤ 1`, `slow ≥ 1`, a positive `delta` and a smooth nonneg `zeta` on the domain | structure; **no** `Nonempty`, **no** `0 < zeta` | OK (gap is real, see A0) |
| 2 | `StripData.growth` | `:50` | ✓ | `slow n * max 1 (delta x)⁻¹` | def | OK |
| 3 | `StripData.one_le_growth` | `:53` | ✓ | `1 ≤ growth` | `one_le_mul_of_one_le_of_one_le` of the two field facts | OK |
| 4 | `majorant` | `:78` | ✓ | `C * epsilon n ^ α * growth n x ^ p * w n x` | def; `^α` is `rpow`, `^p` is `Monoid.npow` | OK |
| 5 | `majorant_nonneg` | `:81` | ✓ | nonneg if `0 ≤ C`, `0 ≤ w` | `mul_nonneg` ×3 + `rpow_pos_of_pos` | OK |
| 6 | `MemClass` | `:107` | ✓ | for all orders `m` there are `C ≥ 0, p` with all jets `≤ majorant` on the domain, **plus** `∀ n, ContDiffOn ℝ ∞ (f n) domain` | structure (3 fields) | OK — the `smooth` field is what stops the `iteratedFDeriv`-junk exploit; the bound alone would be satisfiable by junk |
| 7 | `MeanClass` / `WaveClass` / `UnweightedClass` | `:115, :118, :122` | ✓ | `MemClass` with `w = zeta`, `√zeta · P`, `1` | abbrev | OK; vacuous iff `domain = ∅` (A0.1) |
| 8 | `WeightedRadialPrimitive.zeta` | `WeightedRadialPrimitive.lean:33` | ✓ | `edge cL x * edge cR (L-x)` | def | OK |
| 9 | `zeta_pos` | `:46` | ✓ | `0 < zeta` on `Ioo 0 L` | `mul_pos (edge_pos …) (edge_pos …)` | OK |
| 10 | `logPosition_mem` | `:389` | ✓ | `X ∈ Ioo a b → log (X/a) ∈ Ioo 0 (log (b/a))` | `Real.log_pos`, `Real.log_lt_log` | OK |
| 11 | `logStripData` | `:1005` | ✓ | the concrete strip on `ℝ × E`: `domain = fst ⁻¹' Ioo a b`, log-edge `delta`/`zeta` | def; `zeta_nonneg` via `zeta_pos … |>.le` | OK — concrete, positive `zeta` |
| 12 | `logStrip_majorant_eq` | `:1029` | ✓ | on the strip, `majorant … = (C ε^α S^p) * logWeight cL cR a b p z.1` | `simp only [majorant, growth, logStripData, max_eq_right hi, …]; ring` | OK |
| 13 | `PhysicalMeanDomain.localStripData` | `PhysicalMeanDomain.lean:45` | ✓ | `logStripData` restricted to `stripDomain a b U = {p | p.1 ∈ Ioo a b ∧ p.2.1 ∈ U}` | record update; `zeta_nonneg` from `zeta_pos` | OK |
| 14 | `localSlowStripData` | `:1042` | ✓ | slow strip: `domain = U`, `delta = 1`, `zeta = 1` | record update over `MeanMomentBounds.slowStripData` | OK — `zeta ≡ 1`, so no `zeta` degeneracy possible here at all |
| 15 | `LocalSignedRequest.SlowRegion` | `LocalSignedRequest.lean:111` | ✓ | open `carrier` in the slow plane with `0 < s.1` and `coordinateQ ∈ Icc qlo qhi`, `0 < qlo` | structure | OK; **no** `carrier.Nonempty` field |
| 16 | `movingStripData` | `:182` | ✓ | pullback of `localStripData` along `profileMap coord` over `slowDomain U.carrier` | `localPullbackStrip` | OK |
| 17 | `movingStrip_domain` | `:191` | ✓ | membership ⟺ `x.2.1 ∈ U.carrier ∧ (profileMap coord x).1 ∈ Ioo a b` | `change` + `tauto` (definitional) | OK |
| 18 | `moving_radial_bounds` | `:256` | ✓ | on the strip, `x.1 ∈ Icc (√qlo · a) (√qhi · b)` | `q_mem`, `sqrt_le_sqrt`, two `nlinarith` | OK |
| 19 | `SignedMeanGain.Geometry.strip` | `SignedMeanGain.lean:560` | ✓ | the geometry's strip is `movingStripData region patch.a patch.b …` | def | OK |
| 20 | `Geometry.strip_subset` | `:578` | ✓ | `strip.domain ⊆ domain` | `movingStrip_domain … |>.mp hx |>.1` | OK |
| 21 | `Geometry.strip_radius_pos` | `:593` | ✓ | `0 < x.1` on the strip | `chartQ_pos`, `div_pos_iff`, resolve the negative branch | OK |
| 22 | `SignedStressPrimitive.Patch` / `Patch.a_lt_b` | `SignedStressPrimitive.lean:23, 33` | ✓ | `0 < a < left < right < b`; hence `a < b` | structure; two `trans` | OK — supplies (ii) of A1 |
| 23 | `ActualSignedGeometry.standardSlowRegion` | `ActualSignedGeometry.lean:30` | ✓ | `carrier = {z | 0 < z.1 ∧ coordinateQ (2h) z ∈ Ioo (1/2) 2}`, `qlo = 1/2`, `qhi = 2` | structure instance; `isOpen` from continuity of `coordinateQ` at positive time | OK |
| 24 | `BaseContextAssembly.nativeStrip` | `BaseContextAssembly.lean:231` | ✓ | the actual strip: `movingStrip` on `[leftRadius W, rightRadius W]` with edge weights `edgeExponent/4`, `1` | def | OK |
| 25 | `nativeStrip_mem` | `:236` | ✓ | membership ⟺ slow ∈ carrier ∧ profile radius ∈ `Ioo leftRadius rightRadius` | `rw` chain to `movingStrip_domain`, then `rfl` | OK |
| 26 | `nativeStrip_radius` | `:247` | ✓ | `0 < x.1` on the strip | `movingStrip_radial_bounds` + `mul_pos (sqrt_pos …) (leftRadius_pos)` | OK |
| 27 | `nativeStrip_time` | `:254` | ✓ | `0 < x.2.1.1` on the strip | `U.time_pos` composed with `nativeStrip_mem` | OK — this is what kills the `else 0` branches (C.1) |
| 28 | `nativeStrip_weight` | `:279` | ✓ | `zeta x = FinalSlowBase.weight W (normalizedCoordinates …).2` | `movingStripData_zeta` + `movingWeight_eq` | OK |
| 29 | `PrimaryTargetBounds.movingStripData_zeta` | `PrimaryTargetBounds.lean:770` | ✓ | the moving strip's `zeta` **is** `movingWeight W (meanPoint x)` | `unfold` + `meanPoint_scalar` + `rfl` | OK |
| 30 | `NativeBandExtension.radialInterior_spec` | `NativeBandExtension.lean:372` | ✓ | on the radial interior: `0 < time`, `0 < radius`, `η ∈ Ioo activeLeft activeRight`, **`0 < movingWeight`** | positivity chain: `leftRadius_pos`, `sqrt_pos`, `profileRadius_sq`, `Real.sq_sqrt` | OK — in-cone strict `zeta` positivity |
| 31 | `ActualSignedStageControls.fullStrip_zeta_pos` | `ActualSignedStageControls.lean:764` | ✓ | `0 < fullStrip.zeta x` on the full strip | `nativeStrip_mem` + `nativeStrip_time` → `radialInterior` → `radialInterior_spec.2.2.2`, then `viewStrip_zeta` rewrite | OK |
| 32 | `covariance_margins` | `:777` | ✓ | det gap ≥ `(1/5)²·detGap`, entries ≤ `5·entryBound`, and **weights ≥ `coefficientLower² · inverseLower · zeta x`** | via `copyPoint_radial`, `radialInterior`, `nativeQ ∈ Icc (1/2) 2` | OK — the in-cone *lower* bound that uses `zeta` |
| 33 | `HarmonicWaveInteraction.productStrip` / `class_slice` | `HarmonicWaveInteraction.lean:76, 83` | ✓ | product strip is a pullback along `projection`; slicing at `0` recovers the base class | `class_pullback`; `class_slice` needs `pullbackStrip (productStrip s) inclusion = s`, proved `by cases s; rfl` | OK (kernel note K1) |
| 34 | `ActualInitialization.strip` | `ActualInitialization.lean:383` | ✓ | the actual strip = `nativeStrip nominal standardRegion` | def | OK |
| 35 | `ActualInitialization.geometry` | `:642` | ✓ | the single `SignedMeanGain.Geometry` used by all stages (22 fields, incl. `epsilon := ChartScales.epsilon h`, `slow := slowScale` at **`:651`**) | structure instance; `inner_eq`/`outer_eq`/`length_eq` are `rfl` | OK — and note `:651` is a *scale field*, not a non-degeneracy proof |
| 36 | `geometry_strip` | `:665` | ✗ | `geometry.strip = strip` | `rfl` | OK |
| 37 | `ActualSignedMeanBinding.normalized_axis_scale` | `ActualSignedMeanBinding.lean:48` | ✗ | `coordinateQ (2h) (1,0) = 1` | `eq_coordinateQ` with `0 < 2h`, `2h < 1`, two `norm_num`, `forwardScalar` simp | OK |
| 38 | `actual_strip_nonempty` | `:54` | ✗ | **the actual strip's domain is nonempty** | explicit witness `((a+b)/2, ((1,0),(0,0)))`, `movingStrip_domain.mpr`, `norm_num`, `linarith [a_lt_b]` | OK — closes collapse check A |
| 39 | `ActualInitialMean` mean/covariance classes (empty-index branch) | `ActualInitialMean.lean:318-324` | ✓ | the covariance classes hold; proved by cases on `IsEmpty (Index B N0)` | empty branch: `activeLabels = ∅` → `oscillation = 0` → `MemClass.zero`; nonempty branch: `let := he` supplies the instance | SUSPICIOUS (A5/E2 — not false, but the artifact does not know its labels exist) |
| 40 | `R3.CandidateProperties` / `SpeedUnboundedAtOne` | `R3/ProblemStatement.lean:92`, `ProblemStatement.lean:94` | ✓ | 12-field record incl. `speed_unbounded`: ∀M>0 ∀δ>0 ∃t∈(0,1), t>1−δ, ‖u(t,x)‖>M | structure / def | OK — the tower's real non-degeneracy |
| 41 | `BaseResidual.baseVelocity_axis_tendsto_atTop` + `FinalSlowBase.axis_tendsto`/`speedUnbounded` | `BaseResidual.lean:104`, `FinalSlowBase.lean:372, 380` | ✓ / ✓ / ✗ | on-axis speed `= (1−t)^(−A h)·d.axial 0 (0,0) → ∞` | `negative_power_tendsto_atTop` × `h0 : 0 < d.axial 0 (0,0)`, `congr'` on `𝓝[<]1`; `h0` from `W.axis.small.j_pos` | OK — quantitative, uses strict positivity |

Verdict counts over the 41: **OK 39, SUSPICIOUS 2** (rows 39 and — carried from the child — the
`Index`-emptiness pattern; counted once here plus row 1's structural gap noted as OK-with-gap),
**UNCLEAR 0, KERNEL-RISK 0**.

---

## Kernel-risk assessment

Mechanical scan of **all 26 scope files in full** (comments stripped for counting, line numbers
re-derived on the original files).

**Vector (3) — custom metaprogramming: 0.** Across all 26 files: 0 `macro`/`elab`/`syntax`/
`set_option`/`native_decide`/`axiom`/`unsafe`/`partial`/`sorry`/`opaque`. The repo-wide negative
result holds on my scope too, so there is no finding here.

**Vector (1) — recursors / inductives: 0 inductives, 0 `termination_by`, 0 `Acc.rec`, 0 explicit
`.rec` in my 26 files.** The only kernel-relevant reduction I met is:

* **K1 (low).** `HarmonicWaveInteraction.class_slice` (`:83-91`) needs
  `pullbackStrip (productStrip s) (inclusion (D := D)) = s`, proved `by cases s; rfl`. After
  `cases s` both sides are literal 12-field `StripData.mk` applications, so the kernel checks
  definitional equality of 12 fields — 5 data fields by unfolding `pullbackStrip`/`productStrip`,
  7 `Prop` fields by proof irrelevance. This is structure-defeq + proof irrelevance, not recursor
  reduction, and it is the *safe* way to write it (`cases` avoids relying on structure eta). Cost is
  a constant number of whnf steps. No risk.
* The `Nat.rec` in §B's `cycle_carrier` is in the child's scope, not mine; the child reports it as
  structural with `iterate_succ := rfl`.

**Vector (2) — GMP / numeral arithmetic: 3 `decide` calls, all one-digit; largest literal 100000
in a ℝ hypothesis.** Complete census of my scope:

| site | file:line | what the kernel must do |
|---|---|---|
| `zero_pow (by decide : (2 : ℕ) ≠ 0)` | `ActualSignedMeanBinding.lean:295` | `Nat.decEq 2 0` → `Decidable.decide` on a 1-digit `Nat` |
| `show (1 : Fin 2) ≠ 0 by decide` | `PrimaryTargetBounds.lean:45` | `Fin.decEq` on `Fin 2` |
| `zero_pow (by decide : (2 : ℕ) ≠ 0)` | `ActualPrimaryCovariance.lean:330` | as row 1 |
| `hκsmall : κ ≤ 1 / 100000` | `SignedMeanGain.lean:463, 973, 1329` | `OfNat ℝ 100000` — a `Nat` literal in binary, consumed by `linarith`/`norm_num` rational certificates; no `Nat.pow/div/mod/gcd` anywhere |

Everything else numeric in scope is small: `1/2`, `2`, `1/5`, `5`, `3/8`, `1/16`, `1/10`, `9/10`,
`1/4`. No literal above 6 digits, and the 6-digit one is a real number, never a `Nat` the kernel
must factor, divide or exponentiate. `norm_num` counts per file are 0-20 (total 147) and each one
I read (`ActualSignedMeanBinding.lean:63, 51`; `ActualSignedGeometry.lean:44`) discharges a
one-digit rational inequality. **So the answer to "does the kernel actually have to perform the
risky computation" is: no, other than three 1-digit decidability checks.**

**Junk-value pass.** `iteratedFDeriv` appears 12× in `WeightedClasses.lean` and is a junk-returning
function off differentiability — but `MemClass` (`:107-110`) carries
`smooth : ∀ n, ContDiffOn ℝ ∞ (f n) s.domain` *beside* the bounds, so a class membership can never
be satisfied by junk jets. `Real.sqrt`/`Real.log`/division junk: `logPosition a X = log (X/a)` is
only ever used with `X ∈ Ioo a b`, `0 < a` (`logPosition_mem`, `:389`), and
`Real.sqrt (coordinateQ …)` only where `chartQ_pos` is available
(`LocalSignedRequest.lean:178-180`, used at `SignedMeanGain.lean:597`). The `if _ then _ else 0`
sites in scope (`BaseContextAssembly.lean:454, 697`) are gated by `0 < <slow time>`, which
`nativeStrip_time` (`:254`) provides on the whole strip — same resolution as `InitialPhysicalData`
`:368/:376`.

---

## Escalations

**E1 (highest, and it is the *only* thing left of collapse check A).** The oscillatory correction
may be indexed by an empty type and nobody knows.
`BaseChartJets.lean:825` / `PrimaryRepresentatives.lean:91` / `ActualInitialization.lean:27`;
case-splits at `ActualInitialMean.lean:318`, `ActualSignedUnmaskedBounds.lean:161, 196`,
`ActualSignedStageControls.lean:1132`.
*Question for an expert:* for the `(B, N0)` actually selected by
`ActualCandidate.selected_candidate_one_with_initial_rest` (consumed at `R3/Theorem.lean:32`), is
`Index B N0 = ActualPrimary.Label B N0 × Fin 2` nonempty — i.e. does some dyadic label of band
`≥ N` have `tsupport (nativeMask L.1 L.2)` meeting `referenceCompact h (activeLeft W)
(activeRight W)`?
*What would settle it:* one lemma. `PrimaryRepresentatives.physicalMask_active` (`:159-166`) already
manufactures an `ActiveLabel` from any nonzero mask value at a point of `K`; combined with
non-emptiness of `referenceCompact` and the fact that the dyadic masks at band `n` cover the plane,
`Nonempty (Index B N0)` should be a five-line proof. Its absence is the tell: either it is easy and
the authors did not need it (likely, since they proved both branches), or it is false for the
selected parameters and the whole wave tower is void. **Ask them to exhibit one label.**

**E2 (high, structural, cheap to state).** The blow-up in the headline is produced by the *base*,
not by the construction the 30,000 theorems are about.
`R3/ProblemStatement.lean:109` (`speed_unbounded`) ← `FinalSlowBase.lean:372-382` ←
`BaseResidual.lean:90-114` (`‖u(t,0)‖ = (1-t)^(-A h) · d.axial 0 (0,0)`, `h0 : 0 < d.axial 0 (0,0)`).
*Question:* since the singular behaviour is an explicit `(1-t)^(-A h)` on the axis, the entire
burden of Theorem 1.1 rests on `navier_stokes` + `force_smooth` + `force_support`
(`CompactPositiveTimeSupport`) + `energy_bounded` for the *same* fields. Is the force genuinely
prescribed *independently* of the velocity, or is `f` defined as the residual of the constructed
`u` (in which case `navier_stokes` is definitional and the content is entirely in the force's
smoothness, compact positive-time support, and the energy bound)?
*What would settle it:* read the definition of the `f` returned by
`ActualCandidate.selected_candidate_one_with_initial_rest` and check whether
`CandidateProperties.navier_stokes` is proved by `rfl`/`simp` from that definition. If it is, the
audit's attention should move entirely to `force_support`/`energy_bounded`.

**E3 (medium).** `actual_strip_nonempty` is out of cone. `ActualSignedMeanBinding.lean:54`,
`CONE.csv in_cone = False`.
*Question:* is there any in-cone theorem whose *content* (not just truth) requires the strip to be
inhabited — e.g. an "exists a point where the field is large" statement on the strip? If not, then
every estimate in the correction tower is a conditional statement that would survive an empty
strip, and the tower's connection to the headline runs entirely through the explicit field
*definitions*, not through the class memberships.
*What would settle it:* grep the cone for a statement of the form `∃ x ∈ strip.domain, …` or
`0 < ‖…‖` on the strip. I found none in my scope.

**E4 (low, but it is a name-vs-statement issue like the sibling's E6).**
`SignedMeanGain.Geometry`'s `strip`/`slowStrip`/`domain` triple (`:560-569`) has
`strip.domain ⊆ domain` (`:578`) but the two are *different* sets: many smoothness hypotheses are
stated on the larger `G.domain` (`SmoothOn G.domain …`, e.g. `:826, :827, :848, :856`) while the
estimates are on the smaller `G.strip.domain` (`:823-825`). That is the right direction (smoothness
assumed on more, bounds concluded on less), but a reader checking "the estimate is on the domain of
the fields" will conflate them.
*What would settle it:* nothing to verify — record it so that "in-cone estimate on the strip" is
never read as "estimate on the chart".

---

## Residue — what I could not check

1. **No build.** Everything is source reading. I did not confirm elaboration, implicit arguments,
   or instance resolution. In particular `geometry_strip := rfl` (`ActualInitialization.lean:665`)
   and `class_slice`'s `cases s; rfl` (`HarmonicWaveInteraction.lean:87-89`) are *claims of
   definitional equality* that I read as plausible and did not re-elaborate.
2. **`Index` non-emptiness (E1) is left open.** I established that no proof of it exists in the
   repo; I did **not** establish whether it is true. That requires the concrete `(B, N0)` chosen by
   `ActualCandidate` and the geometry of `referenceCompact`, which I did not open.
3. **The other strips.** I verified that all strips reachable from `ActualInitialization.geometry`
   are pullbacks/products of the one nonempty strip. I did **not** check
   `ActualWaveRegularity.particularStrip` (`:515`), `ActualInitialExcluded.gaussianStrip` (`:1058`),
   `ActualParticularBackground.nativeStrip` (`:161`), `ActualParticularStageControls.slowStrip`
   (`:413`), `ActualSignedPhysicalBinding.strip` (`:90`), `ReferencePath.fullStrip` (`:23`),
   `ActualCycleExcluded.SimilarityData.strip` (`:45`), or `MeanRankUpdate.normalizedStripData`
   (`:964`, out of cone). Each is a separate (cheap) non-emptiness question; the argument pattern of
   §A3 should transfer, but I did not do it.
4. **`edge`.** I read `edge_pos` (`WeightedRadialPrimitive.lean:44`) as a statement and used it; I
   did not read `FlatCutoff.edge`'s definition or verify that `edge` is not identically zero for
   some parameter (it cannot be, given `edge_pos`, but I did not check `edge_pos`'s own proof).
5. **The `9/10`/`1/10` gain chain and everything in the sibling's E1** is untouched here; my two
   questions were vacuity questions, and a non-vacuous tower can still be a wrong tower.
6. **`speed_unbounded`'s upstream witness.** `W.axis.small.j_pos` (`FinalSlowBase.lean:378`) is a
   *field* of a witness structure (`NaturalAxisData.lean:44`). I did not verify that the witness is
   constructed unconditionally (it comes from `Nonempty (NominalProfile.Witness F)`,
   `MatchingDebtBounds.lean:930`, under `F.data.h ≤ 1/1000`).


---

## Addendum — child `potential-terminal` verdict (task C), verbatim summary + my own check

Report: `_sub-potential-terminal.md`. Child verdicts: **OK 20, UNCLEAR 0, KERNEL-RISK 0,
SUSPICIOUS 0**, 2 medium + 1 low escalation.

**(a) Is the `t ≥ 1` regime live? NO for `InitialPhysicalData.lean:368/376.`** The child re-derived
the gate independently: `graph_time_pos` (`PhysicalMeanJetBounds.lean:226-229`) gives
`x.1.1 = (1 - w.1)/Q n`, and `preterminal = {w | w.1 < 1}` (`PhysicalWaveSum.lean:386`). Every
value-reading consumer is stated inside `t < 1`: `potential_smooth`
(`InitialPhysicalData.lean:1333`, `ContDiffOn … preterminal`), `potential_zero_exterior` (`:1743`,
`hw : w ∈ preterminal`), `velocity_chart_slow` (`:2812`, `ht : z.1 < 1`); the assembled consumers
`initialPotential_smooth` / `initialPotential_axisZeroOn`
(`ActualCandidateAssembly.lean:89, 144`, both in-cone) live on `physicalSublevel` /
`localDomain = {w | w.1 < 1 ∧ …}`. The `else` branch is reached by exactly **two** proofs in 2,855
lines (`:556`, `:578`, via `ite_eq_right`), and only to make four *support* lemmas global
(`:550, :572, :1048, :1054`). The author says as much at `:890-891` ("zero on the unused future
side").
**But the child adds a distinction I had missed:** regularity *across* `t = 1` **is** required — of
the **force**, on `futureDomain = Ici 0` (`ComparatorDefinitions.lean:149-151`) — and it is *not*
obtained from the `else 0` branch: it is built by `SpacetimeGluing.smoothExtension 1` out of the
`𝓝[<] 1` limit jets (`CandidateFromLimits.lean:82-87, 128-136`). So the `else 0` branch is not the
mechanism for the only across-`t=1` claim in the artifact. That extension deserves its own worker
(it is the one place where behaviour at and after the singular time is asserted).

**(b) Nonvanishing census: NOT none, and stronger than what I found in §A6.** The child's strongest
in-cone statement is a genuine Sobolev blow-up of the **actual assembled field**, not just the base:
`ActualCandidateAssembly.Witness` (`:1121`, def, `in_cone = True`) has as one of its conjuncts

```lean
-- NavierStokes/ActualCandidateAssembly.lean:1142-1144
      Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
        TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum) (t, x)))
        (𝓝[<] (1 : ℝ)) atTop ∧
```

and `ActualCandidateAssembly.witness (B N0 : ℕ) (hN : geometricThreshold ≤ N0) : Witness B N0 hN`
(`:1153`, `in_cone = True`) proves it. I verified both the text and the two cone rows myself. Plus
the mandatory record field `speed_unbounded` (§A6) with the zero field explicitly excluded.

So the correct form of the sibling's `ipd-audit` claim is: the *potential* is axis-**vanishing** by
design (`MixedAxisPreservation.PotentialStage.zero_germ`, `:179-190`;
`initialized_origin_blowup`, `:434-444`), and the blow-up lives in `base` — **not** "the tower is
satisfied by the zero field", which is false at candidate level
(`R3/ProblemStatement.lean:109`, `ActualCandidateAssembly.lean:1142`).

**Combined answer to the two collapse checks handed up by `ns-correction-step`:** both are
**closed negative**. The strip is nonempty (`ActualSignedMeanBinding.lean:54`), its `zeta` is
strictly positive in-cone (`ActualSignedStageControls.lean:764`,
`NativeBandExtension.lean:372`), `SameCarrier` is discharged unconditionally for all `n`
(`ActualCandidateConstruction.lean:80` → `ActualCycleParameters.lean:499, 62`), the `t ≥ 1` branch
is off-domain, and the constructed field is provably unbounded in `H³` as `t → 1⁻`
(`ActualCandidateAssembly.lean:1142`, in-cone). The one degeneracy that remains open is E1: the
label index type is never proved nonempty.
