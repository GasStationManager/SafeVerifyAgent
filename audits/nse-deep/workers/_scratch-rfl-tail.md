# Bare-`rfl` audit — ranks 18-25 by statement length (worker: rfl-tail)

Subject: theorems in `openai/NavierStokesAndEuler @ f9e8bc5` (local clone `/home/gsm/.openclaw/workspace/repos/NSE`)
whose whole proof is `rfl`. Source-level reading only (no `lake build` — no Mathlib on box).
All line numbers are 1-based in the f9e8bc5 checkout.

Threat vectors: (1) recursor reduction / `Acc.rec` / structure eta, (2) kernel GMP `Nat` arithmetic
(`decide`, `Nat.pow/div/mod`, `Fin`/`Matrix.cons` literal index resolution), (3) custom metaprogramming.
Classification tags (i)-(vi) as in the brief.

## Verdict summary

| # | site | verdict | classes | est. kernel steps |
|---|------|---------|---------|-------------------|
| 1 | `NavierStokes/ActualSignedStageControls.lean:111` `parameters_raw` | OK | (i),(ii) | ~10 delta + ~14 proj + betas |
| 2 | `NavierStokes/ActualPrimaryBounds.lean:1128` `fullCopy_slot` | OK | (i),(ii) | 3 delta + 1 `Prod.snd` proj |
| 3 | `NavierStokes/ParticularWaveBounds.lean:1592` `complexCopyPressure_eq_parts` | OK | (ii) | 1 delta + 8 beta |
| 4 | `NavierStokes/LocalSignedRequest.lean:523` `physicalBarSigma_profile` | OK (most interesting) | (i),(ii),(vi) | ~50-90 delta/proj/beta, Prod-eta load-bearing |
| 5 | `NavierStokes/CorrectionInitialization.lean:1193` `initialized_reconstructed` | OK | (i),(ii) | ~20 delta + ~20 proj |
| 6 | `Euler/PacketCorrectionGrowth.lean:29` `growthCoefficient_eq` | OK | (i),(ii) + 2 zeta | 4 delta + 2 zeta + ~8 proj |
| 7 | `NavierStokes/ActualCycleCoherence.lean:492` `afterParticular_pressure` | OK | (i),(ii) | ~12 delta + ~15 proj |
| 8 | `NavierStokes/MeanChartCompatibility.lean:1258` `stateDebt_eq_sourceDebt` | OK | (i),(ii) + `Pi`/`SMul` instance chain | ~25-60 delta/proj |

**Nothing in these 8 sites forces an iota CHAIN (case (iv)), a recursive `def` at a closed argument,
`Acc.rec`/`WellFounded.fix` unfolding, `decide`, or `Nat` literal arithmetic.** No `Matrix.of ![![…]]`
and no `Fin`/`List.get` literal index RESOLUTION (case (v)) occurs: the one site that contains
`![…]` vectors and `Fin 3` literals (site 8) carries them *identically on both sides and unapplied*,
so the kernel compares them syntactically instead of reducing them. No macro/elab/`set_option`/
`native_decide`/`axiom`/`unsafe`/`partial` appears in any file read here.

General observation confirming the brief's hint: every long statement here is long because of a long
ARGUMENT LIST (10-11 arguments of function type, plus `Finset`/`Oscillation`/`RankData` parameters).
Those arguments are *carried*, never computed: they appear at the same positions on both sides of the
equation, so the kernel compares them as identical subterms and never enters them. Length ≠ work.

---

## 1. `parameters_raw` — `NavierStokes/ActualSignedStageControls.lean:111-116`

```lean
theorem parameters_raw (l : SignedLabel B N0) (s : StripData Point)
    (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (k : Frequency) :
    ((parameters l).copyData s request).raw k = SignedWaveUpdate.coefficients
      (ActualPrimary.chartCoefficients l.2 l.1) (HarmonicWaveInteraction.productStrip s) (directions B)
      (matrix l k) (target l k) request (mask l k) (fundamental l k)
      (normalMotion l k) (action l k) l.2 := rfl
```

Sides. LHS `((parameters l).copyData s request).raw k` : `LinearWaveBounds.WaveCoefficients (Point × ℝ)`.
RHS `SignedWaveUpdate.coefficients a s' d H T R mask v Ndot A j` — 11 arguments, same type.

Defs followed:
* `parameters` — `ActualSignedStageControls.lean:97-109`: a `where`-style literal of
  `CorrectionStep.PeriodizedSignedParameters Point Frequency`; fields `base := ActualPrimary.chartCoefficients l.2 l.1`,
  `directions := directions B`, `matrix := matrix l`, …, `column := l.2`.
* `PeriodizedSignedParameters` structure — `NavierStokes/CorrectionStep.lean:4797-4808` (11 fields).
* `PeriodizedSignedParameters.native` — `CorrectionStep.lean:4813-4824` (`where` literal, field-by-field copy).
* `PeriodizedSignedParameters.copyData` — `CorrectionStep.lean:4828-4834` (`where` literal;
  `amplitude n i := ((p.native i).coefficients s request).amplitude n`, likewise `pressure`).
* `PeriodizedWaveBounds.CopyData` structure — `NavierStokes/PeriodizedWaveBounds.lean:758-763`;
  `CopyData.raw` — `PeriodizedWaveBounds.lean:769-771`:
  `{ a.background with amplitude := fun n => a.amplitude n i, pressure := fun n => a.pressure n i }`.
* `SignedParameters` structure — `CorrectionStep.lean:3475-3486`; `SignedParameters.coefficients` — `3488-3491`.
* `SignedWaveUpdate.coefficients` — `NavierStokes/SignedWaveUpdate.lean:212-217` → `homogeneousCoefficients` — `202-210`,
  which is `{ a with amplitude := fun n x => complexify (v n x), pressure := fun n => projectedPressure … }`.
* `WaveCoefficients` — `NavierStokes/LinearWaveBounds.lean:177-185`: 8 fields, no recursion, no index type.

What the kernel does. Delta-unfold `raw`, `copyData`, `parameters`, `native`, `SignedParameters.coefficients`,
`SignedWaveUpdate.coefficients`, `homogeneousCoefficients` (7 non-recursive defs, plus the `directions`
abbrev). Both `{x with …}` forms elaborate to `WaveCoefficients.mk` applications, so all six untouched
fields on the LHS are `(chartCoefficients l.2 l.1).radius` … `.frequency` — literally the same projections
the RHS produces. The two changed fields need `fun n => (mk … amp …).amplitude n` to meet `amp`: one
structure projection on a constructor application, then one beta (the projected field is itself a lambda
`fun n x => …`), so no eta is even required.

Class: **(i)** projections on explicit `where`/`{… with …}` literals + **(ii)** ~10 delta unfoldings of
non-recursive defs. No iota, no recursion, no literals.

Special check requested: **neither side is `Matrix.of ![![…]]`, a `Fin`-literal index application, or a
list-length claim.** The only `Fin` in sight is the field `column := l.2 : Fin 2`, where `l.2` is a
VARIABLE, copied unchanged to the RHS position `l.2` — the kernel never resolves a `Fin` literal, so
threat vector 2 is not touched. `Vec2`/`Mat2` arguments are opaque function-typed arguments.

Note: the generic form of this same statement, `PeriodizedSignedParameters.copyData_raw`
(`CorrectionStep.lean:4836-4837`), is also `rfl`; `parameters_raw` is its instance at `p := parameters l`
with the projections of `parameters` already reduced. Honest name, no over-claim.

**Verdict: OK.** ~10 delta + ~14 projection + a handful of beta steps; every one on a non-recursive def
or an explicit constructor application.

---

## 2. `fullCopy_slot` — `NavierStokes/ActualPrimaryBounds.lean:1128-1133`

```lean
theorem fullCopy_slot (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (x : ActualPrimary.FullPoint) :
    (fullCopy l n k x).2 =
      (ActualSignedGeometry.slotGeometry ActualPrimary.slots ActualPrimary.vectors_det (spatialLabel l)
        (ChartScales.nativeIndex ActualPrimary.h (spatialLabel l).1 - CommonWindow.index ActualPrimary.h n)).coordinates
          k (ActualSignedGeometry.meanEquiv.symm x.1).2 := rfl
```

Sides. LHS: second component of a `Native` (a nested product). RHS: a `Geometry.coordinates` application.

Defs followed:
* `fullCopy` — `ActualPrimaryBounds.lean:920-921`: `copyPoint l n k (ActualSignedGeometry.meanEquiv.symm x.1)`.
* `ActualPrimaryBounds.copyPoint` — `ActualPrimaryBounds.lean:126-128`:
  `ActualSignedGeometry.copyPoint ActualPrimary.slots ActualPrimary.vectors_det (spatialLabel l) n (CommonWindow.index ActualPrimary.h n) k`.
* `ActualSignedGeometry.copyPoint` — `NavierStokes/ActualSignedGeometry.lean:588-591`:
  body is an explicit pair
  `(slowChange h (Q chart) (Q l.1) x.1, (slotGeometry sys hdet l (ChartScales.nativeIndex h l.1 - common)).coordinates k x.2)`.
* `slotGeometry` — `ActualSignedGeometry.lean:368-370`; `spatialLabel` — `ActualPrimaryBounds.lean:103-104`;
  `ChartScales.nativeIndex` (abbrev) — `NavierStokes/ChartScales.lean:30`;
  `ActualPrimary.slots : PartitionedCovariance.SlotSystem (CoordinateAlgebra.D h) h radialVector temporalVector`
  — `NavierStokes/CorrectionInitialization.lean:3900-3901` (so the implicit `h` of `sys` is syntactically
  `ActualPrimary.h`, matching the RHS spelling).

What the kernel does: delta `fullCopy`, delta `ActualPrimaryBounds.copyPoint`, delta
`ActualSignedGeometry.copyPoint`, beta, then **one `Prod.snd` projection on an explicit `Prod.mk`**.
The result is character-for-character the RHS. `slotGeometry`, `Geometry.coordinates`, `meanEquiv.symm`
are never unfolded — they occur identically on both sides.

Special check requested: no `Matrix.of ![![…]]`, no `Fin` literal, no list length. The `-` in the
statement is ℕ truncated subtraction of two OPEN terms (`nativeIndex ActualPrimary.h (spatialLabel l).1`
and `CommonWindow.index ActualPrimary.h n`, both containing the variables `l`, `n`), so the kernel has
no literal to compute: `Nat.sub` is never reduced, it is only compared as an identical subterm.
Threat vector 2 untouched.

**Verdict: OK.** 3 delta + 1 projection + betas. The statement is long purely because the RHS spells out
`slotGeometry`'s 4 arguments (argument list, not computation).

---

## 3. `complexCopyPressure_eq_parts` — `NavierStokes/ParticularWaveBounds.lean:1592-1597`

```lean
theorem complexCopyPressure_eq_parts (t : TangentData P ProblemStatement.Space)
    (source : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (copy : Frequency) (frequency : ℝ) :
    complexCopyPressure t source g hab copy frequency = fun x =>
      copyPressure (realData t source) g hab copy frequency x +
        Complex.I * copyPressure (imagData t source) g hab copy frequency x := rfl
```

Sides. LHS: `complexCopyPressure` applied to 8 of its 9 arguments (a function `P × Plane → ℂ`).
RHS: an explicit lambda.

Defs followed:
* `complexCopyPressure` — `ParticularWaveBounds.lean:1575-1579`. Its body IS
  `copyPressure (realData t source) g hab copy frequency p + Complex.I * copyPressure (imagData t source) g hab copy frequency p`.
* `copyPressure` — `ParticularWaveBounds.lean:668-670` (never unfolded); `realData`/`imagData` — `1559-1565`
  (`{t with source := …}`, never unfolded).

What the kernel does: **one** delta unfolding plus 8 beta steps; the residual lambda is syntactically the
RHS. This is a pure "eta/definition restatement" theorem: it says the def is its own body. Note the
Volterra solver (`copySolve`) is *not* entered — the theorem is deliberately at function level (the
docstring at `1582-1583` says exactly that; docstring is author evidence only, but here it matches).

Class: **(ii)** only, 1 delta.

Side observation (elaboration-level, not kernel): line 1591 carries
`omit [NormedAddCommGroup P] [NormedSpace ℝ P] in`, i.e. the theorem claims not to need the `P`
instances although `complexCopyPressure` is declared under `variable {P} [NormedAddCommGroup P]
[NormedSpace ℝ P]` (`ParticularWaveBounds.lean:1556`). This is consistent with Lean's use-based
variable inclusion (`CommonCoverSolve.TangentData (P H : Type)` at `NavierStokes/CommonCoverSolve.lean:949`
constrains only `H`), so the instances are genuinely inert. Recorded only because `omit` narrows the
statement: the theorem is *weaker* (more general), never stronger, so it cannot over-claim.

**Verdict: OK.** Trivially true by definition; zero kernel risk; also zero mathematical content beyond
"the definition is the definition".

---

## 4. `physicalBarSigma_profile` — `NavierStokes/LocalSignedRequest.lean:523-529` (most interesting site)

```lean
theorem physicalBarSigma_profile (P : SignedStressPrimitive.Patch) (e : ℕ)
    (coord : ℝ) (f : Point → ℝ) (x : Point) :
    SignedStressPrimitive.physicalBarSigma P e (SimilarityCoordinates.coordinateQ coord) f
        (x.1, x.2.1) =
      Real.sqrt (MeanRankUpdate.chartQ coord x) *
        SignedStressPrimitive.barSigma P e (fun y => f (inverseProfileMap coord y))
          ((profileMap coord x).1, x.2.1) := rfl
```

Sides. Both sides are a real number; the RHS has an explicit `Real.sqrt (…) * …`.
**This is NOT an arithmetic identity closed by computation** — see below.

Defs followed:
* `physicalBarSigma` — `NavierStokes/SignedStressPrimitive.lean:869-871` = `physicalSigma P e q (torusAverage F)`.
* `physicalSigma` — `SignedStressPrimitive.lean:598-599`:
  `lengthScale q z.2 * sigma P e (nativeSource q F) (z.1 / lengthScale q z.2, z.2)`.
  So the RHS's `Real.sqrt … * …` shape is *literally the definition's shape*.
* `lengthScale q p = Real.sqrt (q p)` — `SignedStressPrimitive.lean:589`;
  `nativeSource q F z = F (lengthScale q z.2 * z.1, z.2)` — `590-591`.
* `barSigma` — `SignedStressPrimitive.lean:533-534` = `sigma P e (torusAverage F)`; `sigma` — `164-165`.
* `profileMap coord x = (x.1 / Real.sqrt (MeanRankUpdate.chartQ coord x), x.2)`,
  `inverseProfileMap coord x = (Real.sqrt (MeanRankUpdate.chartQ coord x) * x.1, x.2)` —
  `NavierStokes/LocalSignedRequest.lean:122-126`.
* `MeanRankUpdate.chartQ coord p = PhysicalCoordinateBounds.qCoord coord (chartInput p)` —
  `NavierStokes/MeanRankUpdate.lean:775-776`; `chartInput : ChartPoint →L[ℝ] ModelPoint` — `756-763`
  (a `ContinuousLinearMap` built from `fst/snd/comp/prod`); `qCoord a p = coordinateQ a (p.1, p.2.2)`
  — `NavierStokes/PhysicalCoordinateBounds.lean:35`; `coordinateQ` — `NavierStokes/SimilarityCoordinates.lean:124-127`
  (a `dite` over `0 < a ∧ a < 1 ∧ 0 < p.1` wrapping `Classical.choose`).
* `PressureStream.torusAverage f p = ∫ y in 0..1, torusInner f (p, y)`, `torusInner f p = ∫ x in 0..1, f (p.1.1, (p.1.2, (x, p.2)))`
  — `NavierStokes/PressureStream.lean:66-71`. Hence `Point = PressureStream.Lift Plane = ℝ × (Plane × (ℝ × ℝ))`.

What the kernel actually has to do (three obligations):

1. `Real.sqrt (coordinateQ coord x.2.1)` (LHS, via `lengthScale q (x.1, x.2.1).2` — one `Prod.snd`
   projection on an explicit `Prod.mk`) vs `Real.sqrt (MeanRankUpdate.chartQ coord x)` (RHS). Unfolding
   `chartQ`/`qCoord` gives `coordinateQ coord ((chartInput x).1, (chartInput x).2.2)`, and
   `chartInput` extracts `x.2.1.1` and `x.2.1.2`. So the obligation is
   `x.2.1 ≡ (x.2.1.1, x.2.1.2)` — **this is `Prod` structure ETA, case (vi), and it is load-bearing**:
   the proof would fail in a kernel without structure eta. Reducing `chartInput x` also means unfolding
   Mathlib's bundled-morphism stack (`ContinuousLinearMap.prod/comp/fst/snd`, then the `DFunLike.coe`
   projections `ContinuousLinearMap.toLinearMap → LinearMap.toAddHom → toFun`): ~8 defs and ~3-4
   projection layers each, i.e. the bulk of this site's step count. All non-recursive, all on explicit
   structure literals.
2. `x.1 / Real.sqrt (coordinateQ coord x.2.1)` (LHS first component) vs `(profileMap coord x).1` (RHS):
   one `Prod.fst` projection on the explicit pair in `profileMap`, then the same eta identity as (1).
3. The integrand functions must agree: `nativeSource (coordinateQ coord) (torusAverage f)` (LHS) vs
   `torusAverage (fun y => f (inverseProfileMap coord y))` (RHS). Both delta-unfold to nested
   `intervalIntegral`s of lambdas; comparing the bodies gives
   `f (Real.sqrt (coordinateQ coord z.2) * z.1, (z.2,(u,y)))` on both sides, again via the eta identity
   (`chartQ` of the lifted point ignores the torus components `(u,y)`). The Bochner integral itself is
   NEVER unfolded — same head `intervalIntegral`, arguments compared pairwise.

Crucially, `Real.sqrt`, `*`, `/` are compared as *symbolic terms with identical arguments*: no real
arithmetic is (or could be) computed. `coordinateQ`'s `dite`/`Classical.choose` is likewise never
reduced — it appears identically on both sides, so the kernel never has to decide the `dite` condition.

Class: **(vi)** `Prod` eta (essential) + **(i)** projections on explicit pairs/structure literals +
**(ii)** ~15 delta unfoldings (plus the CLM coercion stack). No iota chain, no `Nat` literal, no recursion.

Mathematical reading: the statement is a genuine change-of-variables identity ("the physical bar-sigma
in the `q` chart is `sqrt q` times the profile-pulled bar-sigma"), and it holds *definitionally* only
because `physicalSigma` was DEFINED as `lengthScale * sigma(rescaled)`. So it is a definitional
bookkeeping lemma dressed as a geometric fact — worth knowing, but not an independent check of the
change of variables. Not vacuous, not junk-value dependent. The sibling `rfl` lemmas
`chartQ_profileMap`/`chartQ_inverseProfileMap` (`LocalSignedRequest.lean:128-133`) rely on the same
"`chartQ` only reads `x.2.1`" fact.

**Verdict: OK** (with the flag: this is the one site in my batch where kernel structure-eta is
required, and where the kernel walks a Mathlib bundled-morphism coercion chain). Estimate ~50-90
delta/projection/beta steps; zero iota over a recursive def.

---

## 5. `initialized_reconstructed` — `NavierStokes/CorrectionInitialization.lean:1193-1198`

```lean
theorem initialized_reconstructed (p : ReconstructionData) (r : RankData S) (h : ℝ)
    (axial : S × PressureStream.Plane) (c : Context (Lift S))
    (labels : Finset ι) (pieces : ι → PrimaryPiece (Lift S × ℝ))
    (baseError : Oscillation (Lift S)) :
    reconstructPressure p c (initialized p r h axial c labels pieces baseError) =
      initialized p r h axial c labels pieces baseError := rfl
```

Sides: two `CorrectionState.State (Lift S)` records. Claim: `initialized` is a fixed point of
`reconstructPressure`.

Defs followed:
* `State` structure (5 fields) — `NavierStokes/CorrectionState.lean:65-70`.
* `reconstructPressure` — `CorrectionState.lean:271-274`:
  `{ u with pressure := fun n => PressureStream.meanPressure … (u.gr c n) }`.
* `State.gr` — `CorrectionState.lean:117-118` = `MeanIncrementBounds.gr c.operators c.base s.mean s.covariance`;
  `State.covariance` — `98-99` = `bilinearCovariance s.oscillation s.oscillation`.
  **`gr` reads only `mean` and `oscillation`.**
* `initialized` — `CorrectionInitialization.lean:1146-1150` = `retainPressureAlias p c (afterRank …)`;
  `retainPressureAlias` — `1141-1144` = `{ u with errors := ⟨…⟩ }` (touches only `errors`);
  `afterRank` — `1133-1137` = `rankStage p r axial c (afterTemporal …)`;
  `rankStage` — `CorrectionState.lean:444-447` = `reconstructPressure p c (u.addIncrement …)`;
  `seed` — `CorrectionInitialization.lean:1096-1102`.

What the kernel does. Write `V := (afterTemporal …).addIncrement (rankIncrement …) 0 0 0 ExcludedErrors.zero`.
Then `afterRank = reconstructPressure p c V` and `initialized = { afterRank with errors := ⟨…⟩ }`, i.e. a
`State.mk` application. The LHS is `State.mk I.mean (fun n => meanPressure … (I.gr c n)) I.oscillation
I.oscillatoryPressure I.errors` with `I := initialized …`. Each `I.<field>` projection reduces through
the two `{… with …}` constructor applications to `V.<field>` (for `mean`, `oscillation`,
`oscillatoryPressure`) and to the explicit `errors` literal. So the only real obligation is
`fun n => meanPressure … (I.gr c n) ≡ afterRank.pressure = fun n => meanPressure … (V.gr c n)`, which
holds because `I.mean ≡ V.mean` and `I.oscillation ≡ V.oscillation` (pressure/errors edits do not touch
them). `State.addIncrement`, `temporalStage`, `rankIncrement`, the `Finset.sum`s in `seed`, and
`PressureStream.meanPressure` are NEVER unfolded — they sit at identical positions on both sides.
`labels : Finset ι` is a variable, so no `Finset.sum` is ever evaluated.

Class: **(i)** + **(ii)**, ~20 delta unfoldings of non-recursive defs and ~20 structure projections on
constructor applications. No iota, no literal arithmetic, no recursion.

Mathematical reading: the name is honest — the claim is exactly "the initialized state is already
pressure-reconstructed", true because (a) `initialized` ends with `rankStage`, whose last step IS
`reconstructPressure`, and (b) the later `retainPressureAlias` only edits `errors`, which `gr` ignores.
Not vacuous; hypotheses (`labels`, `pieces`, `baseError`, `r`, `h`, `axial`) are carried, not used, which
is expected for a definitional projection lemma. `omit [FiniteDimensional ℝ S] in` (line 1192) only
weakens the binders.

**Verdict: OK.**

---

## 6. `growthCoefficient_eq` — `Euler/PacketCorrectionGrowth.lean:29-35`

```lean
theorem growthCoefficient_eq (B0 B1 κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    growthCoefficient D P Kc B0 B1 =
      energyConstant P ((sourceMetricBudget D P κ hκ Z G q).growth0 P B0)
        ((sourceMetricBudget D P κ hκ Z G q).growth1 P)
        ((sourceMetricBudget D P κ hκ Z G q).multiplier P)
        Kc.B Kc.M B0 B1 Kc.A0 Kc.A2 (sourceMetricBudget D P κ hκ Z G q).c := rfl
```

**Answer to the brief's question: `rfl` here is NOT closing a real-arithmetic equation. Both sides have
the SAME head `energyConstant`, so the kernel compares 11 argument positions pairwise; every position
becomes syntactically identical after delta/zeta/projection. No `ℝ` operation is ever evaluated.**

Defs followed:
* `growthCoefficient` — `Euler/PacketCorrectionGrowth.lean:20-27`:
  `let c := D.inverseBound⁻¹; let first := inverseMetricFirstBound D;`
  `energyConstant P (growthBudgetBase c (inverseMetricTimeBound D) first + growthBudgetSlope c first*sobolevEmbeddingConstant P 6*B0) (growthBudgetSlope c first*sobolevEmbeddingConstant P 6*metricAmplification c) (inverseMetricBound D/c) Kc.B Kc.M B0 B1 Kc.A0 Kc.A2 c`.
* `energyConstant (g0 g1 k B M B0 B1 A0 A2 c : ℝ)` — `Euler/NonlinearEnergyConstants.lean:28-30` (never unfolded).
* `MetricBudget.growth0` — `Euler/CorrectionEnergyData.lean:147-149` = `growthBudgetBase K.c K.time K.first + growthBudgetSlope K.c K.first*sobolevEmbeddingConstant period 6*B0`;
  `growth1` — `152-154`; `multiplier` — `157-158` = `K.bound/K.c`.
* `sourceMetricBudget` — `Euler/PacketCorrectionMetricBudget.lean:93-113`: a `where` literal with
  `c := D.inverseBound⁻¹` (line 100), `bound := inverseMetricBound D` (105),
  `first := inverseMetricFirstBound D` (106), `time := inverseMetricTimeBound D` (107).
* `inverseMetricBound/FirstBound/TimeBound` — `PacketCorrectionMetricBudget.lean:44-49`.

Position-by-position: `growth0 ↦ growthBudgetBase K.c K.time K.first + …` matches
`growthBudgetBase c (inverseMetricTimeBound D) first + …` with `K.c ↦ D.inverseBound⁻¹`,
`K.time ↦ inverseMetricTimeBound D`, `K.first ↦ inverseMetricFirstBound D`; argument ORDER and the
`+`/`*` association are identical, which is why `rfl` can work at all. `multiplier = K.bound/K.c`
matches `inverseMetricBound D/c`. Last argument `K.c` matches `c`.

What the kernel does: 4 delta (`growthCoefficient`, `growth0`, `growth1`, `multiplier`) + 1 delta of
`sourceMetricBudget` + 2 zeta (`let c`, `let first`) + ~8 projections on the 24-field `where` literal
(proof-valued fields are carried untouched, never re-checked) . `sobolevEmbeddingConstant P 6` occurs
with the same literal `6` on both sides, so it is compared, not reduced: no `Nat` literal arithmetic and
no `Fin`/`Matrix` indexing. `MetricBudget` is indexed by `(q+1)` with `q` a VARIABLE — symbolic
`Nat.succ`, so even the type-level index needs no computation.

Mathematical reading (a real, if benign, observation): `κ`, `hκ`, `Z`, `G`, `q` are **dead parameters of
the equation** — they occur only inside `sourceMetricBudget …`, whose four relevant fields ignore them.
So the theorem, despite its wide binder list, says only: "the growth constants of the source metric
budget are the fixed constants of `D` and `P`". `rfl` succeeding is positive evidence that there is no
hidden dependence on the correction data. The consumer `growthCoefficient_pos`
(`PacketCorrectionGrowth.lean:37-44`) instantiates `κ := 0`, `Z := G := (Field.zero …).toFieldTower`,
`q := 0` to import `constants_nonneg` — a legitimate use, not a vacuity dodge. The name does not
over-claim (`_eq` for an equation).

**Verdict: OK.** ~15 total reduction steps; the "arithmetic" is structural, not computed.

---

## 7. `afterParticular_pressure` — `NavierStokes/ActualCycleCoherence.lean:492-497`

```lean
theorem afterParticular_pressure :
    (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge (commonContext B)
      ((ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients
        (commonContext B) x.state)).pressure =
      ((ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients
        (commonContext B) x.state).pressure := rfl
```

Sides: two `ScalarField (Lift S)` = `ℕ → Lift S → ℝ` fields. Same shape as site 5 (reconstruction is
idempotent), but with the gauge supplied from a different route on each side.

Defs followed:
* `VariableGaugeMean.reconstructState` — `NavierStokes/VariableGaugeMean.lean:517-523`:
  `{ u with pressure := fun n => meanPressure g.radial.exponent … (g.length n) g.radial.radialDirection (u.gr c n) }`.
* `CycleParameters.afterParticular` — `NavierStokes/CorrectionStep.lean:5042-5044` =
  `gaugeWaveStage p.gauge c u (p.particularVelocity …) (p.particularPressure …) ⟨0, p.particularGaussian …, 0⟩`.
* `gaugeWaveStage` — `CorrectionStep.lean:3328-3332` = `reconstructState g c (u.addIncrement zeroTriple 0 w q e)`.
* `fixedParameters` — `NavierStokes/ActualCycleParameters.lean:415-419` (via `CycleParameters.ofGeometry`);
  the projection fact `(fixedParameters B N0).gauge = ActualInitialization.geometry.gauge` is itself
  `rfl` at `ActualCycleParameters.lean:431-432`, so the two spellings of the gauge in this statement
  are definitionally the same term.
* `State.gr`/`State.covariance` — `CorrectionState.lean:117-118`, `98-99` (read only `mean`,`oscillation`).

What the kernel does. With `V := x.state.addIncrement zeroTriple 0 (particularVelocity …) (particularPressure …) ⟨0,…,0⟩`,
`afterParticular = reconstructState G c V` where `G` reduces (delta `fixedParameters` + delta
`ofGeometry` + projection) to `ActualInitialization.geometry.gauge` — the same term the LHS spells
explicitly. LHS `.pressure` field is `fun n => meanPressure … ((reconstructState G c V).gr c n)`; the
RHS is `fun n => meanPressure … (V.gr c n)`. Since `reconstructState` edits only `pressure`,
`(reconstructState G c V).mean ≡ V.mean` and `.oscillation ≡ V.oscillation` by projection on the
`State.mk` application, so the two `gr` arguments are identical. `addIncrement`, `particularVelocity`
(a `LabelSumBounds.fieldSum`), `particularPressure` (a `∑ l ∈ v.labels n`), and `meanPressure` are never
unfolded. The `Finset.sum` over `v.labels n` is never evaluated (`x.coefficients` is a variable).

Class: **(i)** + **(ii)**, ~12 delta + ~15 projections. No iota, no recursion, no literal arithmetic.

Note this theorem carries no `include H W`, unlike its neighbours at `ActualCycleCoherence.lean:484-490`
— i.e. it needs none of the coherence hypotheses, consistent with a purely definitional claim, and it
does not smuggle a hypothesis that would make a substantive claim trivial.

**Verdict: OK.**

---

## 8. `stateDebt_eq_sourceDebt` — `NavierStokes/MeanChartCompatibility.lean:1258-1263`

```lean
theorem stateDebt_eq_sourceDebt (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) (n : ℕ) (s : S) :
    CorrectionState.debt c u n s =
      sourceDebt (u.gr c n)
        ((MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2 1) n)
        ((MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2 2) n) s := rfl
```

Sides: both are `Fin 3 → ℝ` (`MeanRankUpdate.Debt = FiveRowRank.Debt`, `NavierStokes/MeanRankUpdate.lean:24`)
given as `![_,_,_]` vector literals.

Defs followed:
* `CorrectionState.debt` — `NavierStokes/CorrectionState.lean:242-244`:
  `fun n x => ![pressureDefect c u n x, thetaDefect c u n x, axialDefect c u n x]`.
* `pressureDefect` — `CorrectionState.lean:229-230` = `radialMoment 0 (u.gr c)`;
  `thetaDefect` — `232-234` = `radialMoment 2 (thetaAxial c.base u.mean + u.covariance 2 1)`;
  `axialDefect` — `236-239` = `radialMoment 1 (axialAxial c.base u.mean + u.covariance 2 2) - (1/2 : ℝ) • radialMoment 2 (u.gr c)`.
* `radialMoment k f = fun n p => PressureStream.pressureMass (fun x => x.1 ^ k * f n x) p` — `CorrectionState.lean:226-227`.
* `sourceDebt g qθ qz s = ![sourceMoment 0 g s, sourceMoment 2 qθ s, sourceMoment 1 qz s - (1/2 : ℝ) * sourceMoment 2 g s]`
  — `MeanChartCompatibility.lean:1206-1207`; `sourceMoment m f s = PressureStream.pressureMass (fun z => z.1 ^ m * f z) s` — `1203-1204`.
* `thetaAxial`/`axialAxial` — `NavierStokes/MeanIncrementBounds.lean:313-314`, `319-320`;
  `Field D = ℕ → D → ℝ` — `MeanIncrementBounds.lean:24`.

What the kernel does, component by component:
* component 0: `radialMoment 0 (u.gr c) n s` vs `sourceMoment 0 (u.gr c n) s` — after delta+beta both are
  `pressureMass (fun z => z.1 ^ 0 * u.gr c n z) s`. The exponent `0` is a ℕ literal, but it sits in
  `HPow ℝ ℕ ℝ` at the same position on both sides, so `Monoid.npow` is never entered.
* component 1: same, with `2` and the shared subterm `thetaAxial c.base u.mean + u.covariance 2 1`.
  Note the RHS repeats this subterm VERBATIM from the definition, so the `(2 : Fin 3)`/`(1 : Fin 3)`
  `OfNat` literals — which would otherwise reduce through `Fin.instOfNat`/`Nat.mod` — are compared as
  identical terms and never reduced. **This is why case (v) is avoided.**
* component 2 is the only nontrivial one: the LHS is `(A - (1/2 : ℝ) • B) n s` at the `Field` (Pi) level,
  the RHS is `A n s - (1/2 : ℝ) * B n s` at `ℝ`. The kernel must unfold `Pi.instSub` twice
  (structure-literal projections), and then identify `(1/2 : ℝ) • r` with `(1/2 : ℝ) * r`, i.e. walk the
  `SMul ℝ ℝ` instance chain down to `Mul.toSMul` (plus `Pi.instSMul` twice). That is a chain of
  instance-projection/delta steps — 10-40 steps, all on non-recursive structure-literal instances,
  no arithmetic. `(1 / 2 : ℝ)` itself is compared syntactically (`OfNat 1 / OfNat 2`), never evaluated.
* the two `![…]` vectors are compared as `Matrix.vecCons` applications with pairwise-defeq arguments;
  **neither side is ever APPLIED to an index**, so no `Fin`-literal / `Matrix.cons` index resolution and
  no kernel `Nat` comparison occurs. `Matrix.of ![![…]]` does not appear.

Class: **(i)** + **(ii)** + a `Pi`/`SMul` instance-projection chain. No iota over a recursive def, no
`Nat` literal arithmetic, no recursion.

Mathematical reading: the name is accurate and the content is a real (definitional) bridge: the state's
three-row debt equals the "source" debt of `(gr, θ-flux, z-flux)`. Both sides are definitions written to
match, so this lemma re-expresses `debt` in the `sourceMoment` vocabulary used by the transport lemmas
around it (e.g. `sourceMoment_coverPull`, `MeanChartCompatibility.lean:1209`). Not vacuous, no junk
values exploited (`radialMoment`/`sourceMoment` are total integrals, defined for all inputs).

**Verdict: OK.**

---

## Cross-site notes for the lead auditor

* Every site is an "unfold the definition" lemma. In all 8, the LHS head is a `def` whose body, after
  delta + beta + zeta + structure projection (+ Prod eta at site 4), is literally the RHS. That is the
  cheapest possible use of `rfl` for the kernel.
* Recursive definitions, `Nat.rec`, `Acc.rec`, `WellFounded.fix`, `decide`, `Nat.pow/div/mod/beq/ble`,
  and closed-argument iota chains (case (iv)) are **absent** from all 8 obligations. The only ℕ
  operations visible (`-` at site 2, `^0/^1/^2` at site 8, `q+1` at site 6, `6` at site 6) are on open
  terms or occur identically on both sides, so the kernel compares instead of computing.
* Where structure literals with proof fields are projected (site 6's 24-field `MetricBudget`), the kernel
  projects one field out of a constructor application; the proof-valued siblings are carried, not
  re-elaborated.
* One genuine kernel-feature dependency: **site 4 needs `Prod` structure eta** (`x.2.1 ≡ (x.2.1.1, x.2.1.2)`),
  and also walks Mathlib's `ContinuousLinearMap`/`DFunLike` coercion stack. Still cheap and standard.
* No macro/`elab`/`syntax`/`set_option`/`native_decide`/`axiom`/`unsafe`/`partial` in any of the ~15
  files read for this batch, consistent with the repo-wide scan.
* Author-evidence note: two docstrings in this batch describe the *purpose* of a `rfl` lemma
  ("keep the finite-path solver opaque", `ParticularWaveBounds.lean:1582-1583`; "The row order is exactly
  `(P, Jθ, Jz)`", `CorrectionState.lean:241`). Both are consistent with the code I read, but they are
  author claims, not proof content.
