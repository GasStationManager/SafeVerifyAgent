# Worker report: is the wave/correction tower load-bearing for the headline?
Repo: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5). READ-ONLY, no build (no Mathlib on disk). Source reading + grep only.

QUESTION: if `Index B N0` were empty, would the headline theorem still be PROVED?

## VERDICT: (a) — with one flagged residual risk

Every mandatory field of the headline candidate record is discharged by a chain that (i) never takes an
inhabitant of `Index`/`Label`/`SignedLabel`/`CellIndex`, (ii) never carries an unresolved `[Nonempty …]`
instance for those types, and (iii) in the only four places where emptiness is even mentioned, proves the
SAME conclusion in the empty branch. The blow-up (`speed_unbounded`, the only non-trivial field) is carried
entirely by ONE index-free positive constant of the self-similar slow base, and the wave tower is *proved to
vanish in a neighbourhood of the axis where the blow-up is measured*. So the tower is decoration for the
headline, not load-bearing: a structural finding, not a defect.

Residual risk I could NOT settle from source alone (no build): the tower IS in the chain of the residual
decay rate `gain J → ∞` (`StageEstimates.gain_top` / `finite_residual`), which feeds `VanishingJointJets`
and hence smoothness of the force across t = 1. See §5.

## 1. The headline and its mandatory fields

`NavierStokes/R3/Theorem.lean:46`
```
theorem theorem_1_1 : ProblemStatement.breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hg, _⟩ := theorem_1_1_with_initial_rest ν hν
  exact ⟨u, p, f, K, hc, hg⟩
```
`NavierStokes/R3/ProblemStatement.lean:150`
```
def breakdownStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ u p f K, CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalFiniteEnergySolution ν f)
```
`NavierStokes/R3/ProblemStatement.lean:92-109` — `CandidateProperties` fields: `velocity_smooth`,
`pressure_smooth`, `support_compact`, `velocity_support`, `pressure_support`, `force_smooth`,
`force_support`, `zero_initial_velocity`, `divergence_free`, `navier_stokes`, `energy_bounded`,
`speed_unbounded : SpeedUnboundedAtOne u` (:109).
`NavierStokes/ProblemStatement.lean:94`
```
def SpeedUnboundedAtOne (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ → ∃ t x, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖
```
(`NavierStokes/R3CompactCandidate.lean:24-37` `Properties` is the same list in "option (C)" form, also with
`navier_stokes` :36 and `speed_unbounded` :37.)

Chain: `theorem_1_1` ← `theorem_1_1_with_initial_rest` (Theorem.lean:32) ←
`ActualCandidate.selected_candidate_one_with_initial_rest` (R3/ActualCandidate.lean:143) ←
`ActualCandidateAssembly.selected_witness` (:1177) ← `witness` (:1153) ←
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` (:164).

## 2. Field-by-field: where each is discharged, and whether the index appears

| field | discharged at | needs an `Index` inhabitant? |
|---|---|---|
| navier_stokes | **definitionally**: `CandidateFromLimits.lean:181-182` `exact (force_eq_activated_residual …).symm`, because `force` IS the residual (`CandidateFromLimits.lean:82` `def force := SpacetimeGluing.smoothExtension 1 (tracedResidual u p L) …`) | NO |
| force_smooth | `CandidateFromLimits.lean:86` from `tracedResidual_smooth` (needs only `hu`,`hp`,`hlim`) | NO |
| force_support / time support | `CandidateFromLimits.lean:124` (`force_zero_from`, t ≥ 2), then spatial+time cutoffs `R3/ActualCandidate.lean:88-89,101` | NO |
| velocity/pressure_smooth, supports, support_compact | `R3/ActualCandidate.lean:104-108` from localization | NO |
| zero_initial_velocity, divergence_free | `R3/ActualCandidate.lean:111-112`; curl form | NO |
| energy_bounded | `R3/ActualCandidate.lean:119-122` `CompactEnergy.uniform_finite_energy` (compact support + smooth) | NO |
| **speed_unbounded** | `R3/ActualCandidate.lean:115` `hc.speed_unbounded` ← `MixedPeriodicAssembly.exists_candidate_force … (periodicVelocity_speed_unbounded haxis)` (`MixedPeriodicAssembly.lean:366`) ← `haxis` | see §3 |
| ¬ Nonempty GlobalFiniteEnergySolution | `Theorem.lean:36` `hc.no_global_solution_one` (`R3/CandidateBreakdown.lean:43`, consumes only `h.speed_unbounded` at :29) | NO |

## 3. The blow-up is one index-free positive constant, and the tower is zero there

`NavierStokes/GermCandidateAssembly.lean:264`
```
have haxis := origin_blowup H v upper bandFloor hqbig initial stages D hInitialAxis hStagesAxis hat
```
`GermCandidateAssembly.lean:146-159` `origin_blowup` is proved by
```
apply (FinalSlowBase.axis_tendsto H v upper bandFloor).congr'
exact (origin_eventually_base … ).symm.mono (fun _ ht => congrArg norm ht)
```
and `origin_eventually_base` (:109-144) shows the mixed diagonal EQUALS the bare slow base at x = 0 near
t → 1⁻: the potential stages are killed by `AxisZeroOn` (:112-113, used :134) and the direct/angular stages
by `DirectAngularDiagonal.angularSum_axis` (:136-139, `hd : … = 0`).

`NavierStokes/FinalSlowBase.lean:372-378`
```
theorem axis_tendsto (upper : ℝ) (B : ℕ) :
    Tendsto (fun t : ℝ => ‖velocity H v upper B (t, 0)‖) (𝓝[<] 1) atTop := by
  apply BaseResidual.baseVelocity_axis_tendsto_atTop (scales_strictMono …) … 
  rw [leading_origin]
  exact W.axis.small.j_pos
```
`FinalSlowBase.lean:361-363` `origin`: `velocity H v upper B (t,0) = ((1-t) ^ (-A h) * W.axis.j) • e₂`.
`NavierStokes/BaseResidual.lean:104-114` `baseVelocity_axis_tendsto_atTop` needs exactly
`hz : ∀ j, 0 < j → d.axial j (0,0) = 0` and `h0 : 0 < d.axial 0 (0,0)`; :95-96
`‖baseVelocity a h C d (t,0)‖ = (1-t) ^ (-A h) * d.axial 0 (0,0)`.
The positive constant is `W.axis.small.j_pos`, i.e. `NaturalAxisData.lean:41-45`
```
structure SmallParameters (h j : ℝ) : Prop where
  h_pos : 0 < h ; h_le : h ≤ 1/1000 ; j_pos : 0 < j ; j_le : j ≤ 1/1000
```
The profile it lives in is index-free: `FinalSlowBase.lean:619-634`
`structure ProfileData … noncomputable def actualProfile := Classical.choice profileData_nonempty`, whose
nonemptiness (:627-630) is `NominalConeAssembly.exists_nominal_cone` + `ModulatedProfileAssembly.exists_of_certificate`.
And the wave index is BUILT ON TOP of this profile (`CorrectionInitialization.lean:3886` `abbrev profile := FinalSlowBase.actualProfile`,
:3931 `abbrev Label (B N0) := PrimaryGeometryAssembly.Index nominal (choice B N0).prepared.N`), never the other way round.

LOUD point: the artifact PROVES the whole correction tower is identically 0 on a neighbourhood of every axis
point, i.e. exactly where the headline blow-up is read off.
`GermCandidateAssembly.lean:24-25` `def AxisZeroOn (Ω) (f) := ∀ w ∈ Ω, radialProjection w = 0 → f =ᶠ[𝓝 w] fun _ => 0`.
`ActualCandidateAssembly.lean:680-686` `positivePotential_axisZeroOn` = `particular_axisZeroOn` + `signed_axisZeroOn` + `stream_axisZeroOn`;
`:649-655` `signed_axisZeroOn` via `:642-647`
```
theorem axis_not_active (ht : w ∈ PhysicalWaveSum.preterminal) (ha : radialProjection w = 0) :
    w ∉ ActualPolarCoverage.active
```
(the axis is never in the active carrier, because `PrimaryTargetBounds.leftRadius_pos nominal`).
These AxisZeroOn facts are passed as `hInitialAxis`/`hStagesAxis` at `ActualCandidateAssembly.lean:1161-1162`.
So even with a NONEMPTY index the waves contribute exactly nothing to `speed_unbounded`.

## 4. Emptiness census (grep results)

* `Nonempty (Index …)` / `Nonempty (Label …)` / `Nonempty (SignedLabel …)` / `Nonempty (CellIndex …)`
  instance or theorem: **NONE anywhere in NavierStokes/**. The only nonemptiness instance for an index-like
  type is `ActualParticularPhysicalData.lean:615 instance sourceIndex_nonempty (N) : Nonempty (SourceIndex N)`
  — a different type.
* `isEmpty_or_nonempty` occurs exactly 4 times, and each empty branch proves the SAME statement:
  - `ActualInitialMean.lean:318-339`: empty ⇒ `activeLabels … = ∅` (:320-321 `isEmptyElim`), `(seed B N0).oscillation = 0` (:322), `tangentSum = 0` (:325), then both `MeanClass` conclusions from `MemClass.zero` (:328-339).
  - `ActualSignedUnmaskedBounds.lean:161-164` and `:196-199`: `refine ⟨fun l => isEmptyElim l, fun _ => ⟨0, le_rfl, 0, fun l => isEmptyElim l⟩⟩` — the uniform-local-jets bounds hold with constant 0.
  - `ActualSignedStageControls.lean:1132` same pattern on `SignedLabel B N0`.
* `[Nonempty Λ]` hypotheses do exist in the generic machinery (`ActualSignedControl.lean:379,444,571,683`;
  `ParticularCopyBounds.lean:453,480`; `ActualGaussianCoverage.lean:730,801,1251`), but they are always
  discharged INSIDE the nonempty branch of one of those four case-splits (`let := h` at e.g.
  `ActualSignedUnmaskedBounds.lean:166,201`, `ActualInitialMean.lean:340`). Nothing propagates a
  `Nonempty` obligation upward to `witness`/`selected_witness`/`theorem_1_1`.
* No `sorry`/`axiom`/`native_decide` in `NavierStokes/` (the only `sorry`s are the deliberate placeholders in
  `ComparatorChallenges/Euler.lean:88,184` and `ComparatorChallenges/NavierStokes.lean:277,284`, outside this chain).

So: `Index B N0` is never proved nonempty, is never needed nonempty by the headline chain, and the four
lemmas that notice emptiness deliver identical conclusions either way. With an empty index the headline is
still fully proved, and it then reduces to: bare self-similar slow base + a force DEFINED as that base's own
residual.

## 5. Vacuity notes / the one place the tower is in the chain

1. Vacuous-estimate note: in the empty branch the wave amplitude/covariance estimates
   (`ActualInitialMean.lean:314-339`, `ActualSignedUnmaskedBounds.lean:154-164,189-199`) are true with
   constants 0. The headline does not rely on their *content* — only on upper bounds — so this is
   consistent, not a hole. But it does mean the entire "uniform wave class" apparatus can be satisfied by
   the zero field.
2. The ONLY headline-relevant place the tower appears is the residual decay ladder that yields
   `JointResidualLimits.VanishingJointJets` (`JointResidualLimits.lean:84-86`: jets → 0 at the single point
   (1,0)), which is what makes the force smooth across t = 1 (`CandidateFromLimits.lean:82-87`,
   `MixedPeriodicAssembly.lean:359-363`). It comes from `StageEstimates`
   (`MixedCandidateAssembly.lean:29-65`), whose `gain_top : Tendsto gain atTop atTop` (:38) and
   `finite_residual : ∀ J m, JetRate … (gain J - residualLoss m)` (:62-65) are supplied by
   `ActualCandidateAssembly.estimates:1090-1098` → `GluedStageEstimates.actualStageEstimates:684` →
   `ActualCycleResidualBounds.finite_residual_rates:1190-1206` /
   `Invariant.residual_jetRate:1158-1172`, where the state is `x : CycleState (Index B N0)` (:1152).
   Mathematically, an arbitrarily high rate should require the correction cycles to cancel the base stress
   force (`FinalSlowBase.residual_identity:330-333` `residual = stressForce + error`, only `error` being flat,
   `error_allJetsFlat:346`). None of `ActualCycleResidualBounds`, `ActualCyclePreservation` or
   `GluedStageEstimates` case-splits on emptiness, so the invariant/step proofs are index-uniform; I cannot
   verify without a build whether they would remain true with a zero tower, or whether their geometry
   (active-annulus covering) tacitly forces `Index` nonempty. This is the single remaining question, and it
   does NOT affect the verdict about `speed_unbounded`.

## Bottom line
(a). No mandatory field of `CandidateProperties` needs an inhabitant of `Index`/`Label`/`SignedLabel`.
`navier_stokes` is definitional (force := residual); `speed_unbounded` is one positive small parameter
`W.axis.small.j_pos` in the index-free slow base; and the wave tower is *proved* to vanish near the axis
where the blow-up is measured. The wave/correction tower is decoration for the headline conclusion.
