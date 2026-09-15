# Sub-report C — Is the `t >= 1` regime of the initial potential live?

Worker: task C (`_sub-potential-terminal.md`). Repo: `/home/gsm/.openclaw/workspace/repos/NSE`
(openai/NavierStokesAndEuler @ f9e8bc5). READ-ONLY, source-level only (no `lake build`,
no Mathlib on disk). Cone data: `audits/nse-deep/CONE.csv` (`in_cone` column).

## Scope

1. Quote the two `if 0 < x.1.1 then ... else 0` field definitions at
   `NavierStokes/InitialPhysicalData.lean:368` and `:376`; name the constants and what they feed.
2. Repo-wide consumer chain (2-3 levels out) and, per consumer, whether its domain hypothesis is
   inside `preterminal = {w | w.1 < 1}`.
3. Decide whether any in-cone theorem needs the potential nonzero, or continuous/smooth ACROSS
   `t = 1`, or a limit as `t -> 1^-`; and whether the `else 0` branch is used to buy a cheap global
   regularity/support statement.
4. Separate nonvanishing census of the Navier-Stokes half + the four headline theorems.

## Per-declaration findings

### (1) The two gated definitions

`NavierStokes/InitialPhysicalData.lean:364-371` (in cone: `NavierStokes.InitialPhysicalData.potentialFamily`, mark 4):

```lean
noncomputable def potentialFamily (B N0 : ℕ) (i : Fin 3) :
    PhysicalCopyBounds.CopyFamily 1 Frequency where
  gap := gap
  carrier k L := carrier (B := B) (N0 := N0) L k
  amplitude k I x := if 0 < x.1.1 then
    (ChartScales.Q I.1.val.1 ^ (-ActualPrimary.h)) •
      CartesianCopySource.rotatedSource (nativePotentialSource (B := B) (N0 := N0)) (I, k) I.1.val.1 x i
    else 0
```

`NavierStokes/InitialPhysicalData.lean:373-380` (in cone: `...pressureFamily`, mark 4):

```lean
noncomputable def pressureFamily (B N0 : ℕ) : PhysicalCopyBounds.CopyFamily 1 Frequency where
  gap := gap
  carrier k L := carrier (B := B) (N0 := N0) L k
  amplitude k I x := if 0 < x.1.1 then
    (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A ActualPrimary.h))) •
      nativePressureSource (B := B) (N0 := N0) (I, k) I.1.val.1
        (PhysicalClassBounds.cylindricalMap x)
    else 0
```

Defined constants: the `amplitude` field of the two `CopyFamily` records
`potentialFamily B N0 i` (i : Fin 3, a vector potential component) and `pressureFamily B N0`.
Verdict: **OK** (as definitions; totalization by `else 0` is normal Lean practice).

Gate identity, re-derived independently of the sibling: `PhysicalMeanJetBounds.lean:226-229`

```lean
theorem graph_time_pos (h : ℝ) (n d : ℕ) {w : SpaceTime} (hw : w ∈ preterminal) :
    0 < (graph h n d w).2.1.1 := by
  rw [graph_slow]
  exact div_pos (sub_pos.mpr hw) (ChartScales.Q_pos n)
```

i.e. the lift coordinate `x.1.1` is `(1 - w.1) / Q n`, and `preterminal` is
`PhysicalWaveSum.lean:386`: `noncomputable def preterminal : Set SpaceTime := {w | w.1 < 1}`.
So `0 < x.1.1 <-> w.1 < 1` on the chart image. Sibling's chain CONFIRMED.
(`slowFast_apply`, `PhysicalClassBounds.lean:622-623`: `slowFast x = ((x.1.1, x.1.2.2.2), x.2)`;
`cylindricalMap`, ibid `:637-638`.)

### (2) Direct 1-level consumers inside `InitialPhysicalData.lean`

| decl | file:line | domain hypothesis | inside `t<1`? |
|---|---|---|---|
| `potential` (the field) | `:892-893` | none (a total function) | n/a |
| `pressure` | `:895-896` | none | n/a |
| `copyPotential` | `:898-909` | record of the above | n/a |
| `potentialWaveData` / `pressureWaveData` | `:1269` / `:1299` | records | n/a |
| `potential_amplitude_smooth` | `:1185-1201` | `paddedPast` = `cylindricalDomain ... ∩ {x | 0 < x.1.1}` (`:1172-1173`) | YES (explicit `0 < x.1.1`) |
| `pressure_amplitude_smooth` | `:1203-1212` | same `paddedPast` | YES |
| `potential_amplitude_source` | `:1063-1070` | `EqOn ... sourceStrip.domain`, discharged by `sourceStrip_time hx : 0 < x.1.1` (`:1060`) | YES |
| `pressure_amplitude_source` | `:1072-1079` | same | YES |
| `potential_smooth` | `:1333-1336` | `ContDiffOn ℝ ∞ (potential B N0) PhysicalWaveSum.preterminal` | YES (only `t<1`) |
| `pressure_smooth` | `:1338-1341` | `... preterminal` | YES |
| `potential_zero_exterior` | `:1743-1750` | `(hw : w ∈ PhysicalWaveSum.preterminal)` | YES |
| `pressure_zero_exterior` | `:1752-1759` | `(hw : w ∈ PhysicalWaveSum.preterminal)` | YES |
| `velocity_chart_slow` | `:2812-2815` | `(ht : z.1 < 1) (hr : 0 < z.2 0)` | YES |
| `pressure_chart_slow` | `:2835-2838` | `(ht : z.1 < 1) (hr : 0 < z.2 0)` | YES |
| `potential_amplitude_data` | `:550-570` | **NO domain hypothesis**; instead CONCLUDES `0 < x.1.1` | uses the `else` branch |
| `pressure_amplitude_data` | `:572-587` | same | uses the `else` branch |
| `potential_source_domain` | `:1048-1052` | `(hx : amplitude k I x ≠ 0) : x ∈ sourceStrip.domain` — global | uses the `else` branch |
| `pressure_source_domain` | `:1054-1058` | same | uses the `else` branch |

Census of `else`-branch usage in the whole 2855-line file: exactly **two** sites,
`:556` and `:578`:

```lean
  have ht : 0 < x.1.1 := by
    by_contra ht
    exact hx (by simp only [potentialFamily, ite_eq_right ht])
```

Every other `simp` on these definitions uses `ite_eq_left` with a proof of `0 < x.1.1`
(`:559, :1069, :1078, :1200, :1212, :1517, :1526`), i.e. discharges the `if` to the real formula.
Verdict for the four `..._amplitude_data` / `..._source_domain` lemmas: **OK, noteworthy** — the
`else 0` branch is genuinely load-bearing there, and it makes those SUPPORT lemmas hold globally
(unconditionally in `x`) instead of only on `preterminal`. It is a support/vanishing statement, not
a regularity statement; nothing unsound follows, but it is exactly the "cheap global support" pattern.

### (3) Consumers 2-3 levels out (repo-wide)

`grep 'InitialPhysicalData\.'` outside the defining file returns 50 hits in 6 files. The only
value-level consumers:

- `NavierStokes/ActualCandidateAssembly.lean:36-40` (in cone):
  ```lean
  noncomputable def initialPotential (B N0 : ℕ) : VelocityField :=
    InitialPhysicalData.potential B N0 + ActualCandidateConstruction.streamMeanStages B N0 0
  noncomputable def initialPressure (B N0 : ℕ) : PressureField :=
    InitialPhysicalData.pressure B N0 + ActualCandidateConstruction.pressureMeanStages B N0 0
  ```
- `initialPotential_smooth` `ActualCandidateAssembly.lean:89-93`:
  `ContDiffOn ℝ ∞ (initialPotential B N0) (ActualCandidateConstruction.physicalDomain B N0)`
  with `physicalDomain B N0 = CutStageEstimates.physicalSublevel h (qbig B N0)`
  (`ActualCandidateConstruction.lean:189-190`) — a `physicalQ` sublevel set, i.e. a subset of `t<1`.
- `ActualCandidateAssembly.lean:144-149` (**in cone**), the decisive one:
  ```lean
  theorem initialPotential_axisZeroOn (B N0 : ℕ) :
      GermCandidateAssembly.AxisZeroOn
        (MixedAxisPreservation.localDomain h (ActualCandidateConstruction.qbig B N0))
        (initialPotential B N0) := by
  ```
  with `AxisZeroOn` (`GermCandidateAssembly.lean:24-25`)
  `= ∀ w ∈ Ω, PhysicalGraphBounds.radialProjection w = 0 → f =ᶠ[𝓝 w] fun _ => 0`
  and `localDomain h qbig = {w | w.1 < 1 ∧ PhysicalWaveSum.physicalQ h w < qbig}`
  (`MixedAxisPreservation.lean:448-449`) — again `w.1 < 1`.
- `GermEndpointInputs.lean:378-389, 402-453` and `GluedStageEstimates.lean:678, 697`,
  `WholeDomainInitializationBounds.lean:26-47`: jet/loss bounds on the same wave data.
- Third level: `initialPotential` is consumed by `ActualCandidateAssembly.potentialStages`
  (`:531`) / `Witness` (`:1121`) / `witness` (`:1153`), all in cone.

**No consumer anywhere has a domain hypothesis reaching `t >= 1`.** Every quoted hypothesis is
`preterminal`, `paddedPast` (`0 < x.1.1`), `z.1 < 1`, `physicalSublevel`, or `localDomain`
(`w.1 < 1 ∧ ...`).

### (4) Where regularity across `t = 1` IS required — and it is not the potential

The comparator's solution class requires velocity/pressure smoothness only on
`preSingularDomain` (`ProblemStatement.lean:42`): `Ico 0 1 ×ˢ univ`. But the FORCE must be smooth
on `futureDomain` (`:45`): `Ici 0 ×ˢ univ`, i.e. ACROSS `t = 1`
(`Comparator.ForceCondition.smooth`, `ComparatorDefinitions.lean:149-151`). That across-`t=1`
regularity is NOT supplied by any `else 0`: it is a Whitney-type gluing driven by the `t -> 1^-`
limit jets. `CandidateFromLimits.lean:82-87`:

```lean
def force : VelocityField :=
  SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)
    (tracedResidual_smooth u p hu hp L hlim)

theorem force_smooth : ContDiff ℝ ∞ (force u p hu hp L hlim) :=
```
plus `force_boundary_jets` (`:128-129`): `iteratedFDeriv ℝ n (force ...) (1, x) = L x n`, where `L`
is the locally uniform `𝓝[<] 1` limit of the residual jets
(`PeriodicResidualLimits.lean:436-438`:
`TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n (periodicResidual A p) (t, x)) (fun x => L x n) (𝓝[<] (1 : ℝ))`),
and `force_time_support` (`:124-125`) gives `f = 0` for `t >= 2`.
Verdict: **OK** — the `t >= 1` values of the FORCE are live and load-bearing, but they come from
`smoothExtension`, not from the potential's `else 0`.

## Is the t>=1 regime live?

**NO — not for these two definitions.** Findings, in order of strength:

1. Every value-reading and regularity lemma for `potentialFamily` / `pressureFamily` and for their
   sums `potential` / `pressure` is stated on a domain contained in `t < 1`
   (table above; strongest: `potential_smooth`, `InitialPhysicalData.lean:1333-1334, ContDiffOn ... preterminal`).
   Nothing asserts continuity, smoothness, a value, or a limit of the potential at or beyond `t = 1`.
2. The `else 0` branch is reached by only two proofs in the file (`:556`, `:578`), and only to turn
   `amplitude ≠ 0` into `0 < x.1.1`. It buys the four global support lemmas
   `potential_amplitude_data` (`:550`), `pressure_amplitude_data` (`:572`),
   `potential_source_domain` (`:1048`), `pressure_source_domain` (`:1054`). So the `else 0` branch is
   USED, and it is used to make a SUPPORT statement global/cheap — not a regularity statement.
3. The claimant says so himself in the docstring at `InitialPhysicalData.lean:890-891`:
   `/-- The actual initial primary potential.  The physical construction is / zero on the unused
   future side of the preterminal domain. -/`. (Docstring = evidence about the author only; but the
   Lean above matches it.)
4. Discontinuity at `t = 1` is therefore real and harmless for the headline claim: the claim IS a
   `t -> 1^-` blowup statement, the velocity/pressure smoothness class is `Ico 0 1 ×ˢ univ`
   (`ProblemStatement.lean:42`), and only the force needs `Ici 0` — supplied independently
   (section (4) above).
5. **No in-cone theorem requires the potential to be nonzero.** The opposite is required: the
   in-cone `initialPotential_axisZeroOn` (`ActualCandidateAssembly.lean:144-149`) forces the initial
   potential to VANISH on a neighbourhood of every axis point, and
   `MixedAxisPreservation.PotentialStage.zero_germ` (`:179-190`) propagates that to the whole stage:
   ```lean
   theorem PotentialStage.zero_germ ... (ht : w ∈ PhysicalWaveSum.preterminal)
       (haxis : PhysicalGraphBounds.radialProjection w = 0) :
       p.field =ᶠ[𝓝 w] fun _ => 0
   ```
   and `initialized_origin_blowup` (`MixedAxisPreservation.lean:434-444`) then transports the axis
   divergence from `base` alone:
   ```lean
   (hbase : Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl base (t, 0)‖) (𝓝[<] 1) atTop) :
       Tendsto (fun t : ℝ => ‖initializedDiagonal base initial p D scales (t, 0)‖) (𝓝[<] 1) atTop
   ```
   So the sibling's observation ("all 177 theorems of InitialPhysicalData.lean survive if
   cartesianPotential = 0") is consistent with the design: the potential layer is an upper-bound /
   support / equation-bookkeeping object with ZERO contribution at the axis. It carries no blowup.
   Headline theorems checked: `NavierStokes.Comparator.navier_stokes_breakdown_R3` and
   `..._periodic` (`ComparatorSolution.lean:16-19, 23-26`), `NavierStokesR3.theorem_1_1`
   (`R3/Theorem.lean:46`), `NavierStokes.PeriodicPaper.periodic_corollary`
   (`PeriodicPaperTheorem.lean:155`), and `ActualCandidateAssembly.Witness` (`:1121`).

Verdict tag for the question: **OK** (`else 0` is a sound totalization; genuinely irrelevant to the
`t -> 1^-` content; used only for cheap global SUPPORT lemmas, which is worth recording but is not
a defect). Not vacuous: `𝓝[<] (1:ℝ)` is `NeBot`, and every quoted domain (`preterminal`,
`paddedPast`, `localDomain`) is a nonempty open set.

## Nonvanishing census

The tower is **NOT** satisfied by the zero field. There are explicit, strong lower-bound /
divergence requirements, all inside `t < 1` with the `t -> 1^-` filter.

Ranked:

1. **Strongest, on the actual constructed field** — `ActualCandidateAssembly.Witness`,
   `NavierStokes/ActualCandidateAssembly.lean:1142-1144` (in cone; proved by `witness` `:1153`):
   ```lean
      Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
        TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum) (t, x)))
        (𝓝[<] (1 : ℝ)) atTop ∧
   ```
2. **The mandatory structure field in every candidate record** —
   `NavierStokes/ProblemStatement.lean:94-96` + `:114`:
   ```lean
   def SpeedUnboundedAtOne (u : VelocityField) : Prop :=
     ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
       ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖
   ...
     speed_unbounded : SpeedUnboundedAtOne u
   ```
   Same field in `R3/ProblemStatement.lean:109`, `R3CompactCandidate.lean:37`,
   `PeriodicPaperTheorem.lean:47` — all in cone. And the zero field is explicitly EXCLUDED,
   `ProblemStatement.lean:151-155`:
   ```lean
   theorem zero_velocity_not_unbounded : ¬ SpeedUnboundedAtOne (fun _ => 0) := by
   ```
3. **The analytic root of the blowup**, `NavierStokes/BaseResidual.lean:104-114`:
   ```lean
   theorem baseVelocity_axis_tendsto_atTop {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
       (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
       (hd : SmoothCoefficients d) (C : ℝ)
       (hz : ∀ j, 0 < j → d.axial j (0, 0) = 0) (h0 : 0 < d.axial 0 (0, 0)) :
       Tendsto (fun t : ℝ => ‖baseVelocity a h C d (t, 0)‖) (𝓝[<] 1) atTop := by
   ```
   with the exact identity `BaseResidual.lean:90-96`
   `‖baseVelocity a h C d (t, 0)‖ = (1 - t) ^ (-CoordinateAlgebra.A h) * d.axial 0 (0, 0)` for `t < 1`.
   The strict positivity `h0` is discharged concretely by `W.axis.small.j_pos`
   (`FinalSlowBase.lean:378`, `ConstructedSlowBase.lean:297`), where
   `j_pos : 0 < j` is a structure field at `NaturalAxisData.lean:44` and the concrete witness is
   `ActualPrimary.nominal.axis.small.j_pos` (`BaseWitnessClosure.lean:46`).
4. `NavierStokes/PeriodicResidualLimits.lean:444-446` and `SpatialLocalization.lean:532, 553-564`,
   `MixedPeriodicAssembly.lean:398`: the axis divergence hypothesis
   `Tendsto (fun t : ℝ => ‖SpatialCurl.spatialCurl A (t, 0)‖) (𝓝[<] 1) atTop`, threaded to
   `SpeedUnboundedAtOne`.
5. `NavierStokes/NaturalCore.lean:430-441` `coreVelocity_axis_tendsto_atTop` (same mechanism for the
   core profile, needing `hj : 0 < j`).
6. `NavierStokes/CandidateConsequences.lean:139` `h3_unbounded : PeriodicSobolev.DerivativeH3UnboundedAtOne u`
   and `:151-173` (the growing-trajectory strengthening).
7. `NavierStokes/R3/H3Blowup.lean:40` `candidate_h3Norm_unbounded`.
8. Headline shape (why a nonzero field is forced at all):
   `ComparatorSolution.lean:16-19`
   ```lean
   theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
       ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
       InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
       ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
   ```
   Note `u₀ := fun _ => 0` IS the exhibited datum (`ComparatorR3Theorem.lean:32`,
   `refine ⟨fun _ => 0, toComparator (rescaledForce ν f), ...⟩`), so all the content sits in the
   FORCE `f` and in `¬ ∃ v p, ...`. The `¬ ∃` is discharged through
   `compact_candidate_excludes_global_solution` / `MaximalLifespan.candidate_excludes_global_solution`,
   which consume `speed_unbounded` (see `R3/CandidateBreakdown.lean:29`,
   `R3CompactCandidate.lean:272`: `obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one`).
   So a zero force would not do: with `f = 0` and `u₀ = 0` the zero solution exists.
9. Euler half, for contrast, is even more explicit — `Euler/Solution.lean:45, 54-55`:
   `... ∧ HasCompactSupport u₀ ∧ u₀ ≠ 0 ∧ ...`,
   `Filter.limsup (fun t : ℝ => velocityC1Norm (v · t)) (𝓝[<] Tstar) = ⊤ ∧`,
   `(∫⁻ t in Ico (0 : ℝ) Tstar, vorticityNorm (v · t)) = ⊤ ∧`.

LOUD counter-claim to the sibling's escalation: it is TRUE that the InitialPhysicalData potential
layer could be zero without breaking its own 177 theorems, and TRUE that it is required to vanish
near the axis. It is FALSE that the whole tower is satisfied by the zero field: `speed_unbounded`
(2 above) plus `zero_velocity_not_unbounded` (`ProblemStatement.lean:151`) block that at the
candidate level, and the divergence is produced by `baseVelocity` with `0 < d.axial 0 (0,0)`.
The correct framing is: **the potential layer carries no blowup; it is a bounded, axis-vanishing
corrector, and the singularity lives entirely in `base`.** Where to press instead is `base`:
whether `ActualPrimary.nominal` and `NaturalProfile.IsNaturalSolution` are inhabited by a genuine
construction, and whether the residual really equals the smooth extended force.

## Escalations

1. (medium) `potential_source_domain` / `pressure_source_domain`
   (`InitialPhysicalData.lean:1048, 1054`) and `potential_amplitude_data` / `pressure_amplitude_data`
   (`:550, :572`) are UNCONDITIONAL in `x`, and their strength comes from the `else 0`. Any downstream
   reader who treats "the amplitude support is inside `sourceStrip.domain`" as a statement about the
   real formula is over-reading: off `t < 1` it is vacuous because the field is 0 there.
   Not unsound; worth one line in the final report.
2. (medium, for another worker) The force's `t >= 1` values ARE live and are produced by
   `SpacetimeGluing.smoothExtension 1` from claimed `𝓝[<] 1` limit jets `L`
   (`CandidateFromLimits.lean:82-87, 128-136`; `PeriodicResidualLimits.lean:436-438`). This is the
   real across-`t=1` load-bearing step in the whole NS half, and it is where the `ForceConditionDecay`
   of the headline theorem is met. It deserves its own audit: `SpacetimeGluing.smoothExtension`
   and `JointResidualLimits.VanishingJointJets`.
3. (low) `NavierStokes.ProblemStatement.divergence`/junk-value exposure in the comparator reference:
   `ComparatorDefinitions.lean:51-55` documents `fderiv = 0` off differentiability and
   `divergence_of_not_differentiableAt` (`:62-64`) is a `@[simp]` lemma. In the headline theorems the
   exhibited datum is `u₀ = fun _ => 0`, so `InitialVelocityConditionDecay u₀` is trivially met —
   all content is in the force. Recorded, not a defect of this scope.
4. (nil) No kernel-risk hits in scope: no `macro`/`elab`/`syntax`/`set_option`/`native_decide`/
   `axiom`/`unsafe`/`partial`, no `decide`, no large numerals, no `Acc.rec`, no nested-indexed
   inductives in `InitialPhysicalData.lean` or in the files quoted above.

## Residue

- I did not verify that `SpacetimeGluing.smoothExtension` is a genuine Whitney extension (escalation 2).
- I did not chase `NaturalProfile.IsNaturalSolution` / `ActualPrimary.nominal` inhabitation, i.e.
  whether the concrete `0 < d.axial 0 (0,0)` witness closes; I only located it
  (`BaseWitnessClosure.lean:46`, `NaturalAxisData.lean:44`).
- No build was run, so elaboration-level facts (e.g. that a numeral row elaborates at ℝ not ℕ)
  are unverified; all claims above are read off statements and proof terms.
- `ActualParticularPhysicalData.potentialFamily/pressureFamily` (`:479, :488`) are NOT in cone
  (`in_cone=False`) and were not audited.
