# NSE periodic branch (option D) — read-only source audit

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (clone of `openai/NavierStokesAndEuler`, git `f9e8bc5`).
No build was run (no Mathlib on disk). Everything below is source-level: statements and real proof
terms read line by line. Nothing was modified.

## Scope

Files read (all paths relative to repo root):

| file | lines | what was read |
|---|---|---|
| `NavierStokes/ComparatorSolution.lean` | 32 | whole file (submission root for (C)/(D)) |
| `NavierStokes/ComparatorTheorem.lean` | 55 | whole file (2 decls) |
| `NavierStokes/PeriodicPaperComparator.lean` | 54 | whole file (3 decls) |
| `NavierStokes/PeriodicComparatorSolution.lean` | 43 | whole file (1 def) |
| `NavierStokes/PeriodicPaperTheorem.lean` | 164 | whole file (2 structures, 4 decls, 1 def) |
| `NavierStokes/ComparatorBridge.lean` | 253 | whole file (~22 decls) |
| `NavierStokes/ComparatorDefinitions.lean` | 245 | whole file (all definitions; diffed vs reference) |
| `ComparatorChallenges/NavierStokes.lean` | 287 | header + all definitions + (C)/(D) placeholders |
| `NavierStokes/PeriodicViscosity.lean` | 78 | whole file (1 decl) |
| `NavierStokes/PeriodicViscosityUniqueness.lean` | — | `classical_uniqueness_on_Icc` (l.65–110) |
| `NavierStokes/PeriodicUniqueness.lean` | — | l.91–140, 200–210, 305–320, 435–460, 491–573, 643–710 |
| `NavierStokes/MaximalLifespan.lean` | 292 | whole file (~18 decls) |
| `NavierStokes/CandidateConsequences.lean` | — | l.1–200 (`futureJet*`, `Consequences`) |
| `NavierStokes/ProblemStatement.lean` | 168 | l.30–168 (defs, `CandidateProperties`, helpers) |
| `NavierStokes/R3/ProblemStatement.lean` | — | l.80–200 (`CandidateProperties`, `GlobalFiniteEnergySolution`, zero-force) |
| `NavierStokes/R3/Theorem.lean` | 81 | whole file (5 decls) |
| `NavierStokes/R3/CandidateBreakdown.lean` | 79 | whole file (4 decls) |
| `NavierStokes/R3/ActualCandidate.lean` | 155 | whole file (~9 decls) |
| `NavierStokes/R3ActualCandidate.lean` | 24 | whole file |
| `NavierStokes/ActualCandidateAssembly.lean` | 1187 | l.1–60 and l.1120–1187 (`Witness`, `selected_witness`) |
| `NavierStokes/R3/ParabolicScaling.lean` | — | l.85–140 (`compressedCandidate`) |
| `NavierStokes/PeriodicPaperScalingSupport.lean` | — | l.75–112 (`exists_compression_scale`) |
| `NavierStokes/PeriodicLocalization.lean` | — | l.40–140, lemma index (`periodize`, `SupportedInCube`) |
| `NavierStokes/PeriodicPaperSupport.lean` | — | `beforeOne` (l.28) |
| `lakefile.toml`, `lean-toolchain`, `formalization.yaml`, `NavierStokes.lean` | — | whole files |

Roughly 90 declarations were read in full or in the parts that carry the periodic claim.

**Route actually used by the deliverable (D):**

```
ComparatorSolution.lean:23  NavierStokes.Comparator.navier_stokes_breakdown_periodic   (declared main result)
 └ ComparatorTheorem.lean:47 ComparatorBridge.navier_stokes_breakdown_periodic
    ├ PeriodicPaperTheorem.lean:155 PeriodicPaper.periodic_corollary   (: breakdownStatement, l.148)
    │  ├ R3/Theorem.lean:26  NavierStokesR3.theorem_1_1_with_initial_rest
    │  ├ PeriodicPaperScalingSupport.lean:82 exists_compression_scale
    │  ├ R3/ParabolicScaling.lean:95 compressedCandidate
    │  ├ PeriodicPaperTheorem.lean:92 of_compact_candidate        (periodize ∘ beforeOne)
    │  └ PeriodicPaperTheorem.lean:65 CandidateProperties.no_global_solution
    │     └ PeriodicViscosity.lean:24 excludes_global_solution
    └ PeriodicPaperComparator.lean:45 option_D_of_paper_candidate
       ├ ComparatorBridge.lean:136 zero_initial_condition
       ├ PeriodicPaperComparator.lean:21 forceConditionPeriodic_of_paper_candidate
       │  ├ ComparatorBridge.lean:117 forceConditionPeriodic_of_decay
       │  └ CandidateConsequences.lean:79 futureJet_decay
       └ PeriodicComparatorSolution.lean:20 periodicPaperSolution_of_comparator
```

**Dead branch:** `ComparatorTheorem.lean:25 option_D_of_candidate` (which uses
`MaximalLifespan.candidate_excludes_global_solution` at l.41 and the viscosity-one
`ProblemStatement.CandidateProperties`) is **not** used by the (D) deliverable. It takes the candidate
as an unproved hypothesis `h`. Grep shows no other reference to it. So question 3 concerns machinery
that is real and proved but off the shipped path; the shipped exclusion is
`PeriodicViscosity.excludes_global_solution`.

## Per-declaration findings

### 1. `NavierStokes.Comparator.navier_stokes_breakdown_periodic` — `ComparatorSolution.lean:23`
Statement: for every `nu > 0` there exist `u₀ : ℝ³ → ℝ³` and `f : ℝ³ → ℝ → ℝ³` with
`InitialVelocityConditionPeriodic u₀`, `ForceConditionPeriodic f`, and no `v, p` satisfying
`NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p`. Proof is one `exact` into
`ComparatorBridge.navier_stokes_breakdown_periodic`. Signature is character-for-character the same as
the frozen reference `ComparatorChallenges/NavierStokes.lean:280`, and the declaration name/namespace
matches `formalization.yaml:65-67`. **[OK]**

### 2. `NavierStokes.Comparator.*` definitions — `ComparatorDefinitions.lean` vs the frozen reference
I stripped doc comments and blank lines from both files and diffed the code lines: 74 code lines in
`ComparatorDefinitions.lean` vs 84 in `ComparatorChallenges/NavierStokes.lean`; the only difference is
the 10 lines of the two `sorry`-carrying challenge theorems `navier_stokes_breakdown_R3` /
`navier_stokes_breakdown_periodic`, which the definitions module omits. Every definition used by (D)
(`divergence`, `IsOnePeriodic` (l.95), `InitialVelocityConditionPeriodic`, `ForceConditionPeriodic`
(l.174–179), `NavierStokesExistenceAndSmoothness` (l.191–209),
`NavierStokesExistenceAndSmoothnessPeriodic` (l.236–243)) is identical. `local notation ℝ^n` at l.40,
`variable {n : ℕ}` at l.43. The challenge module is imported nowhere in the proof libraries (only
`formalization.yaml`, `README.md`, `lakefile.toml` mention it). **[OK]**

### 3. `PeriodicPaper.GlobalSmoothSolution` — `PeriodicPaperTheorem.lean:51`
Fields, line by line:
```
51  structure GlobalSmoothSolution (ν : ℝ) (f : VelocityField) where
52    velocity          : VelocityField
53    pressure          : PressureField
54    velocity_smooth   : ContDiffOn ℝ ∞ velocity futureDomain          -- futureDomain = Ici 0 ×ˢ univ
55    pressure_smooth   : ContDiffOn ℝ ∞ pressure futureDomain
56    velocity_periodic : UnitSpatialPeriodsOn (Ici 0) velocity
57    pressure_periodic : UnitSpatialPeriodsOn (Ici 0) pressure
58    zero_initial_velocity : ∀ x, velocity (0, x) = 0
59    divergence_free   : ∀ t ∈ Ici 0, ∀ x, spatialDivergence velocity t x = 0
61    navier_stokes     : ∀ t ∈ Ioi 0, ∀ x, navierStokesResidual ν velocity pressure t x = f (t, x)
```
It is a **data** structure (not `Prop`), so `Nonempty (GlobalSmoothSolution ν f)` is the competitor
existence statement. `UnitSpatialPeriodsOn` (`ProblemStatement.lean:49`) is
`∀ t ∈ times, ∀ x i, g (t, x + coordinateVector i) = g (t, x)` with
`coordinateVector i = EuclideanSpace.single i 1` (`ProblemStatement.lean:39`) — literally the vector in
the comparator's `IsOnePeriodic` (`ComparatorDefinitions.lean:95-96`), which is why the field transfers
are bare `exact` steps. **[OK]**

Comparison with the comparator structure it negates (fields `navier_stokes`, `div_free`,
`initial_condition`, `velocity_smooth`, `pressure_smooth`, `isOnePeriodic_velocity`,
`isOnePeriodic_pressure`): `GlobalSmoothSolution` requires **strictly less**:
* no energy / `MemLp` / bounded-kinetic-energy clause (contrast
  `NavierStokesExistenceAndSmoothnessRn.globally_bounded_energy`, `ComparatorDefinitions.lean:227`);
* the PDE only on `Ioi 0`, while the comparator gives it on `t ≥ 0`;
* smoothness on `Ici 0 ×ˢ univ`, exactly the comparator's `univ ×ˢ Ici 0` after the coordinate swap
  (`fromComparator_smooth`, `ComparatorBridge.lean:89`).
So the adapter `periodicPaperSolution_of_comparator` (`PeriodicComparatorSolution.lean:20-41`) fills
every field with no side conditions: `velocity/pressure := fromComparator v/p`, periodicity from
`h.isOnePeriodic_velocity` / `h.isOnePeriodic_pressure`, `zero_initial_velocity :=
h.initial_condition` (sound because the exhibited datum is `fun _ => 0`), `divergence_free` via
`divergence_eq` (`ComparatorBridge.lean:28`), `navier_stokes` via `comparator_equation`
(`ComparatorBridge.lean:201`). **No extra requirement is imposed on the competitor. [OK]**

### 4. Escalation E3 — is `pressure_periodic` load-bearing? YES. Where it is consumed
`.pressure_periodic` / `isOnePeriodic_pressure` occurrences on this branch:
* `PeriodicComparatorSolution.lean:31-33` — filled from `h.isOnePeriodic_pressure` (production).
* `PeriodicPaperTheorem.lean:70` (candidate's own `pressure_periodic`) and **`:72`
  (`v.pressure_periodic`, the competitor's)** — both handed to `PeriodicViscosity.excludes_global_solution`.
* `PeriodicViscosity.lean:38` `(hpq : UnitSpatialPeriodsOn (Ici 0) q)`, **consumed at
  `PeriodicViscosity.lean:64-65`** where it is passed into
  `PeriodicViscosityUniqueness.classical_uniqueness_on_Icc`.
* `PeriodicViscosityUniqueness.lean:74` `hpq` → rescaled at `:89` (`normalize_periodic hν hpq`) into
  `PeriodicUniqueness.classical_uniqueness_on_Icc`.
* `PeriodicUniqueness.lean:652` `hpq` → `:667-668` into `energy_rate_le`
  (`PeriodicUniqueness.lean:553`, pressure hypotheses at `:560-561`) → `energy_balance`
  (`:491`, `hpp`/`hpq` at `:498-499`) → **`:533`
  `cubeIntegral_pressure_energy_zero hw (hp.sub hq) hpw (unitPeriods_sub hpp hpq) hdw`**, the lemma at
  `PeriodicUniqueness.lean:435-441` that makes `∫_cube ⟪w, ∇(p−q)⟫ = 0`.
* (Same consumption pattern on the dead branch: `MaximalLifespan.lean:101-103, 254`.)

So the pressure-periodicity of the *competitor* is genuinely used: it is what kills the pressure term
in the Grönwall energy identity on the torus. A hypothetical global smooth periodic-velocity solution
with **non-periodic pressure** would not be excluded by this argument.

Is that legitimate? Yes, relative to the challenge as formalized: the comparator solution structure
itself demands it — `isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)` at
`ComparatorDefinitions.lean:243` **and** at the frozen upstream reference
`ComparatorChallenges/NavierStokes.lean:269` (doc-string: "following the errata appended to the Clay
problem statement"). My line-diff (finding 2) shows the repo did not add, weaken, or edit that field.

**Verdict on E3: [OK] — the periodic claim is not weaker than the comparator's (D).** The repo proves
exactly `¬ ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic ν (fun _ => 0) f v p` with the reference's
own structure. Any residual mismatch between "periodic pressure required" and an unrestricted reading
of Clay (D) is inherited from the upstream formal-conjectures statement and is out of this repo's
control. The direction of the E3 worry (that `GlobalSmoothSolution` might demand *more* than the
comparator supplies, letting solutions escape) does **not** materialise: `GlobalSmoothSolution` demands
strictly less (no energy clause), so the exclusion is stronger than needed for (D).

### 5. `PeriodicPaper.CandidateProperties` — `PeriodicPaperTheorem.lean:26`
Fields, line by line: `velocity_smooth` 28 (`ContDiffOn ℝ ∞ u preSingularDomain`, `Ico 0 1 ×ˢ univ`),
`pressure_smooth` 29, `force_smooth` 30 (`ContDiff ℝ ∞ f`, global), `velocity_periodic` 31
(`UnitSpatialPeriodsOn (Ico 0 1)`), `pressure_periodic` 32, `force_periodic` 33 (`Ici 0`),
`support_compact` 34, `support_interior` 35 (`K ⊆ fundamentalInterior`), `velocity_support` 36-37
(`tsupport ∩ fundamentalCube ⊆ K`), `pressure_support` 38-39, `zero_initial_velocity` 40,
`force_time_support` 41 (`CompactFutureTimeSupport`, i.e. `∃ T ≥ 0, ∀ t ≥ T, f (t,·) = 0`,
`ProblemStatement.lean:89`), `force_zero_nonpos` 42, `divergence_free` 43-44, `navier_stokes` 45-46
(`NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)` on `Ioo 0 1`),
`speed_unbounded` 47 (`SpeedUnboundedAtOne u`, `ProblemStatement.lean:94`: for all `M, δ > 0` there are
`t ∈ Ioo 0 1`, `t > 1 − δ`, `x` with `‖u (t,x)‖ > M`). The support clauses intersect with the
fundamental cube, so they do not falsely claim compact support of a periodic lift. **[OK]**

### 6. `PeriodicPaper.periodic_corollary` — `PeriodicPaperTheorem.lean:155`
Statement (`breakdownStatement`, `:148-151`): `∀ ν > 0, ∃ u p f K, CandidateProperties ν u p f K ∧
¬ Nonempty (GlobalSmoothSolution ν f)`. Proof (`:156-162`): take
`NavierStokesR3.theorem_1_1_with_initial_rest ν hν`; pick a compression scale
(`exists_compression_scale`, `PeriodicPaperScalingSupport.lean:82`, which produces `l > 1` with the
velocity, pressure and all force slices inside the quarter cube via
`exists_spatialScale_into_quarterCube`); apply the delayed parabolic compression
(`R3/ParabolicScaling.lean:95 compressedCandidate`, whose proof discharges every field, using the
`|t| ≤ 3/8` rest clause to extend by zero); periodize with `of_compact_candidate`
(`PeriodicPaperTheorem.lean:92`); conclude non-existence with `no_global_solution` (`:65`). All
hypotheses are supplied; nothing is left as an axiom or hypothesis. **[OK]**

Down to the real field definitions (question 2):
* `NavierStokesR3.theorem_1_1_with_initial_rest` — `R3/Theorem.lean:26`; witnesses are
  `ViscosityScaling.scaledVelocity ν u`, `scaledPressure ν p`, `scaledVelocity ν f` (`:33`).
* those `u, p, f` come from `ActualCandidate.selected_candidate_one_with_initial_rest`
  (`R3/ActualCandidate.lean:143`), whose witnesses are (via `of_localized_fields`, `:79-85`)
  `R3CompactCandidate.velocity A B`, `R3CompactCandidate.pressure P`, and the force
  `PositiveTimeForce.force (R3CompactCandidate.compactForce forcing)`.
* `A, B, P, forcing` come from `ActualCandidateAssembly.selected_witness`
  (`ActualCandidateAssembly.lean:1177`) unfolding `Witness` (`:1121-1151`):
  `ASum/BSum/PSum := SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
  (potentialStages / directStages / pressureStages B N0 hN)` (`:1125-1130`), then
  `TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum)` and
  `TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure PSum)` (`:1136-1137`);
  the stage sequences are built from `initialPotential` (`:37`), `initialPressure` (`:41`),
  `initialDirect` (`:44`) on `InitialPhysicalData` / `ActualCandidateConstruction`, with the closed
  budget/threshold `ActualCandidateConstruction.selectedBudget / selectedThreshold` (`:1165-1181`).
* periodic wrapper: `PeriodicLocalization.periodize` (`PeriodicLocalization.lean:62`, a `tsum` over the
  integer lattice of spatial translates) applied to `PeriodicPaperSupport.beforeOne`
  (`PeriodicPaperSupport.lean:28`).

**FLAG [UNCLEAR]:** velocity and pressure are named closed sums, but the **force is never a named
definition**. In `Witness` it is the existentially bound `∃ forcing : VelocityField` at
`ActualCandidateAssembly.lean:1134`, produced by
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` (`:1155`). So the shipped `(D)`
witness `f` is `toComparator (periodize (beforeOne (ParabolicScaling.force l (scaledVelocity ν
(PositiveTimeForce.force (compactForce forcing))))))` where `forcing` is only known to exist. That is
logically fine but means the force cannot be inspected or evaluated; only `u₀ = fun _ => 0` is explicit.

### 7. `PeriodicViscosity.excludes_global_solution` — `PeriodicViscosity.lean:24` (the real exclusion)
Mechanism (`:44-76`): from the candidate's unbounded speed, apply
`MaximalLifespan.unbounded_excludes_continuous_extension` (`MaximalLifespan.lean:154`) to the global
competitor restricted to `Icc 0 1 ×ˢ univ`; the needed agreement `u = v` on `[0,t]` for every `t < 1`
comes from `PeriodicViscosityUniqueness.classical_uniqueness_on_Icc` (`:65`, ν-version) which rescales
to viscosity one and calls `PeriodicUniqueness.classical_uniqueness_on_Icc`
(`PeriodicUniqueness.lean:643`). Then compactness of the cube bounds the continuous periodic competitor
uniformly (`periodic_bound_on_slab`, `MaximalLifespan.lean:130`), contradicting
`unbounded_speed_excludes_uniform_bound` (`ProblemStatement.lean:159`). Every hypothesis is supplied
from the two structures at `PeriodicPaperTheorem.lean:70-73`. **[OK]**

Load-bearing lemmas of the uniqueness core:
1. `PeriodicUniqueness.classical_uniqueness_on_Icc` — `PeriodicUniqueness.lean:643` (Grönwall on the
   cube energy; `gronwall_zero` invoked at `:672`).
2. `PeriodicUniqueness.energy_rate_le` — `:553`, and `energy_balance` — `:491`.
3. `PeriodicUniqueness.cubeIntegral_pressure_energy_zero` — `:435` (pressure term vanishes; needs
   periodicity of `p − q`).
4. `PeriodicUniqueness.exists_gradient_bound` — `:202` (compactness gradient bound `B`).
5. `MaximalLifespan.periodic_bound_on_slab` — `:130` (compactness bound of a continuous periodic field).

### 8. `MaximalLifespan.candidate_excludes_global_solution` — `MaximalLifespan.lean:237` (question 3)
Mechanism (`:246-258`): a global solution restricted to `lifespanDomain 2` is repackaged as
`ClassicalSolution f (fun _ => 0) 2 v q`; `candidate_no_solution_after_one` (`:168`) then derives
`False` — it uses `ClassicalSolution.agree_on_overlap` (`:79`, itself
`PeriodicUniqueness.classical_uniqueness_on_Icc`) for pre-one agreement, and
`unbounded_excludes_continuous_extension` (`:154`) + `periodic_bound_on_slab` (`:130`) to contradict
`speed_unbounded`. Load-bearing: `:93` uniqueness, `:130` compactness bound, `:159/:168` the
contradiction, `ProblemStatement.lean:159` `unbounded_speed_excludes_uniform_bound`. Every hypothesis
is an explicit argument, all discharged at the one call site (`ComparatorTheorem.lean:41-43`, from
`normalized_solution`, `ComparatorBridge.lean:217`). **No undischarged hypothesis.** It is however
**viscosity-one** machinery (`ProblemStatement.navierStokesResidual` has no `ν`), reached only through
the rescaling `rescaledForce` / `normalized_solution`; and, as noted, this decl is off the shipped path.
**[OK, unused]**

### 9. `ComparatorBridge.zero_initial_condition` — `ComparatorBridge.lean:136`
Proves `Comparator.InitialVelocityConditionPeriodic (fun _ : Space => (0 : Space))` by
`⟨⟨divergence_const, contDiff_const⟩, fun x i => rfl⟩` (`:138-142`). The exhibited datum on the (D)
route is literally `fun _ => 0` (`ComparatorTheorem.lean:37`, `PeriodicPaperComparator.lean:52`).
**[OK]**

### 10. `ComparatorBridge.forceConditionPeriodic_of_decay` — `ComparatorBridge.lean:117`
Real proof (`:124-134`): smoothness by `toComparator_smooth` (`:95`), periodicity transferred
pointwise, and the decay clause obtained by taking `K' = max K 0`, rewriting the comparator jet norm
into the project jet norm with `toComparator_jet_norm` (`:101`, a genuine argument through
`LinearIsometryEquiv.prodComm` and `norm_iteratedFDerivWithin_comp_right`), then `Real.rpow` monotonicity.
No hypothesis is left open; at the call site `forceConditionPeriodic_of_paper_candidate`
(`PeriodicPaperComparator.lean:21-27`) all three inputs come from `CandidateProperties` fields 30, 33, 41.
**[OK]**

### 11. `CandidateConsequences.futureJet_decay` — `CandidateConsequences.lean:79`
Real proof (`:85-110`): from `CompactFutureTimeSupport` get `T`; bound the jet on the slab
`Icc 0 (T+1)` by compactness (`MaximalLifespan.periodic_bound_on_slab`, using `futureJet_continuous`
`:33` and `futureJet_periodic` `:52`); set `C = M (2+T)^K`; for `t > T+1` the jet is exactly zero via
`CompactForceDecay.iteratedFDeriv_eq_zero_after`. This is an honest "compactly supported in time ⇒ any
polynomial time decay" argument, not a restatement. **[OK]**

### 12. Is the force non-zero? (question 4) — **[SUSPICIOUS / gap in the periodic branch]**
* Nothing in the periodic branch proves the emitted `f` is non-trivial. There is **no**
  `PeriodicPaper` analogue of the whole-space inhabitation check.
* Whole-space branch does have it: `R3/ProblemStatement.lean:189
  zero_force_has_global_solution (ν) : Nonempty (GlobalFiniteEnergySolution ν (fun _ => 0))`
  (zero velocity and pressure, `:191-200`), used by `R3/CandidateBreakdown.lean:53
  force_nonzero_of_no_global_solution` to conclude `∃ t > 0, ∃ x, f (t,x) ≠ 0`.
* Viscosity-one periodic branch also has it: `MaximalLifespan.lean:275
  candidate_force_nonzero_before_one` (`∃ t ∈ Ioo 0 1, ∃ x, f (t,x) ≠ 0`), proved from
  `zero_classical_solution_of_zero_force` (`:260`) plus uniqueness; recorded as field `force_nonzero`
  in `CandidateConsequences.Consequences` (`:140`, `:148`). But it applies to
  `ProblemStatement.CandidateProperties`, **not** to `PeriodicPaper.CandidateProperties` and not to the
  periodized force the deliverable exhibits.
* Consistency consequence, and why this matters: `PeriodicPaper.GlobalSmoothSolution ν (fun _ => 0)`
  is trivially inhabited (`velocity = pressure = fun _ => 0`: `ContDiffOn` const, both periodic,
  zero datum, zero divergence, zero residual — cf. the whole-space twin at
  `R3/ProblemStatement.lean:189` and `ProblemStatement.lean:141 zero_residual`). Hence if the `f`
  produced by `periodic_corollary` (`PeriodicPaperTheorem.lean:155`) were identically zero, that
  theorem would prove `False`. So a *provable* zero force would be a proof of inconsistency, and the
  cheapest decisive probe on this branch is to try to derive `Nonempty (GlobalSmoothSolution ν (fun _ =>
  0))` and combine it with `periodic_corollary`.
* No file:line proves the periodic force non-trivial. I state that plainly.

## Kernel-risk assessment

Greps over the 21 spine files listed in Scope (plus a repo-wide pass):

* `sorry` — **0** in `NavierStokes/` and `Euler/`. The only `sorry`s in the repo are the two intentional
  challenge placeholders `ComparatorChallenges/NavierStokes.lean:277, 283` (plus the Euler twin), and
  that module is imported by nothing in the proof libraries (checked by grep; only `lakefile.toml`,
  `formalization.yaml`, `README.md` name it).
* `admit` — 0. `axiom` — 0 declarations (2 hits are prose in `ProblemStatement.lean:8, 117`).
* `native_decide` — 0. `unsafe` — 0. `partial` — 0 (4 hits are `\partial` inside LaTeX doc-strings in
  `ComparatorDefinitions.lean:49, 128, 162, 195`).
* `set_option`, `macro`, `elab`, `syntax` — **0 in the whole repo's `.lean` files**.
* `termination_by`, `WellFounded`, `Acc.rec` — 0 in the spine files. Repo-wide they exist but off this
  branch's read set: `NavierStokes/SlowRecursion.lean:953, 964`, `NavierStokes/GlobalSlowProfiles.lean:910`
  (`rw [WellFounded.fix_eq]`), `NavierStokes/VolterraAnalyticBounds.lean:164, 184` (`termination_by
  w.length`), plus `Euler/*`. These are in the transitive closure of the *construction*
  (`ActualCandidateAssembly` chain), which this audit did not read.
* `decide` — **1 hit**: `NavierStokes/PeriodicUniqueness.lean:610`, `zero_pow (by decide : 2 ≠ 0)`.
  Trivial `Nat` decision, no kernel cost.
* `norm_num` — 7 hits, all on tiny rationals: `PeriodicPaperTheorem.lean:102` (`1/4 < 1/2`), `:132`
  (`0 < 1`), `ComparatorBridge.lean:51` (twice, small `ℕ∞`/order goals), `MaximalLifespan.lean:249, 250`
  (`1 < 2`, `0 < 2`), `CandidateConsequences.lean:178` (`3/4 < 1`), `PeriodicPaperScalingSupport.lean:109`
  (`1/4 < 1/2`).
* `Nat.pow` — 0 in spine files. Large numerals (≥ 5 digits) — 0 in spine files.
* `rfl` — 46 hits in spine files; each one I looked at closes a definitional-unfolding goal
  (`abbrev`/`def` unfolding for `toComparator`, `rescale`, `coordinateVector`, `derivWithin`), e.g.
  `ComparatorBridge.lean:58, 142`, `MaximalLifespan.lean:263-267`,
  `PeriodicViscosityUniqueness.lean:104, 109`. None is a `rfl` on recursive/inductive data or a numeral
  computation.
* Toolchain `leanprover/lean4:v4.34.0-rc2`, Mathlib pinned `v4.34.0-rc2` (`lakefile.toml`).
* Hygiene note: `lakefile.toml` sets `leanOptions = { autoImplicit = false, warningAsError = true }`
  **only for the `Euler` library**. The `NavierStokes` library (which carries (C)/(D)) has no
  `leanOptions`, so `autoImplicit`/`relaxedAutoImplicit` stay at their permissive defaults there.
  Low severity, but it means a mistyped identifier in a NavierStokes statement can silently become an
  auto-bound implicit universe/type variable rather than an error.
* `#print axioms` for both submission theorems is present at `ComparatorSolution.lean:31-32`, and
  `formalization.yaml:69-72` claims only `propext`, `Classical.choice`, `Quot.sound`. **Unverified here**
  — no build available.

Overall kernel risk of the periodic *spine*: low. Kernel risk of the *construction* below
`ActualCandidateAssembly` is unassessed.

## Escalations (ranked)

**E-A (highest value, mechanically checkable).** Force non-triviality on the periodic branch.
Question for an expert with a built Mathlib: *does
`theorem probe (ν : ℝ) : Nonempty (NavierStokes.PeriodicPaper.GlobalSmoothSolution ν (fun _ => 0))`
compile with `velocity := fun _ => 0`, `pressure := fun _ => 0`? If yes, then combined with
`PeriodicPaper.periodic_corollary` the emitted force `f` is provably not identically zero — and, more
importantly, if any independent argument ever forced `f ≡ 0` the repo would be inconsistent. Add the
lemma `∃ t ∈ Ioo 0 1, ∃ x, f (t,x) ≠ 0` for `PeriodicPaper.CandidateProperties`, mirroring
`MaximalLifespan.lean:275`, and check it goes through.* Currently no file:line establishes that the
shipped periodic force is non-zero.

**E-B.** Statement fidelity of the un-imported comparator copy. Question: *the submission proves the
(D) statement against `NavierStokes/ComparatorDefinitions.lean`, a copy of the frozen reference that is
never imported (`ComparatorSolution.lean:8`). I verified by code-line diff that all definitions are
identical (only the two `sorry` theorems are dropped). Does the `leanprover/comparator` tool
(`lakefile.toml` require, `ComparatorChallenges/NavierStokes.json`) in fact compare the elaborated
statement of `NavierStokes.Comparator.navier_stokes_breakdown_periodic` against the reference module,
and does it pass on this commit?* Without a build, the definitional identity is textual only.

**E-C.** Pressure-periodicity of the competitor. Question: *the exclusion consumes the competitor's
periodic pressure essentially (`PeriodicUniqueness.lean:533` via
`cubeIntegral_pressure_energy_zero`, `:435`). The comparator structure demands it
(`ComparatorDefinitions.lean:243` = `ComparatorChallenges/NavierStokes.lean:269`, "Clay errata"). Is the
upstream formal-conjectures periodic structure the accepted formalization of Clay (D), i.e. is
requiring `IsOnePeriodic (p · t)` of the competitor accepted?* This is an upstream-statement question,
not a defect of this repo. (Mathematically the restriction is harmless — on the torus one may normalise
the pressure — but that argument is not formalised here and is not needed for (D).)

**E-D.** Existentially bound force. Question: *the (D) force descends from `∃ forcing : VelocityField`
in `ActualCandidateAssembly.lean:1134` (`GermCandidateAssembly.exists_candidate_witness_of_finite_stages`,
`:1155`). Is that existence theorem proved unconditionally with all stage hypotheses discharged, and does
its own import closure (`SlowRecursion.lean`, `GlobalSlowProfiles.lean`, `VolterraAnalyticBounds.lean`
with `WellFounded.fix_eq` / `termination_by`) stay kernel-clean?* Out of scope for this branch audit.

**E-E (low).** Build hygiene. Question: *should the `NavierStokes` lean_lib get
`leanOptions = { autoImplicit = false, warningAsError = true }` as `Euler` already has
(`lakefile.toml`), and does the library still compile warning-free under those options?*

## Residue

* No `lake build` was possible (no Mathlib on disk, disk full), so: no `#print axioms` verification, no
  check that the files elaborate, no confirmation that the comparator harness accepts the (D)
  declaration. Every verdict above is a source-reading verdict.
* Unread on purpose: the deep construction under `ActualCandidateAssembly` /
  `ActualCandidateConstruction` / `GermCandidateAssembly` (hundreds of files) — the actual analytic
  content of Theorem 1.1 — and `NavierStokes/PeriodicUniqueness.lean` outside the ~200 lines cited
  (the Grönwall and cube-integration infrastructure was read only at its interfaces, e.g.
  `gronwall_zero`, `cubeIntegral_laplacian_energy`, `neg_coupling_le_energy` were not opened).
* Unread: `ComparatorR3Theorem.lean` and the whole (C) branch, `R3FiniteEnergyComparison.lean`,
  `PeriodicSobolev.lean`, `CompactForceDecay.lean` internals.
* Verdict counts: **OK 9**, **UNCLEAR 1** (existentially bound force, finding 6),
  **SUSPICIOUS 1** (no proof that the periodic force is non-zero, finding 12), **KERNEL-RISK 0**.
