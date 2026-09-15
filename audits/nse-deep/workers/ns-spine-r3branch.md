# R3 branch audit — NavierStokes deliverable spine

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (clone of openai/NavierStokesAndEuler @ `f9e8bc5`).
Method: **source-level only** (no `lake build`; no built Mathlib). Every claim below is a statement /
proof-term read, plus mechanical greps. Nothing was modified.

## Scope

Read in full or in the relevant part (24 files, ~60 declarations inspected closely):

| file | why |
|---|---|
| `NavierStokes/ComparatorSolution.lean` (33 L) | submission root, `#print axioms` |
| `NavierStokes/ComparatorR3Theorem.lean` (46 L) | `navier_stokes_breakdown_R3` |
| `NavierStokes/R3/Theorem.lean` (81 L) | `theorem_1_1`, `theorem_1_1_with_initial_rest` |
| `NavierStokes/R3/ActualCandidate.lean` (155 L) | `selected_candidate_one_with_initial_rest` |
| `NavierStokes/R3/ProblemStatement.lean` (222 L) | `CandidateProperties`, `GlobalFiniteEnergySolution` |
| `NavierStokes/ProblemStatement.lean` (168 L) | operators, `SpeedUnboundedAtOne` |
| `NavierStokes/R3/CandidateBreakdown.lean` (79 L) | `no_global_solution_one` |
| `NavierStokes/R3/WholeSpaceUniqueness.lean` (119 L) | comparison core |
| `NavierStokes/R3/WholeSpaceComparisonClosure.lean` (159 L) | energy/Young/Gronwall closure |
| `NavierStokes/R3/WholeSpaceEnergyLimit.lean` (93 L) | R -> infinity limit |
| `NavierStokes/R3/CompactComparisonBounds.lean` (157 L) | constants from compact support |
| `NavierStokes/R3/ComparisonRateBound.lean` (150 L) | Young absorption algebra |
| `NavierStokes/R3/PressureRecovery.lean` (440 L, main decls) | pressure-gradient recovery |
| `NavierStokes/R3/HarmonicTestFunctionals.lean` (112 L) | Liouville step |
| `NavierStokes/R3/PressureFlux.lean` (final thm) | flux bound assembly |
| `NavierStokes/R3/ViscosityScaling.lean` (197 L) | viscosity rescaling |
| `NavierStokes/R3/ComparatorBridge.lean` (90 L) | candidate -> option (C) |
| `NavierStokes/ComparatorR3Bridge.lean` (89 L) | comparator equation translation |
| `NavierStokes/ComparatorBridge.lean` (partial) | `toComparator`, `divergence_eq` |
| `NavierStokes/R3/PositiveTimeForce.lean` (82 L) | time cutoff of the force |
| `NavierStokes/R3/CompactEnergy.lean` (`uniform_finite_energy`) | energy bound |
| `NavierStokes/R3CompactCandidate.lean` (281 L) | periodic -> compact R^3 model |
| `NavierStokes/ActualCandidateAssembly.lean` (1100-1187) | `selected_witness` |
| `NavierStokes/GermCandidateAssembly.lean` (120-308) | `exists_candidate_witness_of_finite_stages` |
| `NavierStokes/BaseResidual.lean` (60-124), `NavierStokes/FinalSlowBase.lean` (250-385) | the **real** blow-up |
| `NavierStokes/SpatialLocalization.lean` (520-589), `NavierStokes/MixedPeriodicAssembly.lean` (300-370), `NavierStokes/CandidateFromLimits.lean` (82-183), `NavierStokes/CorrectionInitialization.lean` (3881-3990) | field/force definitions, concreteness of parameters |

Mechanical scan: the **transitive project-import closure of `NavierStokes/ComparatorSolution.lean` = 609
`.lean` files** (computed by parsing `import` lines; all resolved, none missing).

## Per-declaration findings

### 1. Route from the comparator statement down

**`NavierStokes.Comparator.navier_stokes_breakdown_R3`** — `NavierStokes/ComparatorSolution.lean:16`.
Statement = option (C) with `InitialVelocityConditionDecay u0`, `ForceConditionDecay f`, no
`NavierStokesExistenceAndSmoothnessRn`. Proof = `exact ComparatorBridge.navier_stokes_breakdown_R3`.
**Definitions check (bonus, cheap):** I normalised (strip blanks/`--`) and diffed
`NavierStokes/ComparatorDefinitions.lean` against `ComparatorChallenges/NavierStokes.lean`: the *only*
differences are the module docstring and the two `sorry` challenge theorems. All structures
(`ForceCondition(Decay)`, `InitialVelocityCondition*`, `NavierStokesExistenceAndSmoothness*`,
`divergence`, `gradient`, `IsOnePeriodic`, …) are **textually identical**. `ComparatorChallenges` is
**not** in the 609-file import closure. Verdict **[OK]**.

**`navier_stokes_breakdown_R3`** — `NavierStokes/ComparatorR3Theorem.lean:38`.
`obtain ⟨u,p,f,K,h,hglobal⟩ := NavierStokesR3.theorem_1_1 ν hν; exact comparator_of_breakdown h hglobal`.
Verdict **[OK]**.

**`NavierStokesR3.comparator_of_breakdown`** — `NavierStokes/R3/ComparatorBridge.lean:77`.
Supplies `u0 = 0` and `f` as the comparator force; force decay from compact space-time support
(`forceConditionDecay_of_compact`, :22); a comparator solution is converted to
`GlobalFiniteEnergySolution ν f` by `globalSolutionOfComparator` (:48), whose `navier_stokes` field is
`comparator_equation_Rn` (`NavierStokes/ComparatorR3Bridge.lean:34`). I checked that translation term by
term: comparator `derivWithin (v x) (Ici 0) t + Dv·v - ν Δv + ∇p = f x t` maps onto the project residual
`temporalDerivative + advection - ν • spatialLaplacian + pressureGradient` — viscosity multiplies **only**
the Laplacian, signs match, `toComparator f x t = f (t,x)` (`ComparatorBridge.lean:21`). Energy field is
built from `globally_bounded_energy` and `integrable`, i.e. the competitor really is only
smooth + zero datum + divergence-free + equation + uniformly bounded kinetic energy. Verdict **[OK]**.

**`NavierStokesR3.theorem_1_1`** — `NavierStokes/R3/Theorem.lean:46`, `= ProblemStatement.breakdownStatement`
(`NavierStokes/R3/ProblemStatement.lean:150`). Name matches statement. Verdict **[OK]**.

**`theorem_1_1_with_initial_rest`** — `NavierStokes/R3/Theorem.lean:26`.
Takes the viscosity-one candidate and applies `ViscosityScaling.candidate_at_viscosity` (:172 of
`ViscosityScaling.lean`) and `normalized_global_solution` (:182). I verified the scaling algebra:
`u_a(t,x) = a·u(t,a⁻¹x)`, `p_a = a²·p(t,a⁻¹x)`, `f_a = a·f(t,a⁻¹x)`, `a = sqrt ν`; every residual term
picks up exactly one factor `a` when the viscosity becomes `a²·1 = ν` (`rescale_residual`, :82). **Time is
not rescaled**, hence the singular time stays exactly `t = 1` for every `ν` — the doc claim is honest.
The extra conclusion `u = p = 0` for `|t| ≤ 3/8` is proved from the time-switch of the construction and
is *consistent* with blow-up at `t → 1⁻` (rest first, singularity later). Verdict **[OK]**.

### 2. `selected_candidate_one_with_initial_rest` and where u, p, f really live

**`ActualCandidate.selected_candidate_one_with_initial_rest`** — `NavierStokes/R3/ActualCandidate.lean:143`.
Statement: `∃ u p f K, ProblemStatement.CandidateProperties 1 u p f K ∧ ∀ |t| ≤ 3/8, ∀ x, u (t,x) = 0 ∧ p (t,x) = 0`.
Proof: `obtain ⟨a,_,ea,eb,ep,forcing,hc,hf,_⟩ := ActualCandidateAssembly.selected_witness` then
`of_localized_fields hc hf` (:78) + `TimeLocalization.activated{Velocity,Pressure}_zero_early`.
It is **not** a fixpoint: it consumes a concrete witness theorem. Chain:

* `ActualCandidateAssembly.selected_witness` — `NavierStokes/ActualCandidateAssembly.lean:1177`,
  `= witness selectedBudget selectedThreshold …` (:1153), all parameters concrete:
  `selectedBudget = 0`, `selectedThreshold = ActualCarrierGeometry.startingThreshold 0`
  (`NavierStokes/ActualCandidateConstruction.lean:205,207`), and `certificate/modulation/upper/h` are
  `abbrev`/`def`s of `FinalSlowBase.actualProfile` at `NavierStokes/CorrectionInitialization.lean:3886-3903`
  (`h := outgoing.data.h`, `upper := 2 * NominalConeAssembly.activeRight nominal`). **No un-instantiated
  section variable, so the witness is not vacuously parametric.** (B = 0 is a *budget* index, not an empty
  index set: the stage families `potentialStages/directStages/pressureStages` are still infinite in `j`.)
* `GermCandidateAssembly.exists_candidate_witness_of_finite_stages` — `NavierStokes/GermCandidateAssembly.lean:164`.
* The actual fields:
  * base velocity/pressure: `FinalSlowBase.velocity/pressure` — `NavierStokes/FinalSlowBase.lean:274,277`
    `= BaseResidual.baseVelocity (scales …) h W.axis.normalization (coefficients H v)`; `baseVelocity` is
    the axisymmetric stream/swirl field (`NavierStokes/BaseResidual.lean:73-79`,
    `AxisymmetricFields.velocity (streamFactor …) (swirlPotential …)`), i.e. an honest closed-form field.
  * stage sums: `SolenoidalDiagonal.potentialSum a (PhysicalWaveSum.physicalQ h) (…)`.
  * periodic model: `MixedPeriodicAssembly.periodicVelocity`, `SpatialLocalization.periodicPressure`,
    then `TimeLocalization.activated{Velocity,Pressure}` (time switch, zero for `|t| ≤ 3/8`).
  * **R^3 candidate fields**: `R3CompactCandidate.velocity A B` — `NavierStokes/R3CompactCandidate.lean:201`
    (`activatedVelocity (cutVelocity A + cutPotential B)`), `R3CompactCandidate.pressure P` — `:204`.
  * **force**: `PositiveTimeForce.force (R3CompactCandidate.compactForce f)` —
    `NavierStokes/R3/PositiveTimeForce.lean:46` ∘ `NavierStokes/R3CompactCandidate.lean:88`, where the inner
    `f` is `CandidateFromLimits.force` — **`NavierStokes/CandidateFromLimits.lean:82`:
    `SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)`.**

**Consequence (the single most important structural fact on this branch):** the force is *defined as the
Navier–Stokes residual of the prescribed velocity/pressure*, smoothly extended across `t = 1` using
boundary jet limits `L`. Therefore the `navier_stokes` field of `CandidateProperties` is essentially
definitional (`force_eq_activated_residual`, `CandidateFromLimits.lean:108`), and **all** mathematical
weight sits in (a) *smoothness / compact support / decay of that residual*, (b) the velocity blow-up, and
(c) the non-existence step. This is a legitimate reading of Clay option (C) (the force is arbitrary
`C_c^∞`), but it must be stated loudly. Verdict **[OK, structurally]** with escalation E1.

### 3. Is `speed_unbounded` non-degenerate? (item 2)

`SpeedUnboundedAtOne u` — `NavierStokes/ProblemStatement.lean:94`:
`∀ M > 0, ∀ δ > 0, ∃ t x, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t,x)‖`.
This is a genuine left-neighbourhood-of-one L∞ blow-up: no empty index set, no junk value, no vacuous
`tsupport` clause. Two sanity theorems are *proved* in the same file: `zero_velocity_not_unbounded` (:151)
and `unbounded_speed_excludes_uniform_bound` (:159). So a zero velocity cannot witness it.

Where the witness comes from (all *proved*, none assumed):

1. `FinalSlowBase.origin` — `NavierStokes/FinalSlowBase.lean:361`:
   for `t < 1`, `velocity H v upper B (t, 0) = ((1-t)^(-A h) * W.axis.j) • e₂`.
2. `FinalSlowBase.axis_tendsto` — `:372`: `‖velocity (t,0)‖ → ∞` as `t → 1⁻`, from
   `BaseResidual.baseVelocity_axis_tendsto_atTop` (`NavierStokes/BaseResidual.lean:104`) with
   `0 < A h` (`h ∈ (0,1/2)`) and `0 < W.axis.small.j_pos`. **The blow-up rate is the explicit
   `(1-t)^(-A h)`, at the spatial origin, exactly at `t = 1`.** Not degenerate.
3. `GermCandidateAssembly.origin_blowup` (`:146`) transports it to the diagonal stage sum
   (the angular part vanishes on the axis, `DirectAngularDiagonal.angularSum_axis`).
4. `MixedPeriodicAssembly.periodicVelocity_speed_unbounded` (`NavierStokes/MixedPeriodicAssembly.lean:322`)
   and `TimeLocalization.activatedVelocity_speed_unbounded` (`NavierStokes/TimeLocalization.lean:174`)
   keep it (the time switch is 1 near `t = 1`).
5. `R3CompactCandidate.local_model_unbounded` (`NavierStokes/R3CompactCandidate.lean:162`) moves the
   blow-up point by an integer lattice shift into `PeriodicLocalization.innerCube (1/4)`, where the
   *compactly supported* R^3 field agrees with the periodic one — so the compact candidate inherits it.
6. `ViscosityScaling.rescale_speed_unbounded` (`NavierStokes/R3/ViscosityScaling.lean:93`) keeps it at
   every viscosity, with the same time `t`.

`K = SpatialLocalization.supportCylinder` = `{radialSquare x ≤ 1/16 ∧ |x 2| ≤ 1/4}` — genuinely compact
(`isCompact_supportCylinder`), and it contains the origin, i.e. the blow-up point.
`energy_bounded` is a real `UniformFiniteEnergy (Ico 0 1)` with an explicit integrability side condition
(`R3/ProblemStatement.lean:81`), proved by `CompactEnergy.uniform_finite_energy`
(`NavierStokes/R3/CompactEnergy.lean:343`) via the forced energy identity + Gronwall
(`ScalarEnergyBound.forced_gronwall_uniform`). L∞ blow-up with bounded L² energy is consistent
(concentration), so there is no internal contradiction visible at this level.
Consistency with `u = p = 0` for `|t| ≤ 3/8`: fine — rest on `[-3/8,3/8]`, blow-up as `t → 1⁻`.
Verdict **[OK]**.

### 4. `no_global_solution_one` — the load-bearing non-existence step (item 3)

It is a **theorem**, not a field: `ProblemStatement.CandidateProperties.no_global_solution_one` —
`NavierStokes/R3/CandidateBreakdown.lean:43` (dot notation on `hc` at `R3/Theorem.lean:36`).
Two-line proof: `rintro ⟨v⟩; exact h.not_global_agreement v.velocity_smooth
  (WholeSpaceUniqueness.candidate_global_agrees_before_one h v)`.

Mechanism = **whole-space weak–strong/classical uniqueness (localized energy + Young + Gronwall +
R → ∞), then a compactness contradiction with the blow-up**. Key lemmas:

1. `CandidateProperties.not_global_agreement` — `R3/CandidateBreakdown.lean:18`. If the candidate agreed
   with a globally smooth `v` on `Ico 0 1`, then `v` is bounded by `M` on the *compact* set
   `Icc 0 1 ×ˢ K` (`exists_bound_of_continuousOn`), while `speed_unbounded` produces `‖u(t,x)‖ > max M 1`
   with `x ∈ K` (from `velocity_support`) — contradiction. Elegant and correct. **[OK]**
2. `WholeSpaceUniqueness.candidate_global_agrees_before_one` — `R3/WholeSpaceUniqueness.lean:104` →
   `candidate_unique_on_Icc` (`:72`, every `T < 1`, degenerate case `T ≤ 0` handled by the zero datum) →
   `classical_uniqueness_on_Icc` (`:30`). **[OK]**
3. `WholeSpaceComparisonClosure.eq_of_pressure_flux_bound` — `R3/WholeSpaceComparisonClosure.lean:32`.
   Localized energy balance `LocalizedDifferenceEnergy.difference_energy_balance` for
   `w = u - v` against `weight R = cutoff R ^ 8`; transport flux, weight-Laplacian flux and pressure flux
   are bounded; `WeightedSobolev.cutoffL6_le` gives `B ≤ S(A + M/R)`; `ComparisonRateBound` absorbs
   everything into `E' ≤ 2G·E + D/R`. **The dissipation term `A²` is retained and is what absorbs the
   trilinear/pressure errors** (`R3/ComparisonRateBound.lean:127-148`, Young with `δ = 1/2`); I checked
   the exponent bookkeeping by hand (`R⁻¹A^{3/2}`, `R^{-7/4}A^{3/4}`, `R⁻¹A` all ≤ `δA² + C·R^{-1}`). **[OK]**
4. `WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound` — `R3/WholeSpaceEnergyLimit.lean:70`:
   Gronwall from `E(0) = 0` gives `E_R(t) ≤ C·T·e^{KT}/R`, then dominated convergence
   (`integral_weight_tendsto`, `:25`, `weight ≤ 1`, `weight → 1`) forces `l2Sq w = 0`, hence `w ≡ 0`
   (continuity + no atom). **[OK]**
5. `PressureFlux.exists_uniform_actual_pressure_flux_bound` — `R3/PressureFlux.lean:576`, resting on
   `PressureRecovery` with `Hypotheses` = *exactly* smoothness + both divergence conditions + equality of
   the two residuals + uniform finite energy of both fields (`R3/PressureRecovery.lean:33`). The pressure is
   **not** normalised by fiat: `gradient_recovery` (`:407`) proves that `∫ ∂_k(p-q)·ψ` equals the canonical
   Riesz pairing of `u⊗u - v⊗v`, and the harmonic ambiguity is killed by
   `HarmonicTestFunctionals.eq_zero_of_compact_harmonic` (`R3/HarmonicTestFunctionals.lean:100`): a
   complex-linear Schwartz functional bounded by the Fourier `H³` norm has an `L²` representative
   (`HilbertFunctionalExtension`), annihilating Laplacians forces the representative to vanish off the
   origin, and `volume` has no atom there. This is the mathematically right way to handle "no growth
   condition on the competitor pressure". **[OK]** — with escalation E2 (I did not re-derive
   `averagedPressureDifference_bound`, `LocalizedFluxEstimates`, `ComparisonYoung`, `RieszTestOperators`).

**Hypotheses that could have been suspicious, and how they are discharged:**

* `hvanish` (`WholeSpaceComparisonClosure.lean:47`) — `fderiv (weight R) x (u (t,x)) = 0` looks like it could
  trivialise the localization. It is discharged by `CompactComparisonBounds.exists_radius_weight_derivative_zero`
  (`R3/CompactComparisonBounds.lean:112`): for `R ≥ max 1 (C+1)` with `K ⊆ ball C`, either `x ∈ K` and
  `weight R` is *locally constant* there (`weight_fderiv_eq_zero_of_norm_lt`, `:102`), or `u (t,x) = 0`.
  It only kills the *candidate's* transport flux, not the competitor's (`v`'s term is kept and estimated,
  `htflux'`). **Not vacuous, not circular.** **[OK]**
* `hG` gradient bound for `u` (`exists_gradient_bound`, `:33`) — legitimate, from compact support.
* No support / decay / growth condition is imposed anywhere on the competitor `v` or `q`: I checked
  `GlobalFiniteEnergySolution` (`R3/ProblemStatement.lean:125`) field by field. `zero_force_has_global_solution`
  (`:189`) shows the competitor class is inhabited (so the exclusion is not by an empty class), and
  `force_nonzero_of_no_global_solution` (`R3/CandidateBreakdown.lean:53`) shows the excluding force must be
  nonzero at a positive time. Both are good anti-degeneracy checks *by the authors*. **[OK]**

## Kernel-risk assessment (item 4)

Grep over the 24 files read — every hit listed:

* `decide`: **2** — `R3/CompactComparisonBounds.lean:68` `(by decide : (3:ℕ) ≠ 0)` and `:145`
  `(by decide : (2:ℕ) ≠ 0)`. Trivial `Nat` inequality; kernel cost O(1).
* `native_decide`: **0**. `Nat.pow`: **0**. `Acc.rec`: **0**. `WellFounded`: **0**. `termination_by`: **0**.
  `macro`/`elab`/`syntax`: **0**. `set_option`: **0**. `axiom` declaration: **0** (the 2 hits are the words
  "axiom" in docstrings of `NavierStokes/ProblemStatement.lean:8,117`; the 2 in
  `ComparatorSolution.lean:31,32` are `#print axioms` *commands*). `unsafe`: **0**. `sorry`/`admit`: **0**.
  All 69 "partial" hits are the identifiers `partialD` / `spatial_partial` — false positives.
* `rfl`: 93 hits, all `le_rfl` / `Finset.sum_congr rfl` / definitional unfolding of `smul` on
  `EuclideanSpace`; **no `rfl` on recursive data**.
* Largest numeral in the files read: **32** (in `1/32`), then `21/16`, `16`, and the exponent `8` in
  `weight R = cutoff R ^ 8`. Nothing the kernel must evaluate beyond machine-word arithmetic.

Whole-submission scan (609-file transitive import closure of `NavierStokes/ComparatorSolution.lean`,
all imports resolved, `ComparatorChallenges` **not** among them):

* `sorry` / `admit`: **0**. `axiom` declarations: **0**. `native_decide`: **0**. `set_option`: **0**
  (so no `maxHeartbeats`/`skipKernelTC`-style escape hatch anywhere). `unsafe` / `partial def` /
  `@[implemented_by]`: **0**.
* `termination_by`: **2** (`NavierStokes/VolterraAnalyticBounds.lean:164,184`, on `w.length` — structural,
  on `List`). `WellFounded.fix_eq` rewrites: **3** (`SlowRecursion.lean:953,964`,
  `GlobalSlowProfiles.lean:910`) — used as an equation lemma, no `Acc.rec` in a proof term.
* `by decide` : **86**, sampled ~15: all `(2:ℕ) ≠ 0`, `(0:Fin 3) ≠ 2`, `0 < 1`, `1 ≤ 2`-style goals.
* Largest numerals in the whole closure: `1/1000000` (`ExponentLedger.lean:276`),
  `4501/500000` (`MatchingConeBounds.lean:48`), `1/100000` (`SignedMeanGain.lean`, `PulseCone.lean`).
  These are *real* rational literals inside `norm_num`/`nlinarith` goals — binary `Nat` literals of ~20
  bits; no `Nat.pow` towers, no `decide` on big arithmetic. **Kernel-evaluation risk on this branch: low.**
* Caveat: I could **not** run `#print axioms` (no built Mathlib, disk full), so the claim "only `propext`,
  `Classical.choice`, `Quot.sound`" is *plausible from the source* (no `axiom`, no `sorry`, heavy but
  legitimate `Classical.choice`, e.g. `CorrectionInitialization.lean:3929`) but **not machine-verified here**.

## Escalations (ranked)

**E1 — The force is the residual, so the whole theorem hinges on residual regularity at `t = 1`.**
`CandidateFromLimits.force := SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)`
(`NavierStokes/CandidateFromLimits.lean:82`), with `L = MixedPeriodicAssembly.boundaryLimits …` and the
input `TendstoLocallyUniformly (iteratedFDeriv n (periodicResidual …)) (L · n) (𝓝[<] 1)`
(`MixedPeriodicAssembly.lean:310`), itself from `JointResidualLimits.VanishingJointJets` supplied by
`StageEstimates` in the construction branch.
*Exact question for an expert:* **is `VanishingJointJets`/`StageEstimates` actually established for the
selected schedule (`GermCandidateAssembly.exists_candidate_witness_of_finite_stages`, hypothesis `E`,
`NavierStokes/GermCandidateAssembly.lean:169`), i.e. does every iterated space-time derivative of the
residual of the blow-up field converge locally uniformly as `t → 1⁻`, uniformly enough for
`SpacetimeGluing.smoothExtension` to be `C^∞` across `t = 1`?** If that fails, `ForceConditionDecay`
fails and option (C) is not proved. This is *outside* the R3 branch but it is the branch's single input.

**E2 — Unverified analytic sub-modules of the uniqueness argument.** I read the statements and the
composition, not the interiors, of: `LocalizedFluxEstimates.{neg_coupling_le_weightedEnergy,
weight_laplacian_flux_bound, transport_flux_bound}`, `ComparisonYoung.exists_cutoff_absorption`,
`WeightedSobolev.cutoffL6_le`, `PressureFlux.exists_uniform_canonicalCutoffFlux_bound` +
`actual_flux_integrable_and_le_canonicalNorm`, `PressureRecovery.averagedPressureDifference_bound`,
`RieszTestOperators.*`. *Exact question:* **do the flux estimates and the `H³` functional bound hold with
constants independent of `R` and `t`, in particular is `averagedPressureDifference_bound`'s constant built
only from the L²/L³/L¹ bounds `M₀, U₀, G₀` (finite energy) and not from any hidden decay of `q`?**

**E3 — `#print axioms` not machine-checked.** *Exact question:* **run `lake build NavierStokes.ComparatorSolution`
and confirm the two `#print axioms` lines report only `propext, Classical.choice, Quot.sound`.**

**E4 — Definitional faithfulness of the comparator layer.** I verified `ComparatorDefinitions.lean` is a
character-for-character copy of the challenge definitions, but not that the challenge file itself is
faithful to Fefferman (e.g. `derivWithin … (Ici 0)`, the `ForceConditionDecay` derivative-decay exponents).
*Exact question:* **is `ComparatorChallenges/NavierStokes.lean` an unmodified copy of the DeepMind
formal-conjectures reference at commit `8bf45ed`?** (owner: comparator/definitions branch)

## Residue

* Not audited here (other branches): the periodic construction interior (`ActualCandidateConstruction`,
  `CorrectionInitialization`, `PulseCone`, `SignedMeanGain`, `SlowRecursion`, ~580 files), the
  `ComparatorTheorem`/periodic option (D) route, `Euler/`.
* `ComparatorChallenges/{Euler,NavierStokes}.lean` contain 4 `sorry`s — intentional challenge
  placeholders, **not** imported by the submission (verified by import-closure computation).
* No build was run; all verdicts are source-level. If a declaration name in this report is later found to
  elaborate differently than its printed statement suggests, the affected verdict must be revisited.

## Verdict counts

* **[OK]: 14** (comparator root & definitions diff, `navier_stokes_breakdown_R3`, `comparator_of_breakdown`
  + `comparator_equation_Rn`, `theorem_1_1`, `theorem_1_1_with_initial_rest` + viscosity scaling,
  `selected_candidate_one_with_initial_rest` chain to concrete fields, `speed_unbounded` non-degeneracy,
  `not_global_agreement`, `candidate_global_agrees_before_one`, `eq_of_pressure_flux_bound`,
  `eq_zero_of_weighted_rate_bound` + `ComparisonRateBound`, pressure recovery + Liouville step,
  `hvanish` discharge, `PositiveTimeForce`/`compactForce` equation preservation)
* **[UNCLEAR]: 2** (E1 residual-jet input to the force; E2 unread analytic sub-modules)
* **[KERNEL-RISK]: 0**
* **[SUSPICIOUS]: 0** — but see E1: "the force is defined as the residual" means the *name*
  `navier_stokes` in `CandidateProperties` is definitional bookkeeping, not a solved PDE.
