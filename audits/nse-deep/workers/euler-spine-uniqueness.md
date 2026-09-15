# NSE deep audit — worker: Euler Comparator↔Evolution identification / local conversion / uniqueness

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5,
Lean 4.34.0-rc2 + Mathlib rev 85e3a25e). **Read-only, source-level only** (no Mathlib build, no
`lake build`; disk full). Mathlib statements checked by fetching raw sources at rev 85e3a25e.

## Scope

Entry points read **in full** (line counts):

| file | lines | read |
|---|---|---|
| `Euler/ComparatorEvolutionIdentification.lean` | 131 | full |
| `Euler/ComparatorLocalEvolution.lean` | 99 | full |
| `Euler/ComparatorLocalCompactVorticity.lean` | 182 | full |
| `Euler/ComparatorTruncationFamily.lean` | 105 | full |
| `Euler/CompactVorticityTimeUpgrade.lean` | 200 | full |
| `Euler/CompactProjectedEulerLaw.lean` | 68 | full |
| `Euler/DivCurlTensorRecovery.lean` | 154 | full |
| `Euler/ComparatorUniformSpatialJets.lean` | 96 | full |
| `Euler/CompactCurlBounds.lean` | 32 | full |

Dependency files read in full or in the decisive region (chased because the scope questions
cannot be answered without them): `Euler/SolutionDefinitions.lean` (138, full),
`Euler/OrdinaryEulerDifference.lean` (150, full), `Euler/OrdinaryEulerUniqueness.lean` (47, full),
`Euler/OrdinaryGradientStability.lean` (74, full), `Euler/OrdinaryEulerL2Stability.lean` (regions),
`Euler/OrdinaryEulerGradientControl.lean` (1–50), `Euler/OrdinaryEulerClassicalClass.lean` (180–276),
`Euler/OrdinaryEulerSobolevClass.lean` (1–60), `Euler/OrdinaryHelmholtzField.lean` (1–90),
`Euler/EvolutionTimeShift.lean` (72, full), `Euler/OrdinaryEulerRestriction.lean` (44, full),
`Euler/ComparatorTimeShift.lean` (55, full), `Euler/CompactSolenoidalDensity.lean` (60–192),
`Euler/WeakHilbertODE.lean` (80–206), `Euler/NoIncomingVorticity.lean` (40–154),
`Euler/CompactProjectedPairing.lean` (67, full), `Euler/ProjectedEulerPairing.lean` (90–160),
`Euler/LpSmoothField.lean` (20–70), `Euler/MeanOrbitSmoothL2Field.lean` (20–60),
`Euler/MeanSobolevBoundedField.lean` (60–125), `Euler/TruncationFamily.lean` (27, full),
`Euler/ComparatorIdentification.lean` (46, full), `Euler/Solution.lean` (75, full),
`Euler/ClassicalBridge.lean` (14–45), `Euler/WeakTimeContinuity.lean` (50–100),
`Euler/ReversedVorticityTransport.lean` (1–56), `Euler/LpSmoothJetField.lean` (1–60).

Skimmed by grep only: `Euler/ScalarEulerVorticity.lean`, `Euler/SmoothFieldSobolevTime.lean`,
`Euler/OrdinaryWordTime.lean`, `Euler/TruncatedBackwardFlow.lean`, `Euler/LocalFlowTrap.lean`,
`Euler/SmoothCoefficientTimeRestriction.lean`, `Euler/OrdinaryEulerMaximal.lean`.

Declarations audited with statement **and** proof term: 34 (table below).
Mechanical grep census over the full transitive import closure of
`Euler.ComparatorLocalEvolution` (939 `Euler/*.lean` files) for kernel-risk tokens: see
*Kernel-risk assessment*.

## Per-declaration findings

| # | decl | file:line | what the statement really says | actual proof mechanism | verdict |
|---|---|---|---|---|---|
| 1 | `SmoothL2Field` (structure) | `Euler/LpSmoothField.lean:31-34` | 3 fields: `field : Space → V` (the ONLY data field), `smooth : ContDiff ℝ ∞ field`, `integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume`. Both non-data fields are `Prop`. | — | OK |
| 2 | `smoothL2Field_of_curl_compact` | `Euler/DivCurlTensorRecovery.lean:79-85` | From `ContDiff ℝ ∞ u`, `MemLp u 2`, `div u = 0`, `HasCompactSupport (curl u)` builds a `SmoothL2Field` with `field := u`. | Plain structure literal: `field := u` (l.83), `smooth := hu` (l.84), `integrable := iteratedFDeriv_memLp_of_curl_compact …` (l.85). No choice, no recursion, no fallback. | OK |
| 3 | `iteratedFDeriv_memLp_of_curl_compact` | `Euler/DivCurlTensorRecovery.lean:66-75` | All Fréchet tensors of a smooth solenoidal finite-energy field with compact vorticity are in `L²`. | Reduce to scalar coordinate words (`MemLp.of_eval`, `iteratedFDeriv_coordinate_word` l.23), then reassemble by the CLE `tensorReassembly`. Elliptic content is in `component_wordDerivative_memLp` (not re-read; grep-located only). | OK (mechanism), see Residue |
| 4 | `Euler.ComparatorBridge.recoveredVelocity` | `Euler/ComparatorLocalEvolution.lean:31-39` | For each `t ∈ [0,T]`, the `SmoothL2Field` built by (2) from the Comparator slice `v · t`. | `fun t => smoothL2Field_of_curl_compact (v · t) (h.velocity_contDiff …) (h.velocity_memLp …) (h.div_free …) (hK.of_isClosed_subset …)`. | OK |
| 5 | `recoveredVelocity_field` | `Euler/ComparatorLocalEvolution.lean:41-45` | `(recoveredVelocity … t).field = (v · t)`, proved `rfl`. | **Cheap `rfl`**: beta-reduce (4), then project field #1 of a *literal* `SmoothL2Field` constructor application. One iota/proj step. No `Nat.rec`, no `Acc.rec`, no structure-eta trick, no numerals. (Same `rfl` reused at l.71.) | OK |
| 6 | `recoveredVelocity_jetLp_uniform` | `Euler/ComparatorLocalEvolution.lean:49-60` | Each order `n` has a uniform bound `‖jetLp n‖ ≤ M` over `t ∈ [0,T]`. | `jetLp_norm_uniform_of_coordinate_energy` (`DivCurlTensorRecovery.lean:126`) fed by `component_word_energy_uniform_of_commonCompactCurl`. Genuine `√` of a finite coordinate-energy sum (`max C 0` guard, `Real.le_sqrt`). | OK |
| 7 | `component_word_energy_uniform_of_commonCompactCurl` | `Euler/ComparatorUniformSpatialJets.lean:72-94` | Uniform-in-time `L²` energies for every scalar coordinate word derivative of `v`. | Elliptic: `Δ v = -curl curl v` (l.25, uses `div_free`), so `tsupport (Δ v·t) ⊆ tsupport (curl v·t) ⊆ K`; uniform compact-support source energies (l.56) + `component_wordDerivative_energy_uniform`. Energy input is the *hypothesis* field `globally_bounded_energy` (l.86). | OK |
| 8 | `vorticity_bounded_on_compact` | `Euler/CompactCurlBounds.lean:19-30` | `∃ M ≥ 0, ∀ t ∈ [0,T], ∀ x ∈ K, ‖curl (v·t) x‖ ≤ M`. | `spatial_fderiv_bounded_on_compact` + `vectorCurl_eq_matrix` + `curlMatrixCLM.le_opNorm`; `max C 0` keeps `M ≥ 0`. Not vacuous, not used in this sub-chain (only in `CompactVorticityContradiction.lean:24`). | OK |
| 9 | `isSmoothScalarEuler_of_weak_projectedEquation` | `Euler/CompactVorticityTimeUpgrade.lean:144-198` | Weak (dense-tested) projected Euler equation + uniform spatial `tensorNorm` bounds ⟹ full `IsSmoothScalarEuler`. Conclusion (all-order jet continuity + strong `L²` time law) is **not** among the hypotheses. | Real analysis: bounded projected RHS (l.129/173) ⟹ `LipschitzOnWith` via `WeakHilbertODE.lipschitzOnWith_of_dense_weak_equation` (l.175) ⟹ strong `L²` continuity ⟹ `jetLp` continuity by interpolation (`jetLp_continuous_of_toLp_continuous`, l.83, squeeze on `√(‖Δu‖·M)`) ⟹ strong derivative via `hasDerivAt_of_dense_weak_equation` (l.192). | OK |
| 10 | `WeakHilbertODE.hasDerivAt_of_dense_weak_equation` | `Euler/WeakHilbertODE.lean:196-204` | Dense weak derivative + continuous vector RHS ⟹ strong `HasDerivAt` in `H`. | FTC + `eq_of_dense_inner_eq`: dense scalar identity ⟹ vector integral identity (l.109), primitive differentiation (l.138). Mathematically correct; no hidden assumption of the conclusion. | OK |
| 11 | `compactSolenoidalTests` | `Euler/CompactSolenoidalDensity.lean:141-142` | The set of `L²` classes of `curl φ` for `φ` compactly supported smooth. | — | OK |
| 12 | `compactSolenoidalTests_representation` | `Euler/CompactSolenoidalDensity.lean:145-153` | Every member has an actual compact smooth divergence-free representative. | Destructs the range witness, uses `divergence_curl`. Honest — the test family is *not* all of `solenoidalSpace`. | OK |
| 13 | `compactSolenoidalTests_dense` | `Euler/CompactSolenoidalDensity.lean:164-180` | `Dense compactSolenoidalTests` in `solenoidalSpace`. | Genuine Weyl-type argument: orthogonal complement ∩ solenoidal = ⊥ because an annihilating solenoidal field is weakly harmonic hence 0 (l.103-126), then `Subtype.dense_iff`. Non-vacuous (the space is nontrivial), non-trivial. | OK |
| 14 | `comparator_projected_pairing_hasDerivAt` | `Euler/CompactProjectedEulerLaw.lean:55-66` | For each compact solenoidal test, the pairing `t ↦ ⟪g, (A t).toLp⟫` is differentiable with derivative `⟪g, projectedRhs (A t)⟫`. | Reduces to `comparator_clamped_compact_pairing_hasDerivAt` (`ProjectedEulerPairing.lean:140`) whose engine `velocity_solenoidal_test_pairing_hasDerivAt` (`:102`) **uses `h.pointwise_euler x t₀ ht₀` at `ProjectedEulerPairing.lean:95`** and kills the pressure by `compact_solenoidal_pressure_pairing_zero`. | OK — the Euler equation is genuinely consumed |
| 15 | `projectedRhs` / `pressureField` | `Euler/OrdinaryHelmholtzField.lean:60-81` | `projectedRhs A = -P(A·∇A)`, `pressureField A = P(A·∇A) − A·∇A`; `pressureField ∈ gradientSpace` (l.74) and `projectedRhs.field = -A·∇A − pressureForce` (l.78). | Leray projection `solenoidalProjection = solenoidalSpace.starProjection` (`MeanSolenoidalSpace.lean:104`); smoothness of the projected field via `smoothL2Field` from a *proved* `SmoothOrbit` (`MeanOrbitSmoothL2Field.lean:41`), not a choice-with-fallback. | OK |
| 16 | `IsSmoothScalarEuler` | `Euler/OrdinaryEulerClassicalClass.lean:194-206` | Jet continuity + ∃ derivative field `B` and scalar pressure `p` with strong `L²` time law, `div = 0`, and pointwise `B + A·∇A + ∇p = 0`. | — | OK |
| 17 | `scalarEuler_iff_projected` | `Euler/OrdinaryEulerClassicalClass.lean:245-269` | Scalar-pressure form ⟺ projected form. | `.mpr` builds the pressure from `evolutionOfProjectedEquation` + `scalarPressure_spec`; `.mp` is `isSmoothProjectedEuler_of_scalarEuler`. Honest both ways. | OK |
| 18 | `exists_evolution_iff_scalar` | `Euler/OrdinaryEulerClassicalClass.lean:271-274` | `(∃ U : Evolution T hT, U.velocity = A) ↔ IsSmoothScalarEuler A`. | Composition of `exists_evolution_iff_projected` (`OrdinaryEulerSobolevClass.lean:44`) and (17). The `.mpr` really CONSTRUCTS the record (`evolutionOfProjectedEquation`, `:24`), pressure force `:= pressureField (A t)`. | OK |
| 19 | `Evolution` (structure) | `Euler/OrdinaryEulerDifference.lean:21-32` | `velocity`, `pressureForce : Icc 0 T → SmoothL2Field`, all-order jet continuity of both, `velocity ∈ solenoidalSpace`, `pressureForce ∈ gradientSpace`, and a **pointwise** `HasDerivAt` momentum law `∂ₜu(x) = -Du(x)·u(x) − F(x)` on `Ioo 0 T`. | — | OK — genuine smooth Euler evolution, no junk-satisfiable field |
| 20 | `exists_evolution_of_commonCompactCurl` | `Euler/ComparatorLocalEvolution.lean:64-86` | A Comparator solution with a common compact vorticity support on `[0,T]` is realized by an actual `Evolution T` with `(U.velocity t).field = v · t`. | Assembles (5),(6),(9),(13),(14) then `(exists_evolution_iff_scalar).mpr`. Every obligation of (9) discharged: solenoidality from `h.div_free`, weak continuity from `h.velocityLp_weakly_continuous` (`WeakTimeContinuity.lean:81`, itself from `globally_bounded_energy`). | OK |
| 21 | `local_compact_vorticity_of_truncationFamily` | `Euler/ComparatorLocalCompactVorticity.lean:159-171` | `∃ δ B, 0 < δ ∧ ∀ t ∈ [0,δ], tsupport (curl (v·t)) ⊆ closedBall 0 B`. | Real argument: (i) compact spacetime cylinder gives `A, M, δ` with `δM < 1` (l.32); (ii) truncated global backward flows built at l.73-155; (iii) `BackwardVorticityFlows.support_subset_closedBall`. | OK |
| 22 | `BackwardVorticityFlows` + `support_subset_closedBall` | `Euler/NoIncomingVorticity.lean:48-68`, `:142` | Bundle of measure-preserving approximate backward characteristics with `energy_bound`, `curve_derivative`, `transport_nonzero`, `forward_trap`; conclusion: `support w ⊆ closedBall 0 supportRadius`. | Genuine energy/measure argument: escaping trajectories cost `energy·T²/(R−K₀)²` (l.100), let `R → ∞` ⟹ null set (l.114), then continuity upgrades a.e. to pointwise (l.131). Not vacuous, not circular. | OK |
| 23 | `locallyTrappedBackwardFlows` | `Euler/ComparatorLocalCompactVorticity.lean:73-155` | Constructs (22) for the truncated velocities. | Every field is discharged with a real proof (12 `?_` all filled). `transport_nonzero` uses `h.vorticity_ne_zero_along_reverse_trajectory` (l.124), `forward_trap` uses `norm_lt_of_local_speed_bound` with `T·M < 1`. | OK |
| 24 | `vorticity_ne_zero_along_reverse_trajectory` | `Euler/ReversedVorticityTransport.lean:21-41` | Nonzero vorticity at the endpoint of a reverse trajectory forces nonzero initial vorticity. | Time-reverses the path and applies `vorticity_eq_zero_along_trajectory` (`ScalarEulerVorticity.lean:83`), which consumes `h.vorticity_material_derivative` (`:47`), i.e. the Euler vorticity equation. | OK |
| 25 | `finiteEnergyTruncationFamily` | `Euler/ComparatorTruncationFamily.lean:69-103` | Produces `FiniteEnergyTruncationFamily v` (`TruncationFamily.lean:16-25`: divergence-free, `MemLp`, uniform energy, and *agreement* `coefficient R = v` for `‖x‖ < R`). | Radial-potential truncation of the actual solution, square-time reparametrization; `energy := truncationEnergyConstant * h.globally_bounded_energy.choose` (l.81). `Classical.choose` of a **hypothesis-supplied true** existential (`SolutionDefinitions.lean:80`) with its `choose_spec` actually used at l.98 — not junk-value exploitation. | OK |
| 26 | `HasLocalEvolutionAtCompactCurl` | `Euler/ComparatorEvolutionIdentification.lean:30-33` | For every `a ≥ 0` with compact `curl (v·a)`: `∃ δ > 0` and `U : Evolution δ` with `(U.velocity t).field = v · (a+t)` on `[0,δ]`. Contains no comparison/uniqueness claim. | — | OK |
| 27 | `CompactCurlLocalUpgrade` | `Euler/ComparatorEvolutionIdentification.lean:37-41` | Same at `a = 0` for every Comparator solution with compact initial vorticity. | — | OK |
| 28 | `compactCurlLocalUpgrade` (the DISCHARGE) | `Euler/ComparatorLocalEvolution.lean:91-97` | `CompactCurlLocalUpgrade` is **proved**, not assumed. | `local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc` (l.94) then `exists_evolution_of_commonCompactCurl` on `closedBall 0 B` (l.95-96). Used at `Euler/Solution.lean:30`. | OK |
| 29 | `EulerExistenceAndSmoothnessR3.shiftTime` | `Euler/ComparatorTimeShift.lean:19-53` | Time translation preserves the hypothesis record for data `(v·a, v(a+·), p(a+·))`. | All 7 fields discharged: chain rule for the one-sided `derivWithin` (l.34-45), composition for both `ContDiffOn` fields, and the energy existential re-used with the same `E` (l.52). Faithful. | OK |
| 30 | `hasLocalEvolutionAtCompactCurl_of_upgrade` | `Euler/ComparatorEvolutionIdentification.lean:43-48` | Local upgrade at `t = 0` + time-shift ⟹ local upgrade at every `a ≥ 0`. | `hupgrade (v · a) (fun x t => v x (a+t)) … (h.shiftTime a ha) hc`; the two conclusions are definitionally equal (`(v·(a+t))`). | OK |
| 31 | `Evolution.shiftTime` / `restrictTime` | `Euler/EvolutionTimeShift.lean:29-50`, `Euler/OrdinaryEulerRestriction.lean:18-32` | Restart/restrict an evolution; velocity is literally `U.velocity ∘ (time inclusion)`. | Structure literals over `shiftTimeMap` (`:15`) / `initialInclusion` (`SmoothCoefficientTimeRestriction.lean:84`); `time_law` transported by `HasDerivAt.comp_const_add` and `congr_of_eventuallyEq`. `shiftTime_initial` (`:62`) and `restrictTime_initial` (`:37`) are cheap `rfl`/`Subtype.ext`. | OK |
| 32 | `Evolution.velocity_eq_of_initial` | `Euler/OrdinaryEulerUniqueness.lean:24-30` | Two `Evolution T hT` with equal initial `toLp` have equal velocity at **every** `t ∈ [0,T]` (as `SmoothL2Field`, i.e. pointwise). | **Genuine `L²` energy/Gronwall uniqueness.** `l2_stability_gradientIntegral` (`OrdinaryGradientStability.lean:54`): `‖w(t)‖ ≤ ‖w(0)‖·exp(∫‖∇u‖_∞)`; derived from `d/dt‖w‖² = 2⟪w, differenceRhs⟫ ≤ 2‖∇u‖_∞‖w‖²` (`:18`), which uses the exact spatial cancellation `differenceRhs_l2_bound` (`OrdinaryEulerL2Stability.lean:27-44`, needs `div = 0` and `pressureDifference ∈ gradientSpace`), and Mathlib's Gronwall `le_gronwallBound_of_liminf_deriv_right_le` (`:51`). Then `hinit` makes the bound `≤ 0`, and `smoothField_eq_of_toLp_eq` (`:15`) upgrades a.e. to pointwise via continuity. **Nothing assumes the fields agree.** | OK |
| 33 | `gradientNormPath` / `pointwise_gradient_le` | `Euler/OrdinaryEulerGradientControl.lean:20`, `:37` | `‖∇u(t,x)‖ ≤ gradientNormPath t` for all `x`; the path is a genuine `C(Icc 0 T, ℝ)`. | `‖finiteField (U.velocity t).derivative‖` where `finiteField` (`MeanSobolevBoundedField.lean:104`) is an honest `Space →ᵇ V` built from the `H³→C_b` Sobolev embedding of the `L²` jets, with `finiteField_apply : finiteField A x = A.field x` (`:108`). No junk fallback. | OK |
| 34 | `evolution_field_eq_of_local_evolution` | `Euler/ComparatorEvolutionIdentification.lean:52-129` | If `U : Evolution S` starts at the same datum as the Comparator solution and keeps compact vorticity, and the local upgrade holds, then `(U.velocity t).field = v·t` on ALL of `[0,S]`. | **Continuous induction, not an assumption.** Agreement set `s` (l.59) is closed (l.73, from `finiteField` continuity of `U` and joint smoothness of `v`); `0 ∈ s` from `h.initial_condition` (l.78-83); the right-extension step (l.84-123) restarts the *local* conversion at `a` (l.94), shrinks by `d = min δ (min (S−a) (b−a))`, and identifies `U.shiftTime a … d` with `W.restrictTime d` by (32) at l.114. Closed by Mathlib `IsClosed.Icc_subset_of_forall_exists_gt` (l.124-125) — I fetched the Mathlib source at rev 85e3a25e and the hypothesis shape `(hs)(ha)(hgt)` matches exactly. | OK |

Extra decls checked for the key questions (not in the required list):
`Euler/ComparatorIdentification.lean:17-34` (`maximalVelocity_eq_of_local_evolution`) and
`:38-44`; `Euler/Solution.lean:24-31` (`initialDatum_no_global_solution`).

## Kernel-risk assessment

**Verdict: no kernel-exploiting construct in this sub-chain.**

1. **The two load-bearing `rfl`s are cheap.**
   * `Euler/ComparatorLocalEvolution.lean:45` (and the identical `:71`): the term is
     `(smoothL2Field_of_curl_compact (v · t) _ _ _ _).field`. `smoothL2Field_of_curl_compact`
     is a *structure literal* (`Euler/DivCurlTensorRecovery.lean:82-85`, `field := u`) and
     `SmoothL2Field` has exactly one data field (`Euler/LpSmoothField.lean:31-34`; `smooth`
     and `integrable` are `Prop`s). So the kernel does beta + one projection-of-constructor
     iota step. It does **not** unfold `iteratedFDeriv_memLp_of_curl_compact`, does not touch
     `Nat.rec`/`Acc.rec`, and does not rely on structure eta (the literal is already in
     constructor form).
   * `Euler/ComparatorEvolutionIdentification.lean:121`
     (`(U.velocity ⟨a+d,hmem⟩).field x = (R.velocity ⟨d,…⟩).field x := rfl`, `R = U.shiftTime a _ d _ _`):
     unfolds the `Evolution.shiftTime` structure literal (`Euler/EvolutionTimeShift.lean:31`)
     and the `shiftTimeMap` `ContinuousMap` literal (`:15-18`) to `U.velocity ⟨a + d, _⟩`; the
     two `Subtype` witnesses differ only in their `Prop` components, so definitional **proof
     irrelevance** closes it. Same for the implicit conversion at l.123 through
     `initialInclusion` (`Euler/SmoothCoefficientTimeRestriction.lean:84-85`). Constant cost.
2. **`decide`**: exactly ONE occurrence in the 30+ files I read:
   `Euler/CompactSolenoidalDensity.lean:39`, `(by decide : (3 : ℕ) ≠ 0)`. Kernel cost is one
   `Nat.decEq`-style evaluation on the literal `3`. Not exploitable.
3. **Numeral arithmetic**: the only literals in this chain are small (`2, 3, 4, 13, 39, 3600`,
   e.g. `Euler/CompactVorticityTimeUpgrade.lean:114`, `Euler/OrdinaryEulerDifference.lean:134`),
   discharged by `norm_num`/`positivity`/`ring` over `ℝ`. No GMP-scale `Nat` computation.
4. **Well-founded recursion / `Acc.rec`**: none in any declaration I traced. Repo-wide grep over
   the 939-file import closure finds `termination_by` only in `Euler/EulerProof.lean`
   (l.3202, 3233, 3291, 3331, 3399, 4703) and `Euler/H6Pressure.lean` (l.28, 53, 93) — the
   packet-induction/pressure-construction side, which is *not* reached by any decl of this
   sub-chain (they are only in the import closure). Flagged for the worker who owns those files.
5. **`Nat.rec`**: one explicit use, `Euler/LpSmoothJetField.lean:14-24` (`jetFieldAux`), needed for
   a universe-polymorphic dependent motive. Its `rfl` lemmas (`:32`, `:39`) reduce one iota step at
   `0` / `n+1`. `jetLp` — the object actually used in this chain — is defined *directly*
   (`Euler/LpSmoothField.lean:46`), not via `jetField`, so `Nat.rec` is off the critical path.
6. **Zero occurrences** of `sorry`, `axiom`, `native_decide`, `unsafe`, `partial`, `macro`,
   `elab`, `syntax`, `set_option`, `implemented_by` in any file I read.
   `Euler/Solution.lean:73-75` even ends with `#print axioms` on the two headline theorems
   (I cannot execute it — see Residue).

## Answers to the five key questions

**Q1 — is `ComparatorLocalEvolution.lean:45`'s `rfl` cheap?** Yes. See Kernel-risk §1. It is a
projection of a structure literal; `smoothL2Field_of_curl_compact` builds nothing recursive
(`Euler/DivCurlTensorRecovery.lean:79-85`).

**Q2 — is `evolution_field_eq_of_local_evolution` a real uniqueness proof?** Yes, and it is
*two* real arguments stacked: (a) `Evolution.velocity_eq_of_initial`
(`Euler/OrdinaryEulerUniqueness.lean:24`) is a genuine `L²` energy + Gronwall uniqueness
(`Euler/OrdinaryGradientStability.lean:18/34/54`, `Euler/OrdinaryEulerL2Stability.lean:27/46`,
Mathlib `le_gronwallBound_of_liminf_deriv_right_le`), whose exact cancellation needs
divergence-freeness and the pressure difference being a gradient; (b) the globalization is
continuous induction on the closed agreement set
(`Euler/ComparatorEvolutionIdentification.lean:59-129`) via Mathlib's
`IsClosed.Icc_subset_of_forall_exists_gt`, verified against the rev-85e3a25e source. Nowhere is
agreement of the two fields assumed: the only inputs are equality at `t = 0`
(`hU`, l.55, used at l.78-83) and the local realization.

**Q3 — circularity?** No, on both counts I can check.
* The *local conversion* genuinely consumes the Euler equation: the time regularity that turns
  `recoveredVelocity` into an `Evolution` comes from
  `Euler/ProjectedEulerPairing.lean:95`, `(hderiv t₀ ht₀ x).unique (h.pointwise_euler x t₀ ht₀)`,
  i.e. `h.euler` (`Euler/SolutionDefinitions.lean:67`). A smooth divergence-free field that is
  *not* a solution could not produce it (it would fail the projected pairing derivative).
  The vorticity-support step likewise consumes the vorticity equation
  (`Euler/ScalarEulerVorticity.lean:47` via `Euler/ReversedVorticityTransport.lean:21`).
* The `Evolution` that is later contradicted is **not** built from the Comparator solution:
  at `Euler/ComparatorIdentification.lean:31` the first argument is `L.evolution S hS hSL`,
  the canonical maximal solution of the independently constructed `lifespan`
  (`Euler/Solution.lean:27-30`); the Comparator solution `h` only enters as the hypothesis being
  refuted. Identification is stated only on closed subintervals `S = L.intermediateHorizon t <
  L.duration` — the maximal-interval endpoint is correctly avoided.

**Q4 — are the `Prop`-valued conversion obligations discharged?** Yes, unconditionally:
* `CompactCurlLocalUpgrade` is proved at `Euler/ComparatorLocalEvolution.lean:91-97`
  (`theorem compactCurlLocalUpgrade : CompactCurlLocalUpgrade`), and consumed at
  `Euler/Solution.lean:30`.
* `HasLocalEvolutionAtCompactCurl v` is derived from it at
  `Euler/ComparatorEvolutionIdentification.lean:43-48`, used at `Euler/ComparatorIdentification.lean:44`.
* Neither survives as a hypothesis of the headline theorems `Euler.euler_breakdown_R3`
  (`Euler/Solution.lean:33`) or `Euler.exists_compact_smooth_euler_singularity` (`:43`).
* Still threaded as hypotheses (correctly, since they belong to other workers' files):
  `hcompact` at `Euler/ComparatorIdentification.lean:40`, discharged in `Euler/Solution.lean:30`
  by `canonical_vorticity_hasCompactSupport` — **not verified by me**.

**Q5 — dangerous tactics/constructs?** See Kernel-risk. One `decide` on `(3 : ℕ) ≠ 0`, one
off-path `Nat.rec`, no `Acc.rec`, no eta-`rfl` abuse, no metaprogramming, no `sorry`.

## Escalations (ranked)

1. **`canonical_vorticity_hasCompactSupport` (used `Euler/Solution.lean:30`, consumed as
   `hcompact` at `Euler/ComparatorIdentification.lean:40` → `Euler/ComparatorEvolutionIdentification.lean:56`).**
   Question for an expert: *does the canonical maximal solution really have compactly supported
   vorticity at **every** time of its lifespan, uniformly enough for `hcompact`, and is that
   proved rather than built into the packet construction's definition of "canonical"?*
   Settled by: reading `Euler/CanonicalVorticityConfinement.lean` statement+proof and checking
   the support claim is derived from transport, not asserted. This is the one hypothesis of the
   identification chain that my scope cannot close.
2. **`component_wordDerivative_memLp` / `component_wordDerivative_energy_uniform` (used
   `Euler/DivCurlTensorRecovery.lean:62`, `Euler/ComparatorUniformSpatialJets.lean:88`).**
   Question: *is the elliptic (Biot–Savart / Riesz-transform) recovery of all-order spatial `L²`
   derivatives from compact vorticity + finite energy quantitatively correct, in particular is the
   `n = 1` step really controlled without an `L^p`-endpoint failure?* Settled by: reading
   `Euler/CompactSpatialJets.lean` and the `MeanHarmonic` files' statements. If this were wrong,
   `recoveredVelocity` would not exist and the conversion collapses — but nothing here is vacuous.
3. **Endpoint (`t = 0`) derivative for the uniqueness energy identity**:
   `Euler/OrdinaryWordTime.lean:78-97` → `Euler/SmoothFieldSobolevTime.lean:86-93` →
   `EulerSeparatingTimeDerivative.hasDerivWithinAt`. Question: *is the interior-to-endpoint
   upgrade (interior `HasDerivAt` on `Ioo 0 T` + continuity of both paths on `Icc 0 T` ⟹
   `HasDerivWithinAt` at `0`) proved with a correct MVT argument for the vector-valued path, and
   is the "separating family" really injective on the relevant Sobolev space?* Settled by reading
   `EulerSeparatingTimeDerivative`. It matters because `velocity_eq_of_initial` integrates the
   energy inequality from `0`. (The statement is true mathematically; I only did not read the proof.)
4. **`Euler/SolutionDefinitions.lean:76-80` faithfulness (low risk, high impact).**
   Question: *is `EulerExistenceAndSmoothnessR3` exactly the Clay/formal-conjectures
   hypothesis, in particular is `integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2` (the `norm` function,
   `:79`) and the strict `<E` in `globally_bounded_energy` (`:80`) the reference's wording?*
   Settled by diffing against
   `google-deepmind/formal-conjectures@8323e87 FormalConjectures/Millenium/NavierStokes.lean`.
   A hypothesis record stronger than the reference would weaken the headline theorem. Nothing
   I read makes it vacuous: it is satisfied by `v ≡ 0`, `p ≡ 0`, `u₀ ≡ 0`, so it is inhabited.
5. **Off-path well-founded recursion** at `Euler/EulerProof.lean:3202,3233,3291,3331,3399,4703`
   and `Euler/H6Pressure.lean:28,53,93`. Question: *do these `termination_by` definitions ever get
   forced to reduce by a `rfl`/`decide`/`simp` in the packet-induction chain?* Not reachable from
   any declaration in my scope; belongs to the blowup-construction worker.

## Residue (not checked, and why)

* **No kernel confirmation.** No built Mathlib and no disk, so I could not run `lake build`,
  `#print axioms Euler.euler_breakdown_R3` (`Euler/Solution.lean:73`), or any `#reduce`/timing
  probe. Every "cheap `rfl`" claim above is a *definitional-unfolding analysis of the source*,
  not a measured elaboration. A single `lake build` would settle §1 of Kernel-risk empirically.
* **Elliptic recovery internals** (escalation 2): `Euler/CompactSpatialJets.lean`,
  `Euler/DivCurlRecovery.lean`, `Euler/TensorCoordinateEnergyBound.lean`,
  `Euler/LpFiniteTensorReconstruction.lean` — grep-located only.
* **Truncated-flow internals**: `Euler/TruncatedBackwardFlow.lean`, `Euler/LocalFlowTrap.lean`,
  `Euler/FiniteEnergyTruncation.lean`, `Euler/TruncationFamilySmooth.lean`. I verified that
  `locallyTrappedBackwardFlows` discharges every field of `BackwardVorticityFlows` by citing
  lemmas from those files, but I did not read those lemmas' proofs.
* **`flow_escape_measure_le`** (`Euler/NoIncomingVorticity.lean:101`) — the quantitative escape
  estimate. Statement shape is right (`energy·T²/(R−K₀)²`); proof unread.
* **The maximal-solution side**: `Euler/OrdinaryEulerMaximal.lean` (`FiniteLifespan`,
  `L.evolution`, `L.maximalVelocity_eq_evolution`, `L.evolution_initial`),
  `Euler/EulerFiniteLifespan.lean`, `Euler/CompactVorticityContradiction.lean`,
  `Euler/InitialDataBridge.lean`. Out of scope; the identification result is only as strong as
  `L.evolution_initial` and the blowup they encode.
* **`scalarPressure_spec`** (`Euler/OrdinaryEulerLimit.lean:117`) — used by
  `scalarEuler_iff_projected`; I read its call sites, not its proof.
