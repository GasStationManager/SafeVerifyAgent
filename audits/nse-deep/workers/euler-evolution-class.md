# Worker report: `euler-evolution-class`

**Question owned (raised as P2 by worker `euler-packet`):** is the `Evolution` class that the Euler
contradiction is run against STRONGER than the challenge's notion of an Euler solution — and if so, is
every extra field PROVED from the challenge data, or assumed?

**Answer up front.** `EulerOrdinarySobolev.Evolution` *is* strictly more bundled than the challenge's
classical class `EulerExistenceAndSmoothnessR3`. But the repo **does** contain the missing lemma that
`euler-packet` P2 said it could not find: `Euler.ComparatorBridge.compactCurlLocalUpgrade`
(`Euler/ComparatorLocalEvolution.lean:91`) constructs an `Evolution` **from** an arbitrary challenge
solution (plus compactly supported initial vorticity), and every extra field is *derived*, not assumed.
The bridge lemmas all point challenge-class ⇒ `Evolution`, i.e. the direction the refutation needs.
No step in the negative claim needs the converse. Two analytic sub-steps carry the whole load and are
audited by three sub-workers (their notes are cited below): the all-order L² jet recovery from a
*compact vorticity support* and the local propagation of that support.

**Verdict counts** over the 30 declarations I examined individually (table in §B, plus the 8 in the
positive-headline table): **30 OK, 0 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS**, with 3 delegated cores
(`l2_stability_gradientIntegral`, BKM, `FiniteLifespan`) left to their owning workers and 4
escalations, of which E1/E2/E4 are answered/downgraded by sub-audits and only E3 (H³ point evaluation)
plus E5 (= `euler-packet` P1) remain open. All three sub-workers independently report "nothing
smuggled".

## Scope

Files read for this question (declaration counts from the regenerated `CONE.csv`, which lists
152 non-instance decls + 5 anonymous instances in these 21 files):

| file | decls | how read |
|---|---|---|
| `Euler/Solution.lean` | 3 | line-by-line (all 76 lines) |
| `Euler/SolutionDefinitions.lean` | 11 | line-by-line (all 139 lines) |
| `Euler/OrdinaryEulerDifference.lean` | 19 | line-by-line (all 151 lines) |
| `Euler/ComparatorLocalEvolution.lean` | 5 | line-by-line (all 100 lines) |
| `Euler/ComparatorEvolutionIdentification.lean` | 4 | line-by-line (all 132 lines) |
| `Euler/ClassicalBridge.lean` | 4 | line-by-line (all 50 lines) |
| `Euler/ProjectedEulerPairing.lean` | 3 | line-by-line (all 161 lines) |
| `Euler/CompactProjectedEulerLaw.lean` | 3 | line-by-line (all 69 lines) |
| `Euler/CompactVorticityTimeUpgrade.lean` | 9 | line-by-line (all 201 lines) |
| `Euler/OrdinaryEulerSobolevClass.lean` | 6 | line-by-line (all 74 lines) |
| `Euler/OrdinaryEulerClassicalClass.lean` | 16 | :180-277 line-by-line; :1-179 skimmed |
| `Euler/OrdinaryStrongTime.lean` | 3 | line-by-line (:1-62) |
| `Euler/OrdinaryCauchyInterpolation.lean` | 8 | :17-58 line-by-line; rest skimmed |
| `Euler/OrdinaryHelmholtzField.lean` | 20 | :50-130 line-by-line; rest skimmed |
| `Euler/LpSmoothField.lean` | 15 | :30-70 line-by-line; rest skimmed (also sub-worker) |
| `Euler/ComparatorSobolevEvolution.lean` | 12 | line-by-line (all 162 lines) |
| `Euler/ComparatorMaximalSolution.lean` | 11 | line-by-line (all 114 lines) |
| `Euler/CompactVorticityContradiction.lean` | 1 | line-by-line (all 42 lines) |
| `Euler/ComparatorIdentification.lean` | 2 | line-by-line (all 47 lines) |
| `Euler/InitialDataBridge.lean` | 1 | line-by-line (all 33 lines) |
| `Euler/CompactCurlBounds.lean` | 1 | line-by-line (all 33 lines) |
| `Euler/OrdinaryEulerUniqueness.lean` | (4) | line-by-line (all 48 lines) |

Delegated (read-only sub-workers, own notes files):
`_sub-evoclass-jets.md` (LpSmoothField / DivCurlTensorRecovery / ComparatorUniformSpatialJets /
ClassicalBridge), `_sub-evoclass-timeupgrade.md` (CompactVorticityTimeUpgrade /
CompactProjectedEulerLaw / CompactSolenoidalDensity), `_sub-evoclass-support.md`
(ComparatorLocalCompactVorticity / ComparatorTruncationFamily / FiniteEnergyTruncation).

## A. The two classes, quoted, and the field-by-field correspondence

### The target class (what is refuted)

`Euler/OrdinaryEulerDifference.lean:21-32`, verbatim:

```lean
structure Evolution (T : ℝ) (hT : 0 ≤ T) where
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  pressureForce : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  pressure_continuous : ∀ n, Continuous (fun t => (pressureForce t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  gradient : ∀ t, (pressureForce t).toLp ∈ gradientSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r => (velocity (projIcc 0 T hT r)).field x)
      (-fderiv ℝ (velocity ⟨t,ht.1.le,ht.2.le⟩).field x
        ((velocity ⟨t,ht.1.le,ht.2.le⟩).field x)-
          (pressureForce ⟨t,ht.1.le,ht.2.le⟩).field x) t
```

with (`Euler/LpSmoothField.lean:31-34`)

```lean
structure SmoothL2Field (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  field : Space → V
  smooth : ContDiff ℝ ∞ field
  integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume
```

So `Evolution` demands, per time slice: smoothness, **every** iterated derivative in L², plus
**time-continuity of every L² jet**, plus a Hilbert-space solenoidal/gradient splitting, plus a
*pointwise* time law with the pressure force as a field (not a scalar pressure).

### The challenge classes (what a competitor must satisfy)

`Euler/SolutionDefinitions.lean:64-80` (byte-identical to `ComparatorChallenges/Euler.lean`; verified
by earlier workers):

```lean
structure EulerExistenceAndSmoothness (u₀ v p) : Prop where
  euler : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) = -gradient (p · t) x
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)

structure EulerExistenceAndSmoothnessR3 (u₀ v p) : Prop extends EulerExistenceAndSmoothness u₀ v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E
```

and the Sobolev-class variant used by the *positive* headline (`:94-120`):

```lean
structure SobolevSmoothOn (I : Set ℝ) (v : ℝ³ → ℝ → ℝ³) : Prop where
  spatial_smooth : ∀ t ∈ I, ContDiff ℝ ∞ (v · t)
  integrable : ∀ t ∈ I, MemLp (v · t) 2
  jets_integrable : ∀ m : ℕ, ∀ t ∈ I, MemLp (iteratedFDeriv ℝ m (v · t)) 2
  continuous : ContinuousOn (fun t => toL2 (v · t)) I
  jets_continuous : ∀ m : ℕ, ContinuousOn (fun t => toL2 (iteratedFDeriv ℝ m (v · t))) I

structure EulerSobolevExistenceAndSmoothnessR3On (I) (u₀ v p) : Prop where
  div_free : ∀ x, ∀ t ∈ I, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : SobolevSmoothOn I v
  pressure_differentiable : ∀ t ∈ interior I, Differentiable ℝ (p · t)
  euler : ∃ w : ℝ³ → ℝ → ℝ³, SobolevSmoothOn I w ∧
      (∀ t ∈ interior I, HasDerivAt (fun s => toL2 (v · s)) (toL2 (w · t)) t) ∧
      (∀ x, ∀ t ∈ interior I, w x t + fderiv ℝ (v · t) x (v x t) = -gradient (p · t) x)
```

### Correspondence table

| `Evolution` field | classical challenge `EulerExistenceAndSmoothnessR3` | Sobolev challenge `…R3On` | provenance in the repo |
|---|---|---|---|
| `velocity t : SmoothL2Field` → `.smooth` | `velocity_smooth` (joint `ContDiffOn ∞`) | `velocity_smooth.spatial_smooth` | `ClassicalBridge.lean:21` `velocity_contDiff` — restriction of the joint ContDiffOn. **Direct.** |
| `.integrable 0` (v ∈ L²) | `integrable : MemLp (‖v · t‖) 2` | `velocity_smooth.integrable` | `ClassicalBridge.lean:29` `velocity_memLp` via `memLp_norm_iff` + a.e.-strong-measurability from continuity. **Direct.** |
| `.integrable n`, **all n** (all jets in L²) | **NO COUNTERPART** | `jets_integrable` (direct) | classical case: `smoothL2Field_of_curl_compact` (`DivCurlTensorRecovery.lean:79`) — div-curl/elliptic recovery from `v(·,t)` smooth + L² + div-free + **compact curl support**; engine is Caccioppoli + Fatou with a field-independent constant (`DivCurlRecovery.lean:53-150`, `:174`, `:291`), reassembled by `MemLp.of_eval_piLp` (`DivCurlTensorRecovery.lean:66-85`). **Derived; corroborated by `_sub-evoclass-jets.md`.** |
| `velocity_continuous` (jetLp continuous in t, all orders) | **NO COUNTERPART** | `jets_continuous` (direct) | classical case: `jetLp_continuous_of_toLp_continuous` (`CompactVorticityTimeUpgrade.lean:83`) from strong L² continuity + uniform `tensorNorm` bounds, via the log-convexity interpolation `tensorNorm_interpolate_zero` (`OrdinaryCauchyInterpolation.lean:24`). Strong L² continuity itself is *proved* (Lipschitz from the weak ODE, `:174-178`). **Derived.** |
| `solenoidal` (Hilbert-space membership) | `div_free` (pointwise) | `div_free` | `comparator_velocity_mem_solenoidal` (`CompactVorticityTimeUpgrade.lean:46`) via `smooth_mem_solenoidal`. **Derived.** |
| `pressureForce` + `pressure_continuous` + `gradient` | challenge `p` only enters to *cancel*; the pressure force is **reconstructed** | ditto | `pressureField (A t) = P_sol(adv) - adv` (`OrdinaryHelmholtzField.lean:60`), `pressureField_mem_gradient` (:74), `pressureField_continuous` (:83). **Constructed, so nothing is demanded of the competitor's pressure beyond `pressure_smooth`.** |
| `time_law` (pointwise, two-sided, at interior times) | `euler` (one-sided `derivWithin` on `Ici 0`) | `euler` witness `w` (L²-valued derivative) | classical case: `pointwise_euler` (`ClassicalBridge.lean:33`) upgrades `derivWithin` to `HasDerivAt` at `t>0` by `derivWithin_of_mem_nhds (Ici_mem_nhds ht)`; the Evolution's `time_law` is then produced by `evolutionOfProjectedEquation` (`OrdinaryEulerSobolevClass.lean:24-35`) out of the L² derivative through `pointwise_derivative_of_l2` (`OrdinaryStrongTime.lean:48`, bounded H³ point evaluation). **Derived.** |

Net: exactly **two** kinds of extra content in `Evolution` relative to the classical challenge class —
(i) all-order L² spatial jets and (ii) their time-continuity — plus the packaging of the pressure as a
gradient field. All three are produced by lemmas, none is an added hypothesis on the competitor.

## B. The conversion chain, declaration by declaration

Entry point (`Euler/Solution.lean:24-31`): `initialDatum_no_global_solution` destructs the assumed
competitor `⟨v,p,h⟩` and feeds it to `finiteLifespan_contradiction_of_compact_vorticity`, with the
identification supplied by `maximalVelocity_eq_of_compactCurlLocalUpgrade … compactCurlLocalUpgrade`.

| decl | file:line | statement (my words) | mechanism | verdict |
|---|---|---|---|---|
| `Euler.initialDatum_no_global_solution` | `Solution.lean:24` | no `(v,p)` is a global challenge solution with their datum | assumes one, hands it to the contradiction lemma with four proved side facts | OK |
| `Euler.euler_breakdown_R3` | `Solution.lean:33` | ∃ datum with rapid decay and no global challenge solution | `⟨initialDatum.field, initialVelocityConditionDecay_of_compact …, initialDatum_no_global_solution⟩` | OK |
| `initialVelocityConditionDecay_of_compact` | `InitialDataBridge.lean:16` | compact + smooth + div-free ⇒ challenge decay condition | continuity of `(1+‖x‖)^K ‖D^m u₀‖` with compact support ⇒ global max; `le_div_iff₀`. Honest; no junk value | OK |
| `finiteLifespan_contradiction_of_compact_vorticity` | `CompactVorticityContradiction.lean:18` | a challenge solution that *matches* the maximal solution on the whole lifespan and has vorticity vanishing off a compact set is impossible | `h.vorticity_bounded_on_compact` gives `M` on `K`; off `K` the curl is 0; so `∫ vorticityNorm ≤ M·duration`, contradicting BKM unboundedness `L.vorticityIntegral_unbounded` | OK (BKM itself is worker `euler-spine-bkm`'s scope) |
| `EulerExistenceAndSmoothnessR3.vorticity_bounded_on_compact` | `CompactCurlBounds.lean:19` | curl of a challenge solution is bounded on compact `K × [0,T]` | `spatial_fderiv_bounded_on_compact` + `curlMatrixCLM` operator norm | OK |
| `maximalVelocity_eq_of_compactCurlLocalUpgrade` | `ComparatorIdentification.lean:38` | the maximal velocity equals the competitor on the whole lifespan | wraps `maximalVelocity_eq_of_local_evolution` with `hasLocalEvolutionAtCompactCurl_of_upgrade` | OK |
| `hasLocalEvolutionAtCompactCurl_of_upgrade` | `ComparatorEvolutionIdentification.lean:43` | a *time-shifted* competitor still satisfies the local upgrade | `h.shiftTime a ha` (`ComparatorTimeShift.lean:19`) — the challenge class is closed under forward time shift; **shift only, no strengthening** | OK |
| `evolution_field_eq_of_local_evolution` | `ComparatorEvolutionIdentification.lean:52` | an `Evolution` from the same datum agrees with the competitor on all of `[0,S]` | the agreement set is closed (both sides continuous in `t`), contains 0, and is right-extendable: at any agreement time, `hlocal` produces a *fresh* `Evolution` for the competitor and Euler uniqueness `Q.velocity_eq_of_initial R` (`OrdinaryEulerUniqueness.lean:24`) closes the gap; `Icc_subset_of_forall_exists_gt` finishes | OK — no numeric or recursor content, clean continuity/ connectedness argument |
| `Evolution.velocity_eq_of_initial` | `OrdinaryEulerUniqueness.lean:24` | equal initial L² data ⇒ equal `Evolution`s | H³ difference energy + `l2_stability_gradientIntegral` (worker `euler-spine-uniqueness` scope); `smoothField_eq_of_toLp_eq` upgrades a.e. equality to equality using continuity of both representatives — correct, not a junk-value trick | OK (delegated core) |
| `CompactCurlLocalUpgrade` (the Prop) | `ComparatorEvolutionIdentification.lean:37` | *statement* of "challenge solution + compact initial curl ⇒ short `Evolution` with the same field" | a `def … : Prop`; it is **discharged** at `ComparatorLocalEvolution.lean:91`, not left as a hypothesis of the headline | OK — **this is the lemma `euler-packet` P2 asked for** |
| `compactCurlLocalUpgrade` | `ComparatorLocalEvolution.lean:91` | proof of the above | `h.local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc` gives `δ>0` and a ball `B` containing the curl support on `[0,δ]`; then `exists_evolution_of_commonCompactCurl` | **OK, corroborated** by sub-worker `evoclass-support`: the truncation family is a *construction* from `h` (`ComparatorTruncationFamily.lean:69-103`), and the support propagation is the curl of `h.euler` + Grönwall + a real Picard flow, not an assumption |
| `exists_evolution_of_commonCompactCurl` | `ComparatorLocalEvolution.lean:64` | with the curl support inside one compact `K` on `[0,T]`, the competitor **is** an `Evolution` | `recoveredVelocity` (:31) makes the slices `SmoothL2Field`; `recoveredVelocity_jetLp_uniform` (:49) gives uniform per-order bounds; `isSmoothScalarEuler_of_weak_projectedEquation` upgrades weak data to the full class; `exists_evolution_iff_scalar` converts | OK modulo the two sub-audits — **this is the crux** |
| `recoveredVelocity` | `ComparatorLocalEvolution.lean:31` | the `SmoothL2Field` slices, *definitionally equal* to the competitor field (`recoveredVelocity_field` is `rfl`, :45) | `smoothL2Field_of_curl_compact` from `h.velocity_contDiff`, `h.velocity_memLp`, `h.div_free`, compact curl support | OK; note `rfl` means **no re-definition of the velocity** — the object refuted is literally the competitor's field |
| `isSmoothScalarEuler_of_weak_projectedEquation` | `CompactVorticityTimeUpgrade.lean:144` | solenoidal + uniform spatial bounds + a *dense* family of weak time-derivative identities ⇒ the full smooth scalar Euler class | `WeakHilbertODE.lipschitzOnWith_of_dense_weak_equation` gives strong L² Lipschitz continuity, then `jetLp_continuous_of_toLp_continuous` (interpolation) gives all-order jet continuity, then `hasDerivAt_of_dense_weak_equation` gives the strong L² time law | **OK, corroborated.** Sub-worker `evoclass-timeupgrade` re-read all 6 hypotheses and confirms each is discharged at `ComparatorLocalEvolution.lean:73-81` from `h` (with `hA` literally `rfl`), that density is used only as "dense pairings determine a vector" (`WeakHilbertODE.lean:27,40`), that `compactSolenoidalTests_dense` (`CompactSolenoidalDensity.lean:164`) is a genuine density proof (curl-curl + L² Liouville, `:21/:115`), and that no hypothesis already contains the conclusion |
| `comparator_projected_pairing_hasDerivAt` | `CompactProjectedEulerLaw.lean:55` | the weak projected identity on the dense compact solenoidal test family | reduces to `comparator_clamped_compact_pairing_hasDerivAt` | OK |
| `comparator_clamped_compact_pairing_hasDerivAt` | `ProjectedEulerPairing.lean:140` | tested identity survives replacing `v` by any pointwise-equal smooth L² representative and the clamped `projIcc` reparameterisation | `congr_of_eventuallyEq` on `Ioo`; a.e. rewriting through `toLp_ae` | OK |
| `velocity_solenoidal_test_pairing_hasDerivAt` | `ProjectedEulerPairing.lean:102` | `d/dt ∫⟨φ,v⟩ = -∫⟨φ,(v·∇)v⟩` for compact smooth **solenoidal** `φ` | pressure is killed by `compact_solenoidal_pressure_pairing_zero` (integration by parts, `div φ = 0`, compact support — **no pressure decay assumed**), integrability from compact support | OK — this is the honest use of the challenge equation |
| `velocity_test_pairing_hasDerivAt` | `ProjectedEulerPairing.lean:32` | differentiation under the compact spatial integral, pressure retained | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the bound from continuity on `Icc (t₀/2) (t₀+1) × tsupport φ`; the time derivative is identified with the Euler RHS by `HasDerivAt.unique` against `h.pointwise_euler` | OK |
| `EulerExistenceAndSmoothnessR3.pointwise_euler` | `ClassicalBridge.lean:33` | at `t>0` the one-sided `derivWithin` challenge equation is a genuine two-sided `HasDerivAt` | `derivWithin_of_mem_nhds (Ici_mem_nhds ht)`, differentiability from the joint `ContDiffOn` on a set that is a neighbourhood at `t>0` | OK — legitimate, and this is the *only* place the one-sidedness matters |
| `IsSmoothScalarEuler` / `scalarEuler_iff_projected` / `exists_evolution_iff_scalar` | `OrdinaryEulerClassicalClass.lean:194, 245, 271` | `∃ Evolution with velocity = A ↔ IsSmoothScalarEuler A ↔ IsSmoothProjectedEuler A` | both directions proved; the `←` direction builds the `Evolution` from the projected equation | OK — an **iff**, so the target class is *characterised*, not merely sufficient |
| `evolutionOfProjectedEquation` | `OrdinaryEulerSobolevClass.lean:24` | builds the 7 fields | `pressureForce := pressureField (A t)`; `time_law` from `pointwise_derivative_of_l2` + `Icc_mem_nhds` | OK |
| `pointwise_derivative_of_l2` | `OrdinaryStrongTime.lean:48` | an L² time derivative with continuous jets yields the *pointwise* time law | lifts to Sobolev order 3 (`sobolev_derivative_of_l2`) and applies the bounded point-evaluation functional `observation 3` | OK, but the H³→C⁰ evaluation machinery (`observation`, `ordinaryLift`, `AddCircle 1`) is not in my scope — see Residue |
| `tensorNorm_interpolate_zero` | `OrdinaryCauchyInterpolation.lean:24` | `‖D^q F‖_{L²} ≲ (‖F‖_{L²}·N)^{1/2}` when `H^{2q}` is bounded by `N` | log-convexity of `wordMaximum` (`EulerNonnegativeLogConvex.between`) — the standard interpolation inequality | OK (log-convexity lemma not re-derived: Residue) |
| `Evolution` (structure) | `OrdinaryEulerDifference.lean:21` | the target class | plain structure, no indices, no recursion | OK |
| `evolutionOfClassical` | `OrdinaryEulerDifference.lean:34` | an alternative constructor from a jointly classical solution | **`in_cone=False`** — dead code for both headlines; harmless, but note it is *not* the bridge actually used | OK (unused) |
| `Evolution.energyDerivative_bound` etc. | `OrdinaryEulerDifference.lean:132` | H³ difference-energy differential inequality | used by uniqueness; delegated to `euler-spine-uniqueness` | — |

### The positive headline (`exists_compact_smooth_euler_singularity`) needs the *other* direction

| decl | file:line | direction | verdict |
|---|---|---|---|
| `sobolevSmoothOn_of_path` | `ComparatorSobolevEvolution.lean:22` | `Evolution`-style jet data ⇒ challenge `SobolevSmoothOn` | OK |
| `toL2_field`, `toL2_jet` | `ComparatorSobolevEvolution.lean:15,18` | the challenge's total `toL2` **never hits its `else 0` junk branch** on these fields (`dite_eq_left A.memLp`) | OK — explicit junk-value check, and it is discharged, not dodged |
| `evolution_sobolevSolution` | `ComparatorSobolevEvolution.lean:109` | their `Evolution` ⇒ challenge Sobolev solution on `Icc 0 T` (all 5 fields, incl. the `w` witness = `U.derivative` and `pressure_differentiable` from `scalarPressure_spec`) | OK |
| `hasScalarEulerEvolution_of_sobolev` | `ComparatorSobolevEvolution.lean:79` | challenge Sobolev solution ⇒ their scalar Euler class | OK — nearly definitional, because `SobolevSmoothOn` already *is* "all jets in L², continuous in time" |
| `exists_sobolevSolution_iff` | `ComparatorSobolevEvolution.lean:151` | **iff** | OK |
| `maximal_sobolevSolution` | `ComparatorMaximalSolution.lean:82` | their maximal extension is a challenge Sobolev solution on `Ico 0 Tstar` | OK |
| `maximal_sobolev_existence_iff` | `ComparatorMaximalSolution.lean:107` | `(∃ v p, challenge-Sobolev on Icc 0 T) ↔ T < Tstar` | OK — uses both directions, both proved |
| `maximalDerivativeExtension` | `ComparatorMaximalSolution.lean:34` | `dite … else 0` extension outside `Ico 0 duration` | OK — the `else 0` branch is never used inside the interval (`maximalDerivativeExtension_eq`, :37); no vacuity gain because the challenge conditions are only imposed on `I` |

## C. Direction check (explicit)

For the **negative** claim the required implication is *challenge class ⇒ refuted class*. Every bridge
lemma above points that way:

* `ClassicalBridge.lean:21/29/33` : `EulerExistenceAndSmoothnessR3 → (spatial smoothness | L² | pointwise HasDerivAt)`.
* `ComparatorTimeShift.lean:19` `h.shiftTime` : challenge ⇒ challenge (shifted). No converse used.
* `ComparatorLocalEvolution.lean:64,91` : challenge (+ compact curl) ⇒ `Evolution`.
* `ComparatorEvolutionIdentification.lean:52` : `Evolution` + challenge ⇒ *equality of fields*; the
  `Evolution` side of that lemma is instantiated with **their own** constructed solution
  (`L.evolution`), never with a hypothetical competitor object, so nothing is assumed about the
  competitor beyond the challenge structure.
* `CompactVorticityContradiction.lean:18` consumes only `h` plus the equality and their own BKM bound.

The one place a converse is used is `exists_evolution_iff_scalar` / `exists_sobolevSolution_iff`, and
there it is an honest **iff** whose `Evolution ⇒ …` direction is used only for the *positive* claim
(their own solution belongs to the challenge Sobolev class) and for the `→` half of
`maximal_sobolev_existence_iff`. So: no step of the refutation needs "Evolution ⇒ challenge", and no
step of the positive claim needs an unproved "challenge ⇒ Evolution".

**Residual strength caveat, stated precisely.** The refutation is complete *for the challenge class as
written*, but the bridge is only invoked at times where the vorticity of *their* solution (hence, after
identification, of the competitor) is compactly supported. That is not a restriction on the competitor:
the compactness travels from their datum through the closed-set/right-extension argument. However the
whole refutation does rest on `EulerExistenceAndSmoothnessR3.integrable`/`globally_bounded_energy` and
on the **joint** `ContDiffOn ∞` in `velocity_smooth` (used for differentiation under the integral,
`ProjectedEulerPairing.lean:41-51`). A competitor that is smooth in space and merely `C¹` in time, or
that has infinite energy, is **not** covered — but that is the challenge's own definition, not a
narrowing introduced by this repo.

## D. Kernel-risk assessment for this scope

**(1) Recursive inductive types / recursors / `Acc.rec` / large elimination.** `Evolution`,
`SmoothL2Field`, `InitialVelocityCondition*`, `EulerExistenceAndSmoothness*`, `SobolevSmoothOn` are all
**non-recursive, non-indexed** structures (`Prop`-valued for the challenge classes, `Type`-valued for
`Evolution`/`SmoothL2Field`). Their projections and constructors are the only recursor uses, and those
are trivial `casesOn` reductions on a single-constructor structure — kernel cost is a projection, and
structure-eta makes them defeq-cheap. No `termination_by`, no `WellFounded.fix`, no `Acc.rec`, no
`deriving` in the 21 files (checked by grep for `rec`, `termination_by`, `decreasing_by`,
`WellFounded`, `Nat.rec`, `induction'`). The only inductive recursion in the scope is
`Finset.range`-style summation inside `tensorNorm` proofs, done by lemmas, not by kernel unfolding.
Verdict: **no kernel recursor risk in this slice.**

**(2) Nat/GMP numeral arithmetic.** The numerals appearing in my scope are tiny and symbolic:
`3600*h3ProductConstant` (`OrdinaryEulerDifference.lean:134`), `39 * smoothEmbeddingConstant * M^2`
and `13 * smoothEmbeddingConstant * M` (`CompactVorticityTimeUpgrade.lean:114,120`), `2*q` in the
interpolation, `wordEnergy 3`, `observation 3`, `sobolevPath … 3`, `Fin 3`. All the `by norm_num` goals
I read are of the form `0 ≤ 39`, `(0:ℝ) < 1`, `1 ≤ 2`, `13 ≥ 0` — one- or two-digit rationals. There is
**no `decide`, no `Nat.pow/gcd/mod` on large arguments, no numeral above 4 digits** in these files
(grep for `decide`, `native_decide`, `Nat.pow`, `^ [0-9][0-9]+`: zero hits). The kernel must recompute
`norm_num` certificates for those tiny goals only. Verdict: **negligible.**

**(3) Custom metaprogramming.** Machine grep over the 22 files for `macro`, `elab`, `syntax`,
`set_option`, `decide`, `native_decide`, `axiom`, `unsafe`, `partial`, `sorry`, `termination_by`,
`decreasing_by`, `WellFounded`, `.rec`, `deriving`: **zero hits for every one of them.** The only
`attribute` hit is `attribute [local instance] CompletePartialOrder.toSupSet` at
`Euler/Solution.lean:41`. There are 6 `local instance` lines in total:
`OrdinaryEulerDifference.lean:18,19` (`NormedAddCommGroup Space`, `NormedSpace ℝ Space` — re-derived by
`inferInstance`, so they cannot introduce a different structure), `Solution.lean:41`, and
`OrdinaryEulerClassicalClass.lean:19`, `OrdinaryStrongTime.lean:18`,
`OrdinaryCauchyInterpolation.lean:17` (all `Fact (0 < (1:ℝ))`). The single 5+-digit numeral in the whole
scope is a git commit hash inside a URL comment (`SolutionDefinitions.lean:26`). The `CompletePartialOrder.toSupSet` local instance is already `euler-packet`'s P1
escalation (it can change how the `⨆` in the *statement* at `Solution.lean:52` elaborates); I confirm it
is in force for `exists_compact_smooth_euler_singularity` only (line 41 precedes :43) and **not** for
`euler_breakdown_R3` (:33). The `Fact (0 < (1:ℝ))` instances are innocuous (they select the period-1
`AddCircle`). No `sorry`, no `axiom`, no `native_decide` anywhere in scope.

**One `decide` in the wider bridge (outside the 22 files, inside the used path).**
`Euler/CompactSolenoidalDensity.lean:39` has `by decide : (3 : ℕ) ≠ 0` as the hypothesis of
`tendsto_pow_atTop`. The kernel must evaluate `Nat.beq 3 0` / `Nat.decEq 3 0` — a one-step GMP-free
reduction on single-digit literals. Reported by sub-worker `evoclass-timeupgrade`; **negligible**, but it
is the only `decide` anywhere on this bridge.

**Does the kernel actually have to compute anything hard to accept these files?** No. Every proof in my
scope is a chain of `HasDerivAt`/`Continuous`/`MemLp` lemma applications plus `simp only`, `abel`,
`linarith`, `filter_upwards`. The heaviest kernel work is elaborated-term type-checking of long
`SmoothL2Field`/`Lp` instance chains, i.e. unification, not arithmetic or recursor reduction.

**Cone status (regenerated `CONE.csv`, mark-4 over-approximation).** 157 rows for my 21 files;
139 `in_cone=True`, 18 `in_cone=False`. Every declaration I put weight on is `in_cone=True`:
`compactCurlLocalUpgrade`, `exists_evolution_of_commonCompactCurl`,
`isSmoothScalarEuler_of_weak_projectedEquation`, `comparator_projected_pairing_hasDerivAt`,
`velocity_solenoidal_test_pairing_hasDerivAt`, `pointwise_euler`, `velocity_memLp`,
`evolution_field_eq_of_local_evolution`, `exists_evolution_iff_scalar`, `evolutionOfProjectedEquation`,
`pointwise_derivative_of_l2`, `tensorNorm_interpolate_zero`, `evolution_sobolevSolution`,
`exists_sobolevSolution_iff`, `maximal_sobolevSolution`, `maximal_sobolev_existence_iff`. The
`in_cone=False` rows are: `recoveredVelocity_field` (a `rfl` simp lemma — its *content* is used
definitionally, so this is a cone artefact, not dead code), `evolutionOfClassical`
(`OrdinaryEulerDifference.lean:34`, a genuinely unused alternative constructor),
`evolutionOfScalarEuler` + its 4 spec lemmas, `isSmoothScalarEuler_of_sobolev`,
`SobolevTower.isSmoothScalarEuler`, `l2_timeDerivative_of_sobolev`, `scalarEulerForce_continuous`
(`OrdinaryEulerClassicalClass.lean:31-229` — an alternative route to the same class, superseded by the
projected route), `Evolution.sobolevTimeDerivative`/`sobolevSolutionClass`
(`OrdinaryEulerSobolevClass.lean:53,63`), and the 5 anonymous local instances. **None of the
`in_cone=False` declarations is load-bearing**, which is consistent with the cone being an
over-approximation.

## Escalations (ranked)

**E1 — `euler-packet` P2 is ANSWERED: the class is stronger, but every extra field is proved.**
`Euler/ComparatorEvolutionIdentification.lean:37` + `Euler/ComparatorLocalEvolution.lean:91`.
The lemma P2 said it could not find exists and is discharged; the headline should **not** be re-read as
"no `Evolution`-class solution". Sub-worker `evoclass-jets` re-derived the load-bearing spatial step:
`smoothL2Field_of_curl_compact` (`DivCurlTensorRecovery.lean:79`) is built from a scalar-word L² recovery
(`DivCurlRecovery.lean:317`, an induction that re-proves `MemLp` *and* compact support of `Δ(D^w h)` at
each step) reassembled into full tensors by finite coordinate reassembly
(`DivCurlTensorRecovery.lean:66-85`, `MemLp.of_eval_piLp` + injective `tensorCoordinates`), with the
estimate engine a genuine Caccioppoli + Fatou argument (`DivCurlRecovery.lean:53-150`) whose constant
`C = M² + 1` is **field-independent** (`:174`), which is what makes the uniform-in-`t` bootstrap (`:291`)
honest. So: `v` smooth + `v ∈ L²` + `div v = 0` + compact curl support ⇒ all-order L² jets, uniformly in
`t`, with no extra decay assumed and without needing `v` itself compactly supported.
*Remaining expert question (now the only one on this bridge):* the whole spatial recovery is conditional
on `hsupport` (a **common** compact curl support on `[0,δ]`), which is exactly what E2 covers; both
sub-audits are source-level only. *What would settle both:* one `lake build` of
`Euler/ComparatorLocalEvolution.lean`.

**E2 — DOWNGRADED to a build-only question.** The local compact-vorticity propagation
(`Euler/ComparatorLocalCompactVorticity.lean:159`, consumed at `ComparatorLocalEvolution.lean:94`) was
re-read by sub-worker `evoclass-support` and is **clean**: (i) the `FiniteEnergyTruncationFamily`
argument is a *total construction* from `h` alone (`ComparatorTruncationFamily.lean:69-103`, all four
Prop fields closed from `velocity_smooth`, `div_free`, `integrable`, `globally_bounded_energy.choose`),
so it is not a hypothesis; (ii) the transport is the **curl of the challenge equation itself**
(`ComparatorLocalCompactVorticity.lean:121-138` → `ReversedVorticityTransport.lean:21` →
`ScalarEulerVorticity.lean:30/47/83`, i.e. `pointwise_euler` + `div_free`) plus Grönwall, with a genuine
Picard flow of a *bounded, Lipschitz truncation* (`TruncatedBackwardFlow.lean:39` →
`SmoothBanachFlow.lean:40` → `BoundedLipschitzFlow.lean:21-63`), a first-exit MVT
(`LocalFlowTrap.lean:38`) and a finite-action escape bound (`FlowEscapeBound.lean:171`); (iii) the only
non-`h` hypothesis is `hc`, compact support of the curl of **their own** datum.
The sub-worker's one caveat — "the final contradiction must survive arbitrarily small `T`" — **is
satisfied, and I checked it directly**: the caller never needs a uniform `δ`. In
`evolution_field_eq_of_local_evolution` the right-extension step takes
`d := min δ (min (S - a) (b - a))` (`ComparatorEvolutionIdentification.lean:95`) and only has to produce
*one* point of `s ∩ Ioc a b` (`:84`, `:116`); the interval is then closed by
`IsClosed.Icc_subset_of_forall_exists_gt` (`:124-125`). So any positive `δ`, however small and however
it depends on `a`, suffices. *Residual question for an expert (build-only):* does
`TruncationFamilySmooth.lean:78` really get boundary smoothness from `ContDiffOn.comp` with the `t²`
reparameterisation, as claimed, without a Whitney-extension step? *What would settle it:* elaborate that
file against Mathlib.

**E3 — the H³ point-evaluation route to the pointwise `time_law`.**
`Euler/OrdinaryStrongTime.lean:48-60` uses `observation 3 (le_refl 3) (x, (0 : AddCircle 1))` and
`ordinaryLift`. *Question:* is `observation` a *bounded* linear functional on the order-3 Sobolev
realization for the ℝ³ (not periodic) problem, and does `observation_apply` really evaluate the smooth
representative at `x` (not at a lifted/periodised point)? *What would settle it:* read
`Euler/SobolevPointEvaluation.lean` / `MeanOrdinaryLift` and check the embedding constant statement.
If this failed, `time_law` would be about the wrong function, and the whole `Evolution` construction
would be vacuous-in-x.

**E4 — RESOLVED, no escalation.** The interpolation used for jet time-continuity
(`Euler/OrdinaryCauchyInterpolation.lean:24`) rests on `wordMaximum_logconvex`
(`Euler/OrdinaryWordInterpolation.lean:31`), and that lemma is *proved*: for one directional derivative
`B` and axis `v`, `field_directional_inner` gives `‖∂_v B‖² = -⟪B, ∂_v∂_v B⟫` (integration by parts on
L²), then Cauchy–Schwarz gives `(sup_{n+1})² ≤ sup_n · sup_{n+2}`. Chained by
`EulerNonnegativeLogConvex.between`. This is the genuine inequality, not an assumption
(independently confirmed by sub-worker `evoclass-timeupgrade`).

**E5 — (confirming `euler-packet` P1, not re-opening it)** `Euler/Solution.lean:41`'s
`attribute [local instance] CompletePartialOrder.toSupSet` is the only metaprogramming-ish construct in
this slice and it is in force exactly for the statement containing `⨆` (`:52`). Same question and same
settlement as P1.

## Residue (not checked, and why)

* `smoothL2Field_of_curl_compact`, `component_word_energy_uniform_of_commonCompactCurl`,
  `local_compact_vorticity_of_truncationFamily`, `finiteEnergyTruncationFamily`,
  `compactSolenoidalTests_dense`, `WeakHilbertODE.*` — delegated to three sub-workers, all three of
  which report **clean** (`_sub-evoclass-jets.md`, `_sub-evoclass-timeupgrade.md`,
  `_sub-evoclass-support.md`). My own reading of the *statements* found no assumed field; the estimates
  themselves I did not re-derive, and neither sub-worker could build.
* `TruncationFamilySmooth.lean:78` — boundary smoothness through a `t²` reparameterisation
  (`ContDiffOn.comp`), flagged by `evoclass-support` as source-plausible but build-unverified.
* `l2_stability_gradientIntegral` (H³ difference-energy uniqueness) — worker `euler-spine-uniqueness`.
* `FiniteLifespan` (`OrdinaryEulerLifespan.lean:29`), `vorticityIntegral_unbounded`
  (`OrdinaryEulerBKM.lean:20`), `hasScalarEulerEvolution_iff`, `canonical_vorticity_*` — workers
  `euler-spine`, `euler-spine-bkm`, `euler-packet`.
* The Sobolev-realization machinery (`ordinarySobolev`, `observation`, `ordinaryLift`, `wordMaximum`,
  `tensorNorm`) — only its *interfaces* were read (E3, E4).
* No build: there is no Mathlib on this box, so every claim here is source-level. In particular I could
  **not** confirm that `recoveredVelocity_field` is `rfl` by elaboration; I only read that the author
  wrote `:= rfl` and that the definition makes it plausible (the `field` of
  `smoothL2Field_of_curl_compact` must be its first argument).
* `#print axioms` output (`Solution.lean:73,75`) is unverifiable without a build.
