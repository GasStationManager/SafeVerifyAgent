# Route walk 2: analytic core of the smooth branch (depth 5 and below)

Artifact `/home/user/differential-geometry` @ `7a48598d`, read-only, nothing compiled,
nothing committed. Continues `ROUTE-WALK.md` §6 (priorities 1–5). Auditor model family:
Claude (one family; see PLAYBOOK §4.16).

Path abbreviations: `RF/` = `DifferentialGeometry/Geometry/Flow/RicciFlow/`,
`S/` = `RF/Surgery/`, `X/` = `RF/Extinction/`, `T/` = `DifferentialGeometry/Topology/`.
Every `file:line` cited was read with `sed -n` in this pass unless it is marked
"(located, not read)", which means it was found with grep and its body was not opened.

**What did not run.** No compile, no `#print axioms`, no independent checker, no
trace. The README's claim that the headline's axioms are only `propext`, `Classical.choice`
and `Quot.sound` is taken as given here, as it was in the first walk.

**A structural point that changes what this pass can find (read this first).**
`poincare_conjecture` takes no Prop hypotheses (ROUTE-WALK §2, depth 0). Lean does not let a
closed theorem use a hypothesis that nothing supplies. So on the headline route a named
predicate that is never discharged cannot exist: it would have to show up in the
headline's type, or as `sorryAx` or an axiom in `#print axioms`. The convention "a missing
result is named, not `sorry`-ed" makes an undischarged predicate a hidden `sorry`
**only for theorems that still carry the predicate as a hypothesis**, which means
off-route theorems and intermediate lemmas that someone reuses. On the route, the risk
that is left is *vacuous or weak discharge*: a predicate that is proved only because a
definition it quantifies over is too weak or has no inhabitants. So this pass looked for
places where a hard theorem is proved more easily than the mathematics allows, which is
the sign of a weak definition, and did not look for places where one is missing. It found
none in the parts it read (§3). The claim "the route has no undischarged predicate"
therefore depends on the axiom check, not on this reading. That check is a README claim
until it is run (PLAYBOOK §1.3).

---

## 1. The argument, reconstructed

### 1.1 One surgery (Perelman II §4; Morgan–Tian ch. 13–14)

**Input.** A retained-core history H with canonical cutoff records, identified with
(P₀, g₀) at time 0. An incoming Ricci-flow slab G on the last stage that ends at a
*singular endpoint*, meaning |Rm| is unbounded as t → s
(`S/Topology/EventData.lean:246`, `SingularEndpoint`). It holds canonical, strongly canonical,
derivative, gradient and noncollapsing bounds before s.

**Steps.**
1. *Limit metric.* On the region Ω where curvature stays bounded, the metric converges to
   a limit metric `L` (`IncomingSlab.nonempty_terminalLimitMetric`,
   `S/Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:110`; body at
   `S/Topology/TerminalMetricExistence.lean:84`, located, not read).
2. *Horns and fine necks.* A terminal core presentation cuts Ω into cores plus horns.
   Deep in every ε-horn, each point of curvature ≥ K·max(Λ/r_core², q_can, 1) is the
   centre of a normalized εc-neck (`FineCutNeckSupplyStrong`, discharged by
   `fineCutNeckSupplyStrong_holds`, `S/Contract/FineCutNeckSupplyStrongLeaf.lean:18`,
   through a contradiction sequence of deep-horn blow-ups).
3. *Choice of cut scale.* The cut scale is Q = max(Λq·max(q₀,1), Q_lower,
   2Λ_max/coreFloor², (δ²·coreFloor)⁻²) + 1. The nominal radius is h = Q^{-1/2}, and
   h < δ²·ρ holds (`S/Contract/PoincareHornCutoffRecordOfFineCutNecks.lean:400–425`;
   `S/Contract/HornFineCutoffRecord.lean:51`, the conclusion
   `Real.sqrt Q⁻¹ < δ²·neckRadius`). This is Perelman's h ≤ δ²ρ.
4. *Cut and cap.* In each horn the proof picks a neck at scale Q (first hit), cuts along
   its middle 2-sphere, glues the standard-cap insertion metric onto the retained side,
   and discards every core component that meets no protected point
   (`HornFineCutoffRecord.lean:170–406`, via
   `exists_uniform_metricCutCapEvent_volume_debit_with_recenter_data`,
   `S/Topology/FiniteMetricEventDebit.lean:231`). The output metric is
   `finiteFullPreparedMetric`: the old metric on the retained core, and the rescaled
   `CanonicalStaticInsertionWitness` metric on each cap, recentred at precision c·δ with
   c ≥ 4.
5. *Records.* The event comes with a `GeometricCutoffRecord`
   (`S/Topology/GeometricCutoff.lean:208`). Its fields include `nominal_small` (`:212`),
   `backward` (the neck exists backward in time, i.e. a *strong* neck, `:226`),
   `curvature_preserving` (`:265`) and `scalar_preserving` (`:269`).
6. *Standard discards.* Every discarded component is `isPoincareStandard`
   (`GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_spatiallyCanonical`,
   `S/Topology/DiscardedSpatialClassification.lean:311`). There are two cases. (a) The
   component carries a cut boundary sphere: a capped neck/cap region covered by canonical
   neighbourhoods (`:233`, private, not read). (b) The component is a whole component on
   which scalar curvature exceeds the protected threshold everywhere, so canonical
   neighbourhoods cover it and it is a spherical space form or S²×S¹, or a connected sum
   of those (`isPoincareStandard_discardedComponent_of_cutIndices_eq_empty`, not read).
   This is Perelman II §4–5 / Morgan–Tian's classification of ε-canonically covered
   components.
7. *Volume debit.* vol(output) + (#necks)·Q^{-3/2} ≤ vol_L(K) for a compact K ⊂ Ω
   (`FiniteMetricEventDebit.lean:48`, proof `:120–230`). K is the retained core together
   with the discarded negative half-neck bands. The per-neck inequality
   (`S/StandardCap/FiniteVolumeDebit.lean:75`) is vol(out) + Σ(2π/δ)·R(x₀)^{-3/2} ≤
   vol(core ∪ bands) + Σ vol(caps). With δ below `margin` = π/(8·vol(standard cap)+1)
   (`FiniteMetricEventDebit.lean:149–152`), each cap's volume is absorbed, leaving at
   least Q^{-3/2} per neck. This is Perelman's "each surgery removes volume ≳ h³".
8. *Cap curvature.* R ≥ Q/4 on the cap region (`HornFineCutoffRecord.lean:292–295`).

**Where δ smallness enters.** The route theorem
(`UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:63–70`) takes
δb = min(δold, δmax, δh, δA, (2c)⁻¹):
- δold, the backward (strong) neck selection
  (`exists_uniform_selected_neck_retained_append_backward`,
  `S/Contract/PreparedHistoryCutoff.lean:156`, private, located, not read).
- δmax, noncollapsing through surgery, i.e. the initial-regular-block thresholds δ₁, δ₂
  (§1.4).
- δh, strong necks.
- δA = 1, pinching (vacuous here, see below).
- (2c)⁻¹, the recentering budget.

Separately, the record's own δ is `min δ₀ η` (`HornFineCutoffRecord.lean:180`). There δ₀
is the minimum over the insertion thresholds (`StaticThresholds.lean:68`: δp for pinching
and positive scalar curvature, δw for model-window closeness, δc for cap derivative
bounds, δt for the collapse tip), the volume margin, δV, and δcap/c. The pinching part is
δp = min(τ, 1/2·10⁻⁸) (`S/StandardCap/NormalizedInsertionPinching.lean:134`).

**Does pinching survive surgery, and why (closes ROUTE-WALK E3).** Yes, and the argument
is Hamilton's and Perelman's. The time-t Hamilton–Ivey region with parameter a₀+t
propagates along each slab by the maximum principle
(`S/Topology/HamiltonIveyPinching.lean:187`, `:242`). It passes to the terminal limit
metric because the region is closed (`:280`). It crosses the surgery through the record
fields `curvature_preserving`/`scalar_preserving` (`:340`, `:381–411`, `:521`). Those fields
are *produced* in `finiteFullPreparedMetric_hamiltonIvey`
(`S/StandardCap/FullMetricCurvature.lean:151`), which splits on the point:
- on the retained core the output metric is locally isometric to the old one, so the
  curvature is unchanged;
- on a cap the witness property `StaticInsertionAdditionalProperties.hamiltonIvey`
  (`S/StandardCap/StaticPinchingInsertion.lean:31`, field at `:49–55`) applies. It is
  proved in `exists_normalizedDatum_insertedMetric_pinching`
  (`NormalizedInsertionPinching.lean:111`) by two cases. Deep in the cap, sectional
  curvature is positive, so ν ≥ 0, which needs δ ≤ τ. In the conformal bending collar,
  R and 2ν both *increase* by the gain −f''/2 ≥ 0
  (`exists_insertedMetric_outer_curvature_gain`,
  `S/StandardCap/InsertionOuterCurvature.lean:157`). This needs the neck metric to be
  1e-8-close to the cylinder in C², which holds for δ ≤ 1/2·10⁻⁸. The HI region is
  upward-closed for R ≥ 0 (`mem_fixedHamiltonIveyRegion_of_le`).

`pinchingThroughSurgery` returns δmax = ρmax = εcap = 1 (`S/Topology/PinchingThroughSurgery.lean:12–22`)
because the class hypothesis already carries records, and a record cannot be built
without small δ. The chain from the record constructor down to the insertion threshold
was traced link by link:
`HornFineCutoffRecord.lean:171,180` → `FiniteMetricEventDebit.lean:231,152` →
`S/Topology/FiniteMetricEventVolume.lean:17,96–104` →
`S/StandardCap/PreparedCollarCorrespondence.lean:45` →
`S/StandardCap/RecenteredStaticPreparation.lean:14–47` (c·δ ≤ δi) →
`StaticPinchingInsertion.lean:63` → `StaticThresholds.lean:26,68` →
`NormalizedInsertionPinching.lean:111,134`.

The Lean statement is *stronger* than the standard one: pinching is preserved for every
parameter a > 0, not only for the current-time pinching function. That is valid, because
the gain argument does not depend on a.

### 1.2 Finitely many surgeries, then extinction (Perelman III; Morgan–Tian ch. 18)

`RetainedCoreHistory.exists_poincare_controlled_extinction_of_history_volume_debit`
(`S/Topology/FiniteHorizonExtinction.lean:68`) works as follows.

- *Scalar floor.* The initial R_min ≥ −3/(2c) (`InitialScalarBarrier`,
  `X/Families/InitialScalarBarrier.lean:18`, and c from
  `exists_initialScalarBarrier_of_compact`, `S/Topology/ExtinctionExistenceReduction.lean:18`)
  propagates to R ≥ −3/(2(t+c)) on every slab of every history in S
  (`FiniteHorizonExtinction.lean:106–131`). Across surgery it uses the records'
  `scalar_preserving`, and along the flow the ODE barrier.
- *Finitely many surgeries.* `exists_closedSlab_extension_to_horizon_of_volume_debit`
  (`S/Topology/FiniteHorizonContinuation.lean:49`) bounds the number of events by
  #components(M₀) + 2·e^{CB}·Vol₀/v (`S/Topology/HistoryEventVolumeBound.lean:27`). The
  bound combines three facts: volume grows at most like e^{Ct} under R ≥ −C; each neck
  costs v; and each event has at least one cut or one discarded component
  (`one_le_card_cut_add_card_discarded`), while components out + discarded ≤ components in
  + cuts (`S/Topology/HistoryComponentCount.lean:53–86`). The history with the most events
  in S either reaches B, or its last stage flows smoothly to B, or hits a singular time and
  can be extended by one more surgery, which contradicts maximality. The dichotomy
  "smooth to B, or singular endpoint" is `exists_closedSlab_or_singular_incomingSlab_from_time`
  (`S/Topology/MaximalSlab.lean:97`). It comes from maximal short-time existence plus
  `rmUnbounded_of_maximal` (Hamilton: a maximal solution has unbounded curvature; not
  located). v is fixed before H is chosen, which is what makes the bound uniform.
- *Extinction by width.* The width quantity is
  `canonicalWidth g o = classWidth g (positiveFreeContractibleClass o)`
  (`X/Width/CanonicalClass.lean:19`). That is the infimum over regular S²-families of
  contractible loops in the free homotopy class fixed by the orientation (the positive
  generator of π₂(ΛM) ≅ π₃(M) ≅ ℤ for simply connected M) of the maximum over the family
  of the least filling-disk area. `leastArea` is the infimum of competitor disk areas
  (`X/Width/LeastArea.lean:59`), `familyMaximum` is a supremum over S²
  (`X/Width/ClassWidth.lean:32`, attainment used via `familyMaximum_attained`), and
  `classWidth` is an infimum (`:102`). This is Perelman III's width, not the sweepout
  width of Colding–Minicozzi.
- *Monotonicity is PROVED, not assumed.* On each slab, the upper right Dini derivative of
  W satisfies D⁺W ≤ −2π − ½R_min·W (`history_incoming_component_dini`,
  `X/Families/ActualWidth.lean:428`, from `incoming_component_smooth_width` `:269`,
  `incoming_component_integrated_width` `:141`, and `rfs_integrated_class_width`
  `X/Families/ClassWidth.lean:142`). Those rest on `classWidth_le_affine_familyMaximum_add`
  (`:57–110`), which uses curve-shortening deformation of the family with a λ-ramp
  (`rfs_family_deformation`, `X/Families/Deformation.lean:978`). Each loop either becomes
  shorter than ℓ, and then bounds a disk of area ≤ Kℓ² by
  `rfs_essential_short_family`, or its least area obeys the integrated comparison. The
  per-curve slope bound is `projected_leastArea_slope_le_of_angle_le`
  (`X/Families/RampAreaEvolution.lean:23`), which gives −2π − ½R_min·A plus an angle
  error η²/√(1−η²)·(...). That is Perelman III §§1–3 (Gauss–Bonnet on the minimal disk,
  with the ramp to keep curves embedded). The `*_of_frontier` forms
  (`Deformation.lean:901`, `:933`) receive real proofs inside `rfs_uniform_ramp_alternative`
  (`:933–975`).
- *Across a surgery* W does not jump up (`historyWidth_event_jump`,
  `X/Width/SurgeryWidthEvolution.lean:726`, via `rfs_actual_width_jump` `:312`). The
  proof uses a degree-one collapse map from the parent component at time s to the child's
  output metric that is ℓ(s)-Lipschitz with ℓ(s) → 1 (`GeometricCutoffRecord.rfs_child_comparison`,
  `S/Topology/ChildComparison.lean:41`). Width is monotone under L-Lipschitz degree-one
  maps with factor L² (`rfs_canonical_width_lipschitz`, `CanonicalClass.lean:85`).
- *Threshold.* With R_min ≥ −3/(2(t+c)) we get D⁺W ≤ −2π + 3W/(4(t+c))
  (`X/Families/ObservedWidthDini.lean:146,158,361`). Integrating gives
  W(t)(t+c)^{-3/4} ≤ W₀c^{-3/4} − 8π((t+c)^{1/4} − c^{1/4}), so
  `extinctionThreshold c A = (c^{1/4} + A/(8πc^{3/4}))⁴ − c`
  (`X/Families/ScalarThreshold.lean:11`; the equivalence is `extinctionThreshold_lt_iff`,
  `:53`). The threshold is computed from the initial scalar barrier c and the initial
  canonical width W₀ = `canonicalWidth g P.orientation`. The horizon is
  B = max 1 (threshold + 1) (ROUTE-WALK, SingularEventExtinction). Past the threshold, a
  surviving terminal component would have negative width along its ancestor chain, which
  is impossible, so the final stage is empty (`isExtinctAtHorizon_of_historyWidth`,
  `X/Families/ExtinctionTimeBound.lean:38`).

### 1.3 Simple connectivity through surgery (closes ROUTE-WALK E2)

This is **proved, not assumed.** `rfs_simply_connected_history`
(`S/Topology/Ancestry.lean:17`) inducts over events. Each child component is simply
connected when its parent is (`SmoothCutCapTransition.child_simplyConnected`,
`S/Topology/ChildSimplyConnected.lean:35`), in two steps.

1. *The child core is simply connected.* Removing the open middle bands of the tubes from
   a simply connected component leaves components that are each simply connected
   (`componentwiseSimplyConnected_of_isOpen_removedBand`,
   `S/Topology/TubePuncturedCore.lean:293`). This reduces to
   `TwoSidedCollar.simplyConnectedSpace_connectedComponentIn_compl_iUnion`
   (`T/VanKampen/TwoSidedCollarSimplyConnected.lean:229`): induction over finitely many
   disjoint two-sided S²-collars, where each side of a two-sided collar in a simply
   connected space is simply connected (van Kampen, `:43`, `:78`, `:113`).
   `ChildCoreSimplyConnected.lean:310–345` transports this to the child core.
2. *The child is simply connected.* The child is covered by a core neighbourhood and the
   cap interiors. The pieces and their pairwise intersections are simply connected, and
   the caps are pairwise disjoint (star-cover van Kampen, `ChildSimplyConnected.lean:17–33`).

Stage 0 comes from the initial identification
(`X/Width/SurgeryWidthEvolution.lean:831`, a homeomorphism transport). Every later stage
component is simply connected (`S/Topology/StageComponentSimplyConnected.lean:24`).
Simple connectivity is used only in the `round` case of
`exists_ball_volume_of_spatialCanonicalWitness_of_simplyConnected`
(`RF/Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessBallVolume.lean:533–557`).
It excludes nearly round S³/Γ with large |Γ|, which have small volume at curvature
scale. The neck, cap and positive-curvature cases do not use it.

### 1.4 Noncollapsing through surgery (Perelman II §5; Morgan–Tian ch. 16–17)

The pieces are assembled in `noncollapsingThroughSurgery_of_reducedVolume_of_smallScale`
(`S/Topology/NoncollapsingThroughSurgeryLeaves.lean:242`):
- *Scales r ∈ [r₀, ε].* Take a reduced-volume lower bound c at the initial time. By
  monotonicity it holds at σr. The local upper bound gives
  Ṽ(σr) ≤ C₀·vol(B_r)/(σr)³ + c/2. Together, vol(B_r) ≥ (c/2C₀)(σr)³.
- *Scales r < r₀.* `SmallScaleNoncollapsingThroughSurgery` gives Bishop–Gromov from the
  scale r₀ where curvature is moderate, and canonical-neighbourhood witnesses where it is
  high. This is E2's piece, and it needs simple connectivity.

The reduced volume is *defined* (`NoncollapsingThroughSurgeryLeaves.lean:47–58`) as
limsup_B ∫ over `regularMinimizerEndpoints`, which are endpoints of minimizers of a
regularized L-cost that cross each surgery only through the regular region
(`RegularCrossing`, `:22–38`). Monotonicity holds for every history with no
hypotheses (`historyReducedVolumeMonotone_holds`,
`S/Topology/HistoryReducedVolumeMonotone.lean:189`), because the domain is restricted to
such minimizers. Perelman and Morgan–Tian restrict to the same set. The hard content is
the lower bound (`historyReducedVolumeInitialLowerBound_holds`,
`S/Topology/InitialRegularBlock.lean:510`, via `exists_uniform_initial_regular_block` `:197`).
It produces an open U in the initial layer with volume ≥ κ₀t^{3/2}, every point of which
is reached by a minimizer that crosses surgeries regularly, at cost ≤ C√t. Its two
unread inputs are Perelman's key lemmas:
`exists_uniform_initial_spatial_regularizedCost_minimum_lt_three_mul` (min ℓ < 3 through
surgery; `S/Topology/InitialSpatialMinimum.lean:59`, located, not read) and
`exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_recenter_budget`
(minimizers with bounded cost avoid surgery caps, i.e. barely-avoiding surgery;
`S/Topology/CapWindowActionRegularCrossingRecenter.lean:439`, located, not read). δ₁ and
δ₂ from these are where δ smallness enters noncollapsing.

---

## 2. Per-theorem records

Format: location — statement — literature — calls — named hypotheses and where they are
discharged — not read as argument / discrepancy.

### Priority 1: the surgery step

**`exists_horn_cutoff_record_of_fineCutNecks_of_le`** (private) — `S/Contract/UniformDebitSurgeryStepOfFactory.lean:39` (read `:39–278`)
- Statement: this is the uniform one-step surgery factory. Given η, it returns fixed cap
  scaffold data and tolerances. Then, for all horizon constants, it returns δ < 1 with
  δ ≤ η_record, a cut accuracy εcut, and C, Λ. Then, for thresholds, it returns Q and
  v = Q^{-3/2}. For every history H with canonical records, and every singular slab G
  that is spatially canonical and has fine cut necks, the surgery produces:
  - a new neck radius ρ and a core presentation;
  - a `MetricCutCapEvent E` with frame reversal;
  - the extended history K = H.appendEvent E;
  - a `GeometricCutoffRecord` with δ and scale Q, whose windows are canonical;
  - `E.poincareStandardDiscarded`;
  - the volume debit;
  - R ≥ Q/4 on the cap.
- Literature: Perelman II §4 (surgery), plus the volume decrease, plus the standard
  discard classification.
- Calls: `exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks` (private,
  `PoincareHornCutoffRecordOfFineCutNecks.lean:273`);
  `exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical` (private,
  `:522`); `exists_neckRadius_terminalCorePresentation_with_radius_lower_bound_of_spatiallyCanonical`
  (not located); `RetainedCoreHistory.hasCanonicalCutoffRecords_of_appendEvent_eq`
  (private, `PoincareHornCutoffRecord.lean`, not read).
- Named hypotheses: none. The body is bookkeeping: constants are threaded, Q is chosen
  above C₂²/r_core² and the fine-neck threshold, and the standard-discard input is
  aligned via `hRecordDelta`/`hδbar`.
- Discrepancy: none.

**`fineCutNecks_of_le`** — `:280`. Monotonicity of `FineCutNecks` in the accuracy. Trivial.

**`hasCanonicalCutoffRecords_of_le`** — `:288`. Monotonicity in the δ and ρ bounds. Trivial.

**`exists_compact_volume_debit_of_incoming_eq`** — `:295`. Transport along an equality.
Trivial.

**`uniformDebitSurgeryStepStrong_of_long_slabs`** — `:307` (read to `:426`). This is an
*off-route* sibling. It takes `hlong` (a slab-length Prop) and gets pinching from
`exists_admissiblePinchingFunction_for_identified_incomingSlabs`. Not used by the headline.

**`uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong`** — `S/Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:21` (read fully)
- Already recorded at depth 4. New in this pass: δb (`:64`) is a minimum over five
  thresholds (§1.1). p₀.delta = 1/2 (`:89`) is only a template (ROUTE-WALK note
  confirmed). Records are rebuilt with δ ≤ δb (`hδη`), and the `InCutoffClass` witness
  is `⟨initial, hend, hhor, hclass, recenter budget⟩`.

**`exists_horn_cutoff_record_with_uniform_volume_debit_of_fineCutNecks`** (private) — `S/Contract/PoincareHornCutoffRecordOfFineCutNecks.lean:273` (read `:273–300`, `:370–496`)
- Statement: as the factory above, for a fixed history class.
- Calls: `exists_pos_fixedHamiltonIveyRegion_for_identified_histories`
  (`HamiltonIveyPinching.lean:666`); `exists_admissiblePinchingFunction_for_identified_incomingSlabs`
  (`:689`); `exists_pos_le_singular_incoming_time_of_initialIdentification` (the first
  singular time is bounded below uniformly; not located);
  `exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks` (`:31`);
  `exists_presented_cap_scalar_lower_bound_of_canonical_window` (not located).
- Named hypotheses: none. The argument chooses Q, then takes pinching of the past slabs
  and the current slab from the records (`hpinch`, `:484–486`).

**`exists_horn_cutoff_record_at_scale_of_prepared_history_of_fineCutNecks`** (private) — `:31` (read `:31–255`)
- Statement: the surgery at a given scale Q, with the backward (strong) neck record added.
- Calls: `exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks`
  (`HornFineCutoffRecord.lean:407`); `exists_uniform_selected_neck_retained_append_backward`
  (private, `PreparedHistoryCutoff.lean:156`, not read);
  `nonempty_incomingBackwardNeck_record_of_selected_restrictions` (not read).
- Literature: Perelman's strong δ-necks. The cut neck must extend backward in time on
  [t−h², t], and this is where δold enters.

**`exists_poincareStandardDiscarded_of_retainedEvent_heq_of_spatiallyCanonical`** (private) — `:522` (read `:522–553`)
- A transport wrapper around `GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_spatiallyCanonical`
  (`S/Topology/DiscardedSpatialClassification.lean:311`, read `:311–410`). The two-case
  argument is described in §1.1 step 6. Its callees at `:233` (boundary case) and
  `exists_component_poincareStandard_tolerance_of_spatiallyCanonical` (whole component)
  were not read. Frontier.

**`exists_horn_cutoff_history_extension_with_canonical_windows_of_fineCutNecks`** — `S/Contract/HornFineCutoffRecord.lean:407` (read `:407–556`) — packaging. The event comes from `:51`, and the history extension from `exists_append_metricCutCapEvent`.

**`exists_prepared_horn_cutoff_event_with_original_neck_bounds_of_fineCutNecks`** (private) — `HornFineCutoffRecord.lean:51` (read `:51–80`, `:170–406`)
- This is the real surgery construction: δ = min δ₀ η (`:180`), first-hit horn necks at
  scale Q (`exists_finite_first_hit_oriented_horn_neck_data_of_fineCutNecks`, not read),
  retained set R = scalar-sublevel components, and the event from
  `exists_uniform_metricCutCapEvent_volume_debit_with_recenter_data` (`:171`). Pinching
  and scalar preservation go into the record through `terminal_data_transport` (`:308`).
  It also gives R ≥ Q/4 on the cap and an upper bound R ≤ max(coreBound, K_reset·Q).
- Literature: Perelman II §4.4 / Morgan–Tian §13–14.

**`exists_uniform_metricCutCapEvent_volume_debit_with_recenter_data`** — `S/Topology/FiniteMetricEventDebit.lean:231` (read `:231–334`) → private `:48` (proof read `:120–230`)
- The event with HI and scalar preservation plus the volume debit. It calls
  `exists_uniform_metricCutCapEvent_volume_bound` (`FiniteMetricEventVolume.lean:17`,
  read `:17–20`, `:96–104`), `exists_finiteFullPreparedMetric_volume_debit`
  (`S/StandardCap/FiniteVolumeDebit.lean:232`, statement read; inequality `:75`,
  read `:75–124`), `finiteFullPreparedMetric_hamiltonIvey` and `_scalar_floor`
  (`FullMetricCurvature.lean:151`, `:186`, read).

**`finiteFullPreparedMetric_hamiltonIvey`** — `S/StandardCap/FullMetricCurvature.lean:151` (read) — the case split described in §1.1.

**`StaticInsertionAdditionalProperties`** — `S/StandardCap/StaticPinchingInsertion.lean:31` (structure). **`exists_staticInsertion_with_additional_properties`** — `:63` (read `:63–103`) — builds the witness from `exists_uniform_positiveCoordinate_static_estimates` (`StaticThresholds.lean:26`, read fully).

**`exists_normalizedDatum_insertedMetric_pinching`** — `S/StandardCap/NormalizedInsertionPinching.lean:111` (read `:111–228`) — the HI-preservation argument, with δ₀ = `min τ (1/200000000)` (`:134`). **Computation not read**: `exists_insertedMetric_outer_curvature_gain` (`InsertionOuterCurvature.lean:157`, statement read) → `exists_curvature_rounding_collar` (the conformal curvature expansion), and `exists_normalizedDatum_insertedMetric_core_curvature_pos`.

**`exists_uniform_metricCutCapEvent_curvature_preserving`** — `S/Topology/FiniteMetricCutCapCurvature.lean:46` (read fully) — a sibling producer of the same HI preservation, used by `FiniteMetricRestart`/`FiniteMetricCutCapJetBounds`. On-route status: not established.

**HI through history** — `HamiltonIveyPinching.lean:187` (slab maximum principle, `curvatureOperatorRegionPropagationOn_of_initial_region` + `hamilton_ivey_pinching_of_…` not read: that is the README's Hamilton–Ivey theorem), `:242`, `:280`, `:308`, `:340`, `:381`, `:414`, `:521`, `:603`, `:666`, `:689` (all read). This bottoms out in the README-listed Hamilton–Ivey estimate.

### Priority 2: extinction

**`exists_poincare_controlled_extinction_of_history_volume_debit`** — `S/Topology/FiniteHorizonExtinction.lean:68` (read `:1–187`)
- Statement: given a set S of histories closed under the one-step producer, with uniform
  debit v, horizon bound B, records, frame reversal, standard discards, an initial
  barrier c, and threshold(c, W₀) < B, controlled extinction exists.
- Literature: Perelman III plus Perelman II finiteness.
- Calls: `exists_closedSlab_extension_to_horizon_of_volume_debit`
  (`FiniteHorizonContinuation.lean:49`); `…_of_initialScalarBarrier` (`:47`) →
  `isExtinctAtHorizon_of_initialScalarBarrier` (private `:22`) →
  `ObservedHistory.isExtinctAtHorizon_of_historyWidth` (`X/Families/ExtinctionTimeBound.lean:38`);
  `exists_poincare_controlled_extinction_of_observedHistory` (not read);
  `stageInitial_scalarLowerBound_of_history`, `incomingSlab_scalarLowerBarrier_le` (not
  read).
- Named hypotheses: all inline and supplied by the caller (`SingularEventExtinction.lean:33`).

**`exists_closedSlab_extension_to_horizon_of_volume_debit`** — `S/Topology/FiniteHorizonContinuation.lean:49` (read fully) — the maximal-event-count argument, §1.2. It calls `eventCount_le_card_initial_add_volume_bound` (`HistoryEventVolumeBound.lean:27`, read), which uses `eventCount_le_card_initial_add_two_mul_sum_card_cut` (`HistoryComponentCount.lean:53`, read) and `sum_cut_count_mul_le_exp_mul_initial_volume` (not read). It also calls `exists_closedSlab_or_singular_incomingSlab_from_time` (`MaximalSlab.lean:97`, read `:1–140`).

**`isExtinctAtHorizon_of_historyWidth`** — `X/Families/ExtinctionTimeBound.lean:38` (read fully) → `final_empty_of_uniform_records` (`ObservedComparison.lean:66`, located, not read) and `observedComparisonRecord_of_historyWidth_of_scalarLowerBound` (`ObservedWidthDini.lean:375`, read).

**`canonicalWidth`** — `X/Width/CanonicalClass.lean:19` (read fully). **`extinctionThreshold`** — `X/Families/ScalarThreshold.lean:11` (read fully). **`exists_initialScalarBarrier_of_compact`** — `S/Topology/ExtinctionExistenceReduction.lean:18` (read `:18–38`): R_min ≥ −3(1+|R(x₀)|)/2 at the minimum point, so c = 1/(1+|R_min|).

**`history_incoming_component_dini`** — `X/Families/ActualWidth.lean:428`; **`incoming_component_smooth_width`** `:269`; **`incoming_component_integrated_width`** `:141` (read `:50–70`, `:141–470`) — the Dini inequality, hypothesis-free apart from simple connectivity of the component. It uses `rfs_homotopy_groups` (π₂ = 0, not located) for `IsEssentialFamilyClass`.

**`rfs_integrated_class_width`** — `X/Families/ClassWidth.lean:142`; **`classWidth_le_affine_familyMaximum_add`** `:57` (read `:1–260`). **`rfs_family_deformation`** — `X/Families/Deformation.lean:978` (read `:900–1080`). **`projected_leastArea_slope_le_of_angle_le`** — `X/Families/RampAreaEvolution.lean:23` (statement read). **`rfs_prepared_family_flow`** — `X/Families/Flow.lean:35` (read `:35–80`) → `exists_continuous_prepared_ramp_family_on_Icc` (existence of the ramp curve-shortening flow; not read).
- Discrepancy with the brief's framing ("Colding–Minicozzi / Perelman"): the Lean
  follows **Perelman III** (S²-families of loops, curve-shortening with a ramp,
  angle-error term), not Colding–Minicozzi's harmonic-map sweepouts. See §3, A2.

**`historyWidth_event_jump`** — `X/Width/SurgeryWidthEvolution.lean:726` (read `:700–880`) → `rfs_actual_width_jump` `:312` (statement read) → `GeometricCutoffRecord.rfs_child_comparison` (`S/Topology/ChildComparison.lean:41`, read `:1–120`) → `rfs_comparison_support`, `local_length_comparison` (not read). See §3, A4.

### Priority 3: simple connectivity (E2)

**`smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace`** — `S/Topology/SmallScaleNoncollapsingThroughSurgery.lean:522` (read `:515–600`) — it gets `hsimply` from `simplyConnectedSpace_connectedComponent_stage`. The constants (3072, `L`, …) are computation not read.

**`RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage`** — `S/Topology/StageComponentSimplyConnected.lean:24` (read fully) → `rfs_simply_connected_history` (`Ancestry.lean:17`, read `:1–80`) → `child_simplyConnected` (`ChildSimplyConnected.lean:35`, read fully) → `simplyConnectedSpace_childCore_of_parent_simplyConnected` (`ChildCoreSimplyConnected.lean:340`, read `:120–349`) → `componentwiseSimplyConnected_of_isOpen_removedBand` (`TubePuncturedCore.lean:293`, read `:250–330`) → `TwoSidedCollar.simplyConnectedSpace_connectedComponentIn_compl_iUnion` (`T/VanKampen/TwoSidedCollarSimplyConnected.lean:229`, read `:200–260`). **Proved.**

**`initialIdentification_components_simplyConnected`** — `X/Width/SurgeryWidthEvolution.lean:831` (read) — stage 0 only, by homeomorphism transport.

**`exists_ball_volume_of_spatialCanonicalWitness_of_simplyConnected`** — `RF/Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessBallVolume.lean:533` (read `:533–557`) — simple connectivity is used only in the `round` case (`exists_ball_volume_of_spatialRoundComponent`, not read).

### Priority 4: reduced volume

**`noncollapsingThroughSurgery_of_reducedVolume_of_smallScale`** — `S/Topology/NoncollapsingThroughSurgeryLeaves.lean:242` (read `:1–160`, `:236–296`) — §1.4. The four predicates are defined at `:96`, `:101`, `:113`, `:147`.

**`historyReducedVolumeMonotone_holds`** — `S/Topology/HistoryReducedVolumeMonotone.lean:189` (read `:160–240`) → `lintegral_image_historyMinDomain_le_of_lt` (not read; this is the monotonicity integrand computation over the minimizer domain, and the README-listed reduced-volume monotonicity is its single-flow analogue).

**`historyReducedVolumeLocalUpperBound_holds`** — `S/Topology/HistoryReducedVolumeLocalUpperBound.lean:31` (read `:1–80`) — C₀ = (4π)^{-3/2}e³⁶, with a Gaussian tail (`exists_uniform_tail_gaussian_metric`) and a core estimate (`exists_lintegral_image_historyMinDomain_core_le`, not read). The constant is computation not read.

**`historyReducedVolumeInitialLowerBound_holds`** — `S/Topology/InitialRegularBlock.lean:510` (read `:505–567`); **`exists_uniform_initial_regular_block`** `:197` (read `:197–337`) — §1.4. Frontier: `InitialSpatialMinimum.lean:59`, `CapWindowActionRegularCrossingRecenter.lean:439`, `regularizedCost_le_of_initial_tail_replacement`, `exists_initial_small_ball_volume_lower_bound`.

### Priority 5: strong necks and the fine-neck supply

**`strongNecksOfCutoffClass_of_strongSpatialCrossing`** — `S/Topology/StrongNecksOfCutoffClass.lean:45` (read `:1–120`)
- Statement: canonical ⟹ strongly canonical at a higher threshold.
- Argument: a three-way cover of high-curvature points (`key`):
  1. "old" points, R·(t − t_k) ≥ τ_min, are strongly canonical by the backward
     canonical neighbourhood (`stronglyCanonicalWhere_of_canonicalBefore`);
  2. cap-window points near a recent surgery are strongly canonical by comparison with
     the standard solution (`exists_capWindow_stronglyCanonicalWhere`,
     `CapWindowCapWitness.lean:192`, not read);
  3. young points not in a cap window are handled by `StrongSpatialCrossingContinuation`.
- Literature: Perelman II §4–5 / Morgan–Tian ch. 15–16 (necks near surgery come from the
  standard-solution comparison; old necks come from canonical neighbourhoods).

**`strongSpatialCrossingContinuation_holds`** — `S/Topology/StrongSpatialCrossingContinuationLeaf.lean:243` (read `:243–330`; definition `StrongSpatialCrossingContinuation.lean:16`, read `:1–60`) — proof by contradiction. It takes a sequence of counterexamples with q_can = n+1 → ∞ and δ_b ≤ 1/(n+1), and passes to a limit (`exists_eventually_strong_spatialCanonicalWitness_of_isTracedRegion`). This is a compactness argument, not read to the end.

**`fineCutNeckSupplyStrong_holds`** — `S/Contract/FineCutNeckSupplyStrongLeaf.lean:18` (read `:1–80`; definition `FineCutNeckSupplyStrong.lean:15`, read) — by contradiction. It takes a sequence of deep-horn points with R ≥ (n+1)·threshold that are not centres of εc-necks, then applies blow-up (`exists_slices_of_deep_horn_presentation_sequence`, `exists_tolerance_false_of_deep_horn_slices`; not read). This is Perelman's "deep in an ε-horn every point is a δ-neck centre".

---

## 3. Escalations, ranked

None of these is a found gap. Each is either a place where the Lean differs from the
standard argument or a place where this pass could not confirm a step.

**A1 (medium, framing, affects how the whole audit is scoped).** On the headline route
the no-supplier search cannot find a hidden `sorry`. The headline is hypothesis-free,
so every predicate on the route is discharged by construction, conditional only on the
axiom check (see the preamble). A "named predicate not discharged" finding is possible
only for theorems that still carry the predicate as a hypothesis: intermediate or
off-route statements people may reuse, such as `uniformDebitSurgeryStepStrong_of_long_slabs`
(`hlong`, `UniformDebitSurgeryStepOfFactory.lean:307`), `rfs_*_of_frontier` forms, and
`*Frontier*.lean` files. For headline soundness the audit should instead (i) run
`#print axioms` and an independent checker, and (ii) look for weak or junk definitions in
the final structure. For (ii) this pass checked the junk-value risk in width
(sSup/sInf on ℝ): `familyMaximum` attainment is proved
(`familyMaximum_attained`, used at `X/Families/ClassWidth.lean:100`), `classWidth` is an infimum of
a nonempty set that is ≥ 0, and `leastArea` is an infimum of nonnegative competitor areas.
No junk value was seen.
- Artifact side: the README says "Each is `sorry`-free (axioms: `propext,
  Classical.choice, Quot.sound`)".
- Brief side: "an undischarged named predicate on the route is a `sorry` that
  `#print axioms` cannot see".
- Both cannot bite on a hypothesis-free headline.

**A2 (low–medium, literature alignment).** The extinction argument is Perelman III
(S²-families of loops in π₂(ΛM), a curve-shortening flow with λ-ramp, and a least-area
slope bound D⁺A ≤ −2π − ½R_min·A plus an angle error), not Colding–Minicozzi (sweepouts
by 2-spheres and harmonic replacement). Consequences:
- The rate is 2π per unit time on loop *disk areas*. The threshold constant 8π comes
  from integrating with the factor (t+c)^{-3/4} (`ScalarThreshold.lean:11`, `:53`).
- The standard reference for checking is Perelman III §§1–3 / Morgan–Tian ch. 18, not
  CM 2005/2008.
- Artifact: `rfs_family_deformation` (`Deformation.lean:978`),
  `projected_leastArea_slope_le_of_angle_le` (`RampAreaEvolution.lean:23`).
- Brief: "width argument (Colding–Minicozzi / Perelman)".
- There is no mathematical discrepancy with Perelman III as read.

**A3 (medium, already E2; confirmed, not a gap).** κ-noncollapsing through surgery is
split. Scales in [r₀, ε] use the reduced volume. Scales below r₀ use Bishop–Gromov plus
canonical-neighbourhood witnesses, and that part needs every stage component to be simply
connected.
- Perelman II §5: "κ-noncollapsing on scales ≤ ε for any normalized initial metric,
  proved by reduced volume".
- Lean: `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace` requires
  `[SimplyConnectedSpace P₀.Carrier]` (`SmallScaleNoncollapsingThroughSurgery.lean:522`).
- Propagation is proved by van Kampen over two-sided sphere collars (§1.3). Effect: the
  Lean's surgery theory (canonical neighbourhoods and noncollapsing through surgery) is
  established only for simply connected initial data. That suffices for Poincaré, but
  the intermediate theorems are **not reusable** for geometrization.
- Residual check, not done: whether the `positive` (positive sectional curvature compact
  component) canonical case at `SpatialCanonicalWitnessBallVolume.lean:554` covers
  S³/Γ with large |Γ| through the neck-chart bound `h₄`. If it did not, simple
  connectivity would be needed there too, and it is not supplied. The code routes that
  case to `h₄ W hchart …` without simple connectivity, so it must hold for any Γ. That
  lemma (`exists_ball_volume_of_spatialCanonicalWitness`) was not read.

**A4 (low–medium, could not confirm).** The width does not increase across surgery
because of an ℓ(s)-Lipschitz, degree-one, surjective collapse map from the pre-surgery
component at time s to the post-surgery component, with ℓ(s) → 1
(`ChildComparison.lean:41–72`). In the standard argument the surgered-away horn must be
collapsed onto the cap without stretching cross-sections. That is possible only because
the neck of length ~δ⁻¹h with radius ≈ h maps onto a cap of length ~C·h, and everything
beyond maps to the tip. The Lipschitz estimate (`local_length_comparison`,
`rfs_whole_parent_map_localTerminalDistanceControl`) was not read. The δ in play there
and the direction of the comparison (parent metric at time s < t_sing against the
output metric) are what to check.

**A5 (low, definition differs from the textbook).** The reduced volume through surgery
is *defined* as limsup_B of an integral over endpoints of regularized-cost minimizers
whose surgery crossings stay in the retained region
(`NoncollapsingThroughSurgeryLeaves.lean:22–58`). Monotonicity then holds for every
history without hypotheses (`HistoryReducedVolumeMonotone.lean:189`). This matches the
domain restriction of Perelman II §5 / Morgan–Tian ch. 16. All the weight is in the lower
bound, i.e. that this restricted domain has volume ≳ κ₀t^{3/2}
(`InitialRegularBlock.lean:197`). The two lemmas that carry Perelman's "barely avoiding
surgery" estimate (`InitialSpatialMinimum.lean:59`,
`CapWindowActionRegularCrossingRecenter.lean:439`) were not read. They are the highest-value
unread nodes on the smooth branch.

**A6 (low, statement stronger than needed; valid).** Surgery preserves the fixed
Hamilton–Ivey region for **every** a > 0 (`GeometricCutoff.lean:265`), which is more than
the time-t pinching Perelman needs. It is valid because the conformal bending only
increases R and ν (`InsertionOuterCurvature.lean:157`) and the region is upward-closed for
R ≥ 0. This closes ROUTE-WALK E3.

**A7 (low, tooling; extends ROUTE-WALK E4).** The surgery construction is private at
three levels, reached with `open private` across files:
- `UniformDebitSurgeryStepOfFactory.lean:39`;
- `PoincareHornCutoffRecordOfFineCutNecks.lean:31, :273, :522`;
- `HornFineCutoffRecord.lean:51`, plus about 15 private names opened from
  `HornCutoffRecord`, `HornFineCutNecks`, `HornMetricEvent` and `PreparedHistoryCutoff`
  (`HornFineCutoffRecord.lean:5–20`).

Name-level cone and supplier tools will under-report this core.

**A8 (low, located, not read).** Two analytic facts sit under the continuation
dichotomy and the limit metric: Hamilton's "maximal solution ⇒ |Rm| unbounded"
(`rmUnbounded_of_maximal`, used at `MaximalSlab.lean:56`) and the singular-time limit
metric (`TerminalMetricExistence.lean:84`). Neither is in the README list. Both should be
walked to Mathlib or to the Shi/compactness entries.

---

## 4. Named predicates met, and where they are discharged

**Not discharged on the route: none.** This cannot happen for a hypothesis-free headline
(A1). No Prop hypothesis was found on a route theorem at depth ≥ 5 in the parts read,
except inline producer hypotheses that the caller supplies in the same proof.

| predicate / bundle | definition | taken by | discharged at |
|---|---|---|---|
| `StaticInsertionAdditionalProperties C w` (structure, includes `hamiltonIvey`) | `S/StandardCap/StaticPinchingInsertion.lean:31` | `finiteFullPreparedMetric_hamiltonIvey` (`FullMetricCurvature.lean:151`) | `exists_staticInsertion_with_additional_properties` (`StaticPinchingInsertion.lean:63`) ← `StaticThresholds.lean:26` ← `NormalizedInsertionPinching.lean:111` |
| record fields `curvature_preserving` / `scalar_preserving` | `GeometricCutoff.lean:265, :269` | `ObservedHistory.fixedHamiltonIveyRegion_and_scalar_lower` (`HamiltonIveyPinching.lean:521`) | produced at `HornFineCutoffRecord.lean:308` from `FiniteMetricEventDebit.lean:203–213` |
| `PinchingThroughSurgery` | `CanonicalNeighborhoodInduction.lean:239` | route (depth 4) | `PinchingThroughSurgery.lean:12`, via the records |
| `HistoryReducedVolumeMonotone` | `NoncollapsingThroughSurgeryLeaves.lean:96` | `:242` | `HistoryReducedVolumeMonotone.lean:189` (no hypotheses) |
| `HistoryReducedVolumeLocalUpperBound` | `:101` | `:242` | `HistoryReducedVolumeLocalUpperBound.lean:31` |
| `HistoryReducedVolumeInitialLowerBound` | `:113` | `:242` | `InitialRegularBlock.lean:510` |
| `SmallScaleNoncollapsingThroughSurgery` | `:147` | `:242` | `SmallScaleNoncollapsingThroughSurgery.lean:522`; its simple-connectivity input is discharged by `StageComponentSimplyConnected.lean:24` |
| `StrongSpatialCrossingContinuation` | `StrongSpatialCrossingContinuation.lean:16` | `StrongNecksOfCutoffClass.lean:45` | `StrongSpatialCrossingContinuationLeaf.lean:243` |
| `FineCutNeckSupplyStrong` | `S/Contract/FineCutNeckSupplyStrong.lean:15` | `UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:21` | `FineCutNeckSupplyStrongLeaf.lean:18` |
| `InitialScalarBarrier g c` | `X/Families/InitialScalarBarrier.lean:18` | `FiniteHorizonExtinction.lean:68` | `exists_initialScalarBarrier_of_compact` (`ExtinctionExistenceReduction.lean:18`) |
| `IsEssentialFamilyClass ξ` | not opened | `rfs_integrated_class_width` | `isEssentialFamilyClass_of_pi2_zero` + `rfs_homotopy_groups` (`ActualWidth.lean:189–192`) |
| `PreparedFamilyApproximation`, `PreparedFamilyFlowData`, `RampAlternativeData` (frontier bundles) | not opened | `rfs_family_deformation_of_frontier` (`Deformation.lean:901`) | the route uses `rfs_family_deformation` (`:978`), which builds from `rfs_prepared_family`, `rfs_uniform_ramp_alternative` (`:933`) and `rfs_prepared_family_flow` (`Flow.lean:35`); the `_of_frontier` forms are reductions, and their hypotheses are proved in the callers read |
| `hproduce`, `hdebit`, `hprefix`, … (inline) | inline | `FiniteHorizonExtinction.lean:68`, `FiniteHorizonContinuation.lean:49` | the caller, `SingularEventExtinction.lean:33` (ROUTE-WALK) |
| `hlong` (slab-length) | inline | `uniformDebitSurgeryStepStrong_of_long_slabs` (`UniformDebitSurgeryStepOfFactory.lean:307`) | **off-route**; not needed by the headline |
| `PlateauSmoothLoopDiskDensity`, `HasUniformWidthBound`, `HasMorganTianExtinctionInput` | `X/Width/PlateauFrontierAudit.lean:24`, `InitialWidthDataFrontier.lean:12` (defs located) | off-route alternative endgames (`InitialWidthDataFrontier.lean:47, :65`) | not established. `PlateauFrontierAudit.lean:61` (`not_forall_plateauDiskDensity_standardEuclideanLine`) *refutes* a universal form of one Plateau frontier. These are the places where "named but not discharged" is real, and they are off the headline route |

---

## 5. Computation not read (for the independent-computation rung)

1. `NormalizedInsertionPinching.lean:134`: δ₀ = min(τ, 1/200000000); `hclose` at 1e-8 C²
   closeness (`:143–147`); and `InsertionOuterCurvature.lean:157` →
   `exists_curvature_rounding_collar`, the conformal-change curvature expansion that shows
   −f''/2 dominates the C²-error terms. **Most important unread computation** for pinching
   through surgery.
2. `StaticThresholds.lean:62–84`: δt = (2A + 5·transitionEnd/2 + 3)⁻¹ and the collapse-tip
   window.
3. `FiniteMetricEventDebit.lean:149`: margin = π/(8·vol(standard cap ball)+1), and
   `FiniteVolumeDebit.lean:125–231` (`δV` threshold): the band volume 2π/δ·R^{-3/2}
   against the cap volume. This is the "each neck removes ≥ Q^{-3/2}" inequality.
4. `PoincareHornCutoffRecordOfFineCutNecks.lean:400–425`: the choice of Q (max of four
   thresholds + 1), and `hnominal`.
5. `HornFineCutoffRecord.lean:180–196`: ε₀ = min(εbase/2, (2⌊δ⁻¹⌋+4)⁻¹), and the order
   bookkeeping `hεorder`.
6. `ScalarThreshold.lean:53–78` (`extinctionThreshold_lt_iff`, `nlinarith`) and
   `ObservedWidthDini.lean:146–157` (slope comparison).
7. `HistoryEventVolumeBound.lean:27–48`: budget arithmetic.
8. `InitialRegularBlock.lean:197–337`: Cmain = 3 + 2e^{36Kθ₀}(…) + …, c₁ = min(½,
   ρv/√B, √θ₀/(2√B)), κ₀ = κv·c₁³, and `cost_budget_le` (`:35`).
9. `HistoryReducedVolumeLocalUpperBound.lean:33`: C₀ = (4π)^{-3/2}e³⁶.
10. `SmallScaleNoncollapsingThroughSurgery.lean:533–579`: L = 1 + Cgrad + 8Ctime +
    3072(1+φ(1)+φ(0))², c = 1/(4L) (listed before by ROUTE-WALK).
11. `RampAreaEvolution.lean:23–40`: the angle-error term η²/√(1−η²)·(Θ+L)e^{(C+B₀)(b−a)}.

---

## 6. Remaining frontier (unread bodies, in priority order)

1. `S/Topology/InitialSpatialMinimum.lean:59` and
   `S/Topology/CapWindowActionRegularCrossingRecenter.lean:439`: Perelman's ℓ < 3 and
   barely-avoiding-surgery lemmas. This is the core of noncollapsing through surgery (A5).
2. `S/Topology/ChildComparison.lean` →
   `rfs_whole_parent_map_localTerminalDistanceControl`, `local_length_comparison`: the
   Lipschitz collapse map for the width jump (A4).
3. `S/Contract/PreparedHistoryCutoff.lean:156` (private): backward (strong) neck selection
   and δold.
4. `S/Topology/DiscardedSpatialClassification.lean:233` and
   `exists_component_poincareStandard_tolerance_of_spatiallyCanonical`: topology of the
   discarded components.
5. `SpatialCanonicalWitnessBallVolume.lean`: `exists_ball_volume_of_spatialCanonicalWitness`
   (positive case, A3 residual) and `exists_ball_volume_of_spatialRoundComponent`.
6. `S/StandardCap/InsertionOuterCurvature.lean` → `exists_curvature_rounding_collar`;
   `exists_normalizedDatum_insertedMetric_core_curvature_pos` (§5.1).
7. `X/Families/RampAreaEvolution.lean:23` body; `exists_continuous_prepared_ramp_family_on_Icc`
   (ramp curve-shortening flow existence); `rfs_prepared_family`;
   `rfs_essential_short_family` (`EssentialClass.lean:53`); `rfs_homotopy_groups`.
8. `X/Families/ObservedComparison.lean:66` (`final_empty_of_uniform_records`);
   `ObservedComparisonRecord` construction (`observedComparisonRecord_of_historyWidth`).
9. `HistoryReducedVolumeMonotone` → `lintegral_image_historyMinDomain_le_of_lt`;
   `exists_lintegral_image_historyMinDomain_core_le`.
10. `S/Topology/StrongSpatialCrossingContinuationLeaf.lean:243–499` (limit argument to the
    end); `CapWindowCapWitness.lean:192`; `FineCutNeckSupplyStrongLeaf.lean:80–end`
    (deep-horn blow-up).
11. `rmUnbounded_of_maximal` (not located), `TerminalMetricExistence.lean:84` (A8);
    `HistoryComponentCount` `card_connectedComponents_output_add_discarded_le`,
    `one_le_card_cut_add_card_discarded`.
12. Still open from ROUTE-WALK §6: the canonical-neighbourhood continuation leaves
    (`DeepContinuation.lean:213`, `CapWindowContinuationLeaf.lean:366`,
    `CrossingContinuationLeaf.lean:132`, `SpatialCrossingContinuationLeaf.lean:193`). Not
    touched in this pass.
