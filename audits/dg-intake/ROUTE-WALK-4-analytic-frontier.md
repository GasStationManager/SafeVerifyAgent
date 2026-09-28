# Route walk 4: the analytic frontier left by walk 2

Artifact `/home/user/differential-geometry` @ `7a48598d` (checked with `git log -1`),
read-only. Nothing was compiled or committed, and no `#print axioms` or independent
checker was run. Auditor model family: Claude (one family; PLAYBOOK §4.16).

This walk continues `ROUTE-WALK-2-analytic.md` §6. It reads the items that walk left
unread, bottoms each one out, and reconstructs the argument (PLAYBOOK §0).

**Path abbreviations.**
- `RF/` = `DifferentialGeometry/Geometry/Flow/RicciFlow/`
- `ST/` = `RF/Surgery/Topology/`
- `SC/` = `RF/Surgery/StandardCap/`
- `PS/` = `RF/Perelman/StandardSolution/`
- `CN/` = `RF/Perelman/CanonicalNeighborhood/`

**Citations.** Every `file:line` below was read with `sed -n` in this pass unless it is
marked "(located, not read)". "Located" means the declaration was found with grep and its
body was not opened.

**Instrument run.** `audits/junkvalue.py` was run over the whole project (745 rows, output
in the session scratchpad, not in the repo). The only hits inside files on these paths are
false positives:
- `ST/HistoryAction.lean:1511`: the denominator `w` has `(hw : 0 < w)` at `:1520`.
- `SC/InsertionMetric.lean:143–181` (`insertionCutoff A`).
- `ST/ProspectiveNeckSurvival.lean:61,96` (δ via `neckBuffer`, which a `NormalizedNeck`
  certifies as positive).

The hand junk-value lens is in §8.

---

## 0. Summary

| item | verdict | the load-bearing estimate |
|---|---|---|
| A5, reduced-volume lower bound through surgery | **Reconstructed; matches Perelman II §5 / Morgan–Tian ch. 16–17.** No named predicate. | A path that meets a surgery cap at its birth has action > A. Either it stays in the evolving cap, where the standard solution has R ≥ c/(1−t), so ∫R ≥ c·log(1/(1−θ)) → ∞. Or it leaves a ball of radius r in rescaled time ≤ θ, which costs ≥ r²/(Cθ). Or it sits in the cap near the endpoint, where the curvature of the controlled ball is too low. The surgery scale enters as cap scale q ≥ max(q_min(A,B,E,r₀), q_deriv/C_birth, 1/a₀), forced by nominal radius < δ²ρ with δ ≤ δ₀(r₀,…). |
| A4, width jump | **Reconstructed; the map is 1-Lipschitz exactly (not 1+ξ) against the terminal limit metric.** The only loss is ℓ(s) → 1 from g(s) → g_∞ on a compact set. | On the neck the collapse map is (θ,z) ↦ ρ(z)θ with 0 ≤ ρ' ≤ 1 and warping ≤ √2. The inserted cap is the standard cap **scaled by η = 1−√δ**, which equals the neck's cylinder lower bound. Degree one follows from naturality of the positive π₃ generator (Hurewicz). |
| A3, `positive` case | **Reconstructed.** The case covers only S³ and RP³ (`PositiveComponent`). The volume comes from a **field of the canonical witness** plus Bishop–Gromov with Ric ≥ 0. | vol B(x,r) ≥ (r/L)³·vol(component) ≥ (r/L)³·C₂⁻¹R^{-3/2}, with L = 3C₁/√R. |
| A8, maximal ⇒ \|Rm\| unbounded | **Hamilton's restart argument.** Bounded Rm gives metric equivalence and derivative bounds, then a restart with uniform existence time, then gluing by forward uniqueness. | Restart lemmas were not read. |
| A8, terminal limit metric | **Local Shi estimates + Arzelà–Ascoli + time-Lipschitz Cauchy.** | `shiLocalUniformBound` (located, not read). |
| §6.3, strong (backward) neck | Reduced to a **contradiction-sequence limit** (`ProspectiveNeckSurvivalVariableThreshold.lean`, 1865 lines). Body not read. | — |
| §6.4, discarded components with a cut sphere | **Reconstructed.** A neck chain from the cut sphere into the discarded side either closes up standard, or stops at a canonical cap. | — |

No discrepancy with the mathematics was found. The escalations in §6 are places where the
Lean differs from the textbook by design, or where a load-bearing body lies below the
reading frontier.

---

## 1. A5: the reduced-volume lower bound and "barely avoiding surgery"

### 1.1 The object being bounded

**`regularMinimizerEndpoints`** (`ST/NoncollapsingThroughSurgeryLeaves.lean:24`) is the set
of points q at the earlier stage `first` for which some α satisfies all of:
- α is absolutely continuous on every stage;
- α runs from p (at clock 0) to q (at clock v);
- at every event it crosses **regularly** (`RegularCrossing`, `ST/EventData.lean:367`: an
  *interior* point x of the retained region `old` with x = α(before) and `oldOutput x`
  = α(after));
- its extended action **equals** the regularized cost from p to q.

**`regularizedCost`** (`ST/HistoryAction/AbsoluteContinuity.lean:274`) is the `sInf` in
`WithTop ℝ` of `regularizedActionValues` (`:260`). Competitors there must cross every
event through `old`; the boundary of `old` is allowed. So the cost is an infimum over
paths that never pass through a cap at its birth, and a minimizer is additionally
required to cross at interior points.

Perelman II §5 and Morgan–Tian ch. 16 use the same kind of restriction: admissible
curves, and barely admissible ones at the boundary.

**`reducedVolume`** (`NoncollapsingThroughSurgeryLeaves.lean:43`) is
limsup_{B→∞} ∫ over `regularMinimizerEndpoints` of `regularizedDensity`.

**`regularizedDensity`** (`ST/HistoryReducedDensity.lean:330`) is the supremum over action
values A of exp(−A/(2v) − (3/2)log v² − (3/2)log 4π) = (4πv²)^{-3/2}·e^{−A/(2v)}. In the
clock s = √τ, with v = √τ̄, this is exactly (4πτ̄)^{-3/2}e^{−ℓ}, where ℓ = L/(2√τ̄).

**`ReducedVolumeBoundedBelowBefore`** (`:61`) evaluates the reduced volume at
v = √t, which is all the way back to time 0.

### 1.2 The lower bound: `historyReducedVolumeInitialLowerBound_holds` (`ST/InitialRegularBlock.lean:510`)

- **Statement.** Given the horizon bound B, there is c > 0 depending on (P₀, g₀, B) and not
  on r₀. For each r₀ and q_can there are thresholds δ_max, … such that every history in the
  cutoff class satisfies ReducedVolume ≥ c at every point whose parabolic ball of radius
  r ∈ [r₀, ε] is Rm-controlled. The terminal-slab form is included.
- **Literature.** Perelman II Lemma 5.2 (the lower bound on Ṽ from the initial time); Morgan–Tian Prop. 17.x.
- **Structure.**
  1. The proof calls `exists_uniform_initial_regular_block` (`:197`) with ρ = 1, so
     ρ_max = 1.
  2. The canonical, gradient and pinching inputs of the predicate are bound to `_` and
     unused. Only the scalar time-derivative bound is used, through
     `historyScalarDerivativeBoundBefore_of_eventSlabsDerivative`.
  3. The block is then converted into a density bound by
     `reducedVolume_ge_of_initial_regular_block` (`:355`, read `:355–427`):
     - density ≥ exp(−C)(4πt)^{-3/2} on U, because cost ≤ 2C√t means ℓ ≤ C;
     - U ⊆ `regularMinimizerEndpoints`;
     - vol(U) ≥ κ₀t^{3/2};
     - so Ṽ ≥ κ₀e^{−C}(4π)^{-3/2}.
  4. The limsup over B is removed by `reducedVolume_eq_of_scalar_lower_bound_le` (located,
     not read): for B ≥ B_f = 3/a₀ the integrand is independent of B.

### 1.3 `exists_uniform_initial_regular_block` (`:197`, read `:197–337`)

- **Statement.** There is an open U in stage 0 with vol U ≥ κ₀t^{3/2}. Every q ∈ U is a
  regular-minimizer endpoint, and cost(p→q) ≤ 2C√t.
- **Argument.**
  1. *ℓ < 3/2 point* (`hL1`). There is q₀ at time 0 and a minimizer from p to q₀ with
     action L < 3√t, which is ℓ(q₀) < 3/2. It comes from `InitialSpatialMinimum.lean:59`
     (§1.4).
  2. *Tail replacement* (`regularizedCost_le_of_initial_tail_replacement`,
     `ST/InitialEndpointPerturbation.lean:310`, located, not read). On the first-stage window
     [0, θ], θ = min(t, θ₀)/2, the curvature satisfies |Rm| ≤ K. This bound comes from
     `exists_uniform_stage_zero_curvature_bound` (not located), and θ₀ = min(a_S, η), where
     a_S is the uniform lower bound on the first singular time. Replacing the last piece of
     the minimizer by a segment to any q in B_{g₀}(q₀, c₁√t) gives cost ≤ C_main√t
     (`cost_budget_le`, `:35`, statement and algebra read).
  3. *Initial noncollapsing* (`exists_initial_small_ball_volume_lower_bound`,
     `ST/InitialVolume.lean:55`, located, not read): vol B(q₀, c₁√t) ≥ κ_v(c₁√t)³.
  4. *Barely avoiding surgery*. Every q with cost < C_main√B + 1 is a
     regular-minimizer endpoint (`hA24`, from
     `CapWindowActionRegularCrossingRecenter.lean:439`, §1.5).
- **Where δ enters.** δ₀ = min(δ₁, δ₂) comes from the two lemmas in steps 1 and 4.
- **Constants** are computation, not read (§9).

### 1.4 `exists_uniform_initial_spatial_regularizedCost_minimum_lt_three_mul` (`ST/InitialSpatialMinimum.lean:59`, read fully)

- **Statement.** There are (m₀, R₀, ε₀, δ₀) such that, for every history in the class
  (records, HI pinching a₀, derivative bound) and every p with a controlled ball of radius
  r_Term, there are q at stage 0 and L such that:
  - L is realized by a C¹ competitor;
  - L equals the regularized cost;
  - L ≤ cost(p, z) for all z;
  - L < 3√t.
- **Literature.** Perelman I §7 / II §5: min ℓ(·, τ̄) ≤ n/2 = 3/2, obtained from the
  maximum principle for L̄ − 6τ (L̄ = 2√τ L), extended through surgery.
- **Argument.**
  1. Seed (`exists_low_action_seed_off_event_times_of_parabolicallyRmControlledBall`,
     `:17`, read). Pick a ∈ (0, r/2] avoiding the finitely many event clocks √(t − t_j).
     On the controlled ball, a short path has 2aL₀ − 6a² < 0.
  2. Propagation (`ST/HistoryAction/MinimumPropagation.lean:1715`, statement read
     `:1715–1790`). The minimum of 2wL − 6w² stays negative as w increases, stage by stage
     (`exists_propagating_negative_spatial_minimum_on_stage`, `:1424`) and across events
     (`:1553`), both private and not read. At w = √t this gives L < 3√t.
  3. Propagation needs two hypotheses:
     - (i) `hregular`: every competitor with action < Ā = 3E+1 crosses every event
       regularly;
     - (ii) `hbirthRegular`: every point at an event time reached with action < Ā is a
       regular crossing.

     Both are discharged by contradiction from the two "nonregular ⇒ large action" lemmas
     (§1.5). Here E = √B bounds √t.
- **Named hypotheses.** None. (i) and (ii) are discharged inline at `:112–144`.
- **Discrepancy.** None. The Lean gets a strict inequality, which is harmless.

### 1.5 Barely avoiding surgery (`ST/CapWindowActionRegularCrossingRecenter.lean`, read `:1–260`, `:300–336`, `:439–521`)

**`exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_recenter_budget`** (`:439`)
- Statement: cost(p→q) < A implies q ∈ `regularMinimizerEndpoints`.
- Argument:
  1. Finite cost gives a nonempty competitor set.
  2. A minimizer γ exists (`exists_regularizedCost_minimizer_of_ne_top`, located, not
     read). This is **existence of L-minimizers through surgery**, a real analytic input.
  3. γ has action < A, so every crossing is regular by `:337` (not read; it is the
     node-plus-initial-point packaging of the two lemmas below).

**`…_gt_of_nonregular_node_of_recenter_budget`** (`:142`, read `:142–243`)
- Statement: if the path crosses event i non-regularly, its action is > A.
- Argument:
  1. If the event time equals t, then p itself is at the event, and the controlled ball
     forces a regular crossing (`regularCrossing_of_oldOutput_at_event_time`).
  2. Otherwise `regularCrossing_or_cap_of_admissible_node`
     (`ST/MetricCutCapScalarLower.lean:949`, located, not read) says a non-regular crossing
     lands in the cap `(records i).static b` at birth.
  3. The birth lemma below then applies.

**`…_gt_of_nonregular_initial_point_of_recenter_budget`** (`:244`, read `:244–336`) is the
same argument for the path's starting point.

**`…_gt_of_inserted_cap_birth_of_recenter_budget`** (`:60`, read `:60–140`). **This is where
the surgery scale is compared with the reduced-volume scale.**
- Q_min = max(q_min, q_Deriv/C_birth, 1/a₀). Here q_min = q_min(A, B, E, r_Term) comes from
  the canonical cap-birth lemma. Then δ_scale is chosen by
  `exists_uniform_static_cap_scale_lower_bound_of_recenterConstant_mul_delta_le` (`:16`,
  read `:16–56`):
  - The record gives nominal radius < δ²ρ (`R.nominal_small`).
  - With δ ≤ δ₀ this gives 2K·r_nom² < 1, so the neck scale r_nom^{-2} > 2K.
  - The recentred cap scale is at least half of that, because c_rec·δ ≤ 1/2
    (`recenter_scale_comparison`).
  - Hence the cap curvature scale q > Q_min.
- In words, the surgery radius h satisfies h² ≲ δ⁴ρ² < 1/(2Q_min). So h is small relative
  to:
  - the controlled-ball radius r₀ (through q_min ≥ 19/r₀² and C = r₀^{-4});
  - the action budget A (3√B+1 or C_main√B+1);
  - the horizon E = √B;
  - the curvature-derivative threshold;
  - the pinching parameter.

  This is Perelman's choice "δ(t) small depending on r(t) and the time".

**`exists_uniform_canonical_cap_birth_action_lower_bound`** (`ST/CapWindowAction.lean:1537`,
read `:1537–1612`) unpacks the canonical window of the cap and calls the prepared version.

**`…_prepared_cap_birth_action_lower_bound_of_parabolicallyRmControlledBall`** (`CapWindowAction.lean:1327`, read `:1327–1528`). This is the case analysis.
1. *Birth time equals t.* Then p is in the cap. The window-scale bound gives
   |Rm|(p) ≳ q > 19/r², which contradicts the controlled ball's |Rm| ≤ r^{-2}.
2. Otherwise `exists_uniform_prepared_cap_evolution` (`SC/WindowEvolution.lean:17`,
   statement read `:17–137`; body not read) gives a dichotomy:
   - **(survive)** On rescaled time [0, q(s−b)] with q(s−b) ≤ Θ, the cap window
     flows ε-close in C^N to a standard solution Q, and stops only when q(s−b) = Θ or
     s = t;
   - **(discard)** the cap flows close to Q until a later surgery i, at which the whole
     ‖y‖ ≤ a part of the cap lies in a **discarded** component.

   This is Morgan–Tian Prop. 16.x / Perelman II Lemma 4.5: the surgery cap is modelled by
   the standard solution until it is discarded.
3. In the discard case, the path must cross event i through `old`. `old` is disjoint from
   the discarded image of the cap ball, so the path must have left the cap ball. That
   feeds the "left the ball" alternative.
4. Both cases go to `exists_uniform_sum_stageRegularizedAction_gt_of_cap_prefix_near_controlled_terminal_region`
   (`CapWindowAction.lean:564`, read `:564–741`). Split on τ, the clock at which the path
   leaves the cap prefix:
   - **τ ≥ w.** The action on the cap prefix is > τΛ with Λ = (max A 0 + F + 1)/w
     (`exists_uniform_lRegularizedAction_lower_bound_on_cap_prefix`, `:215`, read
     `:215–300`). The rest of the path costs ≥ −F = −(2B/3)E³ by the scalar floor. So the
     total is > A.
   - **τ < w.** The path is in the cap chart at clock σ < w, close to the endpoint.
     `exists_uniform_time_sum_stageRegularizedAction_gt_of_point_in_standard_cap_chart`
     (`:32`, statement read `:32–60`, `:118–121`) applies. The cap point is disjoint from
     the controlled compact region around p, because the curvature there is ≤ C while the
     cap's is ~q ≥ q₀. The path must travel distance ≥ ρ in clock-time σ, which costs
     ≳ ρ²/(2σ) (`ST/HistoryAction.lean:1511`, statement read `:1511–1560`).

**The model estimate** is `exists_lRegularizedAction_lower_bound_of_rescaled_standard_metric_approximation`
(`PS/StandardActionComparison.lean:368`, read `:368–447`).
- The weighted action on the cap stretch is ≥ √(T−s)·(unweighted ∫(R + |γ'|²)dt), because
  R ≥ 0 there by comparison with the standard solution (`:40`).
- The unweighted bound is `exists_standard_unweighted_action_lower_bound`
  (`PS/StandardAction.lean:91`, read `:1–130`). Either:
  - the path stays for rescaled time θ, and R ≥ c/(1−t) on the standard solution
    (`exists_standard_scalar_lower_bound`, `PS/StandardTerminalBlowup.lean:61`, read
    `:55–79`, from "the terminal regular region of the standard solution is empty") gives
    ∫R ≥ c·log(1/(1−θ)) > Λ once θ is close to 1 (`:18`, `:35`); or
  - its endpoints are r apart in the standard-cap metric with r = √(C(Λ+1)), so the energy
    is ≥ r²/(Cτ) > Λ (`:50`).

This is the standard argument (Perelman II Lemma 5.3; Morgan–Tian Prop. 16.x): a path that
is barely admissible through a surgery cap has large L.

**Named predicates on this path.** None were taken as hypotheses. Every threshold is an
existential constant. The inputs "C¹ competitors, scalar floor −B, derivative bound
|∂_tR| ≤ C·R², records, HI pinching" are all discharged in the callers read.

**Not read (analytic frontier under A5).**
- `exists_uniform_prepared_cap_evolution` body (and `WindowCommonFlow`, `WindowDiscarding`,
  `FirstCapDiscarding`, `PreparedCapCommonFlow`).
- `exists_regularizedCost_minimizer_of_ne_top`.
- The per-stage and cross-event propagation lemmas in `MinimumPropagation.lean`.
- `regularizedCost_le_of_initial_tail_replacement`.
- `exists_initial_small_ball_volume_lower_bound`.
- `regularCrossing_or_cap_of_admissible_node`.
- `CapWindowAction.lean:32` body (disjointness from the controlled region).

---

## 2. A4: the collapse map for the width jump

**Route entry.** `GeometricCutoffRecord.rfs_child_comparison` (`ST/ChildComparison.lean:41`,
read fully).
- Hypothesis: simple connectivity of the parent components, discharged through ancestry
  (walk 2 §1.3).
- It chooses a `ComparisonSupport` per child c (`rfs_comparison_support`, `Comparison.lean:277`,
  located, not read) and returns f_c = `rfs_whole_parent_map`.
- Result: degree-one maps with d_out(f x, f y) ≤ ℓ(s)·d_{g(s)}(x, y) for s ∈ (s₀, t_i), where
  ℓ ≥ 1 and ℓ(s) → 1.

### 2.1 How the map is built (`ST/ComparisonDefs.lean:40`, structure read `:40–71`)

The support is: the child core (identity to the child) ∪ one collar per child boundary
sphere b. Each collar is the discarded-side piece of the cut neck, in neck coordinates
(θ, z) with z ∈ [level_b, 0] and −δ⁻¹ < level_b < tipCoordinate < 0.

On a collar, the map is `localCollapse` = inclusion ∘ `witness.collapse`. Its fields
(`ST/StaticCap.lean:306–322`, read `:290–322`):
- identity (retained) for z ≥ 0;
- constant = tip for z ≤ tipCoordinate;
- in between, (θ, z) ↦ capChart(ρ(z)·θ), where the profile ρ is monotone with ρ' ∈ [0,1],
  ρ(tip) = 0 and ρ(0) = L_cap.

Everything outside the support maps to the tips and is locally constant
(`rfs_collapse_degree`, `ChildComparison.lean:22–38`).

### 2.2 Why lengths do not grow by more than ℓ(s)

There are three inequalities.

**(a) Core and neck, against the terminal limit metric g_∞, with factor exactly 1.**

*Core* (`exists_nhds_terminal_edist_le_of_core_interior`, `ST/ChildTerminalDistance.lean:423`,
read `:389–475`). Locally, the retained core lifts smoothly through `old`. The output
metric there is the terminal metric (`terminal_lift_inner_eq`, not read), so the lift is an
isometric immersion (`terminal_lift_edist_le`, `:389`).

*Neck* (`:481`, read `:481–517`). This uses `StaticCapWitness.exists_mem_nhds_collapse_riemannianEDistOf_le`
(`ST/StaticCapDistance.lean:19`, read fully), which localizes the field `collapse_length`.
That field is **proved**, not assumed:
- `canonicalStaticInsertionWitness` (`SC/StaticWitness.lean:189–245`, read `:120–300`)
  discharges it via `positiveSideQuotientCollapseMap_eVariationOn_le`
  (`SC/QuotientCollapse.lean:212`, read `:150–300`), then
  `positiveSideCollapseMap_eVariationOn_le` (`SC/NormalizedCollapse.lean:137`, read
  `:20–222`), then **`collapseMap_eVariationOn_le_of_cylinder_lower`**
  (`SC/CollapseDomination.lean:122`), whose pointwise core is
  `collapseMap_inner_le_of_cylinder_lower` (`:96`, read `:1–135`).
- The pointwise core, case by case:
  - below the tip, the derivative is 0;
  - on the deep cap (z ≤ −2A), `insertedMetric` is **η·(standard cap metric)**
    (`SC/InsertionMetric.lean:260–300`: `insertionInnerMetric = scaleMetric η metric`), and
    `radial_metric_bound` (`CollapseDomination.lean:27`) gives
    cap(ρθ)[dρ·v₂ θ + ρ dθ] ≤ v₂² + |v₁|² = round cylinder, using s = ρ' ∈ [0,1] and
    warping ≤ √2;
  - on the collar, `insertedMetric_inner_le_of_cylinder_lower` (located, not read) applies.
- The pointwise core bounds the pushed-forward vector by η·cylinder ≤ neck metric.
- `η = 1 − √δ` comes from **`controlledMetric_cylinder_lower`** (`RF/../Neck/InsertionInput.lean:103`,
  i.e. `DifferentialGeometry/Geometry/Neck/InsertionInput.lean:103`, read `:95–122`): a δ-neck
  satisfies (1 − √δ)·cylinder ≤ g_neck.

So the Lean **scales the inserted cap down by 1 − √δ**, which makes the collapse exactly
1-Lipschitz against the δ-close neck metric (escalation E3).

**(b) Terminal metric against g(s), with factor ℓ(s).**
`exists_compact_comparison_support_quad_modulus` (located, not read) gives
g_∞ ≤ ℓ(s)²·g(s) on a compact K ⊃ support inside Ω, with ℓ(s) → 1. It is used in
`local_length_comparison_of_local_terminal_edist_comparison` (`ST/ChildLengthComparison.lean:19`,
read fully) through `riemannianCurveVariation_le_of_quad_on`. This rests on the terminal
limit metric converging smoothly on compacts of Ω (§4.2).

**(c) Local to global.** `rfs_child_comparison_metric_of_local_length_comparison`
(`ST/ChildComparisonMetric.lean:60`, read `:36–124`):
- inside the support, the local bound (a)·(b) holds;
- outside, the map is locally constant, so curve length is 0;
- `rfs_local_to_global_length_of_ne_top` (located, not read) turns local curve-length
  domination into a distance bound.

The level sphere lies beyond the tip coordinate (`level_below_tip`), so a neighbourhood of
it maps to the tip. The seam between "support" and "locally constant" therefore carries no
length.

### 2.3 Why degree one transfers the sweepout class

`rfs_canonical_width_lipschitz` (`RF/Extinction/Width/CanonicalClass.lean:85`, read `:1–110`)
gives W_N ≤ L²·W_M:
- `rfs_width_lipschitz` (`Width/Comparison.lean:258`, located, not read): an L-Lipschitz
  map sends loops to loops and filling disks to disks with area ×L²;
- `positiveFreeContractibleClass_natural` (`ST/FreeLoopClass.lean:1786`, read `:1735–1800`):
  push-forward of the positive class by a degree-one map is the positive class. The proof
  goes through `positiveFreeLoopClass_natural`, `freeLoopAdjunction_natural` and
  `rfs_degree_class_transport` (located, not read); the last is the Hurewicz-type statement
  that the degree acts on π₃ ≅ H₃ ≅ ℤ for the 2-connected M.

`orientedDegree` (`ST/Homology.lean:119`, read `:110–135`) is the unique d with
f_*[M] = d·[N], via `fundamentalClass_generator`. It is not a junk definition, provided
`fundamentalClass_generator` holds (located, not read).

The degree-one fact itself is `rfs_whole_parent_map_fundamentalClass`
(`ST/CollapseFundamentalClass.lean:275`, located, not read): a local diffeomorphism that
preserves orientation on the child core, and is locally constant elsewhere.

**Direction** (walk 2 A4 asked for it). The map goes from the parent at time s < t_i to the
child's output metric. With ℓ(s) → 1 this gives W_child(t_i) ≤ ℓ(s)²·W_parent(s), and hence
the `incoming_jump` hypothesis W(e) ≤ liminf_{s↑e} W(s) (`RF/Extinction/Families/ScalarComparison.lean:21–22`,
read `:13–31`). This matches Morgan–Tian ch. 18 / Perelman III: width does not increase
across surgery.

---

## 3. A3: the `positive` case of small-scale noncollapsing

**`exists_ball_volume_of_spatialCanonicalWitness`** (`CN/SpatialCanonicalWitnessBallVolume.lean:496`,
read `:440–558`) dispatches on the alternative:
- `neck`: `exists_pos_mul_cube_le_spatialNeck_ball_volume_of_curvature_bound`, located, not
  read;
- `cap`: `ball_volume_of_cap`, `:375`, tail read `:440–494`;
- `positive`: `ball_volume_of_positive`, `:90`, read `:90–158`;
- `round`: refuted by `requiresVolume = False`.

**`ball_volume_of_positive`** (`:90`).
- Statement: vol B(x,r) ≥ (27·max(C₁,1)³·max(C₂,1))⁻¹·r³ whenever r⁴|Rm(x)|² ≤ 1.
- Argument:
  1. The domain is the whole component and lies inside B(x, L) with L = 3C₁/√Q
     (`inside_ball`, `radius_upper`). Also r ≤ L.
  2. Sectional ≥ C₂⁻¹Q > 0 gives Ric ≥ 0.
  3. Bishop–Gromov (`riemannianBallOf_volume_ratio_ge_of_ricci_nonneg`, located, not read)
     gives vol B(x,r) ≥ (r/L)³·vol B(x,L) = (r/L)³·vol(component).
  4. vol(component) ≥ C₂⁻¹Q^{-3/2} is the **witness field `volume`**
     (`CN/SpatialCanonicalWitness.lean:106–128`, field at `:123`, read `:1–160`).
- **Simple connectivity is not used, and does not need to be.** The `positive` alternative
  carries `PositiveComponent U` (`CN/FiniteHornGeometry.lean:212`, read `:200–250`), which
  is an inductive with two constructors:
  - U ≅ S³ (`sphere`);
  - U ≅ a manifold with a `ProjectivePresentation` (`projective`, i.e. RP³).

  So nearly round S³/Γ with large |Γ| cannot be a `positive` witness; they are `round`.
  This matches Morgan–Tian's C-component (compact, S³ or RP³, positive sectional curvature)
  and closes walk 2's A3 residual.

**Where the `volume` field comes from.**
- `CN/CompactPositiveCanonical.lean:27` (read `:1–160`) builds a positive witness on a
  single compact positive-curvature solution. It **chooses C per manifold**, with
  C > max(Q/m, B/Q, …, (V·Q^{3/2})⁻¹, Q/sec), so `volume` holds by that choice (`:127–129`).
- `CN/CompactAncientPositiveWitness.lean:26` (read `:20–64`) applies this to a compact
  κ-solution.
- `CN/WindowedPositiveCanonical.lean:29` (read `:29–215`) transports a model witness K₀ with
  given (C₁, C₂) to the flow near the model, discharging `volume` by
  `volume_lower_bound_on_canonical_domain_of_le_half` (located, not read).
- The uniformity of C₂ over the space of κ-solutions (the canonical-neighbourhood theorem
  for κ-solutions) was not traced. See escalation E1.

---

## 4. A8

### 4.1 `rmUnbounded_of_maximal` (`RF/Extension/Maximal/Time.lean:262`, read `:35–300`)

- **Statement.** On compact M, a solution on [α, ω) that does not extend past ω
  (`IsMaximalAtEndpoint` = ¬`ExtendsPastEndpoint`, `:45–63`) has sup |Rm|² = ∞ on [α, ω)
  (`Rm04NormSqUnboundedAt`, `:108`).
- **Literature.** Hamilton (1982/1995); Chow–Knopf Thm 6.x.
- **Argument.** By contradiction through `extends_of_rmBounded` (`:144`, read `:144–260`):
  1. Bounded Rm gives bounded Ric (`ric_quad_le_of_solution`).
  2. That gives uniform metric equivalence and covariant-derivative bounds of the metric
     (`exists_metric_equivalence_and_covariant_derivative_bounds_of_solution`, located, not
     read; this is the Shi-type input).
  3. `ricci_flow_interior_restart` (located, not read) gives a restart at t* < ω with
     existence time TT reaching past ω.
  4. The restart agrees with the original on [t*, ω) by `ricci_flow_forward_unique`
     (located, not read).
  5. The glued extension is a solution (`extend_construction_of_restart`).
- **Use on the route.** `IncomingSlab.singularEndpoint_of_maximal`
  (`ST/MaximalSlab.lean:49`, read `:40–70`) turns unboundedness into `SingularEndpoint`
  (`EventData.lean:246`, read), using the curvature bound on each closed prefix.
- No named hypotheses. Discrepancy: none.

### 4.2 The terminal limit metric (`ST/TerminalMetricExistence.lean:84`, read fully, 117 lines)

- **Ω** = `terminalRegularRegion` (`ST/EventData.lean:214`, read `:195–250`): points with an
  open neighbourhood U and a time a' < s such that |Rm| ≤ K on U × [a', s).
- **Argument.**
  1. Pointwise Cauchy: `metric_sequence_inner_cauchy`, `ST/TerminalMetricCauchy.lean:66`,
     located, not read.
  2. A smooth positive pre-limit g_∞ along τ_n ↑ s (`exists_smooth_positive_metric_prelimit`,
     `TerminalMetricPrelimit.lean:69`, located, not read).
  3. On each compact K, a C^p-convergent subsequence
     (`exists_metric_subsequence_tendsto_on_compact_of_eventual_pointwise_lower`, i.e.
     Arzelà–Ascoli, located, not read), identified with g_∞ by `metricLimit_uniq`.
  4. Upgrade from the subsequence to all t ↑ s by a **time-Lipschitz bound on C^q
     differences** (`exists_metric_time_lipschitz_on_terminalRegularOpen`,
     `TerminalMetricCauchy.lean:27`, read `:1–66`, and then
     `ST/TerminalMetricTimeLipschitz.lean:19,76`, read `:15–120`).
- The Lipschitz bound comes from `exists_terminalRegular_fixed_reference_metric_jets`
  (`ST/TerminalMetricJetBounds.lean`, read the statement and first 50 lines). That in turn
  rests on `exists_curvature_derivative_bounds_of_mem_terminalRegularRegion`
  (`ST/TerminalRegularCurvatureDerivatives.lean`, read the statement and first 45 lines):
  **local Shi estimates**, `shiLocalUniformBound n m (K₁(s−t₁)) R · K₁/√(c−t₁)^m` on a ball
  of g(t₁)-radius r/2 inside the bounded-curvature neighbourhood.
- Discrepancy: none as mathematics. Ω is defined by bounded **|Rm|**, where Perelman and
  Morgan–Tian use bounded **R** (escalation E4).

---

## 5. Walk 2 §6 items above A3/A8 that were not listed

**§6.3, strong (backward) neck and δ_old** (`RF/Surgery/Contract/PreparedHistoryCutoff.lean:156`,
private, read `:156–240`).
- It delegates to `exists_threshold_uniform_selected_neck_append_backward`
  (`ST/ProspectiveNeckSurvivalVariableThreshold.lean:1708`, read `:1708–1790`; siblings at
  `:1470`, `:1587`, statements read).
- Content: a normalized neck of precision η ≤ η* and scale ≥ Λ·max(q₀,1) in the terminal
  metric of the last event is an `IncomingBackwardNeck` with radius √(scale⁻¹). That means
  it persists backward in time, i.e. it is **strong**.
- Hypotheses, all supplied by the caller: records, HI pinching a₀, the scalar floor, the
  derivative bound |∂_tR| ≤ C_time·R² above q₀, admissible pinching φ, and the cap scalar
  ≥ scale/2.
- Proof shape (from the private lemma names; the 1865-line body was not read): a
  contradiction sequence with η_i → 0, m_i → ∞, scale_i → ∞. Backward traces of the
  selected necks are extended (`uniform_backward_trace_window_of_threshold_ratio`) and
  shown to converge to the cylinder (`prospective_neck_convergence_*`,
  `selected_neck_traces_cylindrical_of_threshold_ratio`).
- Literature: Morgan–Tian Prop. 13.x / Perelman II §4: the surgery neck is a strong δ-neck.
- Status: **frontier, body not read.**

**§6.4, discarded components with a cut sphere**
(`ST/DiscardedSpatialClassification.lean:233`, read `:233–310`).
- At a late time t < t_i, `SphericalCapping.exists_cut_neck_standard_or_stopped_tolerance`
  (located, not read) follows the cut neck into the discarded side. Two outcomes:
  - **(std)** the realization of the discarded component is standard;
  - **(stop)** a cylinder stops at a point whose parameter lies in the discarded core.
    The spatially canonical witness there (`exists_late_spatiallyCanonical_on_discarded_core`,
    `:25`) must be a cap on the cutting side
    (`exists_late_capCore_cutting_side_of_stopped_cylinder_of_spatialWitness`, `:136`), and
    then `isPoincareStandard_discardedComponent_of_capCore_cutting_side` (located, not read)
    applies.
- `isPoincareStandard` (`DifferentialGeometry/Topology/ThreeManifold/PoincareStandard.lean:20`,
  read `:1–45`) is a finite connected sum of standard factors (the empty list is S³).
  `isStandardFactor` (`StandardFactors.lean:594`, read) is a spherical space form or
  S²×S¹. So the definition is not vacuous. The ε bound is ≤ min(η, 1/8646).
- Literature: Perelman II §4 / Morgan–Tian: discarded components are covered by canonical
  neighbourhoods. No simple connectivity is used.

**§6.8, `final_empty_of_uniform_records`** (`RF/Extinction/Families/ObservedComparison.lean:66`,
read `:1–96`).
- Every final component carries an `ObservedComparisonRecord` whose `value` W satisfies
  `ScalarComparisonHypotheses` (`ScalarComparison.lean:13`, read `:13–31`): W ≥ 0,
  continuity off events, `incoming_jump`, and D⁺W ≤ −2π + 3W/(4(t+c)).
- Then horizon ≤ extinctionThreshold (`horizon_le_threshold`, `:41`), which contradicts
  threshold < horizon. So the final stage is empty.
- This is the "surviving component ⇒ negative width" step of walk 2 §1.2, confirmed.

**§6.9, monotonicity integrand** (`ST/HistoryReducedVolumeMonotone.lean:38`, read `:38–100`).
It is the change of variables through the L-exponential on `historyMinDomain`:
- injective (`injOn_historyLExp_of_lt_of_mem_Ico`);
- the image at v₁ lies in `regularMinimizerEndpoints`
  (`image_historyMinDomain_subset_of_le`);
- the minimizer domain shrinks as v grows (`historyMinDomain_subset_of_le`).

This is Perelman I §7 through surgery. The Jacobian comparison itself is at `:100–`, not
read.

**§6.6, §6.7, §6.10.** Not reached: the conformal-collar computation, the ramp
curve-shortening body, and the strong-crossing and deep-horn limits.

---

## 6. Escalations, ranked

None is a found gap. Each is a design difference or a load-bearing body below the frontier.

**E1 (medium, could not confirm).** The small-scale noncollapsing constant depends on the
witness constants (C₁, C₂). In the `positive` and `cap` cases, the volume comes from a
*field* of the canonical witness, not from an argument.
- Lean, the definition: `volume : alternative.requiresVolume → ENNReal.ofReal (C2⁻¹ /
  (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤ riemannianVolumeMeasure …
  domain.carrier` (`CN/SpatialCanonicalWitness.lean:123–125`).
- Lean, the model-level producer picks the constant per model: `obtain ⟨C, hC⟩ :=
  exists_gt (max 1 (max (Q / m) … (max (V * (Q * Real.sqrt Q))⁻¹ (Q / sec))…))`
  (`CN/CompactPositiveCanonical.lean:85–86`).
- Standard side: in Perelman II §1.5 / Morgan–Tian ch. 9, the constant C of a canonical
  neighbourhood is **uniform** (C = C(ε, κ)), by compactness of κ-noncollapsed κ-solutions.
- A per-model constant is correct *if* the uniform theorem is proved by a contradiction
  sequence, where each limit model supplies a finite constant. The route's continuation
  lemmas have that shape (`strongSpatialCrossingContinuation_holds` uses q_can = n+1, walk 2
  §2, priority 5). But the κ-solution canonical-neighbourhood step that fixes (C₁, C₂) was
  **not read** here.
- Check next: trace which theorem fixes C₂ for `CanonicalBefore`, and confirm that the
  `volume` field survives the limit
  (`CanonicalWitness.eventually_volume_lower_bound_of_windowed_models`,
  `CN/WindowedPositiveCanonicalLimit.lean:110`, located, not read).

**E2 (low–medium, definition carries more than the textbook may).** The Lean canonical
neighbourhood includes a volume clause for the neck, cap and positive alternatives. It
excludes the round alternative (`requiresVolume`, `SpatialCanonicalWitness.lean:101–104`:
`| .round _ _ => False | _ => True`).
- Standard side: I could not confirm from memory whether Morgan–Tian's
  (C,ε)-canonical-neighbourhood definition includes a volume lower bound.
- Consequence either way: the inductive canonical-neighbourhood step must re-prove the
  volume clause at every continuation. The model-level producers read (§3) do.
- This is a **stronger hypothesis** that is carried and discharged, not an assumed one. It
  is recorded because a reuser of `SmallScaleNoncollapsingThroughSurgery` inherits it.

**E3 (low, design).** The inserted cap is the standard cap metric **scaled by η = 1 − √δ**
on its deep part, so that the collapse map is exactly distance-nonincreasing against a
δ-neck.
- Lean: `insertionInnerMetric … := (scaleMetric η hη metric).restrictOpen (insertionInner A)`
  (`SC/InsertionMetric.lean:259–261`), with η = `d.controlledMetric_cylinder_lower.1`
  = 1 − √δ (`SC/NormalizedCollapse.lean:27–31`; `Neck/InsertionInput.lean:103–106`).
- Standard side (Perelman II §4.4, Morgan–Tian ch. 13): glue h²·(standard initial metric).
- The difference is O(√δ). It must be absorbed by the witness's ε-closeness to the standard
  metric (`hclose` in `canonicalStaticInsertionWitness`, `SC/StaticWitness.lean:192–199`),
  discharged by `exists_uniform_positiveCoordinate_static_estimates` (located, not read).
  So the standard-solution comparison (§1.5 step 2) is against a √δ-perturbed cap.
- Not a gap if that estimate holds. It is the one place the collapse-map construction and
  the cap-evolution comparison share a hidden constant.

**E4 (low, definition).** Ω is defined by locally bounded |Rm|, not bounded R.
- Lean: `terminalRegularRegion := {x | ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ a' ∈ Ico a s, ∃ K, 0 ≤ K ∧
  ∀ y ∈ U, ∀ t ∈ Ico a' s, G.riemannNorm t y ≤ K}` (`ST/EventData.lean:214–217`).
- Standard side (Perelman II §3, Morgan–Tian ch. 11): Ω = {x : R(x,t) stays bounded as
  t → T}.
- Under Hamilton–Ivey pinching the two agree up to taking a neighbourhood. Any step that
  goes from "R bounded near x" to x ∈ Ω must invoke pinching. None was met on these paths.

**E5 (low, frontier).** Three real analytic inputs under A5 are below the reading frontier:
- existence of L-minimizers through surgery (`exists_regularizedCost_minimizer_of_ne_top`);
- the cap-evolution dichotomy (`exists_uniform_prepared_cap_evolution` body);
- the L̄ − 6τ propagation lemmas (`MinimumPropagation.lean:1424`, `:1553`).

Their statements match the literature as read. Their bodies are the next reading unit for A5.

---

## 7. Named predicates met

**Not discharged on the route: none.** This is consistent with walk 2 A1: the headline
takes no hypotheses.

The predicates below take a named Prop as a hypothesis in the files as read. The first two
are discharged in files that were only located.

| predicate | defined | taken by | discharged at |
|---|---|---|---|
| `SpatialCanonicalWitness.capTubeHasNeckChart ε` | `CN/SpatialCanonicalWitness.lean:130` | `exists_ball_volume_of_spatialCanonicalWitness` (`CN/SpatialCanonicalWitnessBallVolume.lean:496`, `:533`) | not traced this pass (walk 2's `SmallScaleNoncollapsingThroughSurgery.lean:522` is the caller) |
| `LocalLengthComparison Kc` | `ST/ChildComparisonMetric.lean:42` | `rfs_child_comparison_metric_of_local_length_comparison` (`:60`); also `ChildComparisonInputReduction.lean:169,363`, `CollapseDegreeFrontierReduction.lean:243,268`, `ComparisonResidualFrontier.lean:73` (located, not read) | `local_length_comparison` (`ST/ChildLengthComparison.lean:103`) |
| `LocalTerminalEDistComparison Kc` | `ST/ChildComparisonLocalLength.lean:88` | `local_length_comparison_of_local_terminal_edist_comparison` (`ChildLengthComparison.lean:19`) | `local_terminal_edist_comparison` (`ST/ChildTerminalDistance.lean:599`) |
| `LocalTerminalDistanceControl` | `ST/CollapseDegree.lean:55` (located) | `rfs_collapse_degree` | `rfs_whole_parent_map_localTerminalDistanceControl` (`ChildTerminalDistance.lean:588`) |
| `StaticCapWitness.collapse_length` (structure field) | `ST/StaticCap.lean:317` | `StaticCapDistance.lean:19` | `SC/StaticWitness.lean:241–243` ← `CollapseDomination.lean:122` |
| `SpatialCanonicalWitness.volume` (structure field) | `CN/SpatialCanonicalWitness.lean:123` | `ball_volume_of_positive` (`:90`), `ball_volume_of_cap` | `CompactPositiveCanonical.lean:127`, `WindowedPositiveCanonical.lean:184–187`, `WindowedPositiveCanonicalLimit.lean:181,381` (located). See E1 |
| `PositiveComponent U` (data) | `CN/FiniteHornGeometry.lean:212` | the `positive` alternative | supplied by the κ-solution classification (compact non-round κ-solutions are S³ or RP³); not traced |
| `IsMaximalAtEndpoint` | `RF/Extension/Maximal/Time.lean:58` | `rmUnbounded_of_maximal` | a definition (¬extends); supplied by maximal short-time existence (walk 2 `MaximalSlab.lean:97`) |
| `SingularEndpoint` | `ST/EventData.lean:246` | the surgery step | `singularEndpoint_of_maximal` (`ST/MaximalSlab.lean:49`) |
| `TerminalMetricConverges` | `ST/EventData.lean:231` | `TerminalLimitMetric` | `nonempty_terminalLimitMetric` (`ST/TerminalMetricExistence.lean:84`) |
| `ScalarComparisonHypotheses` | `RF/Extinction/Families/ScalarComparison.lean:13` | `ObservedComparisonRecord` | `observedComparisonRecord_of_historyWidth_of_scalarLowerBound` (walk 2, `ObservedWidthDini.lean:375`) |
| `HistoryReducedVolumeInitialLowerBound` | `ST/NoncollapsingThroughSurgeryLeaves.lean:113` | walk 2 `:242` | `InitialRegularBlock.lean:510` |
| inline `hregular`, `hbirthRegular` | `MinimumPropagation.lean:1720–1746` | `exists_spatial_regularizedCost_minimum_lt_three_mul` | inline in `InitialSpatialMinimum.lean:112–144` |

---

## 8. Junk-value observations

None of these is exploited on the route. Each is recorded so that a reuser does not
inherit it.

1. **`regularizedDensity` at v = 0** (`ST/HistoryReducedDensity.lean:330–334`). There
   `-A / (2 * v) = 0` and `Real.log (v ^ 2) = 0`, so the density is the constant
   (4π)^{-3/2} for any competitor. A lower bound stated at v = 0 would be spuriously easy.
   On the route v > 0 everywhere:
   - `ReducedVolumeBoundedBelowBefore` uses v = √t with t ≥ r² > 0;
   - the local upper bound uses v = σr > 0;
   - monotonicity requires 0 < v₁.
2. **`reducedVolume` degenerate branches** (`NoncollapsingThroughSurgeryLeaves.lean:43–51`).
   - The value is `0` when `first > k`.
   - It is also 0 when v² > T: `projIcc` clamps `first` to stage 0, but the competitor set
     requires T − v² ∈ `stageDomain first`, which is empty. So the integral is over ∅.

   Either branch makes an *upper* bound trivially true and a lower bound unsatisfiable. The
   route evaluates lower bounds only at v = √t, where T − v² = 0 ∈ stage 0 exactly, and
   upper bounds at v = σr ≤ r ≤ √t (`radius_sq_le_time`, `ST/HistoryParabolicBall.lean:77–90`).
   Not exploited.
3. **`regularizedCost` is an `sInf` in `WithTop ℝ`** (`AbsoluteContinuity.lean:274–276`).
   `sInf ∅ = ⊤`, which is correct and not junk. A nonempty set unbounded below would give a
   junk `sInf`. Every use read supplies the scalar floor −B (`hscalar`), which bounds the
   action below by −(2B/3)v³. The minimizer-existence lemma takes `hscalar` explicitly
   (`CapWindowActionRegularCrossingRecenter.lean:492–506`). Not exploited.
4. **`orientedDegree`** (`ST/Homology.lean:119–122`) is `Classical.choose` of surjectivity
   onto ⟨[N]⟩. It is well-defined only because `fundamentalClass_generator` makes ℤ → H₃
   bijective. If `fundamentalClass` were junk (0), "degree one" would be unsatisfiable, not
   trivial, so the direction is safe.
5. **`canonicalWidth`** is `sInf` on ℝ (`CanonicalClass.lean:19`). The set is nonempty
   (`canonical_regularRepresentative_nonempty`, `:30`), and a junk value of 0 would make the
   Dini hypothesis D⁺W ≤ −2π + … unsatisfiable, not easy. Safe (as walk 2 A1 found).
6. **`SingularEndpoint`, `Rm04NormSqUnboundedAt`, `terminalRegularRegion`** quantify over
   `Real.sqrt` of `normSq0S`, which is ≥ 0. No negative argument is possible.
7. Scalar denominators on these paths all have explicit positivity in scope:
   - `C2⁻¹/(Q√Q)`: `Q_pos` is a witness field;
   - `3/a₀`: `ha₀`;
   - `ρ_v/√B`: `hB`;
   - `Real.log ((1−θ)⁻¹)`: θ ∈ [0,1);
   - `(Λ+1)/τ`: τ > 0;
   - `c/(1−t)`: t < 1;
   - `K₁/√(c−t₁)^m`: c > t₁.

   The one scanner hit on these paths (`HistoryAction.lean:1511`, `r²/(2w)`) has
   `(hw : 0 < w)`.

---

## 9. Computation not read (for the independent-computation rung)

1. `CN/SpatialCanonicalWitnessBallVolume.lean`:
   - `cap_constant_le` (`:335`) and the constants 5000, 10000, κ_c =
     e^{−12C₁√C₂}ν·min(1/(4√C₂), 5000)³/(64C₁³);
   - κ_p = 1/(27C₁³C₂) (`:156` `hcoef`, `field_simp; ring`).
2. `ST/InitialRegularBlock.lean:35–95` (`cost_budget_le`, nlinarith) and `:145–196`
   (window-radius algebra).
3. `CN/CompactPositiveCanonical.lean:80–90` (`:85`): the choice of C as a maximum of eight ratios.
4. `PS/StandardAction.lean:50–90`: r = √(C(Λ+1)) and `(Lambda+1)/tau > Lambda` (nlinarith).
5. `SC/CollapseDomination.lean:27–45` (`radial_metric_bound`, nlinarith): warping ≤ √2 and
   ρ' ∈ [0,1] give domination by the round cylinder.
6. `Neck/InsertionInput.lean:103–122`: δ-closeness ⇒ (1−√δ)·cylinder ≤ g.
7. `CapWindowAction.lean:564–741`: F = (2B/3)E³, L = (max A 0 + F + 1)/w, and the final
   `linarith`.
8. `shiLocalUniformBound` (value not read); the 18K(s−c) exponent in
   `metric_inner_bounds_on_tail`.
9. `SC/InsertionMetric.lean` collar inequality (`insertedMetric_inner_le_of_cylinder_lower`,
   not read): the conformal collar must also be dominated by the cylinder lower bound. This
   is the one geometric inequality of A4 not seen.

---

## 10. Remaining frontier (priority order)

1. **E1**: the theorem that fixes (C₁, C₂) for `CanonicalBefore` (the κ-solution
   canonical-neighbourhood step), and
   `CanonicalWitness.eventually_volume_lower_bound_of_windowed_models`
   (`CN/WindowedPositiveCanonicalLimit.lean:110`).
2. `SC/WindowEvolution.lean:17` body: the cap-evolution dichotomy (standard-solution
   comparison or discard).
3. `exists_regularizedCost_minimizer_of_ne_top` (L-minimizers through surgery) and
   `MinimumPropagation.lean:1424,1553`.
4. `SC/InsertionMetric.lean` → `insertedMetric_inner_le_of_cylinder_lower` (collar
   domination, §9.9) and `exists_uniform_positiveCoordinate_static_estimates` (E3's
   absorption of √δ).
5. `ST/ProspectiveNeckSurvivalVariableThreshold.lean` (strong-neck limit, 1865 lines).
6. `rfs_degree_class_transport`, `rfs_whole_parent_map_fundamentalClass`,
   `rfs_width_lipschitz`.
7. `extends_of_rmBounded`'s inputs: `exists_metric_equivalence_and_covariant_derivative_bounds_of_solution`,
   `ricci_flow_interior_restart`, `ricci_flow_forward_unique`; and `shiLocalUniformBound`.
8. `SphericalCapping.exists_cut_neck_standard_or_stopped_tolerance`,
   `isPoincareStandard_discardedComponent_of_capCore_cutting_side`.
9. Walk 2 §6.6, §6.7, §6.10, §6.12 (not reached).
10. Standing: `#print axioms` on the headline and an independent checker (walk 2 A1). The
    claim "no undischarged predicate on the route" still depends on them.
