# Route walk 5: where the canonical-neighbourhood constants are fixed (closes walk 4 E1, E3)

Artifact `/home/user/differential-geometry` @ `7a48598d35109aa99d1cc678e2724c213cdf4ff3`
(checked with `git log -1`), read-only. Nothing was compiled or committed. No `#print axioms`
and no independent checker was run. Auditor model family: Claude (one family; PLAYBOOK §4.16).

This walk answers walk 4's escalation E1: is the canonical-neighbourhood volume constant C₂
uniform where the standard argument needs it to be, or is it chosen per manifold? It also
closes walk 4's E3 (the √δ from the η-scaled cap).

**Path abbreviations** (same as walk 4, plus `KS/`):
- `RF/` = `DifferentialGeometry/Geometry/Flow/RicciFlow/`
- `CN/` = `RF/Perelman/CanonicalNeighborhood/`
- `KS/` = `RF/Perelman/KappaSolutions/`
- `ST/` = `RF/Surgery/Topology/`
- `SC/` = `RF/Surgery/StandardCap/`

**Citations.** Every `file:line` below was read in this pass. Most were read with `sed -n`.
The ones marked "(grep -A)" were read as `grep -n … -A k` context windows, which show the same
lines. "Located" means the declaration was found by grep and its body was not opened.

---

## 0. Answer

**E1 is closed. No quantifier-order defect.** Two things fix the witness constants (C₁, C₂)
before the flow, the history, κ and δ:
- one uniform theorem about ancient κ-solutions;
- an ordering of the surgery-era predicates that chooses C before κ, then the curvature
  threshold q_can, then δ.

The universal constant is proved by the standard contradiction-and-compactness argument:
- take counterexample models with C = n+1;
- move every non-round one to a single universal κ;
- extract a κ-solution limit by fixed-κ compactness;
- the limit supplies a finite C, which is a contradiction.

`CompactPositiveCanonical.lean:85` chooses C per manifold, but its only caller on the route
applies it to the **limit model inside that contradiction**. That is exactly where a
per-model constant is allowed.

| question | answer |
|---|---|
| 1. Order of C in the no-surgery theorem (`CN/HighCurvatureModelBounds.lean:539`) | ∃ε_can ∀ε≤ε_can **∃C₁C₂ ∀M ∀T ∀S** ∃Q_can. C is uniform over manifolds and flows. Only Q_can is per flow. |
| 1. Is the proof the standard argument? | Yes, at two levels. (a) Model approximation: a contradiction sequence, rescaled, with a limit that is an ancient κ-solution (`abstract_model_theorem` → `no_selected_countersequence`). (b) Constant: a contradiction sequence of models with C = n+1, fixed-κ compactness, and the limit's constant (`exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts`). |
| 2. How C reaches the surgery witness | Surgery uses the same universal theorem (`exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts`), through three continuation leaves: deep, cap-window and crossing. Each leaf has the form ∃C₀ before ∀κ, and before the ∃δ_max. The spatial constants (C₁ˢ, C₂ˢ) = max(C, C_w, C_x) are also fixed before κ. |
| 2. Where the per-manifold constant sits | `exists_positive_canonicalWitness_of_compact` (`CompactPositiveCanonical.lean:29`, C at `:85`). Its one route caller is `WindowedPositiveBufferedLimit.lean:122`, applied to the compact positive **limit** L. It is not a producer for any real flow. |
| 3. A wrong-order dependence? | None found. The surgery-era predicates are stated per (P₀, g₀, B, ε), which is weaker than the standard ∀-manifold uniformity. Nothing downstream needs more: the Poincaré endgame is applied to one M at a time. |
| E3 | Closed. The η-scaled cap is within C·(δ + √δ) in C^m of the standard cap metric on each D-ball. The √δ is exactly \|η − 1\| and is passed in explicitly (`SC/NormalizedInsertionNorm.lean:15–46`). |

---

## 1. The no-surgery canonical-neighbourhood theorem

### 1.1 Statement (`CN/HighCurvatureModelBounds.lean:539–565`)

```
theorem smooth_canonical_neighborhood :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ (M : Type u) [...] [CompactSpace M] [ConnectedSpace M] [...] (T : ℝ) (hT : 0 < T)
          (S : SolutionOn ... (RealTimeInterval.closedOpen 0 T hT))
          (_hS : IsSolutionOn S) (_o : TangentOrientationSection M),
          ∃ Qcan : ℝ, 0 < Qcan ∧ ∀ x t, t ∈ Set.Ico 0 T → Qcan ≤ S.scalar t x →
            Nonempty (CanonicalWitness S eps C1 C2 x t)
```

In words: for every small ε there are constants C₁, C₂ such that every Ricci flow on every
closed connected 3-manifold, over any finite interval, has a curvature threshold Q_can above
which every point has an (ε, C₁, C₂) canonical witness. The theorem has no κ hypothesis,
because κ is derived per flow inside the proof.

Only Q_can depends on the flow. In Perelman and in Morgan–Tian the threshold r also depends on
the initial data (through κ and the curvature bound), so the order matches.

### 1.2 Proof structure (`:539–565`, `:507–537`, `:262–330`)

The proof has four steps.
1. `buffered_canonical_pullback` (`:507`) gives ε_can = 1/44, and for each ε it fixes
   **C₁ = max C_n C_r₁ and C₂ = max C_n C_r₂ before ∀κ** (`:512–513`). Here C_n comes from
   `exists_universal_nonround_windowed_bufferedCanonical` (non-round models) and C_r from
   `exists_windowedModelWitness_canonicalWitness_of_round_model` (`CN/WindowedRoundCanonical.lean:145`:
   ∃C₁C₂ ∀ε ∃δ₀ ∀ M, flows, witnesses, δ, κ).
2. `closed_flow_models` (`:262`) is applied **per flow**. It takes κ from
   `spatial_no_local_collapsing`, a pinching function Φ from the initial curvature lower bound,
   and r from `abstract_model_theorem`. It sets Q₀ = max(M_sc, A/r²) + 1, where M_sc bounds
   the curvature on [0, T/2]. The result is that every point with R ≥ Q₀ carries an
   `OrientedWitness`: it is δ-close, on a backward parabolic window, to a normalized ancient
   κ-solution.
3. `htransfer κ` (`:554`) gives δ, and `hm δ` gives Q.
4. The model witness is pulled back to a `CanonicalWitness S ε C₁ C₂ x t`.

### 1.3 Model approximation is the standard contradiction (Perelman I §12.1; Morgan–Tian ch. 10)

**`abstract_model_theorem`** (`:246–260`)
- Statement: there is r with `ModelRadiusWorksClosed ε κ σ Φ r`.
- That predicate (`CN/SelectedCountersequenceAdapter.lean:53–58`) quantifies over **every**
  connected manifold M, every T ≥ 1, and every solution satisfying
  `ClosedModelHypotheses S κ σ Φ`. At every (x, t) with t ∈ [1, T] and R ≥ r⁻², the solution
  has an `OrientedWitness`. So r is uniform over the hypothesis class.
- Proof: `by_contra`, then `selected_countersequence_of_radius_failure` (`:92`), then
  `no_selected_countersequence` (`:227–244`).

**`no_selected_countersequence`** runs the chain below. Each lemma was located, not read.
1. `bounded_curvature_at_distance`: Perelman's curvature bounded at bounded distance.
2. `terminal_limit_global_bound`.
3. `first_backward_slab`.
4. `ancient_extension`.
5. `witness_of_ancient_extension` (`:99–225`, read). Once the rescaled flows converge to an
   ancient κ-solution on a backward window of depth ≥ modelDepth ε, the terms eventually have
   `OrientedWitness`. This contradicts `X.bad`.

**The rescaled sequence.** `NormalizedSequence` (`CN/BlowupConvergence.lean:42–64`) records:
- `scale → ∞` and `depth → ∞`;
- R(base) = 1;
- noncollapsing below scale √scale·σ;
- pinching `rescalePinchingFunction (scale i) Φ`;
- `higher_good` (points with R ≥ 2 in the window already have witnesses). This is Perelman's
  point-picking.

It is the textbook argument.

### 1.4 The constant is the standard compactness argument (Perelman I §11.8–11.9, §12; Morgan–Tian ch. 9)

**`exists_universal_nonround_windowed_buffer_constant_with_cap_neck_charts`**
(`CN/UniformNonroundWindowedBuffer.lean:32–88`, read fully).

Statement:

```
∃ C delta0, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
  ∀ (kappa) (D) (P : PointedFlowData ...) (delta t) (W : WindowedModelWitness delta kappa P.S ...),
    delta ≤ delta0 → (window regular) → ¬ IsShrinkingSphericalSpaceFormFlow W.model → (orientation) →
    ∃ B : BufferedCanonical P.S alpha C H P.basepoint t, B.witness.capTubeHasNeckChart alpha
```

C comes before κ, the flow, the point and the witness.

Proof:
1. `by_contra`. For each n, choose (κ_n, P_n, δ_n ≤ 1/(n+2), W_n) that fails with constant
   n+1 (`:44–60`).
2. Replace each κ_n by `universalKappaConstant`, using
   `ancientKappaThree_universal_kappa_gap … |>.resolve_left (hnotround i)` (`:58–59`;
   `KS/UniversalKappaGap.lean:83–97`). A non-round 3-dimensional ancient κ-solution is a
   κ₀-solution for one universal κ₀ (Perelman I 11.9). This is why C does not depend on κ.
3. Fixed-κ compactness, `exists_ancientKappa_fixed_kappa_compactness` (`:66–68`;
   `KS/AncientKappaFixedCompactness.lean:48–73`, statement read), gives a subsequence φ and
   an ancient κ₀-solution limit L with R(base) = 1.
4. `exists_eventually_buffered_with_cap_neck_charts_of_nonround_oriented_windowed_models`
   (`CN/WindowedNonroundBufferedLimit.lean:30–67`) gives a finite C for L such that the
   terms are eventually buffered-canonical with C. There are two cases:
   - compact L: `nonempty_positiveComponent_of_compact_nonround_pointed_limit` (located), then
     `exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_compact_positive_limit`
     (§3);
   - noncompact L: `…_of_noncompact_oriented_limit` (located, not read).
5. Eventually C < φ(i) + 1 (`:79`). Enlarging the constants then contradicts the failure at
   index φ(i) (`:81–88`).

**Relation to README `:566`.** `fixed_kappa_compactness` (`CN/HighCurvatureModelBounds.lean:566–577`)
wraps a sibling, `exists_ancientKappa_fixed_kappa_compactness_captured`
(`KS/AncientKappaSourceCapture.lean:84`, statement read). The constant argument calls the
non-captured version. Both have the same shape: fixed κ, R(base) = 1, a subsequence and an
ancient κ-solution limit. How the two relate was not traced.

---

## 2. From the universal constant to the surgery-era witness

### 2.1 The quantifier order of the composed statement

**`CanonicalNeighborhoodsThroughSurgeryStrongAt P₀ g₀ B ε Λ`** (`ST/CanonicalNeighborhoodsThroughSurgeryStrong.lean:24–67`)

```
∃ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap) (mcap) (Ctime Cgrad) (κ a₀), ... ∧
  ∀ p₀ δbound ρbound, ... δbound ≤ δmax ... → ∀ H, ... →
    (... CanonicalBefore ε C1 C2 qcan τmin ...) ∧ (... SpatiallyCanonicalBefore ε C1s C2s qcan ...) ∧ ...
```

In words: for the fixed initial data (P₀, g₀), horizon B and accuracy ε, there are constants
and a δ_max such that every surgery history with δ ≤ δ_max has canonical and spatially
canonical neighbourhoods with those constants, plus noncollapsing. A single ∃ block does not
show what depends on what. The order is fixed by the proof,
`canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` (`:272–345`, read `:272–360`).

**The order of choice** (`:282–295`):
1. (C₁, C₂, τ_min, C_time, C_grad) ← `hcont B ε`
   (`CanonicalNeighborhoodContinuation`, `ST/CanonicalNeighborhoodInduction.lean:286–290`:
   `∀ B ε … ∃ C1 C2 τmin Ctime Cgrad, … ∀ C1s C2s Cs, ∀ κ phi, ∀ qfloor, ∃ qcan δmax …`).
2. (C₁ˢ, C₂ˢ, C_s) ← `hspat B ε C1 C2 τmin Ctime Cgrad`
   (`SpatialCanonicalContinuation`, `ST/SpatialCanonicalContinuation.lean:144–151`:
   `∀ C1 C2 … ∃ C1s C2s Cs, ∀ κ phi, ∃ q₄, ∀ qcan ≥ q₄, ∃ qs δmax …`).
3. κ ← `hnon B ε C1 C2 C1s C2s …`
   (`NoncollapsingThroughSurgery`, `ST/CanonicalNeighborhoodInduction.lean:250–255`:
   `∀ … C1s C2s … ∃ κ, ∀ qcan qs, ∃ δmax …`).
4. q₄ ← `hS κ`; then q_can ← `hF … κ phi q₄`; then q_s ← `hS₄ qcan`; then δ_N ← `hN qcan qs`.
5. δ_max = min(δ_P, δ_F, δ_S, δ_N, (2Λ)⁻¹).

This is Perelman's order (II §4–5; Morgan–Tian ch. 17):

  ε → C(ε) → κ(ε, C) → r (= q_can^{-1/2}) → δ.

There is no cycle. κ depends on (C₁ˢ, C₂ˢ); those depend only on (C₁, C₂, C_grad) and on
uniform constants; and none of them depends on κ.

**The time induction** (`:314–345`) extends `CanonicalBefore`, `SpatiallyCanonicalBefore` and
the rest across each slab. It uses `canonicalBefore_end_of_continuation_spatial`
(`ST/SpatialCanonicalContinuation.lean:65`, read the sSup argument at `:100–140`), an
open–closed argument on the time at which the property first fails. All constants stay fixed
during the induction.

### 2.2 Where (C₁, C₂) come from: the three continuation leaves

`canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing`
(`ST/CanonicalNeighborhoodContinuationLeaves.lean:284–330`) sets C₁ = max(C₁d, C₁w, C₁x) and
likewise C₂. The three leaf definitions (`:146`, `:188`, `:232`, read `:136–283`) share one
shape:

  `∀ B ε, ∃ C1₀ C2₀ τ₀ Ctime₀ Cgrad₀, ∀ C1 C2 … ≥ those, ∀ κ phi, …, ∃ q₀ …, ∀ qcan ≥ q₀, ∃ δmax …`

So C is monotone ("any larger C works"), and it is chosen before κ and δ.

| leaf | producer (read) | source of C₀ | uniform over |
|---|---|---|---|
| deep, R·(t − t_k) ≥ θ | `deepContinuation` (`ST/DeepContinuation.lean:213–285`) | `exists_uniform_canonical_threshold_of_parabolically_noncollapsed` (`ST/UniformKappaCanonicalThreshold.lean:55–78`) | every `OrientedThreeStage` P and every slab G. Statement: ∃C ∀κ ρ Φ ∃Q₀ θ ∀P G x t, (pinched and κ-noncollapsed on the backward window) → CanonicalWitness with C. It uses the same `abstract_model_theorem` and the same universal buffered constant as §1. |
| cap window, young point near a recent cap | `capWindowContinuation` → `exists_capWindow_canonicalBoundsOn` (`ST/CapWindowContinuationLeaf.lean:205–240`) → `exists_capWindowPoint_bounds` (`:29–74`, grep -A) | C_ε from `exists_canonicalWitness_of_orientedWitness` (`ST/CapWindowContinuationAssembly.lean:34–48`, grep -A) = `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts` | all P, all slabs. The standard solution supplies an `OrientedWitness` at age ≥ τ_Q (`exists_uniform_orientedWitness_of_standard_close_endpoint`, located). |
| crossing, young point outside a cap window | `crossingContinuation_holds` (`ST/CrossingContinuationLeaf.lean:132–200`, read the head) | C from `exists_eventually_canonical_clauses_of_isTracedRegion` (`ST/CrossingAncientLimit.lean:34–100`) ← `exists_canonicalWitness_of_ancient_pointed_flow_limit` (`ST/AncientLimitCanonicalWitness.lean:117–159`) ← `exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness` (`CN/WindowedModelCanonicalWitness.lean:22–36`, grep -A) | chosen before the sequence of histories. The proof is **Perelman II Prop. 5.1 / Morgan–Tian ch. 17 by contradiction**: q_can = n+1 and δ ≤ 1/(n+1) vary, C is fixed (`:156–170`), and the limit is an ancient κ-solution for **every κ** (`:47`, "∀ {κ ρ}"). |

The last row is the persistence theorem E1 asked for: canonical neighbourhoods persist through
surgery, with the same constants, for small δ.

`exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts` (`CN/WindowedBufferedCanonical.lean:20–53`)
is `max(C_n, C_r) + 1`, where C_n is the universal non-round constant of §1.4 and C_r the
round-model constant (`CN/WindowedRoundCanonical.lean:212–222`, ∃C δ₀ ∀ models).

### 2.3 The spatial witness constants (C₁ˢ, C₂ˢ) that small-scale noncollapsing consumes

`spatialCanonicalContinuation_of_spatialCrossing` (`ST/SpatialCanonicalContinuationCases.lean:41–118`)
sets:
- C₁ˢ = max(C₁, C_w, C_x);
- C₂ˢ = max(C₂, max(C_w, C_grad), C_x);
- C_s = 1.

All three are fixed **before `intro κ`** (`:59–61`). The inputs come from three places.

| input | source | statement |
|---|---|---|
| C_x | `SpatialCrossingContinuation` (`ST/SpatialCrossingContinuation.lean:16–27`, grep -A) | ∀ε ∃C_x before ∀B, C, κ, … |
| C_x (proof) | `spatialCrossingContinuation_holds` (`ST/SpatialCrossingContinuationLeaf.lean:193–218`) | C from `exists_eventually_spatialCanonicalWitness_of_isTracedRegion` (`ST/CrossingAncientLimitSpatial.lean:225`, statement head read), then the same contradiction over q_can = n+1 |
| C_w | `exists_capWindowPoint_spatialCanonicalWitness` (`ST/CapWindowSpatialCanonicalWitness.lean:31–60`) | from `exists_window_spatialCanonicalWitness_of_standard_close` (located): standard-solution windows, uniform |

The three cases of the spatial witness:
- **Old points** get the time-t slice of the `CanonicalWitness` (C₁, C₂):
  `W.toSpatial.enlargeConstants` (`:32–39`).
- **`toSpatial`** carries the `volume` field with the same C₂
  (`CN/SpatialCanonicalWitnessProjection.lean:107`, grep).
- **`enlargeConstants`** (`CN/SpatialCanonicalWitness.lean:162–194`) weakens the volume clause
  correctly: C₂′⁻¹ ≤ C₂⁻¹.

**The consumer.** `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace`
(`ST/SmallScaleNoncollapsingThroughSurgery.lean:522–600`):
1. It takes C₁ˢ, C₂ˢ as universally quantified inputs.
2. It obtains κ_W from `exists_ball_volume_of_spatialCanonicalWitness_of_simplyConnected ε C1s C2s`
   (`CN/SpatialCanonicalWitnessBallVolume.lean:533–558`), which dispatches to `:496–531`.
3. The positive branch uses `W.volume` (`:524–526`) with κ_p = 1/(27·C₁³·C₂).
4. It returns κ = c_T · min(c_BG·κ₁, κ_W, κ₀) **before** `intro qcan qs`.

So the κ that noncollapsing produces depends only on constants fixed before it. That is the
order the composition of §2.1 needs.

---

## 3. Where the per-manifold constant sits

`exists_positive_canonicalWitness_of_compact` (`CN/CompactPositiveCanonical.lean:29–35`; the
choice at `:85–90`):
- It takes one compact M with positive scalar curvature, a `PositiveComponent univ`, and a
  sectional lower bound sec > 0 at time t.
- It returns `∃ A C, …, ∀ eps, ∃ K : CanonicalWitness S eps A C x t` with
  C > max(1, Q/m, B/Q, B_curv/Q, G/(Q√Q), T/Q², (V·Q^{3/2})⁻¹, Q/sec).
- So this is ∀M ∃C: per manifold, by design.

**Callers** (grep over the whole project, excluding the file itself):
- `CN/CompactAncientPositiveWitness.lean:43` (`exists_positive_canonicalWitness_of_compact_ancientKappa`,
  `:26`);
- `:62` and `:71` (buffered variants, no further caller found);
- `CN/CompactPositiveCanonical.lean:145` (its own buffered variant).

`exists_positive_canonicalWitness_of_compact_ancientKappa` has one caller:
`CN/WindowedPositiveBufferedLimit.lean:122`, inside
`exists_eventually_buffered_with_cap_tube_neck_chart_of_windowed_models_of_compact_positive_limit`
(`:101–128`, read). The steps there:
1. It is applied to the **limit** κ-solution L of §1.4 step 4 (compact, so a positive
   component).
2. `CanonicalWitness.eventually_positive_image_of_windowed_models`
   (`CN/WindowedPositiveCanonicalLimit.lean:33–56`, statement; `:170–190`, the construction)
   transports L's witness to the approximating flows with constants (max C₁ 2, C₀), where
   C₀ = max(sourceCurvatureBound 3 C₂, 4C₂, 2·windowedGoodPointConstant(…)).
3. The `volume` field is discharged through `hCinv4 : C⁻¹ ≤ (4C₂)⁻¹` and
   `eventually_volume_lower_bound_of_windowed_models` (`CN/WindowedCanonicalBoundsLimit.lean:152–175`,
   statement read). That lemma says the image of L's domain eventually has
   vol ≥ (4C₂)⁻¹/(R√R).
4. The finite C that results is the "limit supplies a finite constant" step of the
   contradiction in §1.4.

**Verdict.** The per-manifold constant is the positive-curvature special case, used only on
the limit model inside the uniformity proof. It is on the route in that role alone. No real
flow or history receives a constant chosen per manifold.

---

## 4. Question 3: any constant in the wrong order?

Every ∃ that sits after a ∀ over manifolds or flows on this chain was checked.

| ∃ after ∀-flow | where | needed uniform? |
|---|---|---|
| κ, Q₀ in `closed_flow_models` | `CN/HighCurvatureModelBounds.lean:262–267` | No. The standard r and κ also depend on the initial data. C is chosen outside. |
| Q_can in `smooth_canonical_neighborhood` | `:549` | No (as above). |
| A, C in `exists_positive_canonicalWitness_of_compact` | `CompactPositiveCanonical.lean:32,85` | No. It is used only on the limit (§3). |
| Q in `exists_uniform_canonical_threshold_…` clause 1 | `ST/UniformKappaCanonicalThreshold.lean:59` | No. Clause 2 (Q₀, θ) is uniform over all P and G given κ, ρ, Φ, and clause 2 is the one `deepContinuation` uses (`:223–224`). |
| every surgery-era constant, after (P₀, g₀) | `ST/CanonicalNeighborhoodInduction.lean:286`; `ST/SpatialCanonicalContinuation.lean:144`; `ST/CanonicalNeighborhoodsThroughSurgeryStrong.lean:69` | No. `exists_poincare_controlled_extinction` (`RF/Surgery/Skeleton/PoincareEndgame.lean:91–101`) instantiates each predicate at one M. The *values* are in fact uniform in P₀ except C_time and C_grad, which take `exists_slice_bounds_at_slab_start P₀ g₀`. The *statements* are per P₀. |

**Finding: none.** Nothing on the route reads a per-manifold C as though it were uniform.

---

## 5. E3 closed: the η-scaled cap is ε-close to the standard cap

**`exists_uniform_positiveCoordinate_static_estimates`** (`SC/StaticThresholds.lean:26–66`, read fully).
- **Statement.** ∃ derivative constants C_j, A; ∀ D > 0, m, ε > 0, ∃δ₀; ∀δ ≤ δ₀, for every
  normalized δ-neck datum `d`, the rescaled output metric R(x₀)·`d.positiveSideInsertionMetric`,
  pulled back to the model window, is within ε of `StandardCap.metric` in C^m on
  {x : dist₀(x) < D}. The output also has positive scalar curvature, preserves Hamilton–Ivey
  for every a > 0, and has cap derivative bounds.
- **The metric.** `positiveSideInsertionMetric` (`SC/NormalizedInsertion.lean:36–41`) is
  R(x₀)⁻¹·`insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 …`. It is built
  with the **same η** = 1 − √δ as walk 4's collapse map.
- **The proof.** The C^m clause comes from `exists_normalizedDatum_modelWindow_error_lt`
  (`SC/ModelWindow.lean:274–299`), then `exists_normalizedDatum_insertedMetric_ball_error_lt`
  (`SC/NormalizedInsertionNorm.lean:76–97`), then
  `exists_normalizedDatum_insertedMetric_ball_error_bound` (`:15–46`). The error is
  `< C·(δ + √δ)`.
- **The absorption.** It is written out at `:34–38`: `habs : |1 - √δ - 1| = √δ` is passed
  as the |η − 1| term of `exists_insertedMetric_ball_error_bound`
  (`SC/InsertionNorm.lean:290–302`). That lemma states ‖inserted − standard‖_{C^k} ≤
  C·(‖neck − cylinder‖_{C^k} + |η − 1|).
- **The choice of δ₀.** `exists_pos_precision_for_bound` (`:48–74`) picks δ₀ with
  C(δ + √δ) < ε.

**`StandardCap.metric`** (`SC/Metric.lean:84–86`) is the radially warped metric built from
`warpingFunction`, i.e. the standard initial cap. Only its definition line was read.

So the O(√δ) scaling is charged explicitly against the ε-closeness that feeds the
standard-solution comparison. The √δ is not hidden. E3 is closed, and the error constant C
is computation (§7).

---

## 6. Escalations, ranked

No gap was found. The items below are load-bearing statements whose bodies lie below this
walk's frontier.

**F1 (medium, frontier; the one that carries the κ-independence of C).**
`ancientKappaThree_terminal_universal_noncollapsed` is located, not read.
- It is called at `KS/UniversalKappaGap.lean:64–65`, inside
  `ancientKappaThree_universal_noncollapsed` (`:34–81`, read).
- It is the Lean form of Perelman I 11.9: every non-round 3-dimensional ancient κ-solution is
  a κ₀-solution, with κ₀ = `universalKappaConstant`
  = (4πθ)^{3/2}·e^{−27θ/2}·e^{−1}/4 (`KS/UniversalKappaConstant.lean:27–29`).
- It is the reason (C₁, C₂) can be chosen **before κ** in `buffered_canonical_pullback` and
  in every surgery leaf (`∀ κ` after `∃ C`). If it failed, the Lean order would be wrong,
  though the standard order ε → C(ε, κ) with κ fixed per initial data would still be
  available.
- A sibling with explicit hypotheses exists:
  `ancientKappaThree_universal_noncollapsed_of_reducedVolume`
  (`KS/AncientKappaReducedVolumeBound.lean:106–113`). It assumes
  `AncientKappaReducedVolumeLowerBound` and `…UpperBound`. So the route version discharges
  those somewhere. Read it next.

**F2 (low–medium, frontier).** The noncompact-limit branch
`exists_eventually_buffered_with_cap_neck_charts_of_windowed_models_of_noncompact_oriented_limit`
(located, not read) supplies the finite C for neck and cap limits in §1.4 step 4. Its volume
discharge (noncompact κ-solution limit, then the cap or neck volume clause) is the analogue of
§3 for the other two alternatives.

**F3 (low, frontier).** The ancient-limit extraction in the surgery-era contradictions was not
read:
- `exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`
  (`ST/CrossingAncientLimit.lean:93`, call site);
- `exists_eventually_spatialCanonicalWitness_of_isTracedRegion`.

This is Perelman II 5.1's "the limit is a κ-solution". Their statements fix C before the
sequence, which is all E1 needed.

**F4 (low, README precision).** README `:566` names `fixed_kappa_compactness`, a wrapper of
`…_captured`. The uniform-constant proof calls the non-captured
`exists_ancientKappa_fixed_kappa_compactness`, which rests on
`exists_fixed_kappa_compactness` through `ancientKappaThree_toKLim`. Both are the same theorem
in substance. This does not affect soundness.

**F5 (low, design).** The surgery-era predicates are stated per (P₀, g₀). That is weaker than
Perelman's constants, which depend only on ε, so the intermediate statements cannot be reused
to get constants uniform over initial data without re-proving them. The values happen to be
uniform except C_time and C_grad. This does not affect the Poincaré route.

**Walk 4 E1:** closed by §1–§4. **Walk 4 E3:** closed by §5.

---

## 7. Computation not read

1. `CN/CompactPositiveCanonical.lean:85–90`: the eight-ratio max. It only has to exceed each
   ratio, and `max_lt_iff` shows it does.
2. `CN/WindowedPositiveCanonicalLimit.lean:77`: C⁻¹ ≤ (4C₂)⁻¹ from C ≥ 4C₂ in C₀.
3. `SC/InsertionNorm.lean:290` via `exists_insertedMetric_error_bound_of_lt`: the value of C
   in C·(δ + √δ).
4. `KS/UniversalKappaConstant.lean`: θ from `exists_collapsedVolumeTail_small (27/2)`.
5. `ST/SmallScaleNoncollapsingThroughSurgery.lean:531–548`: L, c and the 3072 pinching
   constant (nlinarith).

## 8. Not read

- **Bodies of:** `bounded_curvature_at_distance`, `terminal_limit_global_bound`,
  `first_backward_slab`, `ancient_extension`, `spatial_no_local_collapsing`,
  `nonempty_positiveComponent_of_compact_nonround_pointed_limit`, the noncompact-limit
  branch (F2), `ancientKappaThree_terminal_universal_noncollapsed` (F1),
  `eventually_volume_lower_bound_of_windowed_models` (statement only),
  `exists_uniform_orientedWitness_of_standard_close_endpoint`,
  `exists_window_spatialCanonicalWitness_of_standard_close`,
  `exists_slice_bounds_at_slab_start`, the full contradiction bodies of
  `crossingContinuation_holds` and `spatialCrossingContinuation_holds` (read to the choice of
  C and the sequence set-up only), `ancientKappa_fixed_kappa_compactness_of_capture`.
- **Parts of `UniformKappaCanonicalThreshold.lean`:** everything after `:200` (the
  rescaling of the backward window into `ClosedModelHypotheses`).
- **`CanonicalWitness`** (`CN/FiniteHornGeometry.lean:272`) as a structure. Only its
  projection `toSpatial` (the volume line) and its uses were read.
- **Other routes to `buffered_canonical_pullback`:** `HighCurvatureModelFrontier.lean` and
  `NeckCapMainFrontier.lean` (`buffered_canonical_pullback_of_classification`). They are
  frontier or alternative routes to the same statement, not on the Poincaré route.
