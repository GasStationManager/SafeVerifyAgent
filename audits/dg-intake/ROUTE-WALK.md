# Route walk: `poincare_conjecture`, depth 0–4

Artifact `/home/user/differential-geometry` @ `7a48598d`, read-only, nothing
compiled. Every `file:line` below was read with `sed -n` in this pass. Paths are
relative to `DifferentialGeometry/` unless they start with `Mathlib`. "Depth" is
call depth from the headline through proof terms (the headline is depth 0).
Playbook §0 discipline: each record says what argument the Lean expresses; steps
that are computation are listed in §5, not read.

No file on the route down to depth 4 carries a single docstring (`/--` or `/-!`
count 0 in all nine route files checked). Every "docstring vs Lean" comparison
the brief asks for therefore degenerates to "identifier name and definition vs
the standard mathematics"; see Escalation E1.

---

## 1. The argument, as a mathematician would state it

**Theorem (Poincaré).** A compact Hausdorff simply connected topological
3-manifold M is homeomorphic to S³. — `poincare_conjecture`
(`Topology/ThreeManifold/Poincare.lean:12`). The Lean statement matches
`REFERENCE-poincare.md` clause for clause: charts to ℝ³ (H1, and H4, since the
model has no boundary), `T2Space` (H2), `CompactSpace` (H3),
`SimplyConnectedSpace` (H6), which in Mathlib contains nonemptiness and path
connectedness (H5; `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:73`).

**Step 1 (Moise: every 3-manifold is smoothable).** M carries a smooth atlas
compatible with its topology. — `PiecewiseLinear.exists_isManifold_three`
(`Topology/PiecewiseLinear/Moise352Producer.lean:33`). Proof in two halves:

- *1a, triangulation (Moise).* Cover the compact M by finitely many charts and
  glue them one at a time into a single PL atlas, each time replacing the new
  chart's transition maps by PL approximations of them (`exists_atlasOn_univ_of_plApproximation`,
  `ChartGluing.lean:224`). The approximation input is the PL approximation theorem
  for homeomorphisms between PL 3-manifolds (`PLApproximationManifold 3`),
  which comes from the relative approximation of embeddings on open sets
  (`Moise352Open 3`, the name presumably cites Moise, *Geometric Topology in Dimensions 2 and 3*, §35 Thm 2 — unverified), which is proved by the
  "cell diagram" construction of §34 (`section34CellDiagram`). —
  `plApproximation_three`, `plApproximationManifold_three`, `moise352Open`.
- *1b, PL ⇒ smooth in dimension 3.* Triangulate the PL manifold by a finite
  combinatorial 3-manifold, filter it by derived neighbourhoods into a handle
  decomposition, and build a smooth manifold handle by handle; transport the
  smooth structure back along the resulting homeomorphism. —
  `plSmoothingCompact_three`, `plSmoothingModelCompact_three`
  (`PLSmoothingCompact.lean:411`), `exists_boundarylessManifold_of_isCombinatorialManifold_three` (`:368`).

**Step 2 (smooth Poincaré).** A closed smooth connected simply connected
3-manifold is diffeomorphic to S³. — `smoothPoincareConjecture_holds`
(`Geometry/Flow/RicciFlow/Surgery/Skeleton/PoincareEndgame.lean:103`). A
diffeomorphism is a homeomorphism, which closes the headline.

**Step 2a (reduction to controlled extinction).** Choose any smooth Riemannian
metric g (partition of unity) and an orientation (simply connected ⇒ orientable).
If Ricci flow with surgery from (M, g) goes extinct in finite time and every
piece thrown away at a surgery is a connected sum of spherical space forms and
S²×S¹ ("Poincaré-standard"), then running the surgeries backwards shows M itself
is such a connected sum; since π₁(M) = 1 and π₁ of a connected sum is the free
product, every summand has trivial π₁, which rules out S²×S¹ (π₁ = ℤ) and forces
each spherical space form to be S³; a connected sum of S³'s is S³. —
`Surgery.smoothPoincareConjecture_of_controlledExtinction`
(`Geometry/Flow/RicciFlow/Surgery/Poincare.lean:80`),
`exists_diffeomorph_standardThreeSphere_of_controlledExtinction` (`:72`),
`PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction`
(`Surgery/Topology/ExtinctionReconstruction.lean:39`),
`exists_diffeomorph_standardThreeSphere_of_isPoincareStandard`
(`Topology/ThreeManifold/PoincareStandardClassification.lean:19`).

**Step 2b (existence of controlled extinction: Perelman).** For simply connected
(M, g), Ricci flow with surgery exists and becomes extinct, with Poincaré-standard
discards. — `exists_poincare_controlled_extinction` (`PoincareEndgame.lean:91`).
It combines two uniform statements over all surgery histories that start at
(M, g) and stay in a "cutoff class":

- *(i) canonical neighbourhoods persist through surgery*
  (`CanonicalNeighborhoodsThroughSurgeryStrong`, `CanonicalNeighborhoodsThroughSurgeryStrong.lean:69`):
  for ε small, there are constants such that every such history has Hamilton–Ivey
  pinching, κ-noncollapsing on scales ≤ ε, a time-derivative and gradient bound
  of R at high curvature, and (strong/spatial) ε-canonical neighbourhoods at
  high curvature, both on the recorded slabs and on the next slab up to its
  singular time. This is Perelman II §4–5 (the
  induction "canonical neighbourhoods + noncollapsing ⇒ they persist one more
  surgery interval"). Its proof (`_of_leaves`, `:272`) is exactly that induction
  over surgery indices (`Fin.induction`, `:318`), fed by four inputs:
  Hamilton–Ivey pinching (`pinchingThroughSurgery`), κ-noncollapsing
  (`noncollapsingThroughSurgery`: reduced-volume monotonicity, a local upper and an
  initial lower bound for reduced volume, and a small-scale bound),
  canonical-neighbourhood continuation in time (`canonicalNeighborhoodContinuation`:
  deep / cap-window / crossing cases), and its spatial version
  (`spatialCanonicalContinuation`).
- *(ii) one surgery step with a volume debit*
  (`UniformDebitSurgeryStepStrong`, `CanonicalNeighborhoodsThroughSurgeryStrong.lean:124`):
  under (i)'s conclusions, at a singular time one can cut along strong ε-necks
  with a standard cap, the result is again in the cutoff class, every discarded
  component is Poincaré-standard, and volume drops by at least v per neck. This
  is Perelman II §4 surgery existence plus the "surgery removes volume h³"
  count. — `uniformDebitSurgeryStepStrong`
  (`PoincareEndgame.lean:38`) from pinching, strong necks, and the supply of fine
  cut necks.
- *(iii) extinction.* Put the horizon B past the extinction threshold computed
  from the initial scalar lower bound and the width of the canonical sweepout
  class; iterate (ii) — finitely many surgeries before B because each costs v of
  a volume bounded above — and the width argument (Perelman III / Colding–Minicozzi)
  makes the manifold empty before B. —
  `exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong`
  (`:192`) → `exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants`
  (`Surgery/Topology/SingularEventExtinction.lean:33`) →
  `exists_poincare_controlled_extinction_of_history_volume_debit`
  (`Surgery/Topology/FiniteHorizonExtinction.lean:68`, depth 5).

Where simple connectivity is used: orientability (2a), trivial π₁ of summands
(2a), the width/extinction argument (iii), and — not in Perelman — small-scale
noncollapsing (see E2).

---

## 2. Per-theorem records by depth

Legend: **named** = a Prop predicate or bundle taken as a hypothesis;
"discharged at" = where the route supplies it.

### Depth 0

**`DifferentialGeometry.Topology.poincare_conjecture`** — `Topology/ThreeManifold/Poincare.lean:12`
- Statement: M : Type u, topological, charted on `EuclideanSpace ℝ (Fin 3)`, T2,
  compact, simply connected ⟹ `Nonempty (M ≃ₜ sphere (0 : ℝ⁴) 1)`. Poincaré conjecture.
- Calls: `PiecewiseLinear.exists_isManifold_three` (`Topology/PiecewiseLinear/Moise352Producer.lean:33`);
  `PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds` (`Geometry/Flow/RicciFlow/Surgery/Skeleton/PoincareEndgame.lean:103`);
  `Diffeomorph.toHomeomorph` (Mathlib, stop).
- Named hypotheses: none. Argument: obtain a smooth atlas C with `IsManifold`,
  install it as the charted instance (`let := C`, `:18`), apply smooth Poincaré,
  forget smoothness. `ConnectedSpace M` for the callee comes from Mathlib's
  `SimplyConnectedSpace ⇒ PathConnectedSpace` instance.
- No discrepancy with the reference statement.

### Depth 1

**`PiecewiseLinear.exists_isManifold_three`** — `Topology/PiecewiseLinear/Moise352Producer.lean:33`
- Statement: compact T2 M charted on ℝ³ ⟹ ∃ charted structure C on the same topology with `IsManifold (𝓡 3) ∞`. Moise's theorem (3-manifolds are triangulable/smoothable).
- Calls: `exists_isManifold_of_plApproximation_of_plSmoothingCompact` (`PLSmoothingCompact.lean:59`), `plApproximation_three` (`Moise352Producer.lean:27`), `plSmoothingCompact_three` (`Moise352Producer.lean:30`).
- Named: the callee takes `PLApproximation 3` and `PLSmoothingCompact 3`; both discharged in the same file (depth 2).

**`Surgery.Topology.smoothPoincareConjecture_holds`** — `Surgery/Skeleton/PoincareEndgame.lean:103`
- Statement: smooth (`IsManifold (𝓡 3) ∞`), T2, compact, connected, simply connected M ⟹ `M ≃ₘ⟮𝓡 3, 𝓡 3⟯ S³`. Smooth Poincaré conjecture.
- Calls: `Surgery.smoothPoincareConjecture_of_controlledExtinction` (`Surgery/Poincare.lean:80`, resolved through the enclosing namespace `Surgery`; the only declaration of that name), `exists_poincare_controlled_extinction` (`PoincareEndgame.lean:91`), `standardThreeSphereLiftDiffeomorph` (`Topology/ThreeManifold/StandardSphere.lean:35`, def: ULift transport), `ConnectedClosedOrientedManifold.toClosedOrientedManifold` (def, not opened).
- Named: `hext` of the callee (∀ connected closed oriented simply connected M and metric g, `Nonempty (PoincareControlledExtinction M g)`), discharged here by `exists_poincare_controlled_extinction`.

### Depth 2

**`exists_isManifold_of_plApproximation_of_plSmoothingCompact`** — `Topology/PiecewiseLinear/PLSmoothingCompact.lean:59`
- Statement: `PLApproximation n` ∧ `PLSmoothingCompact n` ⟹ every compact T2 n-charted X has a smooth atlas. Composition "triangulate, then smooth".
- Calls: `ChartedSpace.secondCountable_of_sigmaCompact` (Mathlib, stop); `exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation` (`ChartGluing.lean:252`).
- Named: `hA : PLApproximation n` (def `PiecewiseLinear/Approximation.lean:18`), `hB : PLSmoothingCompact n` (def `PLSmoothingCompact.lean:37`): discharged by the caller with `plApproximation_three`, `plSmoothingCompact_three`.

**`plApproximation_three`** — `Moise352Producer.lean:27`
- Statement: `PLApproximation 3`: a homeomorphism between open sets carrying PL atlases can be ε(x)-approximated by one that is PL in those atlases. Moise approximation theorem, relative form.
- Calls: `plApproximation_of_plApproximationManifold` (`ApproximationManifold.lean:81`), `plApproximationManifold_three` (`Moise352Producer.lean:24`).
- Named: `PLApproximationManifold 3` (def `PiecewiseLinear/Manifold.lean:156`), discharged at depth 3.

**`plSmoothingCompact_three`** — `Moise352Producer.lean:30`
- Statement: `PLSmoothingCompact 3`: a compact PL 3-manifold admits a compatible-topology smooth atlas. Smoothing of PL 3-manifolds (Whitehead/Munkres; here via handles).
- Calls: `plSmoothingCompact_of_plSmoothingModelCompact` (`PLSmoothingCompact.lean:52`), `plSmoothingModelCompact_three` (`PLSmoothingCompact.lean:411`).
- Named: `PLSmoothingModelCompact 3` (def `:45`), discharged at depth 3.

**`Surgery.smoothPoincareConjecture_of_controlledExtinction`** — `Geometry/Flow/RicciFlow/Surgery/Poincare.lean:80`
- Statement: if every connected closed oriented simply connected smooth 3-manifold with any metric admits `PoincareControlledExtinction`, then `smoothPoincareConjecture` (def `:30`). Reduction of Poincaré to finite extinction with standard discards.
- Calls: `Geometry.nonempty_smoothRiemannianMetric` (`Geometry/Metric/Construction/Existence.lean:228`), `Topology.Manifold.exists_manifoldOrientation_of_simply_connected` (`Topology/Manifold/Orientation.lean:436`), `exists_diffeomorph_standardThreeSphere_of_controlledExtinction` (`Surgery/Poincare.lean:72`).
- Named: `hext` (above), discharged by the caller.
- Structure `PoincareControlledExtinction M g` (`Surgery/Topology/ControlledExtinction.lean:14`): a `FiniteSurgeryHistory` (`FiniteHistory.lean:14`: ≥1 events, strictly increasing times from 0, stages that are closed oriented 3-manifolds with metrics, each event a `MetricCutCapEvent` whose incoming slab is a Ricci flow — `EventData.lean:194`, field `equation : IsSolutionOn flow`), an initial isometric orientation-preserving identification with (M, g), `poincareControlled` (every discarded component `isPoincareStandard`, `PoincareControl.lean:10`, `PoincareStandard.lean:88`), and `extinctAt` (final stage empty, `FiniteHistory.lean:40`). This is a faithful rendering of "surgery history from (M,g) that goes extinct with standard discards".

**`exists_poincare_controlled_extinction`** — `PoincareEndgame.lean:91`
- Statement: closed oriented simply connected M, metric g ⟹ `Nonempty (PoincareControlledExtinction M g)`. Perelman: Ricci flow with surgery on simply connected 3-manifolds becomes extinct (Perelman II+III; Morgan–Tian; Colding–Minicozzi).
- Calls: `exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong` (`Surgery/Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:192`), `uniformDebitSurgeryStepStrong` (`PoincareEndgame.lean:38`), `canonicalNeighborhoodsThroughSurgeryStrong` (`PoincareEndgame.lean:84`), `OrientedThreeStage.ofClosedOrientedManifold` (`Surgery/Topology/ClosedOrientedStage.lean:41`, def).
- Named: `hstep : UniformDebitSurgeryStepStrong`, `hcn : CanonicalNeighborhoodsThroughSurgeryStrong` — discharged here by the two endgame theorems.

**`standardThreeSphereLiftDiffeomorph`** — `Topology/ThreeManifold/StandardSphere.lean:35` (def, not a theorem): the ULift diffeomorphism, `ClosedOrientedManifold.uliftDiffeomorph` (frontier).

### Depth 3

**`exists_chartedSpace_hasGroupoid_plGroupoid_of_plApproximation`** — `PiecewiseLinear/ChartGluing.lean:252`
- Statement: `PLApproximation n` ⟹ compact T2 n-charted X has a PL atlas. Triangulation (existence of PL structure) of compact n-manifolds given approximation.
- Calls: `exists_atlasOn_univ_of_plApproximation` (`ChartGluing.lean:224`), `AtlasOn.chartedSpace`, `AtlasOn.hasGroupoid` (not opened).
- Named: `hA`, supplied by caller.

**`plApproximation_of_plApproximationManifold`** — `PiecewiseLinear/ApproximationManifold.lean:81`
- Statement: `PLApproximationManifold n ⟹ PLApproximation n`. Localisation: restrict the atlases to the open source/target, approximate there, re-extend as an `OpenPartialHomeomorph`; empty case separately.
- Calls (read to `:175`): `AtlasOn.subtypeChartedSpace(_hasGroupoid)`, `Opens.openPartialHomeomorphSubtypeCoe`, `isPLAt_iff_of_mem_maximalAtlas`, `mem_plGroupoid_of_isPiecewiseAffineOn`, `ofSet_mem_plGroupoid` (all local bookkeeping; not expanded).
- Named: `h : PLApproximationManifold n`, supplied by caller.

**`plApproximationManifold_three`** — `Moise352Producer.lean:24`
- Statement: `PLApproximationManifold 3`: any homeomorphism between PL 3-manifolds (target metric) is φ-close to a PL homeomorphism. Moise's approximation theorem for homeomorphisms.
- Calls: `plApproximationManifold_three_of_open` (`Moise352OfOpen.lean:17`), `moise352Open` (`Moise352Producer.lean:18`).
- Named: `Moise352Open 3` (def `OpenSourceReduction.lean:210`), discharged by `moise352Open`.

**`plSmoothingCompact_of_plSmoothingModelCompact`** — `PLSmoothingCompact.lean:52`
- Statement: model form (homeomorphic to some smooth N) ⟹ atlas form. Pull back the smooth atlas along the homeomorphism.
- Calls: `Manifold.Homeomorph.pullbackChartedSpace` (`Topology/Manifold/Homeomorph/Transport.lean:12`), `Manifold.Homeomorph.instIsManifoldPullback` (`Transport.lean:47`).
- Named: `h`, supplied by caller.

**`plSmoothingModelCompact_three`** — `PLSmoothingCompact.lean:411`
- Statement: compact PL 3-manifold X is homeomorphic to a smooth closed 3-manifold. Triangulate (combinatorial manifold), smooth, and pass from the half-space model to the boundaryless ℝ³ model; empty X separately.
- Calls: `plManifoldTriangulation` (`PiecewiseLinear/Combinatorial.lean:275`), `exists_boundarylessManifold_of_isCombinatorialManifold_three` (`PLSmoothingCompact.lean:368`), `Manifold.interiorChartedSpace` (`Topology/Manifold/InteriorAtlas.lean:17`), `Manifold.interiorIsManifold` (`InteriorAtlas.lean:33`), `pullbackChartedSpace`/`instIsManifoldPullback` (above), `Homeomorph.ulift`, `IsManifold.empty` (Mathlib, stop).
- Named: none.

**`Geometry.nonempty_smoothRiemannianMetric`** — `Geometry/Metric/Construction/Existence.lean:228`
- Statement: σ-compact T2 manifold has a smooth Riemannian metric. Standard partition-of-unity existence.
- Calls: `nonempty_contMDiffRiemannianMetric_of_sigmaCompact` (`Existence.lean:203`). Named: none.

**`Topology.Manifold.exists_manifoldOrientation_of_simply_connected`** — `Topology/Manifold/Orientation.lean:436`
- Statement: simply connected smooth manifold of dimension n is orientable. Standard (orientation double cover is trivial).
- Calls: `VectorBundle.exists_compatible_orientation_of_simply_connected` (`Bundle/Orientation/Section.lean:69`), `exists_manifoldOrientation_of_compatibleOrientation` (same file, not opened), `ChartedSpace.locallyPathConnectedSpace` (Mathlib). Named: none.

**`exists_diffeomorph_standardThreeSphere_of_controlledExtinction`** — `Surgery/Poincare.lean:72`
- Statement: `PoincareControlledExtinction M g`, M simply connected ⟹ M ≅ S³ (diffeo). Topological endgame of Perelman's proof.
- Calls: `exists_diffeomorph_standardThreeSphere_of_isPoincareStandard` (`Topology/ThreeManifold/PoincareStandardClassification.lean:19`), `PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction` (`Surgery/Topology/ExtinctionReconstruction.lean:39`).
- Named: `W` is a structure hypothesis, supplied by `hext`.

**`exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong`** — `Surgery/Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:192`
- Statement: simply connected P₀, metric g₀; `UniformDebitSurgeryStepStrong` ∧ `CanonicalNeighborhoodsThroughSurgeryStrong` ⟹ controlled extinction. Perelman: surgery can be continued (with canonical neighbourhoods) until extinction.
- Argument: for a horizon B, fix ε from (i) at two accuracies (min(1/22, ε̄) and the ε chosen by (ii)), pull all constants out of (i), feed them to (ii), take the invariant "has canonical cutoff records", and hand the resulting one-step producer to the extinction theorem; monotonicity-in-threshold lemmas reconcile the two instances of (i).
- Calls: `exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants` (`SingularEventExtinction.lean:33`), `RetainedCoreHistory.hasCanonicalCutoffRecords_atZero` (`CanonicalCapWindows.lean:113`), `gradientBoundBefore_of_threshold_le`, `canonicalBefore_of_threshold_le`, `spatiallyCanonicalBefore_of_threshold_le` (not opened, frontier).
- Named: `hstep`, `hcn` (supplied by caller).

**`uniformDebitSurgeryStepStrong`** — `PoincareEndgame.lean:38`
- Statement: `UniformDebitSurgeryStepStrong P₀ g₀` (def `CanonicalNeighborhoodsThroughSurgeryStrong.lean:124`): ∀ B, ε̄ ∃ Λ, ∀ Ctime ∃ ε ≤ ε̄, ∀ constants ∃ cutoff parameters p₀, δ, ρ, v>0 such that every history in the class whose recorded slabs and next slab satisfy the derivative, gradient, canonical, spatially canonical, Hamilton–Ivey, noncollapsing clauses can be extended by one surgery at the singular time of the next slab, with new cutoff records, frame-reversing gluing, Poincaré-standard discards, and output volume + (#necks)·v ≤ volume of a compact part of the regular region. Perelman II §4 surgery + volume decrease.
- Calls: `uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong` (`Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:21`), `pinchingThroughSurgery` (`Surgery/Topology/PinchingThroughSurgery.lean:12`), `strongNecksOfCutoffClass` (`PoincareEndgame.lean:33`), `fineCutNeckSupplyStrong` (`PoincareEndgame.lean:29`).
- Named: `PinchingThroughSurgery`, `StrongNecksOfCutoffClass`, `FineCutNeckSupplyStrong` — discharged at depth 4 by the three endgame theorems.

**`canonicalNeighborhoodsThroughSurgeryStrong`** — `PoincareEndgame.lean:84`
- Statement: `CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀` (def `CanonicalNeighborhoodsThroughSurgeryStrong.lean:69`, clause list `:24`). Perelman II §4–5: canonical neighbourhoods + κ-noncollapsing + pinching through surgery.
- Calls: `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` (`CanonicalNeighborhoodsThroughSurgeryStrong.lean:272`), `pinchingThroughSurgery` (`PinchingThroughSurgery.lean:12`), `noncollapsingThroughSurgery` (`PoincareEndgame.lean:60`), `canonicalNeighborhoodContinuation` (`PoincareEndgame.lean:71`), `spatialCanonicalContinuation` (`PoincareEndgame.lean:80`).
- Named: the four leaf predicates, discharged at depth 4.

### Depth 4

**`exists_atlasOn_univ_of_plApproximation`** — `PiecewiseLinear/ChartGluing.lean:224`
- Statement: compact X ⟹ PL atlas on all of X. Finite subcover by chart sources; induction over a Finset adding one chart at a time.
- Calls (depth 5): `exists_atlasOn_union_of_plApproximation_of_metrizable` (`ChartGluing.lean:207`, which calls `exists_atlasOn_union_of_plApproximation`, not opened), `AtlasOn.ofOpenPartialHomeomorph`, `AtlasOn.empty`, `ChartedSpace.locallyCompactSpace`, `IsCompact.elim_nhds_subcover` (Mathlib). Named: `hA`, supplied.

**`plApproximationManifold_three_of_open`** — `PiecewiseLinear/Moise352OfOpen.lean:17`
- Statement: `Moise352Open 3 ⟹ PLApproximationManifold 3`. Via `moise352_three_of_open` (`:14`) = `moise352_of_inwardPush_of_open moise352InwardPush_three` and `plApproximationManifold_three_of_moise352` (`Endgame.lean:14`: approximate h on U = univ with image-equality, so the PL approximant is a bijection, hence a homeomorphism by invariance of domain `isOpenMap_of_continuous_injective`).
- Calls (depth 5): `moise352_of_inwardPush_of_open` (`OpenSourceReduction.lean:226`), `moise352InwardPush_three` (`Moise352InwardPushProof.lean:15`), `plApproximationManifold_three_of_moise352` (`Endgame.lean:14`), `exists_plh_approx_of_isOpen` (`Transition361.lean:372`).
- Named: `Moise352Open 3` (hyp), `Moise352 3` (def `Transition361.lean:256`), `Moise352InwardPush 3` — the latter discharged by `moise352InwardPush_three` (`Moise352InwardPushProof.lean:15`, one line to `exists_isPLOn_injOn_leftInvOn_dist_lt`, `LocallyFiniteInwardPush.lean:16`).

**`moise352Open`** — `Moise352Producer.lean:18`
- Statement: `Moise352Open 3` (def `OpenSourceReduction.lean:210`): an embedding h of an open U of a PL 3-manifold into a metric PL 3-manifold is φ-approximated on U by a PL embedding. Moise's approximation theorem, open-set form (name suggests §35 Thm 2; unverified).
- Calls (depth 5): `moise352Open_of_section34CellDiagram` (`Section34Endpoint.lean:88`, which assembles a PL embedding from a labelled cell diagram via `exists_isPLHomeomorphInto_dist_lt_of_cellDiagram`, `:21`), `section34CellDiagram` (`Section34Terminal.lean:19`).
- Named: `Section34CellDiagram` (def `Section34Endpoint.lean:59`: existence of matching source/target cell complexes subordinate to φ), discharged by `section34CellDiagram` (proof calls `section34NormalFamilyStatement` `Section34Normalization.lean:174`, `exists_section34FaceDisks` `Section34FaceDisks.lean:36`, `exists_section34ResidualBalls` `Section34ResidualBalls.lean:33`, `section34TargetRecognition_of_tiling` `Section34TargetRecognitionOfTiling.lean:796`). NOSUPPLIER flags `Section34GraphFrame`, `Section34NormalPlus`, `Section34CompactFaceBallInvariants` as having no supplier; they would sit below these — frontier.

**`Manifold.Homeomorph.pullbackChartedSpace` / `instIsManifoldPullback`** — `Topology/Manifold/Homeomorph/Transport.lean:12`, `:47`: transport of an atlas along a homeomorphism; bookkeeping, not expanded.

**`plManifoldTriangulation`** — `PiecewiseLinear/Combinatorial.lean:275`
- Statement: a PL n-manifold admits a triangulation by a combinatorial manifold. Standard PL topology (subdivision of a PL piece).
- Calls (depth 5): `exists_pLTriangulation_isCombinatorialManifold` (`Combinatorial.lean:263`). Named: none.

**`exists_boundarylessManifold_of_isCombinatorialManifold_three`** — `PLSmoothingCompact.lean:368`
- Statement: finite combinatorial 3-manifold K ⟹ a smooth boundaryless manifold (half-space model) homeomorphic to |K|. PL ⇒ smooth in dim 3 by handle attachment.
- Argument: `exists_pl_three_handle_filtration` gives a filtration by derived neighbourhoods N₀=∅ ⊂ … ⊂ N_m = K with each step a PL handle attachment; induction `isSmoothHandleStage_step` builds a smooth stage at each step; at the end the boundary complex of K is empty, so the smooth manifold is boundaryless.
- Calls (depth 5): `exists_pl_three_handle_filtration` (`DerivedNeighborhoodHandleFiltration.lean:18`), `isSmoothHandleStage_step` (`PLSmoothingCompact.lean:245`), `isSmoothHandleStage_of_isEmpty`, `derivedNeighborhood_faces_finite`, `boundaryComplex_space_of_isPLHomeomorphOn`, `boundaryComplex_faces_eq_empty` (not opened). Sphere recognition `nonempty_diffeomorph_sphere_of_homeomorph_sphere` (`:78`) is used by the handle stages (not opened).

**`interiorChartedSpace` / `interiorIsManifold`** — `Topology/Manifold/InteriorAtlas.lean:17`, `:33`: a boundaryless half-space manifold as an ℝ³ manifold. Not expanded.

**`nonempty_contMDiffRiemannianMetric_of_sigmaCompact`** — `Geometry/Metric/Construction/Existence.lean:203`: frontier (not opened beyond the head).

**`VectorBundle.exists_compatible_orientation_of_simply_connected`** — `Bundle/Orientation/Section.lean:69`: frontier.

**`PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction`** — `Surgery/Topology/ExtinctionReconstruction.lean:39`
- Statement: connected M with controlled extinction ⟹ `isPoincareStandard M`. Reverse induction over surgeries: empty final stage; each earlier component is a connected sum of later components and discarded standard pieces.
- Calls (depth 5): `FiniteCutCapTrace.isPoincareStandard_of_initialIdentification_of_poincareControlled_extinct` (`Topology/ThreeManifold/CutCapPoincareStandard.lean:62`; it is `Fin.reverseInduction` over `componentwise_isPoincareStandard_of_poincareControlled`, `CutCapPoincareStandard.lean:15`), `controlled_extinct_trace` (`ControlledExtinction.lean:45`).
- Named: none. Note: this is the hypothesis-free variant. The sibling `PoincareControlledExtinction.isPoincareStandard` (`ExtinctionReconstruction.lean:22`) takes `hsum` and `hsumClosed`; it is off the route.

**`exists_diffeomorph_standardThreeSphere_of_isPoincareStandard`** — `Topology/ThreeManifold/PoincareStandardClassification.lean:19`
- Statement: smooth closed connected simply connected M, `isPoincareStandard M` (M ≅ #ᵢFᵢ with each Fᵢ an oriented spherical space form S³/Γ or S²×S¹, def `StandardFactors.lean:594`) ⟹ M ≅ S³. π₁(M) = *ᵢ π₁(Fᵢ) (van Kampen for connected sums) trivial ⟹ each π₁(Fᵢ) trivial (a free product is trivial iff each factor is) ⟹ Fᵢ ≅ S³ (Γ trivial; S²×S¹ excluded by π₁ ≅ ℤ) ⟹ # of S³'s ≅ S³. Read as an argument; matches the standard one.
- Calls (depth 5): `fundamentalGroupMulEquivOfHomotopyEquiv` (local, `FundamentalGroup/HomotopyEquiv`), `fundamentalGroup_finiteConnectedSum_freeProduct` (`Topology/VanKampen/FiniteConnectedSumFreeProduct.lean:277`), `Algebra.Group.coprodI_subsingleton_iff` (`Topology/Algebra/Group/FreeProduct.lean:17`), `exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor` (`PoincareStandardOriented.lean:62`, read: case split exactly as described, via `exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group` and `exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle`), `exists_diffeomorph_finiteConnectedSum_standardThreeSphere` (`PoincareStandardOriented.lean:86`).
- Named: none.

**`exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants`** — `Surgery/Topology/SingularEventExtinction.lean:33`
- Statement: if for every horizon B there is a one-step producer (as in (ii), preserving an invariant `Inv`), then controlled extinction. Finite extinction by width + volume debit.
- Argument: `exists_initialScalarBarrier_of_compact` gives c with R ≥ −3/(2c) initially; B := max 1 (extinctionThreshold c W + 1) with W = `canonicalWidth g P.orientation`; S = histories that prefix-extend the trivial one, stay below B, satisfy Inv and carry records, frame reversal, standard discards and debits; show S closed under the producer; hand to `exists_poincare_controlled_extinction_of_history_volume_debit`.
- Calls (depth 5): `exists_initialScalarBarrier_of_compact` (`ExtinctionExistenceReduction.lean:18`), `extinctionThreshold` (`Extinction/Families/ScalarThreshold.lean:11`), `canonicalWidth` (`Extinction/Width/CanonicalClass.lean:19`), `RetainedCoreHistory.exists_poincare_controlled_extinction_of_history_volume_debit` (`FiniteHorizonExtinction.lean:68`), `appendEvent_isPrefixOf`, `appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded`, `appendEvent_compact_volume_debit`, `GeometricCutoffRecord.spliceParametersAt/appendEvent` (not opened).
- Named: `hproduce` (the one-step producer), discharged by the caller (depth 3) from `hstep` + `hcn`.

**`RetainedCoreHistory.hasCanonicalCutoffRecords_atZero`** — `Surgery/Topology/CanonicalCapWindows.lean:113`: the zero-event history vacuously has records. Read: all fields `Fin.elim0`.

**`uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong`** — `Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:21`
- Statement: pinching ∧ strong necks ∧ fine-cut neck supply ⟹ `UniformDebitSurgeryStepStrong`. Perelman surgery step.
- Argument: pick ε below all thresholds; build explicit cutoff parameters (`:91–105`); use strong necks to upgrade canonical to strongly canonical at high curvature; take the terminal limit metric on the regular region (`G.nonempty_terminalLimitMetric`, `:110`); apply the horn cutoff-record factory `hF` with fine cut necks from the supply; unpack a surgery event, records, frame reversal, standard discards (`hstdE`) and the volume debit.
- Calls (depth 5): `exists_horn_cutoff_record_of_fineCutNecks_of_le`, `fineCutNecks_of_le`, `hasCanonicalCutoffRecords_of_le`, `exists_compact_volume_debit_of_incoming_eq` — all PRIVATE in `Surgery/Contract/UniformDebitSurgeryStepOfFactory.lean:39, :280, :288, :295`, reached by `open private` (`:6–8`); `IncomingSlab.nonempty_terminalLimitMetric` (`Surgery/Topology/TerminalMetricExistence.lean:84`); `CutoffParameters.recenterConstant_mul_le_half` (`CanonicalNeighborhoodsThroughSurgeryStrong.lean:262`); `RetainedCoreHistory.hasCanonicalCutoffRecords_appendEvent`, `toRetainedCoreEvent` (not opened).
- Named: `PinchingThroughSurgery`, `StrongNecksOfCutoffClass`, `FineCutNeckSupplyStrong` (supplied by caller). The Poincaré-standard discard property is produced inside the private factory (`hstdE`, `:141`), i.e. at depth 5.
- Checked and NOT an escalation: `p₀.delta := fun _ => 1/2` (`:91`) looks like a non-small surgery parameter, but `hasCanonicalCutoffRecords` (`CanonicalCapWindows.lean:103`) quantifies over a fresh parameter set p whose `delta` must be ≤ δbound = δb, and δb ≤ δmax is chosen small (`:63–70`); only p₀'s `fixed`, `modelRadius`, `modelOrder`, `modelAccuracy`, `recenterConstant` are carried. The records' neck scale (`GeometricCutoffRecord.nominal_small`, `GeometricCutoff.lean:208`, field `nominal_small`) is h < δ(t)² ρ(t) with the per-history δ.

**`pinchingThroughSurgery`** — `Surgery/Topology/PinchingThroughSurgery.lean:12`
- Statement: `PinchingThroughSurgery` (def `CanonicalNeighborhoodInduction.lean:239`): ∃ admissible pinching function φ such that every slab of every history in the cutoff class is φ-almost-nonnegative (Hamilton–Ivey). Hamilton–Ivey pinching through surgery (Hamilton–Ivey; Perelman II §4).
- Argument: take φ from `exists_admissiblePinchingFunction_for_identified_incomingSlabs`; choose δmax = ρmax = εcap = 1 (i.e. no smallness needed); the record family carried by the class hypothesis supplies what is needed.
- Calls (depth 5): `Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs` (`Surgery/Topology/HamiltonIveyPinching.lean:689`, read: fixed Hamilton–Ivey region `a₀` from the initial metric, propagated through every history with records by `ObservedHistory.fixedHamiltonIveyRegion_and_scalar_lower`, `HamiltonIveyPinching.lean:242/280/521`).
- Named: none (unconditional). See E3.

**`strongNecksOfCutoffClass`** — `PoincareEndgame.lean:33`
- Statement: `StrongNecksOfCutoffClass` (def `StrongNecksOfCutoffClass.lean:15`): canonical ⇒ strongly canonical (strong ε-necks, i.e. necks that exist backwards in time) at a higher threshold. Perelman II §4 strong δ-necks (Morgan–Tian, surgery chapters).
- Calls (depth 5): `strongNecksOfCutoffClass_of_strongSpatialCrossing` (`StrongNecksOfCutoffClass.lean:45`), `strongSpatialCrossingContinuation_holds` (`StrongSpatialCrossingContinuationLeaf.lean:243`).
- Named: `StrongSpatialCrossingContinuation` (def `StrongSpatialCrossingContinuation.lean:16`), discharged at depth 5 by the hypothesis-free `_holds`.

**`fineCutNeckSupplyStrong`** — `PoincareEndgame.lean:29`
- Statement: `FineCutNeckSupplyStrong` (def `Surgery/Contract/FineCutNeckSupplyStrong.lean:15`): at a singular time, the terminal core presentation has fine ε_c-necks at every curvature scale ≥ K·max(Λ/coreRadius², qcan, 1) (horns contain arbitrarily fine necks). Perelman II §3–4 (ε-horns and δ-necks deep in them).
- Calls (depth 5): `fineCutNeckSupplyStrong_holds` (`Surgery/Contract/FineCutNeckSupplyStrongLeaf.lean:18`, hypothesis-free).
- Named: none at this depth.

**`canonicalNeighborhoodsThroughSurgeryStrong_of_leaves`** — `CanonicalNeighborhoodsThroughSurgeryStrong.lean:272`
- Statement: pinching ∧ noncollapsing ∧ CN continuation ∧ spatial CN continuation ⟹ `CanonicalNeighborhoodsThroughSurgeryStrong`. The Perelman induction on surgery intervals.
- Argument: constants chosen in the dependency order ε → (C1,C2,τ,Ctime,Cgrad) → (C1s,C2s,Cs) → κ → thresholds; induction over k ∈ Fin(n+1) (`:318`): at step k+1 continue canonical/derivative/gradient/spatial bounds across slab k using `canonicalBefore_end_of_continuation_spatial` (open-closed continuity argument in time) with noncollapsing as the side condition; then the same on the terminal slab (`:361–380`).
- Calls (depth 5): `IncomingSlab.canonicalBefore_end_of_continuation_spatial` (`SpatialCanonicalContinuation.lean:65`), `exists_boundsOn_spatiallyCanonicalOn`, `exists_pos_fixedHamiltonIveyRegion_for_identified_histories` (`HamiltonIveyPinching.lean:666`), `noncollapsedBefore_zero` (`CanonicalNeighborhoodInduction.lean:186`, read: vacuous since r² ≤ t = 0), `terminalNoncollapsedBefore_start` (`:203`), `isContinuationSlab_event` (`:232`), monotonicity lemmas.
- Named: the four leaves, supplied by caller.

**`noncollapsingThroughSurgery`** — `PoincareEndgame.lean:60`
- Statement: `NoncollapsingThroughSurgery` (def `CanonicalNeighborhoodInduction.lean:250`): κ-noncollapsing on scales < ε for every history in the class, given pinching and canonical bounds up to t₀. Perelman II §5 (κ-noncollapsing through surgery via reduced volume; Morgan–Tian, noncollapsing chapter).
- Calls (depth 5): `noncollapsingThroughSurgery_of_reducedVolume_of_smallScale` (`NoncollapsingThroughSurgeryLeaves.lean:242`), `historyReducedVolumeMonotone` (`PoincareEndgame.lean:43` → `_holds`, `HistoryReducedVolumeMonotone.lean:189`), `historyReducedVolumeLocalUpperBound` (`:47` → `HistoryReducedVolumeLocalUpperBound.lean:31`), `historyReducedVolumeInitialLowerBound` (`:51` → `InitialRegularBlock.lean:510`), `smallScaleNoncollapsingThroughSurgery` (`:55` → `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace`, `SmallScaleNoncollapsingThroughSurgery.lean:522`).
- Named: `HistoryReducedVolumeMonotone`, `…LocalUpperBound`, `…InitialLowerBound` (defs `NoncollapsingThroughSurgeryLeaves.lean:96, 101, 113`), `SmallScaleNoncollapsingThroughSurgery` (def `:147`); all four discharged in `PoincareEndgame.lean:43–58` by hypothesis-free `_holds` / `_of_simplyConnectedSpace` theorems (depth 5–6). See E2.

**`canonicalNeighborhoodContinuation`** — `PoincareEndgame.lean:71`
- Statement: `CanonicalNeighborhoodContinuation` (def `CanonicalNeighborhoodInduction.lean:286`): canonical, derivative and gradient bounds that hold before t₀ (with noncollapsing and pinching) hold on [t₀, t₀+η). Perelman II §4–5 (the open part of the continuity argument: blow-up limits are κ-solutions).
- Calls (depth 5): `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing` (`CanonicalNeighborhoodContinuationLeaves.lean:284`), `deepContinuation` (`DeepContinuation.lean:213`), `capWindowContinuation` (`CapWindowContinuationLeaf.lean:366`), `crossingContinuation` (`PoincareEndgame.lean:67` → `crossingContinuation_holds`, `CrossingContinuationLeaf.lean:132`).
- Named: `DeepContinuation`, `CapWindowContinuation`, `CrossingContinuation` (defs `CanonicalNeighborhoodContinuationLeaves.lean:146, 188, 232`), discharged by hypothesis-free theorems at depth 5.

**`spatialCanonicalContinuation`** — `PoincareEndgame.lean:80`
- Statement: `SpatialCanonicalContinuation` (def `SpatialCanonicalContinuation.lean:144`): the spatial (single-time) canonical-neighbourhood version of the above.
- Calls (depth 5): `spatialCanonicalContinuation_of_spatialCrossing` (`SpatialCanonicalContinuationCases.lean:41`), `spatialCrossingContinuation` (`PoincareEndgame.lean:76` → `spatialCrossingContinuation_holds`, `SpatialCrossingContinuationLeaf.lean:193`).
- Named: `SpatialCrossingContinuation` (def `SpatialCrossingContinuation.lean:16`), discharged at depth 5.

Branches that entered Mathlib and stopped: `Diffeomorph.toHomeomorph`, `ChartedSpace.secondCountable_of_sigmaCompact`, `ChartedSpace.locallyCompactSpace`, `ChartedSpace.locallyPathConnectedSpace`, `IsCompact.elim_nhds_subcover`, `Homeomorph.ulift`, `IsManifold.empty`, `isOpenMap_of_continuous_injective` (invariance of domain, used at `Endgame.lean:27`), the `SimplyConnectedSpace` instances. No `External/` code was met at depth ≤ 4.

---

## 3. Escalations (ranked)

None of the escalations below is a found gap: at depth ≤ 4 every step that is an
argument reads as the standard one. They are the places where the Lean route
differs from, or does not let a reader confirm, the standard mathematics.

**E1 (medium, affects the whole audit): no docstrings anywhere on the route.**
Nine route files checked, zero `/--`/`/-!`. The mapping from Lean predicate to
literature theorem (e.g. `Moise352Open` ↔ Moise §35 Thm 2; `StrongNecksOfCutoffClass` ↔
Perelman's strong necks; `FineCutNeckSupplyStrong` ↔ fine necks deep in horns) is
by identifier and by the author's own reading of the `def`s in this report, not
by any claim the artifact makes. A reviewer cannot check "the docstring says X,
the Lean says Y" because the docstring side is empty.

**E2 (medium): noncollapsing goes through simple connectivity, unlike Perelman.**
Lean: `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace (P₀) [SimplyConnectedSpace P₀.Carrier]`
(`SmallScaleNoncollapsingThroughSurgery.lean:522`) uses
`exists_ball_volume_of_spatialCanonicalWitness_of_simplyConnected`
(`Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessBallVolume.lean:533`), whose
`round` case needs `SimplyConnectedSpace (connectedComponent x)` at every later
stage, supplied by `RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage`
(`StageComponentSimplyConnected.lean:24`). Standard: Perelman II §5 proves κ-noncollapsing through surgery for any normalized initial metric,
by reduced volume alone, with no topological input. Consequence: the Lean
surgery theory (canonical neighbourhoods through surgery included, since they
depend on noncollapsing) is only established for simply connected initial data.
That is enough for Poincaré and is mathematically sound *if* simple
connectivity of components does propagate through surgery (it does: in a simply
connected 3-manifold every 2-sphere separates and π₁ of a connected sum is the
free product). The propagation proof (`rfs_simply_connected_history`,
`initialIdentification_components_simplyConnected`,
`Extinction/Width/SurgeryWidthEvolution.lean:831`) is beyond depth 4 and must be read.
Also check that the round-component bound is the only reason, i.e. that small
spherical space forms S³/Γ with large Γ are what is being excluded.

**E3 (low–medium): Hamilton–Ivey pinching through surgery is proved with no smallness on surgery parameters.**
Lean: `pinchingThroughSurgery` returns `δmax = ρmax = εcap = 1` (`PinchingThroughSurgery.lean:17`),
i.e. pinching holds for every history carrying `GeometricCutoffRecord`s with any δ < 1.
Standard: pinching survives a surgery only because the standard cap glued in at
scale h ≪ δ² r is itself pinched and the gluing region is δ-close to a round
cylinder (Perelman II §4), which needs δ small. So either
`GeometricCutoffRecord` (`GeometricCutoff.lean:208`; parameters `:191`; its static caps via `StaticCapWitness`)
already carries the pinching of the output metric as a field or consequence, or
`ObservedHistory.fixedHamiltonIveyRegion_and_scalar_lower`
(`HamiltonIveyPinching.lean:242/280/521`) proves it from the record for all δ < 1.
Either is possible; the burden has moved into the record, and the constructor of
records (the private factory, E4) must then prove it with small δ. Read those
three lines of `HamiltonIveyPinching.lean` first.

**E4 (low, tooling/visibility): the surgery construction sits in private declarations.**
`uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong` reaches
`exists_horn_cutoff_record_of_fineCutNecks_of_le` and three siblings with
`open private … from …UniformDebitSurgeryStepOfFactory` (`UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:6–8`).
That private theorem (`UniformDebitSurgeryStepOfFactory.lean:39`) is where the
surgery event, the cutoff record, the standard-discard property and the volume
debit are actually produced — the core of Perelman's surgery existence. Private
names are mangled in the environment, so `cone.py`/`nosupplier.py` and
`#print axioms` tooling that works by name may not see it as a supplier. Nothing
unsound in `open private`; the point is that the most important depth-5 node is
hidden from name-level tools.

**E5 (low, tooling): a NOSUPPLIER false negative on the route.**
`NOSUPPLIER.md` lists `IncomingSlab.TerminalLimitMetric` (`MetricEvent.lean:74`
bundle, 86 sites) as `no_supplier`. On the route the `OrientedThreeStage` version is
supplied by `IncomingSlab.nonempty_terminalLimitMetric`
(`TerminalMetricExistence.lean:84`, used at
`UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:110`) — a real argument
(limit metric on the bounded-curvature region, derivative convergence), i.e. the
existence of the singular-time limit metric (Hamilton). The
`MetricEvent.lean` namesake may be a different structure; confirm before
quoting that row.

**E6 (low): off-route siblings carry named hypotheses the route avoids.**
`Surgery.smoothPoincareConjecture_of_poincareControlledExtinction` (`Surgery/Poincare.lean:36`, takes `hsum`),
`topologicalPoincareConjecture_of_smoothStructureInput` (`:56`, takes `hsm`, `hsmooth`),
`PoincareControlledExtinction.isPoincareStandard` (`ExtinctionReconstruction.lean:22`, takes `hsum`, `hsumClosed`),
`hext_of_…`/`smoothPoincareConjecture_of_uniformDebitSurgeryStepStrong_of_canonicalNeighborhoodsStrong`
(`CanonicalNeighborhoodsThroughSurgeryStrong.lean:239, 254`). The headline uses none
of them. A reader must not mistake their hypotheses for route obligations, nor
their discharge for evidence about the route.

---

## 4. Named open results met on the route (depth ≤ 4, plus their dischargers)

| predicate / bundle | definition | first taken as hypothesis by | discharged at |
|---|---|---|---|
| `PLApproximation n` | `PiecewiseLinear/Approximation.lean:18` | `exists_isManifold_of_plApproximation_of_plSmoothingCompact` (`PLSmoothingCompact.lean:59`) | `plApproximation_three` (`Moise352Producer.lean:27`) |
| `PLSmoothingCompact n` | `PLSmoothingCompact.lean:37` | same | `plSmoothingCompact_three` (`Moise352Producer.lean:30`) |
| `PLApproximationManifold n` | `PiecewiseLinear/Manifold.lean:156` | `plApproximation_of_plApproximationManifold` (`ApproximationManifold.lean:81`) | `plApproximationManifold_three` (`Moise352Producer.lean:24`) |
| `PLSmoothingModelCompact n` | `PLSmoothingCompact.lean:45` | `plSmoothingCompact_of_plSmoothingModelCompact` (`:52`) | `plSmoothingModelCompact_three` (`:411`), no hypotheses |
| `Moise352Open n` | `OpenSourceReduction.lean:210` | `plApproximationManifold_three_of_open` (`Moise352OfOpen.lean:17`) | `moise352Open` (`Moise352Producer.lean:18`) |
| `Moise352 n` | `Transition361.lean:256` | `plApproximationManifold_three_of_moise352` (`Endgame.lean:14`) | `moise352_three_of_open` (`Moise352OfOpen.lean:14`) |
| `Moise352InwardPush n` | not opened | `moise352_of_inwardPush_of_open` (`OpenSourceReduction.lean:226`) | `moise352InwardPush_three` (`Moise352InwardPushProof.lean:15`) |
| `Section34CellDiagram` | `Section34Endpoint.lean:59` | `moise352Open_of_section34CellDiagram` (`:88`) | `section34CellDiagram` (`Section34Terminal.lean:19`), no hypotheses; its callees are the depth-6 frontier |
| `smoothPoincareConjecture` (conclusion only) | `Surgery/Poincare.lean:30` | — | `smoothPoincareConjecture_of_controlledExtinction` |
| `hext : ∀ M g, Nonempty (PoincareControlledExtinction …)` | structure `ControlledExtinction.lean:14` | `smoothPoincareConjecture_of_controlledExtinction` (`Surgery/Poincare.lean:80`) | `exists_poincare_controlled_extinction` (`PoincareEndgame.lean:91`) |
| `UniformDebitSurgeryStepStrong` | `CanonicalNeighborhoodsThroughSurgeryStrong.lean:124` | `exists_…_of_uniformDebitSurgeryStepStrong` (`:192`) | `uniformDebitSurgeryStepStrong` (`PoincareEndgame.lean:38`) |
| `CanonicalNeighborhoodsThroughSurgeryStrong` | `CanonicalNeighborhoodsThroughSurgeryStrong.lean:69` | same | `canonicalNeighborhoodsThroughSurgeryStrong` (`PoincareEndgame.lean:84`) |
| `hproduce` (one-step producer, inline Prop) | inline, `SingularEventExtinction.lean:35–75` | `exists_…_of_singular_events_of_horizon_invariants` (`SingularEventExtinction.lean:33`) | built in `CanonicalNeighborhoodsThroughSurgeryStrong.lean:197–237` from `hstep`, `hcn` |
| `PinchingThroughSurgery` | `CanonicalNeighborhoodInduction.lean:239` | `uniformDebit…_of_strongNecks…` (`Contract/…:21`), `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` (`:272`) | `pinchingThroughSurgery` (`PinchingThroughSurgery.lean:12`), no hypotheses |
| `StrongNecksOfCutoffClass` | `StrongNecksOfCutoffClass.lean:15` | `uniformDebit…_of_strongNecks…` | `strongNecksOfCutoffClass` (`PoincareEndgame.lean:33`) ← `StrongSpatialCrossingContinuation` (def `StrongSpatialCrossingContinuation.lean:16`) ← `strongSpatialCrossingContinuation_holds` (`StrongSpatialCrossingContinuationLeaf.lean:243`), no hypotheses |
| `FineCutNeckSupplyStrong` | `Contract/FineCutNeckSupplyStrong.lean:15` | `uniformDebit…_of_strongNecks…` | `fineCutNeckSupplyStrong` (`PoincareEndgame.lean:29`) ← `fineCutNeckSupplyStrong_holds` (`Contract/FineCutNeckSupplyStrongLeaf.lean:18`), no hypotheses |
| `NoncollapsingThroughSurgery` | `CanonicalNeighborhoodInduction.lean:250` | `…_of_leaves` | `noncollapsingThroughSurgery` (`PoincareEndgame.lean:60`) ← four predicates below |
| `HistoryReducedVolumeMonotone` | `NoncollapsingThroughSurgeryLeaves.lean:96` | `noncollapsingThroughSurgery_of_reducedVolume_of_smallScale` (`:242`) | `historyReducedVolumeMonotone_holds` (`HistoryReducedVolumeMonotone.lean:189`) |
| `HistoryReducedVolumeLocalUpperBound` | `:101` | same | `historyReducedVolumeLocalUpperBound_holds` (`HistoryReducedVolumeLocalUpperBound.lean:31`) |
| `HistoryReducedVolumeInitialLowerBound` | `:113` | same | `historyReducedVolumeInitialLowerBound_holds` (`InitialRegularBlock.lean:510`) |
| `SmallScaleNoncollapsingThroughSurgery` | `:147` | same | `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace` (`SmallScaleNoncollapsingThroughSurgery.lean:522`) — see E2 |
| `CanonicalNeighborhoodContinuation` | `CanonicalNeighborhoodInduction.lean:286` | `…_of_leaves` | `canonicalNeighborhoodContinuation` (`PoincareEndgame.lean:71`) ← three below |
| `DeepContinuation` | `CanonicalNeighborhoodContinuationLeaves.lean:146` | `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing` (`:284`) | `deepContinuation` (`DeepContinuation.lean:213`) |
| `CapWindowContinuation` | `:188` | same | `capWindowContinuation` (`CapWindowContinuationLeaf.lean:366`) = `capWindowContinuation_of_slab_start_bounds … (exists_slice_bounds_at_slab_start …)` |
| `CrossingContinuation` | `:232` | same | `crossingContinuation_holds` (`CrossingContinuationLeaf.lean:132`) |
| `SpatialCanonicalContinuation` | `SpatialCanonicalContinuation.lean:144` | `…_of_leaves` | `spatialCanonicalContinuation` (`PoincareEndgame.lean:80`) ← `SpatialCrossingContinuation` (def `SpatialCrossingContinuation.lean:16`) ← `spatialCrossingContinuation_holds` (`SpatialCrossingContinuationLeaf.lean:193`) |

Every named predicate met is discharged, and every discharger at the leaves of
`PoincareEndgame.lean` has a signature with no Prop hypothesis. Whether those
`_holds` bodies bottom out in real mathematics is not established by this walk:
their bodies are depth 5 and deeper (§6). The only structure-valued hypothesis
supplied anonymously on the route at depth ≤ 4 is `TerminalLimitMetric` (E5).

Off-route named hypotheses (not obligations of the headline): `hsum`,
`hsumClosed`/`poincareStandardSumClosed` (discharged anyway by
`Topology.poincareStandardSumClosed_holds`, used at `Surgery/Poincare.lean:28`),
`hsm`, `hsmooth` (E6).

---

## 5. Computation, not read

For the independent-computation rung. Each is a step whose content the source
text does not show.

1. `Poincare.lean:17–20`: instance resolution after `let := C` and `let : IsManifold … := hC` — which `ChartedSpace` instance the callee's `[ChartedSpace]` and `[IsManifold]` binders pick up. It type-checks only if both refer to `C`; that is elaboration, not text.
2. `PoincareEndgame.lean:96–101`: `inferInstanceAs` and the definitional equality `(OrientedThreeStage.ofClosedOrientedManifold M).toClosedOrientedManifold ≡ M` needed for the `exact` to close `PoincareControlledExtinction M g` (structure eta; the propositional version is `rfl` after `cases`, `ClosedOrientedStage.lean:56–60`), and `P₀.Metric ≡ SmoothRiemannianMetric (𝓡 3) M.Carrier` (`ThreeModel` vs `𝓡 3`).
3. `Surgery/Poincare.lean:88`: `(by simp)` for `finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3`.
4. `StandardSphere.lean:17–21`: `by decide` (sphere orientation dimension), `simp`, `norm_num` for the sphere's connectedness side conditions.
5. `CanonicalNeighborhoodsThroughSurgeryStrong.lean:202–203` (`norm_num`: 1/22 < 1/11 etc.), `:262–270` (`nlinarith`, `field_simp` in `recenterConstant_mul_le_half`), `:295` (`positivity`), and the `min`/`max` bookkeeping `:296–305`, `:214–215`.
6. `UniformDebitSurgeryStepOfFineCutNeckSupplyStrong.lean:47–105`: numeric constants (tol = 1/1000, Dtrace > 64(r + tol⁻¹), `⌈tol⁻¹⌉₊ + 2`, `(2c)⁻¹`), `linarith`, `positivity`, `norm_num`.
7. `SingularEventExtinction.lean:103–106, 150–166`: `Fin.elim0`, `Fin.lastCases`, `Eq.mp`/`congrArg` casts for records on the appended history.
8. `PoincareStandard.lean:65` (`simp` for the empty connected sum), `PoincareStandardClassification.lean:60–66` (`simp` in list membership).
9. `PLSmoothingCompact.lean:395–405`: `simp`, `rw` chain for "boundary complex of K empty ⇒ boundary of M empty".
10. `ApproximationManifold.lean:81–175`: the `rw`/`simp` chains on `OpenPartialHomeomorph` sources/targets (bookkeeping, read as such, not verified).
11. Beyond depth 4 but visible: `SmallScaleNoncollapsingThroughSurgery.lean:533–579` (constants 3072, `L = 1 + Cgrad + 8 Ctime + 3072 (1+φ(1)+φ(0))²`, `nlinarith`), `HistoryReducedVolumeLocalUpperBound.lean:33` (constant `(4π)^{-3/2} e^{36}`).

---

## 6. Depth-5 frontier (unread bodies; start here)

Smooth branch, analytic core (highest priority first):

- `UniformDebitSurgeryStepOfFactory.lean:39` — PRIVATE `exists_horn_cutoff_record_of_fineCutNecks_of_le` (surgery existence, records, standard discards; E3, E4). Siblings `:280`, `:288`, `:295`.
- `Surgery/Topology/FiniteHorizonExtinction.lean:68` — `RetainedCoreHistory.exists_poincare_controlled_extinction_of_history_volume_debit` (read to `:140`: finite surgeries by volume debit, then extinction); next `FiniteHorizonContinuation.lean:49` `exists_closedSlab_extension_to_horizon_of_volume_debit` (Ricci flow continuation to the horizon), `Extinction/Families/ExtinctionTimeBound.lean:38` `isExtinctAtHorizon_of_historyWidth` (width argument), `Extinction/Width/CanonicalClass.lean:19` `canonicalWidth`, `Extinction/Families/ScalarThreshold.lean:11` `extinctionThreshold`, `ExtinctionExistenceReduction.lean:18` `exists_initialScalarBarrier_of_compact`.
- `Surgery/Topology/SmallScaleNoncollapsingThroughSurgery.lean:522` (E2) and `StageComponentSimplyConnected.lean:24`, `Extinction/Width/SurgeryWidthEvolution.lean:831`.
- `NoncollapsingThroughSurgeryLeaves.lean:242`; `HistoryReducedVolumeMonotone.lean:189`; `HistoryReducedVolumeLocalUpperBound.lean:31`; `InitialRegularBlock.lean:510`.
- `HamiltonIveyPinching.lean:689` (read), `:666`, `:242`, `:280`, `:521` (E3), `:82`, `:100`.
- `StrongNecksOfCutoffClass.lean:45`; `StrongSpatialCrossingContinuationLeaf.lean:243`.
- `Surgery/Contract/FineCutNeckSupplyStrongLeaf.lean:18`.
- `CanonicalNeighborhoodContinuationLeaves.lean:284`; `DeepContinuation.lean:213`; `CapWindowContinuationLeaf.lean:366`; `CrossingContinuationLeaf.lean:132`.
- `SpatialCanonicalContinuationCases.lean:41`; `SpatialCrossingContinuationLeaf.lean:193`; `SpatialCanonicalContinuation.lean:65` (`canonicalBefore_end_of_continuation_spatial`).
- `CapWindowCapWitness.lean:192` (`exists_capWindow_stronglyCanonicalWhere`); `TerminalMetricExistence.lean:84` (E5).

Smooth branch, topological core:

- `Topology/ThreeManifold/CutCapPoincareStandard.lean:15` (`componentwise_isPoincareStandard_of_poincareControlled`: one surgery reversed = connected sum), `:62`.
- `Topology/VanKampen/FiniteConnectedSumFreeProduct.lean:277`; `Topology/Algebra/Group/FreeProduct.lean:17`; `Topology/ThreeManifold/PoincareStandardOriented.lean:62` (read), `:86`; `exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group`, `exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle` (not located).
- `Geometry/Metric/Construction/Existence.lean:203`; `Bundle/Orientation/Section.lean:69`.
- `ClosedOrientedManifold.uliftDiffeomorph` (not located).

Moise branch:

- `ChartGluing.lean:207` → `exists_atlasOn_union_of_plApproximation` (not located).
- `OpenSourceReduction.lean:226`; `Moise352InwardPushProof.lean:15` → `LocallyFiniteInwardPush.lean:16`; `Endgame.lean:14` → `Transition361.lean:372`.
- `Section34Endpoint.lean:21` → `LabelledCellAssembly.lean:357`; `Section34Terminal.lean:19` → `Section34Normalization.lean:174`, `Section34FaceDisks.lean:36`, `Section34ResidualBalls.lean:33`, `Section34TargetRecognitionOfTiling.lean:796` (and the NOSUPPLIER `Section34*` rows beneath them).
- `Combinatorial.lean:263`; `DerivedNeighborhoodHandleFiltration.lean:18`; `PLSmoothingCompact.lean:245` (`isSmoothHandleStage_step`), `:78` (2-sphere recognition); `InteriorAtlas.lean:17, :33`; `Homeomorph/Transport.lean:12, :47`.
