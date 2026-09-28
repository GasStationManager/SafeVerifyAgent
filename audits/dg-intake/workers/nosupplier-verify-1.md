# NOSUPPLIER verification, worker 1

Artifact `differential-geometry` @ `7a48598d`, read-only. Nothing was compiled or elaborated.
Every `file:line` below was read with `sed -n`. Paths are relative to `DifferentialGeometry/`.
Scope: the 40 rows of "Top 40 by in-cone hypothesis sites" in `NOSUPPLIER.md`, the 7 further
rows whose `declared` path contains `Frontier`, plus `positiveRicciMetric` (a suspected false
positive the brief asked me to check). That is 48 predicates.

**What did not run.** No `lake build`, no `#print axioms`, no elaboration. "On route" below
means I read an application chain from an unconditional producer. I did not extract a proof
term. The route producers I read are `Poincare.lean:12`, `Surgery/Skeleton/PoincareEndgame.lean`,
`Topology/PiecewiseLinear/Moise352Producer.lean`, `LoopTheorem/Moise252Producer.lean`,
`Moise341Producer.lean` and `DimensionThree/PositiveRicci/Classification.lean:171`.

## Summary

**48 predicates: 44 SUPPLIED, 4 UNSUPPLIED, 0 left CONDITIONAL.** Every conditional chain was
followed to its leaf. The leaf was supplied in every case except `MetricCompactnessAssumptions`,
whose leaf is unsupplied, so it is counted UNSUPPLIED.

On the 47 required rows the split is 43 SUPPLIED and 4 UNSUPPLIED.

**0 of the 4 UNSUPPLIED predicates sit on a route-relevant theorem.** Their in-cone consumers
are in cone only because `cone.py` resolves generic short names (`refine`, `.trans`, `.mono`,
`.subseq`) to declarations; see instrument bug C1.

All 44 SUPPLIED verdicts disagree with the CSV status. Each disagreement has a named cause below
(N1–N6). None was averaged away.

### Structural bound on what this pass can find

`poincare_conjecture` (`Topology/ThreeManifold/Poincare.lean:12`) has no Prop hypotheses; its
binders are the statement's type-class assumptions. Its whole chain down to
`smoothPoincareConjecture_holds` (`PoincareEndgame.lean:103`) and `exists_isManifold_three`
(`Moise352Producer.lean:33`) is `..._holds` terms with no Prop arguments.

If the build succeeds with the three standard axioms (README claim, not re-checked here), then
no unsupplied named hypothesis can occur on the elaborated proof term. Every theorem applied
there has its arguments built. The no-supplier pass on this artifact can therefore find only:

- (a) dead or legacy branches, which is what the 4 UNSUPPLIED rows are, and
- (b) instrument errors.

The residual risk from the named-hypothesis convention moves to a different question. It is no
longer "is P ever built?" but "is the `XStatement : Prop` that a producer proves the right
statement?". That is the statement and vacuity rung, and it is the thing to hand an expert
(finding F2).

## Table

Column key:

- **Route**: 1 = a declaration concludes it; 2 = an in-proof `have`, `let`, record literal,
  `.mk` or `fun` argument builds it; 4 = it is a field of a structure that is itself supplied;
  5 = same-named twin.
- **stmt-def**: the predicate occurs inside `def XStatement : Prop := ∀ …, ∃ a : P, …`, and that
  statement is discharged by `theorem x : XStatement`.
- **Route-relevant consumer** is an in-cone theorem taking the predicate as a hypothesis, with a
  note on what it is for.

| # | predicate | csv status | verdict | route | supplier / refutation `file:line` | route-relevant consumer | note |
|---|---|---|---|---|---|---|---|
| 1 | `CheegerGromovCompactness.NetLimitData` | conditional | SUPPLIED | 1 | `exists_netLimitData_with_stable_intersections` `Geometry/Compactness/CheegerGromov/Covering/GoodCovering/Sequence.lean:687` (→ `nonempty_netLimitData` :148), invoked via `exists_stable_net` `…/Gluing/MetricCompactness/Assumptions.lean:147` at `…/ApproximateIsometry/PairwiseApproximation/BoundedGeometry.lean:324` | `BoundedGeometryNormalChartData.has_pairwise_approximate_isometries_of_radius_tails` `PairwiseApproximation/BoundedGeometry.lean:192`: Cheeger–Gromov pairwise approximate isometries inside Hamilton's blow-up limit (on route via `Classification.lean:72-78`) | N1. The chain dies at leaf `FlowDerivBounds`, which is built by an in-proof `have hsp : FlowDerivBounds … := by refine { … }` at `Geometry/Flow/RicciFlow/DimensionThree/PositiveRicci/Compactness/SmoothFlowLimit.lean:1185` and packed into `{ spacetime := hsp, atZeroGeom := hsp.atTime hzero }` at :1266. Suspected FP confirmed. |
| 2 | `CheegerGromovCompactness.InjectivityRadiusDecay` | conditional | SUPPLIED | 1 | `injectivityRadiusDecayOfBoundedGeometry` `…/BoundedGeometry/InjectivityRadiusDecay/Existence.lean:151`, called at `…/Pointed/Compactness/BoundedGeometry.lean:32` in `metricCompactSeedOfBoundedGeometry` (:23), called on route at `Classification.lean:72` | `nonempty_bounded_geometry_normal_chart_data` `…/NormalChart/Existence.lean:301`: normal charts for the CG limit | N1, same leaf as #1. Suspected FP confirmed. |
| 3 | `Topology.PiecewiseLinear.SingularTwoCell` | conditional | SUPPLIED | 1 (stmt-def) + 2 | `∃ (A : SingularTwoCell …) (_ : NormalSingularCellData A Bd B)` inside `GeneralPositionInDoubleBufferedStatement` `Topology/PiecewiseLinear/LoopTheorem/LemmaTwoBuffered.lean:97/123`, discharged by `generalPositionInDoubleBuffered` `Topology/PiecewiseLinear/GeneralPositionInDouble.lean:876`, used by `moise252` `LoopTheorem/Moise252Producer.lean:14`; also `let D : SingularTwoCell M` `LoopTheorem/CellGluing.lean:570` (in cone) | `NormalSingularCellData.exists_adaptedCleanCap_of_disjoint_innermost_cleanDisk` `LoopTheorem/AdaptedCleanCap.lean:26`: loop-theorem descent step, Moise §2.5, on the Moise route (`exists_isManifold_three`) | N3. The chain reported an out-of-cone `CrossSeamTubeData` supplier. |
| 4 | `…PiecewiseLinear.NormalSingularCellData` | conditional | SUPPLIED | 1 (stmt-def) | same `∃` at `LemmaTwoBuffered.lean:123`, discharged at `GeneralPositionInDouble.lean:876` | same as #3 | N3 |
| 5 | `…CurveShortening.ProductCurve.SmoothOn` | no_supplier | SUPPLIED | 4 | field `smooth : c.SmoothOn J` of `ProductCurve.IsSolutionOn` (`Geometry/Flow/RicciFlow/Extinction/CurveShortening/Product.lean:134-136`); the parent is supplied by `rfs_family_deformation` `Extinction/Families/Deformation.lean:978` (`∀ p, (solutions p).IsSolutionOn …`) | `ProductCurve.field_smoothOn_X` `CurveShortening/ProductCurveFieldRegularity.lean:22`: regularity for curve-shortening in the width/extinction argument (`isExtinctAtHorizon_of_historyWidth` chain) | N2. The dot-notation supplier is unresolvable because the short name is not unique. Suspected FP confirmed. |
| 6 | `…MetricCompactSeedWithDivisor` | conditional | SUPPLIED | 1 | `MetricCompactSeed.withDivisor` `Gluing/MetricCompactness/Assumptions.lean:57`, invoked at `PairwiseApproximation/BoundedGeometry.lean:309`; its `MetricCompactSeed` is the record literal at `Pointed/Compactness/BoundedGeometry.lean:39` | `MetricCompactSeedWithDivisor.exists_stable_net` `Assumptions.lean:147`: stable net for the CG gluing | N1 (FlowDerivBounds leaf). The chain went via `toSeed`/`MetricCompactBase` (dead). |
| 7 | `…CurveShortening.CurveMap.Field.SmoothOn` | no_supplier | SUPPLIED | 1 | `ProductCurve.field_smoothOn_X` `ProductCurveFieldRegularity.lean:22` (concludes `(c.X).SmoothOn J`); also `field_smoothOn_unitTangent` :138 (in cone) | `ProductCurve.chartRepAt_differentiableAt_of_field_smooth` `CurveShortening/ProductCoveringDerivative.lean:43`: derivative of the covering lift in the CSF estimates | N2. Also, the CSV's example sites include `AreaEvolution/Basic.lean:694`, which is `(curveOfLoopFamily γ).SmoothOn`, i.e. the CurveMap twin. The site count 190/107 pools twins. |
| 8 | `…InjectivityRadiusDecay.PackingBound` | conditional | SUPPLIED | 1 | `packInputOfBg` `Covering/VolumeOverlap.lean:179`, called at `Pointed/Compactness/BoundedGeometry.lean:37` (on route) | field `packAll` of `MetricCompactSeed` (`Assumptions.lean:50`), consumed by `withDivisor` :57 on route | N1 (FlowDerivBounds leaf) |
| 9 | `…PiecewiseLinear.NormalSingularSetTriangulation` | conditional | SUPPLIED | 1 | `nonempty_normalSingularSetTriangulation_of_piece` `LoopTheorem/SingularSetOfCell.lean:192` (in cone), conditional on `SingularTwoCell` (#3, supplied) | `NormalSingularSetTriangulation.isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary` `LoopTheorem/BranchCarrier.lean:441`: branch analysis in the loop theorem | N3 via chain |
| 10 | `…BoundedGeometryNormalChartData` | conditional | SUPPLIED | 1 | `nonempty_bounded_geometry_normal_chart_data` `…/NormalChart/Existence.lean:301`, called on route at `Classification.lean:75` | `MetricCompactSeed.higherRegularityCanonicalMetricCompactness` `Pointed/Compactness/NormalCharts.lean:22`: smooth CG limit of Hamilton blow-ups | N1 |
| 11 | `…Surgery.IncomingSlab.TerminalLimitMetric` | no_supplier | SUPPLIED | 1 | `OrientedThreeStage.IncomingSlab.TerminalLimitMetric.toSurgery` `Surgery/Topology/EventBridge.lean:27` (type `(G.toSurgery).TerminalLimitMetric`, in cone). It rests on the `Topology` twin, built e.g. by `ClosedSlab.endpointTerminalLimitMetric` `Surgery/Topology/SlabTerminalConvergence.lean:139` | field `terminal` of `Surgery.MetricCutCapEvent` `Surgery/Topology/MetricEvent.lean:83` (closed-manifold event bridge); the CSV's site `Surgery/Contract/HornCutoffRecord.lean:724` is on the horn-cutoff surgery route | N2. Dot notation, twin short name (`unique=NO`). |
| 12 | `…MetricCompactnessAssumptions` | conditional | **UNSUPPLIED** (CONDITIONAL, leaf unsupplied) | – | Suppliers are `ofBase` `Assumptions.lean:396` (needs `MetricCompactBase`) and `MetricCompactBase.exists_center_of_mass_on_source` `Gluing/CenterMap/Construction/Support.lean:846` (needs `MetricCompactBase`). `MetricCompactBase` is built only by `toBase` :384, which needs `MetricCompactnessAssumptions`. This is a cycle with no base. Its fields `normalBounds`/`normalRadius` (#14, #38) have no constructor anywhere. | none on route. Consumer: `HasStageSeed.refine` `Gluing/StageConstruction/Seed.lean:96`, the legacy stage construction. It is in cone only via `smoothPoincareConjecture_holds → MetricComparisonOn.trans → HasStageSeed.refine` (the `.trans` / `refine` short-name bug, C1). The route uses the `…On` / `MetricCompactSeed` variants (`NormalCharts.lean:22-44`, `Seed.lean:59,86`). | Agrees with CSV in substance: a dead legacy interface. |
| 13 | `…HamiltonPositiveRicci.HamiltonFiniteTimeFlow` | conditional | SUPPLIED | 1 | `exists_hamilton_finite_time_flow_on_closed_open` `DimensionThree/PositiveRicci/Extinction.lean:35`, used on route at `Classification.lean:180`; leaf `positiveRicciMetric` supplied (#48) | `hamilton_constant_positive_sectional_curvature_of_pinching` `Classification.lean:148`: Hamilton's positive-Ricci theorem, used for compact ancient κ-solutions → spherical space form (`CompactAncientSphericalCover.lean:24`) | N1, cascaded from #48 |
| 14 | `…NormalCoordMetricBounds` | no_supplier | **UNSUPPLIED** | – | Structure `…/NormalCoordinates/Metric/Bounds.lean:128`. It appears only as a field of `MetricCompactBase` (`Assumptions.lean:178`) and `MetricCompactnessAssumptions` (:358). No `where`, `.mk`, `⟨…⟩` or `metricC … :=` builder of this type exists; the `metricC_nonneg :=` hits all build other structures. | none on route. `MetricCompactnessAssumptions.exists_live_metric` `NormalCoordinates/Metric/Convergence.lean:29` is legacy; the route uses `BoundedGeometryNormalChartData`. | Agrees |
| 15 | `…ProductCurve.ImmersedOn` | conditional | SUPPLIED | 4 | field `immersed` of `ProductCurve.IsSolutionOn` (`Product.lean:136`), parent supplied at `Deformation.lean:978` | `ProductCurve.exists_projection_immersedOn_areaError_le` `CurveShortening/ProjectedAreaVariation.lean:203` (uses `hc.immersed`): area-error control in width monotonicity | N2 and N6. The CSV's credited supplier `ProjectedAreaVariation.lean:203` concludes `c.projection.ImmersedOn`, the **CurveMap** twin. That is route 5 and must not be credited. |
| 16 | `…Surgery.Topology.SmoothCutCapTransition` | no_supplier_in_cone | SUPPLIED | 2 | `let X : SmoothCutCapTransition … := @SmoothCutCapTransition.mk …` `Surgery/Topology/BufferedMetricCutCapEvent.lean:108-112`, in `exists_metricCutCapEvent_boundaryFrameReversing_of_buffered_finite_caps_trace` (:54, in cone, on the `uniformDebitSurgeryStepStrong` route) | `SmoothCutCapTransition.toSphericalCapping` `Surgery/Topology/SphericalCappingCompletion.lean:233`: topology of a surgery event | N1 (`.mk` inside `let`) |
| 17 | `…PiecewiseLinear.IsHandleDecompositionOfTube` | no_supplier_in_cone | SUPPLIED | 1 (stmt-def) | `∃ …, IsHandleDecompositionOfTube …` in `Moise323` `Topology/PiecewiseLinear/PseudoCell.lean:407/419`, discharged by `moise323` `Section32PseudoCell.lean:260`, obtained on route at `Section33TubeApproximation.lean:321` (`moise331OnTube_of_…` :302 ← `Moise341Producer.lean:14`) | `exists_isPolyhedralTubeNeighborhood` `PolyhedralTubeNeighborhoodExists.lean:168`: Moise §3.3 tube approximation | N3 |
| 18 | `…ProductCurve.IsSolutionOn` | no_supplier | SUPPLIED | 1 | `rfs_family_deformation` `Families/Deformation.lean:978` (`∀ p, (solutions p).IsSolutionOn …`, in cone d=17) | `rfs_uniform_ramp_alternative` `Deformation.lean:933`: Colding–Minicozzi-type width deformation step in finite extinction | N2 |
| 19 | `…Section34FaceBallInvariants` | conditional | SUPPLIED | 1 | `exists_section34FaceBalls` `Section34FaceBalls.lean:624`, conditional on #20 (supplied) | `exists_section34TerminalFaceBalls` `Section34TerminalFaceBalls.lean:196`: Moise §3.4 cell diagram (`section34CellDiagram` `Section34Terminal.lean:19`) | N3 via chain |
| 20 | `…Section34GraphFrame` | no_supplier | SUPPLIED | 4 (conjunct) + 1 (stmt-def) | third conjunct of `Section34NormalPlus` (`Section34Frame.lean:621`), which is supplied (#34); also obtained from `ControlledGraphNeighborhoodStatement` at `Section34Normalization.lean:97` | `section34Trace_of_noOperation` `Section34TraceNormalization.lean:27` | N3 |
| 21 | `…HamiltonBlowup` | conditional | SUPPLIED | 1 | `exists_hamilton_blowup_point_sequence` `PositiveRicci/Blowup.lean:506`, on route at `Classification.lean:187` | `Classification.lean:148` (as #13) | cascaded from #48 |
| 22 | `…Section34CompactFaceBallInvariants` | no_supplier | SUPPLIED | 2 | `have hinv₁ : Section34CompactFaceBallInvariants …` `Section34Compact.lean:182`, in `moise341OnNeighborhood` (:163, on route via `moise341` `Moise341Producer.lean:21`) | `exists_compactFaceDisks` `Section34CompactFaceDisks.lean:26` | N1 (hint pointed here correctly) |
| 23 | `…Width.SmoothWeaklyMonotoneCircleMap` | no_supplier_in_cone | SUPPLIED | 2 + 1 | `let σ : SmoothWeaklyMonotoneCircleMap := { … }` `Extinction/Width/PlateauExistence.lean:32`; `∃ σ : SmoothWeaklyMonotoneCircleMap` concluded by `conformal_disk_producer` :54 (in cone d=22) | `leastArea_slope_le_of_conformal_minimizing_disk` `CurveShortening/AreaEvolution/MinimizingDisk.lean:438`: least-area slope bound (Plateau) in width monotonicity | **N4.** `split_sig` splits at the *last* top-level `:`, which in :54 is `∀ v : SmoothDisk` *after* `∃ σ : SmoothWeaklyMonotoneCircleMap`. So a real supplier was read as a hypothesis site. |
| 24 | `…InjectivityRadiusDecay.RealizesDistance` | conditional | SUPPLIED | 1 | `injectivity_radius_decay_realizes_distance` `…/InjectivityRadiusDecay/Existence.lean:772`, called at `Pointed/Compactness/BoundedGeometry.lean:34` | `nonempty_bounded_geometry_normal_chart_data` `NormalChart/Existence.lean:301` | N1 |
| 25 | `…hamiltonBlowupPointSelection` | conditional | SUPPLIED | 1 | `Blowup.lean:506` (the `∃ Q, hamiltonBlowupPointSelection P Q`), on route at `Classification.lean:187` | `hamiltonSourceCompactnessBounds` `SmoothFlowLimit.lean:1159` | cascaded from #48 |
| 26 | `Topology.SphericalCapping` | conditional | SUPPLIED | 1 (+4) | `SmoothCutCapTransition.toSphericalCapping` `SphericalCappingCompletion.lean:233` (in cone), conditional on #16; also field `capping` of `SphericalCutCapTransition` `Topology/ThreeManifold/CutCap.lean:142` | `SphericalCapping.component_meets_core` `Surgery/Topology/SphericalCappingBridge.lean:132` | cascaded from #16 |
| 27 | `…Section34CompactFaceDiskFamily` | conditional | SUPPLIED | 1 | `exists_compactFaceDisks` `Section34CompactFaceDisks.lean:26`, conditional on #22 (supplied) and `compactTrace_of_noOperation` (`Section34Compact.lean:205`) | `Section34CompactCutFrame.exists_residualBall` `Section34CompactResidualBall.lean:103` | cascaded from #22 |
| 28 | `Topology.disjointInl` | no_supplier | SUPPLIED | 1 (unfolded) | Private `abbrev` (`ConnectedSum/AssociativeFlattening.lean:59`). Its *body* is supplied by `exists_disjointOrientedBallChart_closedBall`, obtained at `AssociativeFlattening.lean:728` in `connectedSumAssociative_of_flatteningIsoCanonical` (:725). `ConnectedSumFlatteningIsoCanonical` (:712) states the body, not the name. | `factorChartInl` (AssociativeFlattening ~:78) → `connectedSumAssociative_holds` :1559 (in cone): associativity of connected sum, used in the prime-decomposition endgame | N5 |
| 29 | `Topology.SmoothBoundaryAtlas` | conditional | SUPPLIED | 1 | `NeckFrontierState.exists_boundaryAtlas` `Geometry/Neck/SpatialCapEnd.lean:491` (in cone), conditional on #39 (supplied) | `PairedBallGluing.exists_finite_connectedSum_diffeomorph` `Topology/ThreeManifold/PairedBallFinite.lean:373` | cascaded from #39 |
| 30 | `…IsPolyhedralTubeNeighborhood` | conditional | SUPPLIED | 1 | `exists_isPolyhedralTubeNeighborhood` `PolyhedralTubeNeighborhoodExists.lean:168`, on route at `Section33TubeApproximation.lean:324`; conditional on #17 | `exists_hasConnectedHandlePieces` `PolyhedralTubeHandlePieces.lean:519` (called :326) | cascaded from #17 |
| 31 | `…Section34FaceDiskFamily` | conditional | SUPPLIED | 1 | `exists_section34FaceDisks` `Section34FaceDisks.lean:36`, on route at `Section34Terminal.lean:36`; conditional on #34 | `exists_section34ResidualBalls` `Section34ResidualBalls.lean:33` | cascaded from #34 |
| 32 | `Topology.disjointInr` | no_supplier | SUPPLIED | 1 (unfolded) | as #28 (`AssociativeFlattening.lean:55`, supplied at :728) | `factorChartInr` :63 → `connectedSumAssociative_holds` | N5 |
| 33 | `…HasLocalCurvDerivBound` | no_supplier_in_cone | SUPPLIED | 2 + 1 | `have hjetsX : ∀ R … ∀ᶠ n, HasLocalCurvDerivBound …` `Compactness/Limits/LocalPointedFlowLimit.lean:276`; theorem `exists_terminal_normalized_inner_ball_curvature_derivative_bounds_of_backward_traces` `Surgery/Topology/TracedTerminalCompactness.lean:110` (in cone) concludes it | `exists_pointed_convergence_on_base_components_of_eventually_compact_balls` `…/Pointed/Compactness/CompactBalls.lean:206`: pointed CG convergence for flow limits | N1, and **N4b.** The statement at :110 opens its conclusion with `let X : … := { … }`, and `split_sig` cuts the signature at that top-level `:=`. |
| 34 | `…Section34NormalPlus` | no_supplier | SUPPLIED | 1 (stmt-def) | `Section34NormalFamilyStatement` `Section34Normalization.lean:77` (body `∃ …, Section34NormalPlus …` :90), discharged by `section34NormalFamilyStatement` :174, obtained on route at `Section34Terminal.lean:34-35` | `exists_section34FaceDisks` `Section34FaceDisks.lean:36` | N3 |
| 35 | `Schoenflies.CellStructure.SplitData` | no_supplier | SUPPLIED | 2 | `let d : T.str.SplitData := { … }` `External/Schoenflies/FiniteTransfer.lean:1223`, in `exists_sourceEarStepData` (in cone d=23; Schoenflies is on the Moise route) | field `splitData` of `SourceEarStepData` `FiniteTransfer.lean:1105` | N1 and N2 (`T.str.SplitData` dot type) |
| 36 | `…NormalSingularSetTriangulation.IsBoundaryBranch` | conditional | SUPPLIED | 1 | `isBoundaryBranch_of_mem_branchComplex_space_of_map_mem_boundary` `LoopTheorem/BranchCarrier.lean:441`, conditional on #9 | `NormalSingularCellData.exists_descendingSurgery_of_disjoint_innermost_cleanDisk` `LoopTheorem/DescentStepOrientable.lean:44` | a case predicate (branch meets ∂), not an open result |
| 37 | `…CheegerGromovCompactness.BInter` | conditional | SUPPLIED | 1 | `exists_netLimitData_with_stable_intersections` `GoodCovering/Sequence.lean:687` gives eventually `BInter ∨ ¬BInter` (see `exists_stable_net` `Assumptions.lean:147-158`) | `IsStableNet` `Gluing/StageConstruction/Seed.lean:33` | a case predicate; N1 leaf |
| 38 | `…NormalRadiusProfile` | no_supplier | **UNSUPPLIED** | – | Structure `…/NormalCoordinates/RadiusProfile.lean:25`, a field only of `MetricCompactBase` (`Assumptions.lean:179`) and `MetricCompactnessAssumptions` (:360). No builder; `le_exp_radius :=` / `ratio_pos :=` grep finds none for this type. | none on route. `NormalRadiusProfile.phaseRadius` `NormalCoordinates/Phase/Smallness.lean:34` is legacy. `.subseq` has 734 name-level consumers (C1). | Agrees |
| 39 | `…FiniteHorn.NeckFrontierState` (Frontier) | no_supplier | SUPPLIED | 2 | `let W₀ : NeckFrontierState g eps ι := NeckFrontierState.mk W … sphere …` `Geometry/Neck/SpatialCapEnd.lean:894`, in `exists_saved_end_decomposition_of_anchors` (:829, in cone d=11) → … → `exists_neckRadius_terminalCorePresentation_…` (terminal-core presentation on the surgery route); also `FiniteFrontierEnd.lean:1745` (out of cone) | `NeckFrontierState.exists_boundaryAtlas` `SpatialCapEnd.lean:491` | N1. The type is private, reached via `open private … from` (`CanonicalProperEnd.lean:14-24`). "Frontier" here means the topological frontier of a region, not the open-result convention (F5). |
| 40 | `…CurveShortening.SmoothMetricWindow` | no_supplier_in_cone | SUPPLIED | 4 (+1) | `RicciBackground … extends SmoothMetricWindow` `CurveShortening/Basic.lean:167`; `RicciBackground` concluded by `∃ B : RicciBackground …` `Extinction/Families/ActualWidth.lean:80` (in cone) and `let B' : RicciBackground …` `Families/ClassWidth.lean:158` | `curveShorteningLocalUniqueness_of_compact` `CurveShortening/ParabolicUniqueness.lean:212` | route 4 is not credited by design; the hint was right |
| 41 | `…FiniteHorn.RecordedNeckSphere` (Frontier) | conditional | SUPPLIED | 2 | `let sphere := fun i => RecordedNeckSphere.mk (point i) (neck i) (level i) …` `SpatialCapEnd.lean:891` (in cone); also `⟨p, nk, 3, …⟩` `FiniteFrontierEnd.lean:341` | field `sphere` of `NeckFrontierState` `FiniteFrontierEnd.lean:74` | N1 |
| 42 | `…FiniteHorn.OrdinaryNeckMoveAt` (Frontier) | conditional | SUPPLIED | 1 | `NeckFrontierState.exists_step_at_of_neck_central` `FiniteFrontierEnd.lean:297` (a disjunct of the conclusion; in cone), called at `SpatialCapEnd.lean:190`; conditional on #39 | `spatial_cap_fair_frontier_process` `SpatialCapEnd.lean:229` | cascaded from #39; a move predicate, not an open result |
| 43 | `…curveShorteningTotalCurvatureBound` (Frontier) | no_supplier_in_cone | SUPPLIED | 2 (+1 out of cone) | `have hcurv : curveShorteningTotalCurvatureBound B := by intro …` `Extinction/Families/Flow.lean:617`, in `rfs_ramp_area_bounds` (:612, in cone), invoked on route at `Deformation.lean:963`; unconditional `rfs_csf_total_curvature_bound` `CurveShortening/TotalCurvatureSlope.lean:216` (out of cone) | `rfs_csf_projection_upper_control` `CurveShortening/ProjectedAreaBounds.lean:25`: projected least-area upper control | N1 (hinted) |
| 44 | `…HasBoundaryIsotopyVelocityExtension` (Frontier) | no_supplier_in_cone | SUPPLIED | 2 | `fun _ hγ hi hemb => loopFamilyVelocityExtension_of_smoothOn …` passed as the `hfront` argument at `CurveShortening/AreaEvolution/Basic.lean:800-801` in `rfs_csf_boundary_isotopy` (:788, in cone); producer `VelocityExtensionChartReading.lean:286`; unconditional `loopFamilyVelocityExtensionProducer_holds` :296 (out of cone; `↔` by `⟨fun h => h, fun h => h⟩` at `VelocityExtensionProducer.lean:24`) | `rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension` `BoundaryIsotopyFrontier.lean:47`: boundary isotopy along CSF in width monotonicity | N1 (a `fun` term as an argument, not even a `have`) |
| 45 | `…Families.PreparedFamilyFrontier` (Frontier) | no_supplier_in_cone | SUPPLIED | 2 | `apply rfs_prepared_family_of_preparedFamilyFrontier …; refine { profile := P … }` `Extinction/Families/PreparedFamily.lean:83-96`, in `rfs_prepared_family` (:21, in cone d=18, only `heta : 0 < eta` as a Prop hypothesis) | `rfs_prepared_family_of_preparedFamilyFrontier` `PreparedFamilyFrontier.lean:144`: polygonal preparation of the sweepout | N1 (record literal against the expected type from `apply`) |
| 46 | `…Surgery.Topology.GeometricCutoffFrontier` (Frontier) | no_supplier_in_cone | SUPPLIED | 2 | `let frontier : GeometricCutoffFrontier H i p := by refine { … }` `Surgery/Contract/HornCutoffRecord.lean:209`, in `exists_geometricCutoffRecord_of_preparedEventGeometry` (in cone d=10) | `GeometricCutoffRecord.ofFrontier` `Surgery/Topology/GeometricCutoffFrontier.lean:218`: builds the cutoff record for a surgery event | N1 (hinted) |
| 47 | `…GeometricCutoffRecord.TerminalParentRegionConvexity` (Frontier) | no_supplier | **UNSUPPLIED** | – | Prop def `Surgery/Topology/ChildComparisonFrontierReduction.lean:148`. All 16 grep hits are the def, `.mono` (:171) or binders (:203, :229, :244, :257, :273; `ChildComparisonInputReduction.lean:241,282`; `CoreRestrictedDistanceComparison.lean:282,406`). No producer. | none on route. Consumer: `collapseDegreeMetricHalfFrontier_of_regionMetricHalfFrontier_and_noShortcut` `CoreRestrictedDistanceComparison.lean:402` (out of cone): child/parent distance comparison. In cone only via `.mono` (152 name-level consumers, C1). | Agrees. A genuine open result on an abandoned reduction. |
| 48 | `Geometry.Curvature.positiveRicciMetric` (extra) | no_supplier_in_cone | SUPPLIED | 2 | `have hric : positiveRicciMetric (F.S.base.metric 0) := by intro x v hv …` `Perelman/KappaSolutions/CompactAncientSphericalCover.lean:32` (in cone d=15). Confirmed that the named supplier `HasPositiveSectionalCurvature.positive_ricci_metric` `Geometry/Curvature/PositiveSectionalRicci.lean:21` is out of cone. | `exists_hamilton_finite_time_flow_on_closed_open` `PositiveRicci/Extinction.lean:35` | N1. Suspected FP confirmed; the cascade flips #13, #21, #25. |

## Findings worth an expert (ranked by route relevance)

**F1. No unsupplied named hypothesis reaches the headline.**

- The four UNSUPPLIED predicates are `MetricCompactnessAssumptions`, `NormalCoordMetricBounds`,
  `NormalRadiusProfile` and `TerminalParentRegionConvexity`.
- The first three form one closed cycle with no base: `MetricCompactnessAssumptions ← ofBase ←
  MetricCompactBase ← toBase ← MetricCompactnessAssumptions`, and the two normal-coordinate
  fields have no constructor.
- That cycle is a legacy Cheeger–Gromov interface. The route replaced it with
  `MetricCompactSeed` + `BoundedGeometryNormalChartData` + the `…On` stage predicates
  (`NormalCharts.lean:22`, `PairwiseApproximation/BoundedGeometry.lean:286`, called from Hamilton
  at `Classification.lean:72-78`).
- Their 84 / 80 / 31 "in-cone sites" are cone artifacts (C1).
- Any paper-alignment or reuse claim citing a theorem stated over `MetricCompactnessAssumptions`
  or `MetricCompactBase` cites an unreachable theorem and must be marked dead.

**F2. The Moise route discharges its open results through `XStatement : Prop` definitions.**

- Examples: `Moise323` (`PseudoCell.lean:407`), `GeneralPositionInDoubleBufferedStatement`
  (`LemmaTwoBuffered.lean:97`), `Section34NormalFamilyStatement` (`Section34Normalization.lean:77`),
  `ControlledGraphNeighborhoodStatement`, `Moise252`, `Moise331OnTube`, `Moise352Open`.
- Each is proved by a theorem (`moise323`, `generalPositionInDoubleBuffered`,
  `section34NormalFamilyStatement`, …), so supply is not the risk.
- The risk is statement fidelity: whether each `XStatement` says what Moise's lemma says, and is
  not vacuous or weakened. An expert should diff these defs against Moise, *Geometric Topology in
  Dimensions 2 and 3*, §2.5, §3.2–3.4, §35.
- This is the natural next audit rung for the Moise half. It is invisible to both `#print axioms`
  and the no-supplier pass.

**F3. `TerminalParentRegionConvexity` is a genuine, never-discharged open result.**

- It is a local convexity of the parent region for distance comparison
  (`ChildComparisonFrontierReduction.lean:148`).
- It sits on an abandoned reduction (`CoreRestrictedDistanceComparison.lean:402`, out of cone).
- It is harmless to the headline. It matters only if the README or any docs present the
  `…_of_regionMetricHalfFrontier_and_noShortcut` path as proved.

**F4. The Hamilton positive-Ricci branch is genuinely on route and fully supplied.**

- The route runs `nonempty_positiveComponent_of_compact_nonround_ancientKappa` →
  `exists_spherical_cover_of_compact_ancientKappa` → `hamilton_positive_ricci`.
- In that branch the CG compactness data are built by record literals inside
  `hamiltonSourceCompactnessBounds` (`SmoothFlowLimit.lean:1185,1266`).
- A reader checking "Hamilton 1982 is proved, not assumed" should read that def. It is the one
  place `FlowDerivBounds` exists, and it carries the Shi-type derivative bounds.

**F5. The `Frontier` file-name heuristic in INTAKE.md over-selects.**

- `Geometry/Neck/FiniteFrontierEnd.lean` uses "frontier" for the topological boundary of a
  region. Its `NeckFrontierState`, `RecordedNeckSphere` and `OrdinaryNeckMoveAt` are private
  process states, not open results.
- Of the 8 `Frontier`-path rows, 7 are SUPPLIED; `TerminalParentRegionConvexity` is the only
  real open result.

## Instrument bugs

`nosupplier.py` (all 44 SUPPLIED rows disagree with the CSV; causes, with the rows they flip):

- **N1. Route-2 constructions are invisible, and one invisible leaf flips a whole cluster.**
  - Forms seen: `have`/`let x : P :=`, `refine {…}`, `@P.mk`, a `fun` passed as an argument.
  - Directly: #16, 22, 35, 39, 41, 43, 44, 45, 46, 48.
  - By cascade:
    - `FlowDerivBounds` (`SmoothFlowLimit.lean:1185`) → #1, 2, 6, 8, 10, 24, 37.
    - `positiveRicciMetric` → #13, 21, 25.
    - `NeckFrontierState` → #29, 42.
    - `SmoothCutCapTransition` → #26.
    - `Section34CompactFaceBallInvariants` → #27.
  - Suggest: emit a supplier edge for `have`/`let … : P` inside an in-cone declaration, with the
    enclosing declaration's binder predicates as the Horn body.
- **N2. Dot-notation conclusions are not resolved to the namespace.**
  - Cases: `(solutions p).IsSolutionOn`, `(c.X).SmoothOn`, `(G.toSurgery).TerminalLimitMetric`,
    `T.str.SplitData`.
  - Rows flipped: #5, 7, 11, 15, 18, 35.
  - The same defect pools *hypothesis sites* across twins. `Field.SmoothOn`'s example site
    `AreaEvolution/Basic.lean:694` is `CurveMap.SmoothOn`, so the 190/107 and 220/138 site counts
    for the `SmoothOn` rows are not per-predicate.
- **N3. Statement-def indirection.** A predicate inside `def S : Prop := ∀ …, ∃ a : P, …` that is
  supplied by `theorem s : S` is not seen. Rows: #3, 4, 9, 17, 19, 20, 30, 31, 34, 36. Suggest
  unfolding Prop-valued defs whose body ends in `∃`/`∧` one level when reading conclusions.
- **N4. `split_sig` takes the *last* top-level `:`.** Any `∀ x : T,` or `∃ x : T,` in a conclusion
  moves conclusion text into the binder region. That both deletes suppliers and invents
  hypothesis sites.
  - Measured: 7,987 of 145,545 declaration signatures (5.5%) have more than one top-level colon.
  - Row #23: `conformal_disk_producer`, `PlateauExistence.lean:54`, loses `∃ σ :
    SmoothWeaklyMonotoneCircleMap` to the later `∀ v : SmoothDisk`.
  - Fix: the binder region ends at the *first* depth-0 `:`, because every binder is bracketed.
- **N4b. `split_sig` cuts at a top-level `:=` belonging to a `let` inside the statement.** Row #33:
  `TracedTerminalCompactness.lean:110` has a conclusion beginning `let X : … := { … }`, so its
  `HasLocalCurvDerivBound` supplier is lost.
- **N5. Abbrev by body.** #28 and #32: private `abbrev disjointInl/Inr`, whose supplier and
  statement both spell out the unfolded body.
- **N6. Route-5 false credit.** #15: `ProjectedAreaVariation.lean:203` is credited as a supplier of
  `ProductCurve.ImmersedOn`, but it concludes `c.projection.ImmersedOn` (the CurveMap twin). The
  verdict is unaffected (the predicate is supplied via route 4), but a false credit could equally
  mask a real gap.

`cone.py`:

- **C1. Generic identifiers resolve by short name, so tactic names and generic lemma names pull
  unrelated declarations into the cone.** Observed via-chains and consumer counts:
  - `smoothPoincareConjecture_holds` (the endgame's `f.trans …`) → `MetricComparisonOn.trans`
    (depth 2) → `HasStageSeed.refine` (depth 3; the `refine` tactic).
  - `TerminalParentRegionConvexity.mono`: 152 consumers.
  - `BInter.symm`: 2,251 consumers.
  - `ExponentialRadiusScaleBounds.at`: 3,137 consumers.
  - `NormalRadiusProfile.subseq`: 734 consumers.
  - This plausibly explains much of the 54% cone. It is why dead interfaces (#12, 14, 38, 47)
    show large "in-cone" site counts. The cone should resolve by `open`/namespace context and
    skip tactic keywords.
