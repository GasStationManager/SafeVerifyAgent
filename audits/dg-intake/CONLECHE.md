# con-leche over differential-geometry: 50 declarations, 42 streams, all accepted

**Checker:** [con-leche](https://github.com/leanprover/con-leche) `ae0c0c4`, built from source
at Lean v4.33.0 (statically linked binary), run in `--verified` mode, the mode covered by its
consistency theorem. **Exporter:** lean4export `15f6055` rebuilt against the artifact's own
toolchain v4.33.1. **Artifact:** `qinz1yang/differential-geometry` @ `7a48598d`, compiled
`.olean` files produced on this machine (13,493 modules of the Poincaré closure).
**Method:** for each target declaration, `lake env lean4export <module> -- <decl>` exports the
declaration and its transitive dependencies (Mathlib included) as one NDJSON stream; con-leche
checks the whole stream from scratch with its own term representation. Exit code and verdict line
both recorded. Driver: `conleche/cldrive.py`; raw results: `conleche/results.jsonl`.

## Result

| | |
|---|---|
| declarations targeted | 50 (28 from the README's theorem list, 22 from the audit's own picks) |
| export streams | 42 (targets sharing a module were exported together) |
| verdict | **accepted, exit 0, in every stream** |
| records checked | 606,875,322 export records; 2,697,234 declaration checks (Mathlib dependencies are re-checked in every stream, so this overlaps heavily) |
| axioms in the streams | exactly `propext`, `Quot.sound`, `Classical.choice` (listed from a representative stream; con-leche declines any other axiom, so an accept implies no others) |
| declined / rejected / errors | none |
| targets skipped | 17: their modules are outside the compiled Poincaré closure (the headline itself and its smooth form, Perelman's no-local-collapsing theorem in its README form, de Rham cohomology, the Schauder estimates, the Morse handle results, Hamilton's differential Harnack, the parallel-cone maximum principle, the cut-and-cap reconstruction in `SphericalCutCapTransition`) |

What an accept means here, and what it does not. con-leche re-derives every typing judgement in
the stream with an implementation that shares nothing with Lean's C++ kernel; its `--verified`
mode is the one its theorem (`ConLeche.model_exists`) is about, so the accepted environment has a
set-theoretic model. It says nothing about whether a theorem's statement is the one intended (that
is the statement rung and the route walk), and its trust boundary still contains the compiled
binary, Lean's runtime `Nat`, and the exporter. Its scope caveats are in the ReadingGroup note and
`DESIGN.md` §3. Timing is dominated by the export's I/O on this machine; con-leche itself checked
between 5 seconds (1.3 M records) and 10 minutes (87 M records, 6.3 GB resident).

## Per-declaration table

| target | declaration | module | import closure (modules) | records | declarations checked | export / check | verdict |
|---|---|---|---|---|---|---|---|
| Mayer–Vietoris exactness | `singularMayerVietoris_exact_sum` | `Topology.Homology.MayerVietorisExactness` | 3,701 | 2,402,517 | 22554 | 133 s / 9.8 s | accepted (exit 0) |
| Compact PL triangulations | `exists_pLTriangulation` | `Topology.PiecewiseLinear.TriangulationExistence` | 3,921 | 2,829,597 | 27059 | 53 s / 11.0 s | accepted (exit 0) |
| invariance of domain (vendored) | `invariance_of_domain_open_map` | `External.ClassificationOfSurfaces.Topology.InvarianceOfDomain` | 4,211 | 4,160,973 | 37550 | 39 s / 16.0 s | accepted (exit 0) |
| Morse lemma | `morse_lemma` | `Topology.Morse.NormalForm.Manifold` | 4,340 | 6,474,189 | 48195 | 39 s / 26.7 s | accepted (exit 0) |
| no-critical-values theorem | `no_critical_values` | `Topology.Morse.RegularLevel.NoCriticalValues` | 4,403 | 6,714,181 | 48942 | 36 s / 27.4 s | accepted (exit 0) |
| extinction threshold | `extinctionThreshold` | `Geometry.Flow.RicciFlow.Extinction.Families.ScalarThreshold` | 4,494 | 1,310,712 | 15584 | 28 s / 5.0 s | accepted (exit 0) |
| no retraction | `not_exists_retraction_closedBall_sphere` | `Topology.FixedPoint.NoRetraction` | 4,510 | 5,043,728 | 41491 | 28 s / 22.8 s | accepted (exit 0) |
| trivial space form is S3 | `exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group` | `Topology.ThreeManifold.SphericalSpaceFormTrivial` | 4,547 | 4,874,830 | 38904 | 31 s / 19.6 s | accepted (exit 0) |
| Voss–Weyl divergence formula | `voss_weyl_divergence_formula` | `Analysis.Integration.DivergenceTheorem.Local.ChartInvariance` | 4,555 | 7,128,412 | 52661 | 39 s / 29.2 s | accepted (exit 0) |
| nilpotent exterior derivative | `exteriorDerivative_sq` | `Tensor.Exterior.Basic` | 4,702 | 4,243,923 | 34189 | 24 s / 16.2 s | accepted (exit 0) |
| Brouwer instance (native) | `exists_fixedPoint_closedBall_of_continuous` | `Topology.FixedPoint.Brouwer` | 4,766 | 5,065,148 | 41582 | 25 s / 21.5 s | accepted (exit 0) |
| Ricci-tensor naturality under diffeomorphisms | `ricciTensor_pullback` | `Geometry.Curvature.CurvatureOperator.Ricci.Naturality` | 5,302 | 7,641,341 | 52606 | 51 s / 31.2 s | accepted (exit 0) |
| Lichnerowicz eigenvalue bound | `lichnerowicz_eigenvalue_ge_dim_mul_curvature_of_closed` | `Analysis.Elliptic.Lichnerowicz` | 5,322 | 8,667,688 | 57009 | 43 s / 36.0 s | accepted (exit 0) |
| Scalar-curvature evolution under Ricci flow | `scalar_curvature_evolution` | `Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation` | 5,385 | 8,764,187 | 54508 | 53 s / 38.5 s | accepted (exit 0) |
| Bonnet–Myers diameter bound | `bonnet_myers_diameter_of_ricci_bound` | `Geometry.Comparison.BonnetMyers.Diameter` | 5,545 | 10,247,181 | 59359 | 63 s / 44.2 s | accepted (exit 0) |
| fundamental groups of finite connected sums | `fundamentalGroup_finiteConnectedSum_freeProduct` | `Topology.VanKampen.FiniteConnectedSumFreeProduct` | 5,694 | 6,116,765 | 44989 | 35 s / 26.7 s | accepted (exit 0) |
| extinction structure | `PoincareControlledExtinction` | `Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinction` | 5,759 | 8,862,666 | 56909 | 47 s / 42.3 s | accepted (exit 0) |
| cut-cap reversal is connected sum | `componentwise_isPoincareStandard_of_poincareControlled` | `Topology.ThreeManifold.CutCapPoincareStandard` | 6,631 | 12,791,440 | 69903 | 98 s / 63.2 s | accepted (exit 0) |
| Moise 34.1 | `moise341` | `Topology.PiecewiseLinear.Moise341Producer` | 7,753 | 23,180,170 | 90797 | 177 s / 105.4 s | accepted (exit 0) |
| Section 34 cell diagram | `section34CellDiagram` | `Topology.PiecewiseLinear.Section34Terminal` | 8,643 | 28,776,903 | 95712 | 182 s / 134.9 s | accepted (exit 0) |
| Moise's theorem: compatible smooth structures in d | `exists_isManifold_three` | `Topology.PiecewiseLinear.Moise352Producer` | 9,023 | 34,179,234 | 108010 | 201 s / 166.2 s | accepted (exit 0) |
| PL approximation | `plApproximation_three` | `Topology.PiecewiseLinear.Moise352Producer` | 9,023 | 34,179,234 | 108010 | 201 s / 166.2 s | accepted (exit 0) |
| compact PL smoothing | `plSmoothingCompact_three` | `Topology.PiecewiseLinear.Moise352Producer` | 9,023 | 34,179,234 | 108010 | 201 s / 166.2 s | accepted (exit 0) |
| Strong parabolic maximum principles | `scalar_strong_maximum_principle_time_dependent_metric_with_drift_spatial` | `Analysis.Parabolic.MaximumPrinciple.Scalar.Strong` | 10,832 | 7,009,025 | 51369 | 104 s / 31.7 s | accepted (exit 0) |
| Hopf boundary point theorem | `scalar_hopf_boundary_point_of_barrier_with_boundary` | `Analysis.Parabolic.MaximumPrinciple.Scalar.Hopf.ManifoldBoundary` | 10,840 | 4,599,036 | 37857 | 26 s / 19.3 s | accepted (exit 0) |
| Weitzenböck identity | `weitzenbock_integrated_covGrad_l2_normSq` | `Analysis.Elliptic.ConnectionLaplacian.Weitzenbock.IntegratedCovariantTensor` | 10,893 | 8,618,987 | 56953 | 47 s / 41.1 s | accepted (exit 0) |
| Bochner formula | `bochner_polarised_pointwise` | `Analysis.Elliptic.Regularity.Bochner.PolarisedLpSmooth` | 10,999 | 8,459,634 | 55899 | 57 s / 38.4 s | accepted (exit 0) |
| Li–Yau Harnack inequality | `heat_solution_harnack_of_nonnegative_ricci` | `Analysis.Parabolic.Harnack.LiYauHarnack` | 11,035 | 11,376,700 | 65314 | 63 s / 56.7 s | accepted (exit 0) |
| Quasilinear parabolic local existence | `quasilinear_strong_existence_locally_lipschitz` | `Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.LocallyLipschitz` | 11,038 | 10,585,183 | 64239 | 65 s / 54.7 s | accepted (exit 0) |
| Hamilton–Ivey pinching estimate | `hamilton_ivey_pinching` | `Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.MaximumPrinciple` | 11,476 | 13,054,647 | 63192 | 77 s / 65.8 s | accepted (exit 0) |
| asymptotic pinching estimate | `hamilton_ivey_asymptotic_pinching` | `Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.MaximumPrinciple` | 11,476 | 13,054,647 | 63192 | 77 s / 65.8 s | accepted (exit 0) |
| 0, T)$ with $g(0) = g_0$, jointly smooth in $(t, x | `redVolume_anti` | `Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic` | 11,504 | 14,611,365 | 70380 | 112 s / 72.3 s | accepted (exit 0) |
| Perelman's W-entropy monotonicity | `w_rev_antitone` | `Geometry.Flow.RicciFlow.Entropy.W.Variation.Monotonicity` | 12,060 | 11,199,138 | 63856 | 100 s / 51.3 s | accepted (exit 0) |
| exact integral-square derivative formula | `w_rev_square` | `Geometry.Flow.RicciFlow.Entropy.W.Variation.Monotonicity` | 12,060 | 11,199,138 | 63856 | 100 s / 51.3 s | accepted (exit 0) |
| Ricci–DeTurck flow short-time existence | `deturck_ricci_flow_parabolic_short_time_existence` | `Geometry.Flow.RicciFlow.ShortTime.DeTurck.InitialData` | 12,080 | 24,330,113 | 88536 | 177 s / 171.5 s | accepted (exit 0) |
| Shi's derivative estimates | `time_weighted_curvature_derivative_bound_of_complete` | `Geometry.Flow.RicciFlow.Estimates.Shi.TimeWeighted` | 12,091 | 14,094,569 | 68185 | 83 s / 71.0 s | accepted (exit 0) |
| Ricci flow short-time existence | `ricci_flow_short_time_existence` | `Geometry.Flow.RicciFlow.ShortTime.Existence` | 12,265 | 25,022,742 | 89523 | 150 s / 190.3 s | accepted (exit 0) |
| pinching delta threshold | `exists_normalizedDatum_insertedMetric_pinching` | `Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertionPinching` | 12,286 | 13,895,591 | 70151 | 102 s / 74.2 s | accepted (exit 0) |
| event count bound | `eventCount_le_card_initial_add_volume_bound` | `Geometry.Flow.RicciFlow.Surgery.Topology.HistoryEventVolumeBound` | 12,489 | 9,634,403 | 61944 | 56 s / 46.2 s | accepted (exit 0) |
| Hamilton's compactness theorem | `compactnessSolution` | `Geometry.Flow.RicciFlow.Compactness.Limits.Hamilton` | 12,539 | 20,718,770 | 78508 | 131 s / 120.0 s | accepted (exit 0) |
| simple connectivity through surgery | `child_simplyConnected` | `Geometry.Flow.RicciFlow.Surgery.Topology.ChildSimplyConnected` | 12,865 | 5,088,809 | 41298 | 34 s / 20.8 s | accepted (exit 0) |
| Hamilton's matrix Harnack inequality for Ricci flo | `hamilton_matrix_harnack_of_compact` | `Geometry.Flow.RicciFlow.HamiltonHarnack.MatrixHarnack` | 13,129 | 17,784,808 | 73009 | 134 s / 92.8 s | accepted (exit 0) |
| nonnegative initial curvature operator suffices | `hamilton_matrix_harnack_of_compact_of_initial_nonnegative` | `Geometry.Flow.RicciFlow.HamiltonHarnack.MatrixHarnack` | 13,129 | 17,784,808 | 73009 | 134 s / 92.8 s | accepted (exit 0) |
| Hamilton's theorem (1982) | `hamilton_positive_ricci` | `Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Hamilton` | 13,635 | 44,495,811 | 118148 | 283 s / 317.6 s | accepted (exit 0) |
| width decay on a slab | `history_incoming_component_dini` | `Geometry.Flow.RicciFlow.Extinction.Families.ActualWidth` | 15,134 | 39,777,762 | 128423 | 320 s / 295.5 s | accepted (exit 0) |
| Perelman's canonical neighborhood theorem | `smooth_canonical_neighborhood` | `Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds` | 18,212 | 87,322,066 | 181062 | 863 s / 599.1 s | accepted (exit 0) |
| curvature-scale bounds for all mixed space-time cu | `high_curvature_derivatives` | `Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds` | 18,212 | 87,322,066 | 181062 | 863 s / 599.1 s | accepted (exit 0) |
| Compactness of ancient κ-solutions | `fixed_kappa_compactness` | `Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds` | 18,212 | 87,322,066 | 181062 | 863 s / 599.1 s | accepted (exit 0) |
| universal mixed curvature-derivative estimates | `kappa_universal_derivatives` | `Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds` | 18,212 | 87,322,066 | 181062 | 863 s / 599.1 s | accepted (exit 0) |
| pinching through surgery | `pinchingThroughSurgery` | `Geometry.Flow.RicciFlow.Surgery.Topology.PinchingThroughSurgery` | 20,767 | 15,720,378 | 70875 | 144 s / 86.7 s | accepted (exit 0) |

## Skipped (closure not compiled here)

- Poincaré conjecture — `DifferentialGeometry.Topology.poincare_conjecture`
- smooth version — `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds`
- Finite-time extinction with surgery, simply connected case — `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction`
- Perelman's no local collapsing theorem — `DifferentialGeometry.PDE.RicciFlow.Perelman.no_local_collapsing`
- de Rham cohomology — `DifferentialGeometry.DifferentialForm.deRhamCohomology`
- graded Leibniz rule — `DifferentialGeometry.DifferentialForm.exteriorDerivative_wedge`
- functorial pullback maps — `DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_comp`
- single-critical-point cell attachment — `DifferentialGeometry.Topology.Morse.ManifoldCellAttachment.one_critical_point_cell_attachment`
- smooth handle-adjunction diffeomorphisms — `DifferentialGeometry.Topology.Morse.exists_morseHandleAdjunction_diffeomorph_upperSublevel_of_morseChart`
- Elliptic variable-coefficient Schauder estimates — `DifferentialGeometry.Analysis.Schauder.variable_coefficient_schauder_estimate_of_small_oscillation`
- parabolic nondivergence Schauder estimates — `DifferentialGeometry.Analysis.Parabolic.Euclidean.exists_parabolic_nondivergence_schauder_estimate`
- parallel proper cones — `DifferentialGeometry.Analysis.Parabolic.parallelProperCone_mem_dualZeroFace_of_terminal_eq_zero`
- symmetric tensors — `DifferentialGeometry.PDE.RicciFlow.tensor_positive_definite_on_of_null_reaction_lower_bound`
- Hamilton differential Harnack inequality — `DifferentialGeometry.Analysis.Parabolic.Harnack.heat_solution_hamilton_differential_harnack_of_ricci_lower_bound`
- Cut-and-cap reconstruction — `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_connectedSum_capComponents`
- simple connectivity is preserved by capping — `DifferentialGeometry.Topology.SphericalCutCapTransition.simplyConnectedSpace_capComponent`
- surgery step (public wrapper) — `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong`

## Reproducing

```bash
# in the artifact checkout, with its closure built and lean4export built at the same toolchain
lake env <lean4export> <Module> -- <Decl> > out.ndjson
con-leche --verified out.ndjson   # exit 0 and "accepted N declarations" is the only pass
```
