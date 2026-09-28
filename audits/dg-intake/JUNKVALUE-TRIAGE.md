# JUNKVALUE triage: differential-geometry @ 7a48598d

Read-only pass over `/home/user/differential-geometry`. Nothing was compiled and nothing was committed. Input: `dg-intake/JUNKVALUE.csv` (617 hits, 494 in the Poincaré headline's file closure `/tmp/closure_files.txt`).

**Scope.**
- All 250 in-closure rows under `Geometry/Flow/RicciFlow/`, `Geometry/Neck/`, `Geometry/Compactness/` (0 hits), `Geometry/Comparison/`, `Topology/` and `External/`. These are 226 distinct declarations; a declaration flagged for two denominators or two hiding definitions gets one row each.
- A seeded random sample (`random.seed(20260928)`) of 40 of the 229 in-closure `Analysis/` rows.
- The 15 in-closure rows in other directories were left out. The exception is `Geometry/Curvature/HamiltonIveyRegion.lean:15`, which is on the Hamilton–Ivey route and was checked as an aside (§5).

**Method.**
- Every flagged signature was read with `sed -n` from the flagged line up to its `:=`.
- Every hiding definition behind a "(via X)" row was read.
- Callers were found with `grep -rnw` on the short name, restricted to closure files. The enclosing declaration's signature was then read for a guard on the passed value.
- All 314 caller sites cited below were re-read with `sed -n`.
- "Depth" is the declaration's BFS depth in `ROUTE.md` (the name-level cone of `poincare_conjecture`); "-" means the file is in the closure but the declaration is not in the cone.
- "On the route walk" means the file is named in `ROUTE-WALK*.md`.

**Classes (as briefed).**
- **A**: the degenerate value is excluded by every caller in the closure. Transitively, a caller that only forwards to a guarded caller counts as guarded.
- **B**: the degenerate value is excluded in the same signature or by a structure field the scanner missed. These are scanner false positives; the pattern is given.
- **C**: the degenerate value is reachable, and the statement is a property claim or an identity that stays true with no content lost.
- **D**: the degenerate value is reachable, and an exact-value or bound claim that some consumer relies on for content collapses there.

## 1. Counts

| set | rows | A | B | C | D |
|---|---|---|---|---|---|
| in-scope directories (all in-closure rows) | 250 | 67 | 113 | 70 | **0** |
| `Analysis/` sample | 40 | 6 | 4 | 30 | **0** |
| **total triaged** | **290** | **73** | **117** | **100** | **0** |

In-scope rows by directory: `Geometry/Flow/RicciFlow` 122, `Topology` 68, `Geometry/Comparison` 29, `Geometry/Neck` 21, `External` 10, `Geometry/Compactness` 0.

- 169 of the 250 rows are in the name-level cone.
- 8 of the 250 rows are in files named by the route walk:
  - rows 5, 26, 70, 71 and 133–135 are A or B;
  - row 159, `Comparison/Variation/Flow.lean:76` `flowTimeRetract_contDiff`, is C.

**Scanner mode matters.** 260 of the 290 rows come from mode 2 ("via" a hiding definition): A 55, B 109, C 96. The other 30 come from mode 1 (the division is in the statement itself): A 18, B 8, C 4. Most of the noise is in mode 2 (§4).

The per-row classification is in the appendix.

## 2. D rows

**None.** No row in scope or in the sample is an exact-value or bound claim whose degenerate value is both reachable and relied on by a consumer.

Closest candidates, all cleared:
- `Neck/HalfBandVolume.lean:26` `referenceMetric_negative_closed_band_volume`: an exact volume `8π·(δ⁻¹−1)` for every δ. At δ = 0 both sides are 0. Its sole caller, `HalfBandVolume.lean:72`, holds `d : normalizedDatum` (`precision_pos`). → A.
- `Surgery/Topology/TerminalNeckNormalization.lean:77` and `:120` `exists_terminal_neckBuffer_pullback_bound`: a bound on `neckBuffer δ`. `hfit : δ⁻¹ + 1 ≤ eps⁻¹` admits δ = 0. The only live caller, `:341`, has `hδ : 0 < δ`. → A.
- `Surgery/Topology/FiniteHorizonContinuation.lean:28` `prefix_initial_budget`: an exact identity with `/ v`. Its caller at `:95` sits under `hv : 0 < v` (`:52`). → A.
- `Analysis/Parabolic/TimeSobolev/H1/Approximation/Ramp.lean:39` `rampUp_apply`: `hT : 0 ≤ T` admits T = 0. All 6 callers have `0 < T`, including `T = b − c` with `hcb : c < b`. → A.
- `Topology/Morse/Attachment/ModelCell.lean:3679` `modelLevelDampedUnstretch_posPart`: ε₀ is free at its callers. The consuming claims are bounds that hold uniformly in ε₀ because `smoothTransition ∈ [0,1]`, so nothing is emptied. The file is not in the cone. → C.

## 3. Route-relevant C rows

These are the 35 in-scope C rows that lie in the name-level cone. None is an exact value that a consumer uses at the degenerate point. Each is either a property (smoothness, compactness, membership in `[0,1]`, a set or metric identity), an identity whose flagged term is already zero, or a count clamped by `max`.

| file:line | decl | depth | statement (truncated) | degenerate value | caller that excludes it, or does not |
|---|---|---|---|---|---|
| Topology/Planar/PolygonGraphCharts.lean:2132 | `matched_profile_eq_smul_of_le_neg` | 25 | `r * (s * (x - Real.smoothMax ε x 0) + Real.smoothMax ε x 0 / d - y) = r * (s * (x - Real.smooth` | d = 0 (the /d term already 0 because smoothMax ε x 0 = 0 for x ≤ −ε) | x <= -eps forces smoothMax eps x 0 = 0, so the /d term is 0 for every d |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/CylindricalComparisonRestriction.lean:57 | `restrictedCylinderTensor_norm` | 19 | `tensor02CovDerivNormWith a (restrictedCylinderTensor e epsilon A) ((DifferentialGeometry.Diffeo` | ε = 0: spatialNeckBuffer 0 = S²×(−1,1) | norm of restricted tensor = norm of tensor, valid for every epsilon; caller CylindricalComparisonRestriction.lean:173 shows no epsilon guard |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckCoreSize.lean:22 | `spatialNeckCoreRadiusConstant_pos` | 11 | `0 < spatialNeckCoreRadiusConstant epsilon` | ε = 0: constant = 13/12·√2·π, still > 0 | 0 < const holds for every epsilon; SeparatingSphere.lean:72 caller shows no epsilon guard |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:28 | `neckReflectionMap_involutive` | 13 | `Function.Involutive (neckReflectionMap epsilon)` | ε = 0: buffer S²×(−1,1) | used to build spatialNeckReflection epsilon for every epsilon (SpatialNeckReflection.lean:49-257) |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:35 | `neckReflectionMap_smooth` | 13 | `ContMDiff SpatialNeckCylinderModel SpatialNeckCylinderModel ∞ (neckReflectionMap epsilon)` | ε = 0: buffer S²×(−1,1) | used to build spatialNeckReflection epsilon for every epsilon (SpatialNeckReflection.lean:49-257) |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:73 | `spatialNeckReflection_core_iff` | 14 | `spatialNeckReflection epsilon x ∈ spatialNeckClosedCore epsilon ↔ x ∈ spatialNeckClosedCore eps` | ε = 0: core S²×{0} | used to build spatialNeckReflection epsilon for every epsilon (SpatialNeckReflection.lean:49-257) |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:82 | `spatialNeckReflection_image_core` | 13 | `spatialNeckReflection epsilon '' spatialNeckClosedCore epsilon = spatialNeckClosedCore epsilon` | ε = 0: core S²×{0} | used to build spatialNeckReflection epsilon for every epsilon (SpatialNeckReflection.lean:49-257) |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:128 | `spatialNeckReflection_pullback_reference` | 13 | `DifferentialGeometry.Diffeomorph.pullbackMetric (unitCylinderMetric.restrictOpen (spatialNeckBu` | ε = 0: buffer S²×(−1,1) | used to build spatialNeckReflection epsilon for every epsilon (SpatialNeckReflection.lean:49-257) |
| Geometry/Flow/RicciFlow/Perelman/KappaSolutions/StrongNeck.lean:29 | `strongNeckBackgroundMetric_of_nonpos` | 18 | `strongNeckBackgroundMetric epsilon s = (scalarOneShrinkingCylinderMetric s (hs.trans_lt (by nor` | ε = 0: buffer S²×(−1,1) | metric identity valid for every epsilon; CylinderBackgroundJets.lean:49 shows no epsilon guard |
| Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/WitnessNormalizedTimeJets.lean:58 | `hasDerivWithinAt_rescaledTensorTimeTower` | 13 | `HasDerivWithinAt (fun r => rescaledTensorTimeTower A t Q q r y) (rescaledTensorTimeTower A t Q ` | Q = 0: s/Q = 0 in the rescaled time | derivative identity valid for every Q; WitnessOriginalError.lean:62 passes Q from a structure without visible guard |
| Geometry/Flow/RicciFlow/Surgery/StandardCap/InsertionMetric.lean:143 | `contDiff_insertionCutoff` | 15 | `ContDiff ℝ ∞ (insertionCutoff A)` | A = 0: insertionCutoff 0 ≡ smoothTransition 0 | ContDiff / Icc-membership for every A; callers inside insertionCollarMetric (hAB : 2A < B does not force A != 0) |
| Geometry/Flow/RicciFlow/Surgery/StandardCap/InsertionMetric.lean:158 | `insertionCutoff_mem` | 14 | `insertionCutoff A z ∈ Icc (0 : ℝ) 1` | A = 0: constant cutoff | ContDiff / Icc-membership for every A; callers inside insertionCollarMetric (hAB : 2A < B does not force A != 0) |
| Geometry/Flow/RicciFlow/Surgery/StandardCap/InsertionMetric.lean:161 | `smooth_cutoff_collar` | 14 | `ContMDiff IC 𝓘(ℝ) ∞ (fun q : insertionCylinder A B => insertionCutoff A q.val.2)` | A = 0: constant cutoff | ContDiff / Icc-membership for every A; callers inside insertionCollarMetric (hAB : 2A < B does not force A != 0) |
| Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:43 | `pullback_shrinkingCylinderMetric_bufferedCylinderRotation` | 8 | `Diffeomorph.pullbackMetric ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ)) (buf` | δ = 0: bufferedCylinder 0 = S²×(−1,1) | metric identity for every δ; sole caller is the unguarded Cross sibling |
| Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:69 | `pullback_shrinkingCylinderMetric_bufferedCylinderOrientation` | 8 | `Diffeomorph.pullbackMetric ((shrinkingCylinderMetric t).restrictOpen (bufferedCylinder δ)) (buf` | δ = 0: bufferedCylinder 0 = S²×(−1,1) | metric identity for every δ; sole caller is the unguarded Cross sibling |
| Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/CutoffExtension.lean:39 | `cutoffEta_contDiff` | 17 | `ContDiff ℝ ∞ (cutoffEta a b δ)` | δ = 0: cutoffEta ≡ smoothTransition(0)² | ContDiff for every parameter value; callers do not constrain it |
| Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/CutoffExtension.lean:72 | `cutoffEta_section_contMDiff` | 16 | `ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => cutoffEta a b δ q.1)` | δ = 0: constant cutoff | ContDiff for every parameter value; callers do not constrain it |
| Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/Variation.lean:79 | `flowTimeRetract_contDiff` | 16 | `ContDiff ℝ ∞ (flowTimeRetract t δ w)` | w = 0: retract factor constant | ContDiff for every parameter value; callers do not constrain it |
| Geometry/Neck/BufferedRotation.lean:13 | `rotation_image_le` | 9 | `roundCylinderImage (n := 2) e 0 (bufferedCylinder δ) ≤ bufferedCylinder δ` | δ = 0: band S²×(−1,1) | used to build the rotation/orientation diffeomorphism for every δ |
| Geometry/Neck/BufferedRotation.lean:70 | `image_bufferedCylinderRotation_controlledCylinder` | 8 | `bufferedCylinderRotation δ e '' controlledCylinder δ = controlledCylinder δ` | δ = 0: controlled set S²×{0} | used to build the rotation/orientation diffeomorphism for every δ |
| Geometry/Neck/Orientation.lean:19 | `orientation_image_le` | 8 | `cylinderAxialImage (I := 𝓡 2) 0 σ hσ (bufferedCylinder δ) ≤ bufferedCylinder δ` | δ = 0: band S²×(−1,1) | used to build the rotation/orientation diffeomorphism for every δ |
| Geometry/Neck/Orientation.lean:87 | `image_bufferedCylinderOrientation_controlledCylinder` | 8 | `bufferedCylinderOrientation δ σ hσ '' controlledCylinder δ = controlledCylinder δ` | δ = 0: controlled set S²×{0} | used to build the rotation/orientation diffeomorphism for every δ |
| Geometry/Comparison/Variation/Flow.lean:76 | `flowTimeRetract_contDiff` | 21 | `ContDiff ℝ ∞ (flowTimeRetract t δ w)` | w = 0: retract factor constant | ContDiff for every parameter value; callers do not constrain it |
| Topology/Manifold/SublevelCutoff.lean:20 | `sublevelCutoff_mem_Icc` | 19 | `sublevelCutoff ρ R x ∈ Set.Icc 0 1` | R = 0: cutoff ≡ CutoffProfile.value 0 | Icc 0 1 for every R; RiemannianExhaustion.lean:57 passes R n without visible guard |
| Topology/ThreeManifold/ConnectedSum/SphereCapProfile.lean:41 | `capDensity_of_le` | 12 | `capDensity ρ = (2 - ρ)⁻¹` | ρ = 0: ρ⁻¹ term has weight 0 | capWeight rho = 0 for rho <= 3/2 kills the rho⁻¹ term |
| Topology/ThreeManifold/ConnectedSum/SphereCapProfile.lean:47 | `capDensity_pos'` | 14 | `0 < capDensity ρ` | ρ = 0: capDensity 0 = 1/2 | 0 < capDensity rho for every rho |
| Topology/Morse/Attachment/ModifiedSublevel.lean:189 | `modGamma_nonneg` | 26 | `0 ≤ modGamma δ s` | δ = 0: modGamma 0 ≡ 1 − smoothTransition 0 | bounds/monotonicity/differentiability of modGamma for every δ; ModelHandle.lean:25,188,200,181 show no δ guard |
| Topology/Morse/Attachment/ModifiedSublevel.lean:195 | `modGamma_le_one` | 29 | `modGamma δ s ≤ 1` | δ = 0: constant | bounds/monotonicity/differentiability of modGamma for every δ; ModelHandle.lean:25,188,200,181 show no δ guard |
| Topology/Morse/Attachment/ModifiedSublevel.lean:200 | `modGamma_antitone` | 28 | `AntitoneOn (modGamma δ) (Ici (0 : ℝ))` | δ = 0: constant | bounds/monotonicity/differentiability of modGamma for every δ; ModelHandle.lean:25,188,200,181 show no δ guard |
| Topology/Morse/Attachment/ModifiedSublevel.lean:315 | `differentiableAt_modGamma` | 28 | `DifferentiableAt ℝ (modGamma δ) x` | δ = 0: constant | bounds/monotonicity/differentiability of modGamma for every δ; ModelHandle.lean:25,188,200,181 show no δ guard |
| External/Schoenflies/LocalGrid.lean:633 | `one_le_localGridCount` | 20 | `1 ≤ localGridCount s ε` | ε = 0: localGridCount s 0 = 1 (max-clamped) | localGridCount = max 1 (...): clamped, bound holds for every ε |
| External/Schoenflies/SquareMesh.lean:1072 | `two_le_meshCount` | 10 | `2 ≤ meshCount δ` | δ = 0: meshCount 0 = 2 (max-clamped) | meshCount δ = max 2 (...): clamped; mesh identities hold for any count |
| External/Schoenflies/SquareMesh.lean:1097 | `squareMesh_pointSet` | 10 | `Graph.pointSet (squareMesh δ fresh anchors) segmentDrawing = cover (meshSegments (meshCount δ) ` | δ = 0: meshCount 0 = 2 | meshCount δ = max 2 (...): clamped; mesh identities hold for any count |
| External/Schoenflies/SquareMesh.lean:1130 | `squareMesh_cover_outerEdges` | 26 | `⋃ P ∈ outerEdges (meshCount δ) fresh anchors, P.seg = modelCurve` | δ = 0: meshCount 0 = 2 | meshCount δ = max 2 (...): clamped; mesh identities hold for any count |
| External/Schoenflies/SquareMesh.lean:1136 | `squareMesh_inner_edge_at_fresh` | 23 | `∃ z ∈ fresh, P.seg ∩ modelCurve = {z} ∧ (z = P.1 ∨ z = P.2) ∧ P.seg ⊆ (spokePiece (meshCount δ)` | δ = 0: meshCount 0 = 2 | meshCount δ = max 2 (...): clamped; mesh identities hold for any count |

**The one route-shaped junk effect: neck buffers at δ = 0 are short, not long.** Because `0⁻¹ = 0`, the following all degenerate to a band of half-length 1, or to the central sphere, at δ = 0:
- `neckBuffer δ` (`Surgery/Topology/StaticCap.lean:92`)
- `bufferedCylinder δ` (`Neck/NormalizedDatum.lean:23`)
- `spatialNeckBuffer ε` (`Perelman/KappaSolutions/SpatialNeck.lean:25`)
- their closed and central cores

So small positive δ means a long neck, but δ = 0 means the shortest one. Any lemma quantified over a bare δ is therefore weaker at δ = 0 than "δ-neck" suggests.

On the route this is neutralised because every neck object carries its own positivity field:
- `NormalizedNeck.delta_pos` (`StaticCap.lean:109`)
- `normalizedDatum.precision_pos` (`NormalizedDatum.lean:50`)
- `SpatialNeck.eps_pos` (`Neck/Spatial.lean`)
- `StrongNeck.eps_pos`, `CanonicalWitness.eps_pos` (`CanonicalNeighborhood/FiniteHornGeometry.lean`)
- `SpatialNeckWitness.epsilon_pos`, `StrongNeckWitness.epsilon_pos`
- `TerminalCorePresentation.epsilon_pos` (`Surgery/Contract/Terminal.lean:59`)

The bare-δ lemmas in the table are all reached through one of these structures or a `0 < δ` hypothesis, or they are properties that stay true on the short band. `meshCount δ = max 2 (...)` (`External/Schoenflies/SquareMesh.lean:1070`) is the analogous clamp for the Schoenflies mesh; its quantitative spec `meshCount_spec` requires `0 < δ`.

## 4. Scanner false-positive patterns for `junkvalue.py`

| id | pattern | B rows | example (read) | suggested fix |
|---|---|---|---|---|
| P3 | **Structure-field guard**: the scalar is the index of a structure binder (`N : NormalizedNeck g δ k`, `W : SpatialNeckWitness h y p ε`, `nk : SpatialNeck g eps x`, `d : normalizedDatum ..`, `P : TerminalCorePresentation D ε Λ`) whose fields include `0 < δ`. The binder can sit in the signature or be quantified inside the conclusion. | 34 | `ChartTailHornBridge.lean:70`, `HornFineCutNecks.lean:77`, `TerminalCapCapture.lean:115` | Build a table of structures with a `*_pos : 0 < param` field (a one-pass scan of `structure … where` bodies). Treat a binder `(x : S … name …)` as a constraint on `name`. |
| P1 | **Short-name collision**: `risky_defs` is keyed on the last name component. The private defs `alpha`, `beta`, `gamma` (`Geometry/Metric/RadialCurvature.lean:121-123`) and `FlowTo.scale` (`Extension/Maximal/Scaling.lean:20`) match local binders named `alpha`/`gamma` (curves, constants) and projections like `N.scale`. The def's parameter name (`r`, `c`) is then matched by name against an unrelated binder of the theorem. | 29 + 7 | `ActualWidth.lean:93` (`gamma : ℝ → …` a curve), `Toponogov/Completion.lean:113`, `MetricComparisonAngle.lean:57` | Resolve the reference: require the def's namespace to be open or the name to be fully qualified, skip `private` defs outside their file, and skip identifiers bound in the theorem's own binders. Map the def's parameter by **argument position** at the call site, not by name. |
| P9 | **`if`-guard in the def body**: the division sits in the branch where the denominator is nonzero. | 22 | `hyperbolicSn q r := if q = 0 then r else sinh(q r)/q` (`Comparison/Volume/HyperbolicModel.lean:17`); `standardCapRho` (`EventData.lean:27`); `radialSigma`/`radialPhi` (`SphereUnitFilling.lean:38-42`) | Do not count a division under `if name = 0`, `if name ≤ 0`, `if c ≤ name` (c > 0) or `dite` on the same name. |
| P2 | **Transitive positivity**: `0 < l` with `l ≤ r`; `0 < s₁` with `s₁ < s₂`; `0 < r` with `2*r ≤ L`; or a structure's positive parameter `eps` with `eps ≤ δ`. | 18 | `TraceIntegralGeodesic.lean:19`, `CircleFourPoints.lean:129`, `Trapezoid.lean:49`, `ProspectiveNeckSurvival.lean:61` | One-step closure over the signature's `<`, `≤` and `ofReal` facts, seeded by `0 < x` and by P3 fields. |
| P7 | **Self-guarded def**: the risky def's own signature (`FlowTo.scale … (hc : 0 < c)`) or body (`historicalNeckRecognition := 0 < d ∧ …`, `Contract/Terminal.lean:231`) already constrains the parameter. | 1 (+7 with P1) | `EndNeckFields.lean:246` | In `risky_defs`, apply the `NONZERO` test to the def's own binders and to a leading `0 < name ∧` in a `Prop` body. |
| P8 | **Division only inside the def's proof**: `rhs` includes `by` blocks. | 1 | `CanonicalWitness.enlarge_constants` (`CanonicalStrictBounds.lean:141`: `C2'⁻¹` in a `have`) | Strip tactic blocks before scanning a def body, or only scan the term after `:=` when it is not `by`. |
| P4 | **Preimage notation**: `f ⁻¹' S` matched as `q⁻¹`. | 1 (3 in the full CSV) | `PrismMap.lean:196`, `OverlapBand.lean:94`, `IntervalCompletionSpace.lean:53` | Exclude `⁻¹'` in `INV`. |
| P6 | **Qualified name and type ascription**: `/ Real.sin u` captured as `/ Real`, and `(-Real.cos u / Real.sin u : ℝ)` matched `SCALAR_BINDER`. | 1 | `DiskAutomorphism/Transitivity.lean:130` (also guarded by `hu : Real.sin u ≠ 0`) | Require the identifier not to be followed by `.`. Require a binder to open a binder group (after `theorem name` or `)`/`}`), not an expression. |
| P5 | **Nonzero implied by an equation**: `hac : a ≠ c` together with `hx : c + α/2‖x‖² = a` forces α ≠ 0. | 1 | `Analysis/ODE/QuadraticLevelScaling.lean:103` | Not syntactic; accept as residual noise. |
| P10 | **Inverse bounded below**: `0 ≤ R` with `R < δ⁻¹` forces δ > 0. | 1 | `HornBaseCoordinates.lean:114` | Add the `NONZERO` forms `… < name⁻¹` and `0 < name⁻¹`. |
| P11 | **Nonempty open interval**: `p.1 ∈ Ioo (R - h) R` forces h > 0. | 1 | `AnnulusEnergy.lean:60` | Residual. |

**Noise that is not a false positive but inflates the C count** (worth filtering):
- **P12, mode 2 skips the equality filter.** Mode 1 drops conclusions that are not value equalities (`informative()`); mode 2 does not. Applying `informative()` to the mode-2 statements in this triage marks **160 of 260** as non-equalities (68 B, 63 C, 29 A). Examples: `IsCompact (neckClosedTest δ)`, `ContDiff ℝ ∞ (cutoffEta a b δ)`, `0 ≤ modGamma δ s`. The docstring's own rationale ("a bound, regularity … claim does not collapse to 0 = 0 in any interesting way") applies here unchanged. **Recommend applying `informative()` in mode 2.**
- **Identity valid at 0** (C): `t⁻¹*(a-c) = a*t⁻¹ - c*t⁻¹`, `n*√(Λ/n) = √(nΛ)` with `0 ≤ n`, `max x 0 / fc = …`, `smoothMax (ε/a) (x/a) (y/a) = smoothMax ε x y / a`. These are ring identities that hold at the junk point with nothing lost. They are cheap to detect by re-checking the identity with the denominator replaced by 0, which is the "semantic test" the docstring defers.
- **Numerator vanishes under the hypotheses** (C): `PolygonGraphCharts.lean:2132` (smoothMax is 0 for x ≤ −ε), `SphereCapProfile.lean:41` (`capWeight ρ = 0` for ρ ≤ 3/2), `ThinAnnulus.lean:52`.
- **Clamped definitions** (C): `max 1 (…)` / `max 2 (…)` in `localGridCount` and `meshCount`.
- **Uniform-in-h difference quotients** (C, 23 of the 40 Analysis rows): `diffQuot k h` lemmas stated for every h. At h = 0 they hold trivially, which is the intended Nirenberg shape (uniform bounds, then h → 0).

## 5. Route junk-value checks beyond the scanner

The brief asked for route lemmas that a junk value could make weaker than they read: an infimum over the empty set giving 0, `Real.sqrt` of a negative, or `Nat` subtraction. What was checked:

- **κ-noncollapsing** (`Perelman/Noncollapsing/Defs.lean:60`): `IsKappaNoncollapsed` is `0 < κ ∧ κ·rⁿ ≤ vol`. It is multiplicative, with no division, and `FlowMetricBall.radius_pos` is a structure field (`:33`). Junk-safe.
- **Hamilton–Ivey** (`Surgery/Topology/GeometricCutoff.lean:36-44`): `InFixedHamiltonIveyRegion` uses `ν := sInf {Rayleigh quotients over unit vectors in ℝ³}`. The set is nonempty and bounded (a quadratic form on the sphere), so the infimum is not junk. The `log (a·(−ν))` sits in the branch where `ν < 0`, and `a` comes from `exists_pos_fixedHamiltonIveyRegion_for_identified_histories` (`HamiltonIveyPinching.lean:666`, `0 < a`). The out-of-scope scanner hit `Geometry/Curvature/HamiltonIveyRegion.lean:15` (`/a` via `a⁻¹`) is **A**: its callers are `HamiltonIvey/Initial.lean:43`, under `ha : 0 < a` (`:18`), and `HamiltonIveyRegion.lean:27`, under `ha : 0 < a` (`:21`).
- **Extinction width**: `ROUTE-WALK-2-analytic.md:464-468` already checked `familyMaximum`, `classWidth` (infimum of a nonempty set ≥ 0) and `leastArea`. No junk value.
- **Canonical neighbourhoods and surgery scales**: the neck and witness structures carry `eps_pos`, `Q_pos` and `scalar_pos` (§3). Of the forms read:
  - `Real.sqrt Q⁻¹` in `HornCutoffRecord.lean:1161` sits next to `0 < Q` in the same conclusion;
  - `⌊δ⁻¹⌋₊` orders appear only with a `NormalizedNeck … δ`.
- **Moise and Van Kampen** (`Topology/PiecewiseLinear`, `External/ClassificationOfSurfaces/Moise`): the hits are `PrismMap.lean:196` (P4), `PrismHomotopy.lean:150` (A), `CircleFourPoints.lean:129` (B) and `LineSubdivision.lean:387` (A, where the callers `simp` with `ha0.ne'`/`hb0.ne'`). None is weakened.

`Nat` subtraction was not searched systematically. It is outside `junkvalue.py`'s scope and would need its own pass.

## Verdict

**No D touches the Poincaré route.** Of 290 triaged rows (250 in scope, 40 sampled), none is an exact-value or bound claim whose degenerate value is both reachable and relied on. Every exact-value hit on a route file is caller-guarded (A) or excluded by a structure field (B). The remaining C rows are properties, identities or clamped counts that lose no content at the junk point.

The headline is hypothesis-free and compiles, so junk values can at most weaken intermediate statements, and none of the ones read is weakened where it is used.

## Appendix: per-row classification

`grp`: S = in-scope directory, A = Analysis sample. Row numbers are internal worksheet indices; `file:line` identifies the row.

| # | grp | file:line | decl | denominator | depth | class | pattern |
|---|---|---|---|---|---|---|---|
| 0 | S | Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution/Basic.lean:64 | `inv_mul_sub` | t | 26 | **A** | rewrite |
| 1 | S | Geometry/Flow/RicciFlow/Extinction/CurveShortening/AreaEvolution/Basic.lean:125 | `areaExpansion` | h | 23 | **A** | rewrite |
| 2 | S | Geometry/Flow/RicciFlow/Perelman/LGeometry/Hamilton/TraceIntegralGeodesic.lean:19 | `integral_lHamSq_mul_eq_of_geodesic` | r | 17 | **B** | P2-transitive |
| 3 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/PointedNoncollapse.lean:505 | `pointedNC_sqrt_inverse_fourth` | r | 17 | **A** | rewrite |
| 4 | S | Geometry/Flow/RicciFlow/Perelman/StandardSolution/TravelingPhaseCoefficients.lean:23 | `traveling_phase_laplacian` | T | 20 | **A** | unfold |
| 5 | S | Geometry/Flow/RicciFlow/Surgery/Topology/FiniteHorizonContinuation.lean:28 | `prefix_initial_budget` | v | 7 | **A** | rewrite |
| 6 | S | Geometry/Flow/RicciFlow/Surgery/Topology/TerminalCapCapture.lean:115 | `exists_compact_containing_cap_neck_windows` | eps | - | **B** | P3-structure |
| 7 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornCutoffRecord.lean:1161 | `exists_prepared_horn_cutoff_event_at_scale_with_canonical_windows_precision_bound_and_original_neck_bounds` | ε | - | **B** | P3-structure |
| 8 | S | Geometry/Flow/RicciFlow/Estimates/Distance/LocalCutoff.lean:25 | `mul_sqrt_div_eq_sqrt_mul` | n | - | **C** | identity-at-0 |
| 9 | S | Geometry/Neck/InsertionOrientation.lean:31 | `controlledOrientation_buffered` | δ | 12 | **A** | unfold |
| 10 | S | Geometry/Neck/SpatialNormalization.lean:146 | `exists_normalizedNeck_of_two_mul_le` | ε | 8 | **B** | P2-transitive |
| 11 | S | Geometry/Comparison/Variation/RadialIndex.lean:57 | `indexFormIntegrand_eq_of_radial_data` | L | 22 | **A** | rewrite |
| 12 | S | Topology/Embedding/CylinderCapRounding.lean:28 | `cylinderCapCoordinates_apply` | a | 23 | **A** | unfold |
| 13 | S | Topology/Embedding/CylinderCapRounding.lean:44 | `cylinderCapCoordinates_symm_apply` | a | 23 | **A** | unfold |
| 14 | S | Topology/Embedding/CylinderCapRounding.lean:84 | `roundedCapRadiusSq_eq_of_neg_le` | a | 26 | **A** | unfold |
| 15 | S | Topology/Planar/PolygonGraphCharts.lean:2132 | `matched_profile_eq_smul_of_le_neg` | d | 25 | **C** | numerator-vanishes |
| 16 | S | Topology/Planar/PolygonGraphCharts.lean:2754 | `removed_raw_threshold_eq` | fc | - | **C** | identity-at-0 |
| 17 | S | Topology/Planar/VertexRoundingProfile.lean:14 | `affine_smoothCorner_vertex_coordinates` | h | 22 | **A** | unfold |
| 18 | S | Topology/Planar/VertexRoundingProfile.lean:38 | `affine_smoothCorner_vertex_coordinates_of_unit` | h | 22 | **A** | unfold |
| 19 | S | Topology/PiecewiseLinear/CircleFourPoints.lean:129 | `exists_arc_pair_of_two_interior` | s₂ | 18 | **B** | P2-transitive |
| 20 | S | Topology/PiecewiseLinear/PrismHomotopy.lean:150 | `heightRescale_apply` | h | - | **A** | unfold |
| 21 | S | Topology/PiecewiseLinear/PrismMap.lean:196 | `preimage_stripToSquare` | q | - | **B** | P4-preimage |
| 22 | S | Topology/Morse/Attachment/ModelCell.lean:3679 | `modelLevelDampedUnstretch_posPart` | ε₀ | - | **C** | uniform-in-param |
| 23 | S | External/DeGiorgi/UnitBallApproximationCore/Rescaling.lean:28 | `unitBallDilate_apply` | lam | 38 | **A** | unfold |
| 24 | S | External/ClassificationOfSurfaces/Moise/LineSubdivision.lean:387 | `referenceOuterAffine_planePoint` | a | 11 | **A** | unfold |
| 25 | S | External/ClassificationOfSurfaces/Moise/LineSubdivision.lean:387 | `referenceOuterAffine_planePoint` | b | 11 | **A** | unfold |
| 26 | S | Geometry/Flow/RicciFlow/Extinction/Families/ActualWidth.lean:93 | `component_covDerivAlong` | r (via gamma) | - | **B** | P1-name-collision |
| 27 | S | Geometry/Flow/RicciFlow/Extinction/CurveShortening/ProductGeometry.lean:30 | `verticalUnit_eq_coverVerticalUnit` | lambda (via verticalUnit) | - | **C** | identity-no-caller |
| 28 | S | Geometry/Flow/RicciFlow/Extinction/CurveShortening/ProductGeometry.lean:30 | `verticalUnit_eq_coverVerticalUnit` | lambda (via coverVerticalUnit) | - | **C** | identity-no-caller |
| 29 | S | Geometry/Flow/RicciFlow/Extinction/CurveShortening/Sobolev/Uniqueness.lean:914 | `circle_physical_rhs_sub_laplacian_eq_shifted` | r (via alpha) | 31 | **B** | P1-name-collision |
| 30 | S | Geometry/Flow/RicciFlow/Perelman/LGeometry/Hamilton/TraceIntegralGeodesic.lean:19 | `integral_lHamSq_mul_eq_of_geodesic` | r (via alpha) | 17 | **B** | P2-transitive |
| 31 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/CylindricalComparisonRestriction.lean:57 | `restrictedCylinderTensor_norm` | epsilon (via spatialNeckBuffer) | 19 | **C** | identity |
| 32 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/PoleEndpointDirectionalDerivativeConvergence.lean:44 | `tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic` | r (via beta) | 30 | **B** | P1-name-collision |
| 33 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/ScalarScaleComparison.lean:61 | `contMDiff_invRootScalar` | η (via invRootScalar) | - | **A** | property |
| 34 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeck.lean:57 | `spatialNeckClosedCore_isCompact` | epsilon (via spatialNeckClosedCore) | 11 | **A** | property |
| 35 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckCoreSize.lean:22 | `spatialNeckCoreRadiusConstant_pos` | epsilon (via spatialNeckCoreRadiusConstant) | 11 | **C** | property |
| 36 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckCoreSize.lean:42 | `core_dist_le` | epsilon (via spatialNeckCoreRadiusConstant) | 11 | **B** | P3-structure |
| 37 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckCoreSize.lean:118 | `core_edist_le` | epsilon (via spatialNeckCoreRadiusConstant) | 16 | **B** | P3-structure |
| 38 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckOrientedSides.lean:22 | `exists_oriented_compact_end_sides` | epsilon (via spatialNeckBuffer) | 17 | **B** | P3-structure |
| 39 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckOrientedSides.lean:57 | `exists_oriented_compact_end_sides_of_homotopic_disjoint` | epsilon (via spatialNeckBuffer) | 11 | **B** | P3-structure |
| 40 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckPositiveTopology.lean:31 | `compact_end_sides` | epsilon (via spatialNeckBuffer) | 18 | **B** | P3-structure |
| 41 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckRays.lean:24 | `exists_pos_ray_mem_slice` | epsilon (via spatialNeckBuffer) | 21 | **B** | P3-structure |
| 42 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckRays.lean:83 | `eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop` | epsilon (via spatialNeckCoreRadiusConstant) | 20 | **B** | P3-structure |
| 43 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:28 | `neckReflectionMap_involutive` | epsilon (via neckReflectionMap) | 13 | **C** | property |
| 44 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:35 | `neckReflectionMap_smooth` | epsilon (via neckReflectionMap) | 13 | **C** | property |
| 45 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:73 | `spatialNeckReflection_core_iff` | epsilon (via spatialNeckClosedCore) | 14 | **C** | property |
| 46 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:82 | `spatialNeckReflection_image_core` | epsilon (via spatialNeckClosedCore) | 13 | **C** | property |
| 47 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/SpatialNeckReflection.lean:128 | `spatialNeckReflection_pullback_reference` | epsilon (via spatialNeckBuffer) | 13 | **C** | property |
| 48 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/StrongNeck.lean:29 | `strongNeckBackgroundMetric_of_nonpos` | epsilon (via spatialNeckBuffer) | 18 | **C** | identity |
| 49 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/StrongNeckDetection.lean:106 | `cylindricalComparison_jet_zero` | epsilon (via spatialNeckBuffer) | 19 | **A** | identity |
| 50 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/UnitCylinderConnector.lean:91 | `unitCylinder_exists_short_core_connector` | epsilon (via spatialNeckBuffer) | 14 | **A** | property |
| 51 | S | Geometry/Flow/RicciFlow/Perelman/KappaSolutions/UnitCylinderConnector.lean:91 | `unitCylinder_exists_short_core_connector` | epsilon (via spatialNeckClosedCore) | 14 | **A** | property |
| 52 | S | Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/BufferedCanonical.lean:61 | `exists_bufferedCanonical_with_witness` | C2 (via enlarge_constants) | 9 | **B** | P8-proof-body-division |
| 53 | S | Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/InverseSpatialNeckTransfer.lean:65 | `eventually_spatialNeck_inverse_transport_of_window_subset_ball` | r (via alpha) | 13 | **B** | P1-name-collision |
| 54 | S | Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/NoncompactPositiveBufferedCap.lean:27 | `exists_bufferedCanonical_of_noncompact_ancient_positive` | r (via alpha) | 13 | **B** | P1-name-collision |
| 55 | S | Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/NoncompactPositiveCap.lean:139 | `exists_localCap_ball_sandwich_of_noncompact_ancient_positive` | r (via alpha) | 14 | **B** | P1-name-collision |
| 56 | S | Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/StrongNeckModel.lean:23 | `strongNeckBackgroundMetric_eq_reference` | epsilon (via spatialNeckBuffer) | 18 | **A** | identity |
| 57 | S | Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/WitnessNormalizedTimeJets.lean:58 | `hasDerivWithinAt_rescaledTensorTimeTower` | Q (via rescaledTensorTimeTower) | 13 | **C** | identity |
| 58 | S | Geometry/Flow/RicciFlow/Perelman/StandardSolution/TravelingPhaseCoefficients.lean:23 | `traveling_phase_laplacian` | T (via travelingBallPhase) | 20 | **A** | unfold |
| 59 | S | Geometry/Flow/RicciFlow/Perelman/StandardSolution/TravelingPhaseCoefficients.lean:87 | `traveling_phase_time_derivative` | T (via travelingBallPhase) | 20 | **A** | unfold |
| 60 | S | Geometry/Flow/RicciFlow/Perelman/StandardSolution/TravelingPhaseCoefficients.lean:123 | `traveling_phase_gradient_lower` | T (via travelingBallPhase) | 19 | **A** | unfold |
| 61 | S | Geometry/Flow/RicciFlow/Surgery/StandardCap/InsertionMetric.lean:143 | `contDiff_insertionCutoff` | A (via insertionCutoff) | 15 | **C** | property |
| 62 | S | Geometry/Flow/RicciFlow/Surgery/StandardCap/InsertionMetric.lean:158 | `insertionCutoff_mem` | A (via insertionCutoff) | 14 | **C** | property |
| 63 | S | Geometry/Flow/RicciFlow/Surgery/StandardCap/InsertionMetric.lean:161 | `smooth_cutoff_collar` | A (via insertionCutoff) | 14 | **C** | property |
| 64 | S | Geometry/Flow/RicciFlow/Surgery/StandardCap/InsertionMetric.lean:181 | `insertionCollarMetric_inner` | A (via insertionCutoff) | 14 | **A** | identity |
| 65 | S | Geometry/Flow/RicciFlow/Surgery/StandardCap/LocalInitialSpatialCap.lean:189 | `exists_uniform_spatial_cap_frontier_of_local_curvature` | δ (via neckBuffer) | 24 | **B** | P3-structure |
| 66 | S | Geometry/Flow/RicciFlow/Surgery/Topology/BoundedCurvatureAtDistanceNecks.lean:109 | `nonempty_scaled_spatialNeck_of_minimizing_segment` | r (via alpha) | 12 | **B** | P1-name-collision |
| 67 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ChartTailHornBridge.lean:70 | `isPreconnected_upperSide` | δ (via neckBuffer) | - | **B** | P3-structure |
| 68 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ChartTailHornBridge.lean:96 | `isPreconnected_lowerSide` | δ (via neckBuffer) | - | **B** | P3-structure |
| 69 | S | Geometry/Flow/RicciFlow/Surgery/Topology/EventAction.lean:1465 | `lRegularizedAction_le_of_minimal_event_competitor` | r (via gamma) | 15 | **B** | P1-name-collision |
| 70 | S | Geometry/Flow/RicciFlow/Surgery/Topology/EventData.lean:52 | `standardCapRho_eq_expNegInvGlue` | r (via standardCapRho) | 14 | **B** | P9-if-guard |
| 71 | S | Geometry/Flow/RicciFlow/Surgery/Topology/GeometricCutoff.lean:120 | `metric_smooth_up_to` | δ (via neckBuffer) | - | **B** | P3-structure |
| 72 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoricalNeckIncomingAdapter.lean:43 | `incoming_footprint_point_smoothEmbedding` | δ (via neckBuffer) | 18 | **B** | P3-structure |
| 73 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoricalNeckIncomingAdapter.lean:66 | `exists_historical_pullback_solution_from_incoming_slab` | δ (via neckBuffer) | 17 | **B** | P3-structure |
| 74 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoricalNeckIncomingAdapter.lean:148 | `exists_historical_pullback_solution_from_incoming_slab_with_scalar_bounds` | δ (via neckBuffer) | 16 | **B** | P3-structure |
| 75 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction.lean:1511 | `sum_stageRegularizedAction_ge_of_confined_curves_of_curvature_bound` | r (via alpha) | 18 | **B** | P1-name-collision |
| 76 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HornSeparationFrontierScalar.lean:78 | `neckCentralDomain_subset_horn_of_frontier_scalar_lt` | δ (via neckCentralDomain) | 10 | **B** | P3-structure |
| 77 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HornSeparationFrontierScalar.lean:116 | `exists_neck_coordinates_in_horn_of_frontier_scalar_lt` | δ (via neckCentralOpen) | 9 | **B** | P3-structure |
| 78 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HornSeparationSliceTransfer.lean:62 | `eventually_exists_spatialNeck_of_normalizedNeck` | δ (via neckBuffer) | 9 | **B** | P3-structure |
| 79 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckCylindricalChartBridge.lean:132 | `isOpen_neckCentralDomain` | δ (via neckCentralDomain) | 19 | **A** | property |
| 80 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckCylindricalChartBridge.lean:138 | `neckCentralDomain_subset_neckClosedTest` | δ (via neckClosedTest) | - | **A** | property |
| 81 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckCylindricalChartBridge.lean:138 | `neckCentralDomain_subset_neckClosedTest` | δ (via neckCentralDomain) | - | **A** | property |
| 82 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckMarkSideBridge.lean:108 | `referenceMetric_eq_roundCylinderMetric_neckBuffer` | δ (via neckBuffer) | 7 | **A** | identity |
| 83 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckMarkSideBridge.lean:113 | `metricDerivNormSupOn_self_neckClosedTest` | δ (via neckClosedTest) | - | **A** | identity |
| 84 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckSpatialBridge.lean:19 | `exists_partialDiffeomorph` | δ (via neckBuffer) | 10 | **B** | P3-structure |
| 85 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckSpatialBridge.lean:56 | `exists_spatialNeck` | δ (via neckBuffer) | 9 | **B** | P3-structure |
| 86 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckTimeJetConvergence.lean:30 | `shrinkingCylinderMetric_isSolutionOn_neckBuffer_closed` | δ (via neckBuffer) | 18 | **A** | property |
| 87 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckTimeJetConvergence.lean:47 | `exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence` | δ (via neckBuffer) | 17 | **A** | property |
| 88 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NeckTimeJetConvergence.lean:127 | `exists_neckBuffer_metric_difference_time_jets_of_spatial_convergence` | δ (via neckBuffer) | - | **C** | property-no-caller |
| 89 | S | Geometry/Flow/RicciFlow/Surgery/Topology/NormalizedConvergence.lean:19 | `metricCInfConvergenceOn_restrict_of_precision_tendsto_zero` | δ (via neckBuffer) | 16 | **B** | P2-transitive |
| 90 | S | Geometry/Flow/RicciFlow/Surgery/Topology/PresentedStaticCapRecentering.lean:23 | `recenter_fields_of_neck_heq` | c (via scale) | 13 | **B** | P1-name-collision+P7-self-guarded-def |
| 91 | S | Geometry/Flow/RicciFlow/Surgery/Topology/PresentedStaticCapRecentering.lean:65 | `recenter_fields_of_neck_heq_terminal` | c (via scale) | - | **B** | P1-name-collision+P7-self-guarded-def |
| 92 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ProspectiveNeckSurvival.lean:61 | `normalized_restrict_inner` | δ (via neckBuffer) | 19 | **B** | P2-transitive |
| 93 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ProspectiveNeckSurvival.lean:96 | `normalized_restrict_inner_of_index_eq` | δ (via neckBuffer) | 18 | **B** | P2-transitive |
| 94 | S | Geometry/Flow/RicciFlow/Surgery/Topology/RecenterAux.lean:58 | `isCompact_neckClosedTest` | δ (via neckClosedTest) | 7 | **A** | property |
| 95 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:43 | `pullback_shrinkingCylinderMetric_bufferedCylinderRotation` | δ (via bufferedCylinder) | 8 | **C** | identity |
| 96 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:55 | `pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderRotation` | δ (via bufferedCylinder) | 7 | **A** | identity |
| 97 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:64 | `image_bufferedCylinderRotation_neckClosedTest` | δ (via neckClosedTest) | 7 | **A** | identity |
| 98 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:69 | `pullback_shrinkingCylinderMetric_bufferedCylinderOrientation` | δ (via bufferedCylinder) | 8 | **C** | identity |
| 99 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:81 | `pullbackMetricCross_shrinkingCylinderMetric_bufferedCylinderOrientation` | δ (via bufferedCylinder) | 7 | **A** | identity |
| 100 | S | Geometry/Flow/RicciFlow/Surgery/Topology/ShrinkingCylinderIsometries.lean:90 | `image_bufferedCylinderOrientation_neckClosedTest` | δ (via neckClosedTest) | 7 | **A** | identity |
| 101 | S | Geometry/Flow/RicciFlow/Surgery/Topology/StaticCap.lean:145 | `standardCapRho_eq_expNegInvGlue` | r (via standardCapRho) | 14 | **B** | P9-if-guard |
| 102 | S | Geometry/Flow/RicciFlow/Surgery/Topology/TerminalCapBarrier.lean:60 | `exists_cap_midpoint_region_of_normalizedNeck` | δ (via neckBuffer) | - | **B** | P3-structure |
| 103 | S | Geometry/Flow/RicciFlow/Surgery/Topology/TerminalNeckNormalization.lean:77 | `exists_terminal_neckBuffer_pullback_bound` | δ (via neckBuffer) | 10 | **A** | bound |
| 104 | S | Geometry/Flow/RicciFlow/Surgery/Topology/TerminalNeckNormalization.lean:120 | `exists_terminal_neckBuffer_pullback_bound` | δ (via neckBuffer) | 10 | **A** | bound |
| 105 | S | Geometry/Flow/RicciFlow/Surgery/Topology/TerminalSpatialCanonicalAlternatives.lean:719 | `exists_cap_midpoint_region_of_normalizedNeck_of_spatialCap` | δ (via neckBuffer) | 10 | **B** | P3-structure |
| 106 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:1292 | `exists_stage_identity_join` | r (via alpha) | 16 | **B** | P1-name-collision |
| 107 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:1292 | `exists_stage_identity_join` | r (via beta) | 16 | **B** | P1-name-collision |
| 108 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:2002 | `exists_directed_local_joins_of_pullback_germ` | r (via alpha) | 15 | **B** | P1-name-collision |
| 109 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:2002 | `exists_directed_local_joins_of_pullback_germ` | r (via beta) | 15 | **B** | P1-name-collision |
| 110 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:2765 | `exists_smooth_terminal_stage_piece` | r (via beta) | 13 | **B** | P1-name-collision |
| 111 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:2765 | `exists_smooth_terminal_stage_piece` | r (via gamma) | 13 | **B** | P1-name-collision |
| 112 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:3745 | `exists_global_smooth_stage_representative_of_regularizedExtendedAction_eq_regularizedCost` | r (via beta) | 14 | **B** | P1-name-collision |
| 113 | S | Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Index.lean:3745 | `exists_global_smooth_stage_representative_of_regularizedExtendedAction_eq_regularizedCost` | r (via gamma) | 14 | **B** | P1-name-collision |
| 114 | S | Geometry/Flow/RicciFlow/Surgery/Contract/EndNeckFields.lean:246 | `mono_order` | d (via historicalNeckRecognition) | - | **B** | P7-self-guarded-def |
| 115 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornBaseCoordinates.lean:35 | `neckCentralDomain_subset_positive_horn_of_scale_gt` | δ (via neckCentralDomain) | 17 | **B** | P3-structure |
| 116 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornBaseCoordinates.lean:77 | `exists_neck_coordinates_in_horn_of_base_scalar_bound` | δ (via neckCentralOpen) | 16 | **B** | P3-structure |
| 117 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornBaseCoordinates.lean:114 | `exists_pos_height_lower_on_neck_compact` | δ (via neckCentralOpen) | 17 | **B** | P10-inverse-lower-bound |
| 118 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornBaseCoordinates.lean:138 | `exists_neck_coordinates_with_positive_height_of_base_scalar_bound` | δ (via neckCentralOpen) | 16 | **B** | P3-structure |
| 119 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornCutoffRecord.lean:2079 | `exists_record_from_original_backward_with_static` | δ (via neckBuffer) | 9 | **B** | P2-transitive |
| 120 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornCutoffRecord.lean:2150 | `exists_record_from_original_backward_with_neck` | δ (via neckBuffer) | - | **B** | P2-transitive |
| 121 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornCutoffRecord.lean:2195 | `exists_record_from_original_backward` | δ (via neckBuffer) | - | **B** | P2-transitive |
| 122 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornFineCutNecks.lean:77 | `exists_horn_first_scalar_level_inner_scalar_bound_tolerance_of_fineCutNecks` | δ (via neckCentralOpen) | 15 | **B** | P3-structure |
| 123 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornFirstScalarLevel.lean:233 | `exists_horn_first_scalar_level_inner_scalar_bound_tolerance` | δ (via neckCentralOpen) | - | **B** | P3-structure |
| 124 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckCoordinates.lean:26 | `isPreconnected_neckCentralDomain` | δ (via neckCentralDomain) | 11 | **A** | property |
| 125 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckCoordinates.lean:52 | `neckCentralDomain_subset_horn_of_scalar_high` | δ (via neckCentralDomain) | - | **B** | P3-structure |
| 126 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckCoordinates.lean:116 | `neckCentralOpen_le_buffer` | δ (via neckBuffer) | 9 | **A** | property |
| 127 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckCoordinates.lean:116 | `neckCentralOpen_le_buffer` | δ (via neckCentralOpen) | 9 | **A** | property |
| 128 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckCoordinates.lean:167 | `exists_neck_coordinates_in_horn` | δ (via neckCentralOpen) | - | **B** | P3-structure |
| 129 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckCoordinates.lean:217 | `exists_scale_threshold_neck_coordinates_beyond_depth` | δ (via neckCentralOpen) | - | **B** | P3-structure |
| 130 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckEssentiality.lean:125 | `exists_horn_neck_end_separation_tolerance` | δ (via neckCentralOpen) | 9 | **B** | P3-structure |
| 131 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornNeckEssentiality.lean:280 | `exists_deep_horn_neck_end_separation_tolerance` | δ (via neckCentralOpen) | - | **B** | P3-structure |
| 132 | S | Geometry/Flow/RicciFlow/Surgery/Contract/HornReparametrization.lean:151 | `reparametrizeHorns_eq_neck_on_collar` | δ (via neckCentralOpen) | - | **B** | P3-structure |
| 133 | S | Geometry/Flow/RicciFlow/Surgery/Contract/PreparedHistoryCutoff.lean:28 | `lowerOrder_oriented_rotatedDatum` | δ (via monoDelta) | 9 | **B** | P2-transitive |
| 134 | S | Geometry/Flow/RicciFlow/Surgery/Contract/PreparedHistoryCutoff.lean:79 | `exists_selected_neck_of_event_heq` | δ (via monoDelta) | 10 | **B** | P2-transitive |
| 135 | S | Geometry/Flow/RicciFlow/Surgery/Contract/PreparedHistoryCutoff.lean:117 | `nonempty_selected_restriction_retained_append` | δ (via monoDelta) | 9 | **B** | P2-transitive |
| 136 | S | Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/CutoffExtension.lean:39 | `cutoffEta_contDiff` | δ (via cutoffEta) | 17 | **C** | property |
| 137 | S | Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/CutoffExtension.lean:72 | `cutoffEta_section_contMDiff` | δ (via cutoffEta) | 16 | **C** | property |
| 138 | S | Geometry/Flow/RicciFlow/ShortTime/ConjugatingFlow/Variation.lean:79 | `flowTimeRetract_contDiff` | w (via flowTimeRetract) | 16 | **C** | property |
| 139 | S | Geometry/Neck/BufferedRotation.lean:13 | `rotation_image_le` | δ (via bufferedCylinder) | 9 | **C** | property |
| 140 | S | Geometry/Neck/BufferedRotation.lean:70 | `image_bufferedCylinderRotation_controlledCylinder` | δ (via controlledCylinder) | 8 | **C** | property |
| 141 | S | Geometry/Neck/BufferedRotation.lean:107 | `metricDerivENormSupOn_bufferedCylinderRotation` | δ (via controlledCylinder) | 7 | **A** | identity |
| 142 | S | Geometry/Neck/BufferedRotation.lean:133 | `image_bufferedCylinderRotation_height` | δ (via bufferedCylinder) | - | **A** | identity |
| 143 | S | Geometry/Neck/CrossSectionGraph.lean:108 | `exists_graph_of_full_cross_section_and_gradient_close` | c (via scale) | 16 | **B** | P1-name-collision+P7-self-guarded-def |
| 144 | S | Geometry/Neck/FiniteEnd.lean:221 | `axis_mem_interior_of_frontier_eq_central_sphere` | r (via gamma) | 13 | **B** | P1-name-collision |
| 145 | S | Geometry/Neck/HalfBandVolume.lean:26 | `referenceMetric_negative_closed_band_volume` | δ (via bufferedCylinder) | 16 | **A** | exact-value |
| 146 | S | Geometry/Neck/InsertionInput.lean:23 | `openCylinder_inv_le_bufferedCylinder` | δ (via bufferedCylinder) | 9 | **A** | property |
| 147 | S | Geometry/Neck/NormalizedDatum.lean:220 | `isCompact_controlledCylinder` | δ (via controlledCylinder) | 7 | **A** | property |
| 148 | S | Geometry/Neck/NormalizedFootprint.lean:19 | `exists_compact_long_neck_footprint` | δ (via monoDelta) | - | **B** | P2-transitive |
| 149 | S | Geometry/Neck/NormalizedFootprint.lean:19 | `exists_compact_long_neck_footprint` | δ (via neckBuffer) | - | **B** | P2-transitive |
| 150 | S | Geometry/Neck/NormalizedFootprint.lean:117 | `exists_buffered_long_neck_region` | δ (via monoDelta) | - | **B** | P2-transitive |
| 151 | S | Geometry/Neck/NormalizedFootprint.lean:117 | `exists_buffered_long_neck_region` | δ (via neckBuffer) | - | **B** | P2-transitive |
| 152 | S | Geometry/Neck/NormalizedFootprint.lean:221 | `interior_neckClosedSlab` | δ (via neckBuffer) | 15 | **A** | identity |
| 153 | S | Geometry/Neck/Orientation.lean:19 | `orientation_image_le` | δ (via bufferedCylinder) | 8 | **C** | property |
| 154 | S | Geometry/Neck/Orientation.lean:87 | `image_bufferedCylinderOrientation_controlledCylinder` | δ (via controlledCylinder) | 8 | **C** | property |
| 155 | S | Geometry/Neck/Orientation.lean:124 | `metricDerivENormSupOn_bufferedCylinderOrientation` | δ (via controlledCylinder) | 7 | **A** | identity |
| 156 | S | Geometry/Neck/OverlapBand.lean:94 | `full_band_subset_transition_range_of_gradient_close` | c (via scale) | - | **B** | P1-name-collision+P7-self-guarded-def |
| 157 | S | Geometry/Neck/SectionCurvature.lean:117 | `metricRm04_chart_lower_bound_of_normalized` | c (via scale) | - | **B** | P1-name-collision+P7-self-guarded-def |
| 158 | S | Geometry/Comparison/Soul/SoulConvexCore.lean:261 | `geodesicSegment_eqOn_intrinsic` | r (via gamma) | 18 | **B** | P1-name-collision |
| 159 | S | Geometry/Comparison/Variation/Flow.lean:76 | `flowTimeRetract_contDiff` | w (via flowTimeRetract) | 21 | **C** | property |
| 160 | S | Geometry/Comparison/Nonnegative/BoundaryConcavity.lean:673 | `geodesicSegment_eqOn_intrinsic'` | r (via gamma) | - | **B** | P1-name-collision |
| 161 | S | Geometry/Comparison/Nonnegative/BoundaryConcavityTangent.lean:687 | `tangent_geodesicSegment_eqOn_intrinsic` | r (via gamma) | 23 | **B** | P1-name-collision |
| 162 | S | Geometry/Comparison/Nonnegative/BoundaryShift.lean:252 | `shift_geodesicSegment_eqOn_intrinsic` | r (via gamma) | 21 | **B** | P1-name-collision |
| 163 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:23 | `hasDerivAt_hyperbolicSn` | q (via hyperbolicSn) | 12 | **B** | P9-if-guard |
| 164 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:40 | `hasDerivAt_hyperbolicSnD` | q (via hyperbolicSn) | 17 | **B** | P9-if-guard |
| 165 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:62 | `hyperbolicSn_energy` | q (via hyperbolicSn) | 17 | **B** | P9-if-guard |
| 166 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:74 | `hyperbolicSn_continuous` | q (via hyperbolicSn) | 17 | **B** | P9-if-guard |
| 167 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:77 | `hyperbolicSn_pos` | q (via hyperbolicSn) | 12 | **B** | P9-if-guard |
| 168 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:168 | `hasDerivAt_hyperbolicLog` | q (via hyperbolicSn) | 16 | **B** | P9-if-guard |
| 169 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:179 | `hyperbolicLog_tendsto` | q (via hyperbolicSn) | 16 | **B** | P9-if-guard |
| 170 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:213 | `hyperbolicSnRatio_tendsto` | q (via hyperbolicSn) | 22 | **B** | P9-if-guard |
| 171 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:230 | `hyperbolicSn_le_two` | q (via hyperbolicSn) | 21 | **B** | P9-if-guard |
| 172 | S | Geometry/Comparison/Volume/HyperbolicModel.lean:268 | `weightedMean_anti` | q (via hyperbolicSn) | 16 | **B** | P9-if-guard |
| 173 | S | Geometry/Comparison/Volume/Model.lean:79 | `modelRadius_neg_sq` | q (via hyperbolicSn) | - | **B** | P9-if-guard |
| 174 | S | Geometry/Comparison/Volume/Segment/Count.lean:36 | `hyperbolicSn_le_mul_exp` | q (via hyperbolicSn) | 12 | **B** | P9-if-guard |
| 175 | S | Geometry/Comparison/Volume/Segment/Count.lean:45 | `hyperbolicSn_ge_self` | q (via hyperbolicSn) | 10 | **B** | P9-if-guard |
| 176 | S | Geometry/Comparison/Volume/Segment/Polar/Basic.lean:889 | `hyperbolicSn_scale_one` | q (via hyperbolicSn) | - | **B** | P9-if-guard |
| 177 | S | Geometry/Comparison/Toponogov/Completion.lean:113 | `convexOn_squared_distance_defect_of_completion_point_avoidance` | r (via beta) | 18 | **B** | P1-name-collision |
| 178 | S | Geometry/Comparison/Toponogov/Completion.lean:196 | `exists_minimizing_geodesic_with_completion_comparison` | r (via beta) | - | **B** | P1-name-collision |
| 179 | S | Geometry/Comparison/Toponogov/Completion.lean:299 | `convexOn_squared_distance_defect_along_completion_segment_regular_center` | r (via gamma) | 17 | **B** | P1-name-collision |
| 180 | S | Geometry/Comparison/Toponogov/Completion.lean:359 | `convexOn_squared_distance_defect_along_completion_segment` | r (via gamma) | 16 | **B** | P1-name-collision |
| 181 | S | Geometry/Comparison/Toponogov/Completion.lean:390 | `comparisonAngle_shorten_first_of_completion_segment` | r (via gamma) | 15 | **B** | P1-name-collision |
| 182 | S | Geometry/Comparison/Toponogov/Completion.lean:424 | `radialComparisonAngle_nonincreasing_of_completion_segments` | r (via gamma) | 14 | **B** | P1-name-collision |
| 183 | S | Geometry/Comparison/Toponogov/MetricComparisonAngle.lean:51 | `comparisonCosine_scale` | c (via scale) | - | **B** | P1-name-collision+P7-self-guarded-def |
| 184 | S | Geometry/Comparison/Toponogov/MetricComparisonAngle.lean:57 | `comparisonAngle_scale` | c (via scale) | - | **B** | P1-name-collision+P7-self-guarded-def |
| 185 | S | Geometry/Comparison/Toponogov/SquaredDistanceDefectConvexity.lean:51 | `mfderiv_shift_zero_apply_one` | r (via beta) | 20 | **B** | P1-name-collision |
| 186 | S | Topology/Manifold/SublevelCutoff.lean:20 | `sublevelCutoff_mem_Icc` | R (via sublevelCutoff) | 19 | **C** | property |
| 187 | S | Topology/LoopSpace/ThinAnnulus.lean:52 | `thinAnnulusParameter_inner` | h (via thinAnnulusParameter) | 33 | **A** | numerator-vanishes |
| 188 | S | Topology/Embedding/CylinderCapRounding.lean:28 | `cylinderCapCoordinates_apply` | a (via cylinderCapCoordinates) | 23 | **A** | unfold |
| 189 | S | Topology/Embedding/CylinderCapRounding.lean:44 | `cylinderCapCoordinates_symm_apply` | a (via cylinderCapCoordinates) | 23 | **A** | unfold |
| 190 | S | Topology/Embedding/CylinderCapRounding.lean:74 | `contDiff_roundedCapRadiusSq` | a (via roundedCapRadiusSq) | 27 | **A** | unfold |
| 191 | S | Topology/Embedding/CylinderCapRounding.lean:79 | `roundedCapRadiusSq_eq_of_le` | a (via roundedCapRadiusSq) | 28 | **A** | unfold |
| 192 | S | Topology/Embedding/CylinderCapRounding.lean:84 | `roundedCapRadiusSq_eq_of_neg_le` | a (via roundedCapRadiusSq) | 26 | **A** | unfold |
| 193 | S | Topology/Embedding/CylinderCapRounding.lean:89 | `hasDerivAt_roundedCapRadiusSq` | a (via roundedCapRadiusSq) | 27 | **A** | unfold |
| 194 | S | Topology/ThreeManifold/ConnectedSum/SphereCapProfile.lean:41 | `capDensity_of_le` | ρ (via capDensity) | 12 | **C** | numerator-vanishes |
| 195 | S | Topology/ThreeManifold/ConnectedSum/SphereCapProfile.lean:47 | `capDensity_pos'` | ρ (via capDensity) | 14 | **C** | property |
| 196 | S | Topology/ThreeManifold/ConnectedSum/SphereUnitFilling.lean:46 | `radialSigma_of_lt` | s (via radialSigma) | - | **B** | P9-if-guard |
| 197 | S | Topology/ThreeManifold/ConnectedSum/SphereUnitFilling.lean:52 | `radialPhi_of_lt` | s (via radialPhi) | - | **B** | P9-if-guard |
| 198 | S | Topology/ThreeManifold/ConnectedSum/SphereUnitFilling.lean:80 | `radialSigma_eq_phi_mul` | s (via radialSigma) | - | **B** | P9-if-guard |
| 199 | S | Topology/ThreeManifold/ConnectedSum/SphereUnitFilling.lean:80 | `radialSigma_eq_phi_mul` | s (via radialPhi) | - | **B** | P9-if-guard |
| 200 | S | Topology/ThreeManifold/ConnectedSum/SphereUnitFilling.lean:94 | `radialSigma_nonpos` | s (via radialSigma) | - | **B** | P9-if-guard |
| 201 | S | Topology/ThreeManifold/ConnectedSum/SphereUnitFilling.lean:145 | `nu_smul` | s (via radialSigma) | - | **B** | P9-if-guard |
| 202 | S | Topology/PiecewiseLinear/PrismHomotopy.lean:150 | `heightRescale_apply` | h (via heightRescale) | - | **A** | unfold |
| 203 | S | Topology/Morse/Attachment/ManifoldHandle.lean:5859 | `continuous_modelHandleMapRawSymm` | r (via modelHandleMapRawSymm) | - | **C** | uniform-in-param |
| 204 | S | Topology/Morse/Attachment/ManifoldHandle.lean:8874 | `morseUncompressLevel_fixed` | δ (via morseUncompressLevel) | - | **C** | uniform-in-param |
| 205 | S | Topology/Morse/Attachment/ManifoldHandle.lean:9341 | `morseFarExpandTimeSmooth_nonpos` | ρ (via morseFarExpandTimeSmooth) | - | **A** | property |
| 206 | S | Topology/Morse/Attachment/ModelCell.lean:3673 | `modelLevelDampedUnstretch_negPart` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | uniform-in-param |
| 207 | S | Topology/Morse/Attachment/ModelCell.lean:3679 | `modelLevelDampedUnstretch_posPart` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | uniform-in-param |
| 208 | S | Topology/Morse/Attachment/ModelCell.lean:3721 | `contDiff_modelLevelDampedUnstretch` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | property-no-caller |
| 209 | S | Topology/Morse/Attachment/ModelCell.lean:3820 | `modelLevelDampedUnstretch_mem_upper` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | property-no-caller |
| 210 | S | Topology/Morse/Attachment/ModelCell.lean:3876 | `modelLevelDampedUnstretch_norm_sq_le` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | uniform-in-param |
| 211 | S | Topology/Morse/Attachment/ModelCell.lean:4099 | `modelLevelDampedUnstretch_f_le_unstretch_f` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | uniform-in-param |
| 212 | S | Topology/Morse/Attachment/ModelCell.lean:4176 | `modelLevelRadiusDampedUnstretch_negPart` | ε₀ (via modelLevelRadiusDampedUnstretch) | - | **C** | uniform-in-param |
| 213 | S | Topology/Morse/Attachment/ModelCell.lean:4182 | `modelLevelRadiusDampedUnstretch_eq_levelDamped_of_norm_le` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | uniform-in-param |
| 214 | S | Topology/Morse/Attachment/ModelCell.lean:4182 | `modelLevelRadiusDampedUnstretch_eq_levelDamped_of_norm_le` | ε₀ (via modelLevelRadiusDampedUnstretch) | - | **C** | uniform-in-param |
| 215 | S | Topology/Morse/Attachment/ModelCell.lean:4232 | `modelLevelRadiusDampedUnstretch_eq_self_of_norm_large` | ε₀ (via modelLevelRadiusDampedUnstretch) | - | **C** | property-no-caller |
| 216 | S | Topology/Morse/Attachment/ModelCell.lean:4282 | `contDiff_modelLevelRadiusDampedUnstretch` | ε₀ (via modelLevelRadiusDampedUnstretch) | - | **C** | property-no-caller |
| 217 | S | Topology/Morse/Attachment/ModelCell.lean:4406 | `modelLevelRadiusDampedUnstretch_norm_sq_le` | ε₀ (via modelLevelRadiusDampedUnstretch) | - | **C** | property-no-caller |
| 218 | S | Topology/Morse/Attachment/ModelCell.lean:6407 | `contDiff_modelRoundDip` | θ (via modelRoundDip) | - | **C** | uniform-in-param |
| 219 | S | Topology/Morse/Attachment/ModelCell.lean:6711 | `modelLowerRoundMap_posPart` | θ (via modelRoundScale) | - | **A** | property |
| 220 | S | Topology/Morse/Attachment/ModelCell.lean:6865 | `modelLowerRoundMapGlobal_posPart` | η (via modelLowerRoundScaleGlobal) | - | **C** | identity |
| 221 | S | Topology/Morse/Attachment/ModelCell.lean:8121 | `modelLowerRoundMapUnround_posPart` | θ (via modelRoundScale) | - | **A** | property |
| 222 | S | Topology/Morse/Attachment/ModelHandle.lean:4638 | `cutoffFunction_nonpos` | η₁ (via cutoffFunction) | - | **C** | uniform-in-param |
| 223 | S | Topology/Morse/Attachment/ModelHandle.lean:4643 | `cutoffFunction_eq_affine` | η₁ (via cutoffFunction) | - | **C** | uniform-in-param |
| 224 | S | Topology/Morse/Attachment/ModelHandle.lean:4660 | `cutoffFunction_nonneg` | η₁ (via cutoffFunction) | - | **C** | property-no-caller |
| 225 | S | Topology/Morse/Attachment/ModelHandle.lean:4690 | `cutoffFunction_le_one` | η₁ (via cutoffFunction) | - | **C** | property-no-caller |
| 226 | S | Topology/Morse/Attachment/ModelHandle.lean:4909 | `cutoffFunction_deriv_affine` | η₁ (via cutoffFunction) | - | **C** | uniform-in-param |
| 227 | S | Topology/Morse/Attachment/ModelHandle.lean:4933 | `cutoffFunction_differentiableAt_affine` | η₁ (via cutoffFunction) | - | **C** | uniform-in-param |
| 228 | S | Topology/Morse/Attachment/ModelHandle.lean:4952 | `modelSublevelFamilyCutoff_notCritical_of_affine_ratio` | η₁ (via cutoffFunction) | - | **C** | property-no-caller |
| 229 | S | Topology/Morse/Attachment/ModelHandle.lean:5078 | `modelSublevelFamilyCutoff_notCritical_of_ratio_neg` | η₁ (via cutoffFunction) | - | **C** | property-no-caller |
| 230 | S | Topology/Morse/Attachment/ModelHandle.lean:5267 | `modelLevelDampedUnstretch_strict` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | property-no-caller |
| 231 | S | Topology/Morse/Attachment/ModelHandle.lean:5344 | `modelLevelDampedUnstretch_eq_modelFlow` | ε₀ (via modelLevelDampedUnstretch) | - | **C** | property-no-caller |
| 232 | S | Topology/Morse/Attachment/ModelHandle.lean:5344 | `modelLevelDampedUnstretch_eq_modelFlow` | ε₀ (via modelLevelDampedUnstretchTime) | - | **C** | property-no-caller |
| 233 | S | Topology/Morse/Attachment/ModelHandle.lean:5429 | `contDiff_modelLevelDampedUnstretchTime` | ε₀ (via modelLevelDampedUnstretchTime) | - | **C** | property-no-caller |
| 234 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:189 | `modGamma_nonneg` | δ (via modGamma) | 26 | **C** | property |
| 235 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:195 | `modGamma_le_one` | δ (via modGamma) | 29 | **C** | property |
| 236 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:200 | `modGamma_antitone` | δ (via modGamma) | 28 | **C** | property |
| 237 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:315 | `differentiableAt_modGamma` | δ (via modGamma) | 28 | **C** | property |
| 238 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:415 | `hasDerivAt_modifiedNormalForm_posCoord` | δ (via modGamma) | 27 | **A** | identity |
| 239 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:569 | `hasDerivAt_modifiedNormalForm_negCoord` | δ (via modGamma) | - | **C** | property-no-caller |
| 240 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:712 | `contDiff_modGamma` | δ (via modGamma) | 27 | **A** | identity |
| 241 | S | Topology/Morse/Attachment/ModifiedSublevel.lean:799 | `modifiedNormalForm_split` | δ (via modGamma) | 26 | **A** | identity |
| 242 | S | Topology/ProjectiveSpace/AffineThreeBall.lean:24 | `realProjectiveThreeAffineBallMap_zero` | L (via realProjectiveThreeAffineBallMap) | 16 | **A** | numerator-vanishes |
| 243 | S | External/Schoenflies/LocalGrid.lean:633 | `one_le_localGridCount` | ε (via localGridCount) | 20 | **C** | clamped-def |
| 244 | S | External/Schoenflies/SquareMesh.lean:1072 | `two_le_meshCount` | δ (via meshCount) | 10 | **C** | clamped-def |
| 245 | S | External/Schoenflies/SquareMesh.lean:1097 | `squareMesh_pointSet` | δ (via meshCount) | 10 | **C** | clamped-def |
| 246 | S | External/Schoenflies/SquareMesh.lean:1130 | `squareMesh_cover_outerEdges` | δ (via meshCount) | 26 | **C** | clamped-def |
| 247 | S | External/Schoenflies/SquareMesh.lean:1136 | `squareMesh_inner_edge_at_fresh` | δ (via meshCount) | 23 | **C** | clamped-def |
| 248 | S | External/DeGiorgi/UnitBallApproximationCore/Rescaling.lean:28 | `unitBallDilate_apply` | lam (via unitBallDilate) | 38 | **A** | unfold |
| 249 | S | External/ClassificationOfSurfaces/Moise/LineSubdivision.lean:387 | `referenceOuterAffine_planePoint` | a/b (via referenceOuterAffine) | 11 | **A** | unfold |
| 250 | A | Analysis/Sobolev/Nirenberg/TestFunction/WeakDerivative.lean:32 | `nirenbergTest_partial_congr` | h (via diffQuot) | 46 | **C** | diffQuot-uniform-in-h |
| 251 | A | Analysis/Sobolev/Nirenberg/TestFunction/Integration.lean:17 | `memLp_sq_mul_diffQuot` | h (via diffQuot) | 43 | **C** | diffQuot-uniform-in-h |
| 252 | A | Analysis/Sobolev/Interpolation/AnnulusEnergy.lean:142 | `integral_annulus_energy_attachThinAnnulus_le` | h (via affineCylinderInterpolation) | 33 | **A** | bound |
| 253 | A | Analysis/Sobolev/Nirenberg/TestFunction/WeakRegularity.lean:40 | `hasWeakPartialDeriv_nirenbergTestFunction` | h (via diffQuot) | 43 | **C** | diffQuot-uniform-in-h |
| 254 | A | Analysis/Sobolev/Nirenberg/MasterInequality/Coercivity.lean:562 | `principal_pointwise_bound` | h (via diffQuot) | - | **C** | diffQuot-uniform-in-h |
| 255 | A | Analysis/Sobolev/Nirenberg/SubstitutionIdentity/SubstitutionNonSmoothChartBilinear.lean:710 | `nirenbergTestFunction_eq_diffQuot_neg_h` | h (via diffQuot) | - | **C** | property-no-caller |
| 256 | A | Analysis/Sobolev/Nirenberg/MasterInequality/WeakSolution.lean:103 | `exists_extension_nirenberg_master_inequality` | h (via diffQuot) | 41 | **C** | diffQuot-uniform-in-h |
| 257 | A | Analysis/Calculus/SmoothMax.lean:128 | `div` | a | 14 | **A** | identity |
| 258 | A | Analysis/Parabolic/TimeSobolev/H1/Approximation/Trapezoid.lean:49 | `trapezoid_toFun_right` | L (via trapezoid) | 14 | **B** | P2-transitive |
| 259 | A | Analysis/Schauder/Holder/Interpolation.lean:843 | `bufferedParabolicC2HolderGaugeWithLowerJetsConst_eq_factor_mul` | delta (via bufferedParabolicC2HolderGaugeWithLowerJetsFactor) | - | **C** | identity |
| 260 | A | Analysis/Integration/Lp/SpatialSteklov.lean:181 | `coeFn_spatialSteklovAverage` | h (via spatialSteklovAverage) | 43 | **C** | diffQuot-uniform-in-h |
| 261 | A | Analysis/Sobolev/Tools/DifferenceQuotient/Support.lean:28 | `hasCompactSupport_diffQuot_of_hasCompactSupport` | h (via diffQuot) | 34 | **C** | diffQuot-uniform-in-h |
| 262 | A | Analysis/Sobolev/Tools/DifferenceQuotient.lean:115 | `diffQuot_neg` | h (via diffQuot) | - | **C** | property-no-caller |
| 263 | A | Analysis/Sobolev/Nirenberg/TestFunction/Sobolev.lean:153 | `diffQuot_indicator_eq_on_support` | h (via diffQuot) | 43 | **C** | diffQuot-uniform-in-h |
| 264 | A | Analysis/Parabolic/TimeSobolev/H1/Approximation/Ramp.lean:39 | `rampUp_apply` | T (via rampUp) | 17 | **A** | exact-value |
| 265 | A | Analysis/Sobolev/Nirenberg/ChartBilinearDischarge/SubstitutionIBP.lean:749 | `diffQuot_testFactor_support_subset` | h (via diffQuot) | - | **C** | diffQuot-uniform-in-h |
| 266 | A | Analysis/Sobolev/Tools/DiffQuotLocal.lean:102 | `eLpNorm_diffQuot_le_eLpNorm_weakPartial_local` | h (via diffQuot) | 41 | **C** | diffQuot-uniform-in-h |
| 267 | A | Analysis/Sobolev/Nirenberg/TestFunction/Basic.lean:143 | `tsupport_eta_sq_diffQuot_subset` | h (via diffQuot) | - | **C** | property-no-caller |
| 268 | A | Analysis/Sobolev/Nirenberg/MasterInequality/CrossBoundsSummandContinuityIntegrability.lean:68 | `cross_1_summand_compactSupport` | h (via diffQuot) | - | **A** | property |
| 269 | A | Analysis/Integration/Integral/HalfPlaneLaplacian.lean:48 | `boundaryCutoff_laplacian` | ε (via boundaryCutoff) | 41 | **A** | exact-value |
| 270 | A | Analysis/Sobolev/Nirenberg/CrossTermBoundsNonSmooth/CoefficientDifferenceQuotient.lean:40 | `cross_2_pointwise_bound_nonsmooth` | h (via diffQuot) | 32 | **C** | diffQuot-uniform-in-h |
| 271 | A | Analysis/ODE/QuadraticLevelScaling.lean:103 | `quadraticRadialCurve_eq_quadraticLevelScaling` | α | 22 | **B** | P5-implied |
| 272 | A | Analysis/Elliptic/WithBoundary/DirichletNirenbergOperator.lean:245 | `exists_norm_dirichletNirenbergTest_le` | h (via dirichletNirenbergTest) | - | **C** | property-no-caller |
| 273 | A | Analysis/Sobolev/Nirenberg/TestFunction/TranslatedCutoffDiffQuot.lean:190 | `eLpNorm_translatedCutoffSqDiffQuot_le` | h (via diffQuot) | - | **C** | diffQuot-uniform-in-h |
| 274 | A | Analysis/Integration/Lp/Steklov.lean:22 | `steklovAverage_congr_ae` | h (via steklovAverage) | 46 | **C** | diffQuot-uniform-in-h |
| 275 | A | Analysis/Sobolev/Tools/DifferenceQuotientProductWeakLimit.lean:36 | `norm_spatialDiffQuot_eq` | h (via diffQuot) | 43 | **C** | diffQuot-uniform-in-h |
| 276 | A | Analysis/Sobolev/Nirenberg/TestFunction/SourceBounds.lean:267 | `abs_integral_mul_nirenbergTestFunction_le_local` | h (via diffQuot) | 45 | **C** | diffQuot-uniform-in-h |
| 277 | A | Analysis/Sobolev/Nirenberg/TestFunction/Integration.lean:163 | `integral_mul_nirenbergTestFunction_eq_local` | h (via diffQuot) | 41 | **C** | diffQuot-uniform-in-h |
| 278 | A | Analysis/Sobolev/Nirenberg/TestFunction/TranslatedCutoffDiffQuot.lean:319 | `hasWeakPartialDeriv_translatedCutoffSqDiffQuot` | h (via diffQuot) | - | **C** | diffQuot-uniform-in-h |
| 279 | A | Analysis/Sobolev/Nirenberg/TestFunction/FluxBounds.lean:691 | `integral_coefficient_mul_nirenberg_flux_eq_local` | h (via diffQuot) | 44 | **C** | diffQuot-uniform-in-h |
| 280 | A | Analysis/Schauder/Holder/Scaling.lean:977 | `parabolicDilation_mapsTo_preimage` | r (via parabolicPreimage) | - | **C** | property-no-caller |
| 281 | A | Analysis/Complex/DiskAutomorphism/Transitivity.lean:130 | `exp_two_mul_I_eq_neg_cot_fraction` | Real | 37 | **B** | P6-qualified-name |
| 282 | A | Analysis/Parabolic/TimeSobolev/Steklov.lean:196 | `norm_steklovAverage_le` | h (via steklovAverage) | - | **C** | diffQuot-uniform-in-h |
| 283 | A | Analysis/Sobolev/Interpolation/AnnulusEnergy.lean:60 | `fderiv_attachThinAnnulus_normalized_polar` | h (via affineCylinderInterpolation) | 35 | **B** | P11-nonempty-interval |
| 284 | A | Analysis/Sobolev/Nirenberg/TestFunction/Integration.lean:26 | `integral_mul_nirenbergTestFunction_eq` | h (via diffQuot) | 42 | **C** | diffQuot-uniform-in-h |
| 285 | A | Analysis/Sobolev/Interpolation/Cylinder.lean:50 | `fderiv_affineCylinderInterpolation_snd` | h | 33 | **A** | unfold |
| 286 | A | Analysis/Parabolic/Dirichlet/LocalNirenbergTimeEnergy.lean:312 | `exists_abs_integral_mul_chart_source_dual_dirichletNirenbergTest_sum_le` | h (via dirichletNirenbergTest) | 39 | **C** | diffQuot-uniform-in-h |
| 287 | A | Analysis/Sobolev/Nirenberg/CrossTermBoundsNonSmooth/CrossBoundsNonSmooth.lean:230 | `integrable_cross_1_summand_nonsmooth` | h (via diffQuot) | 32 | **C** | diffQuot-uniform-in-h |
| 288 | A | Analysis/Sobolev/Nirenberg/TestFunction/SourceBounds.lean:12 | `compact_diffQuot_integral_sq_le` | h (via diffQuot) | 48 | **C** | diffQuot-uniform-in-h |
| 289 | A | Analysis/Sobolev/Nirenberg/TestFunction/Integration.lean:229 | `neg_integral_weight_mul_nirenbergTestFunction_ge_local` | h (via diffQuot) | - | **C** | property-no-caller |
