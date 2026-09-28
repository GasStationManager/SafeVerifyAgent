# Trust surface: metaprogramming, options, attributes, vendored code

Target: `/home/user/differential-geometry` @ `7a48598d35109aa99d1cc678e2724c213cdf4ff3`
(toolchain `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1` = `0df444a360`). Read-only audit: nothing
compiled, nothing modified. Inputs: `audits/PLAYBOOK.md` §0–§1, `SCAN.md`, `CONE.csv`,
`STATEMENT.md`. Every `file:line` below was read with `sed -n` (paths are relative to
`DifferentialGeometry/` unless they start with `DifferentialGeometry/`). Lean sources cited
are under `/root/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`.

The question at every site: could this change what the kernel accepts, hide something from
`#print axioms`, or make a statement mean something other than it reads?

## Summary (escalations first)

**Escalations (both are provenance/statement-reading escalations, not soundness findings):**

1. **E1 — Vendored statements changed (Part C).** Five of the six Lean-bearing vendored
   projects have changed *statements* relative to upstream, not only relocations and
   toolchain fixes. Each recorded change *drops a hypothesis* or *widens a typeclass*
   (generalizations): Schoenflies (finiteness / `Infinite γ` removed from four theorems and
   from the `EarStep` family of predicates; auto-bound parameters made explicit),
   CanonicalTopology (`InnerProductSpace`+`FiniteDimensional` → `NormedSpace`,
   5+ declarations, two in cone), DeGiorgi (redundant hypotheses removed, including a `MemLp`
   hypothesis from Dirichlet uniqueness; "unchanged or generalized"), RiemannMapping
   (`x ∈ U` hypothesis replaced by an arbitrary point on the normalized seed),
   ClassificationOfSurfaces (two `_ : a ≠ b` / `_ : Injective` hypotheses dropped, a 170-line
   realization-bridge block deleted, Brouwer generalized from the plane to an arbitrary
   inner-product space). Also, and more significantly, the four ClassificationOfSurfaces
   **adapter modules** (`PrePolygonTriangulation`, `PrePolygonDeletion`,
   `TriangleMeshCrosscut`, `TriangleMeshGeometricFree`) restate the upstream results over a
   *different object* (the project's `Schoenflies.PrePolygon`, `Schoenflies.inside`) in
   place of upstream's `PolygonalJordan J` / `J.interiorRegion`. Those statements have no
   upstream counterpart to compare with, and 13+ of their declarations are in the headline's
   dependency cone. No change found narrows a statement or strengthens a hypothesis, and the
   kernel rechecks all of it, so none of this can make the headline *false*. The consequence is
   that **"vendored" gives no upstream warrant for these statements.** The in-cone adapter
   statements must be read as native code. Schoenflies ships no full upstream snapshot
   (only `ArcComplement.lean`), so its recorded changes cannot be diffed locally. That needs
   a clone of `alonamaloh/schoenflies-lean@05a43d2`.
2. **E2 — The `run_cmd` axiom tripwires are local, and 9 of the 28 bind names by string.**
   All 28 are read-only checks that fail the build on violation (Part A). Nine sites build
   names from strings or single-backtick literals. `Lean.collectAxioms` returns `#[]` for an
   unknown constant (`Lean/Util/CollectAxioms.lean:56–67`, `| none => pure ()` at `:67`), so a
   misspelled name would pass silently. I resolved all 125 string-built names against source
   declarations (namespace-tracked grep) and every one exists, so none is vacuous today.
   None of the 28 checks names the headline `poincare_conjecture` or
   `smoothPoincareConjecture_holds`, so the tripwires do not replace `#print axioms` on the
   headline.

**No soundness-affecting site was found:**
- 0 `debug.skipKernelTC`, 0 `maxHeartbeats`, 0 `maxRecDepth`, 0 `synthInstance.*`, 0 `pp.*`
  and 0 `linter.*` in any `.lean` file.
- 0 `@[implemented_by]`, 0 `@[extern]`, 0 `@[csimp]`, 0 `unsafe`, 0 `native_decide`,
  0 `ofReduceBool`, 0 `addDecl` / `setEnv` / `modifyEnv` / `addAndCompile`, 0 `partial def`.
- 0 `macro` / `macro_rules` / `elab` / `syntax` / `#eval` / `initialize` / `simproc`.
- The headline file `Topology/ThreeManifold/Poincare.lean` carries only
  `set_option autoImplicit false`, no attribute and no notation.
- No project instance targets the types the headline statement resolves
  (`↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)`, `EuclideanSpace`).

**Two scanner defects in `SCAN.md`:**
- The per-option table attributes each stacked `set_option … in` site to the *first* option
  in its snippet. `useBackward true` is actually 6 sites, not 12, and
  `respectTransparency false` is 927, not 921. The total, 7,584, is right.
- `External/README.md` lists 3 vendored projects, not 7. TauCeti, CanonicalTopology,
  CanonicalTopologyProvenance and RiemannMapping have `MODIFICATIONS.md` files but no
  README entry.

**Bottom line:** A: every site is read-only and fails the build on violation. B: every option
and attribute is elaboration-strength or cosmetic, with no kernel effect. C: no vendored
statement was narrowed, but vendored statements were changed (E1).

---

## A. The 28 `run_cmd` sites

**How it runs:**
- `run_cmd` elaborates to `elabEvalCore … (CommandElabM Unit)`
  (`Lean/Elab/BuiltinEvalCommand.lean:274–279`).
- The auxiliary `_eval` declaration is added inside `withoutModifyingEnv`
  (`:230–232`), so evaluating the check leaves no declaration behind.
- The action then runs in `CommandElabM`. An exception is caught and passed to
  `logException` (`:249–253`), which logs an **error**. The module then fails, and so does
  `lake build`.
- Every one of the 28 bodies does only three things:
  - calls `Lean.collectAxioms n`, which reads the kernel-checked environment
    (`env.checked.get.find?`, `CollectAxioms.lean:56`);
  - tests `axs.all (allowed.contains ·)` against `[propext, Classical.choice, Quot.sound]`;
  - calls `throwError` on a miss.
- None calls `addDecl`, `addAndCompile`, `setEnv`, `modifyEnv` or `setOption`, or elaborates
  a declaration. `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` or any user axiom
  would fail the check.

**Name binding:**
- *Checked* (``` `` ```): the name is resolved when the check itself is elaborated, and an
  unknown name is an elaboration error.
- *String* (`ns.str "…"`, `` `a ++ `b ``, `` `name ``): nothing is resolved. The name is
  only as good as the text. I resolved every one statically; all exist.

Paths abbreviated: `RF/…` = `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/`,
`PL/…` = `DifferentialGeometry/Topology/PiecewiseLinear/`.

| file:line | what it does (names checked, binding) | can it add to the environment? | fails the build on violation? | verdict |
|---|---|---|---|---|
| `RF/ChildComparisonInputReduction.lean:414` | axiom allowlist, 16 names, checked | no | yes (`throwError`) | benign tripwire |
| `RF/ClosedThreeManifoldTopHomologyCriterion.lean:245` | allowlist, 20 names, **string** | no | yes | benign; all 20 resolve |
| `RF/CollapseDegreeCoreReduction.lean:185` | allowlist, 10 names, checked | no | yes | benign |
| `RF/CollapseDegreeGeneratorReduction.lean:175` | allowlist, 8 names, **`` `a ++ `b ``** | no | yes | benign; all 8 resolve |
| `RF/ComparisonResidualFrontier.lean:101` | allowlist, 6 names, checked | no | yes | benign |
| `RF/FundamentalClassDisconnectedObstruction.lean:89` | allowlist, 6 names, checked | no | yes | benign |
| `RF/FundamentalClassExistenceConnected.lean:163` | allowlist, 13 names, **string** | no | yes | benign; all 13 resolve |
| `RF/FundamentalClassExistenceReduction.lean:143` | allowlist, 14 names, **string** | no | yes | benign; all 14 resolve |
| `RF/FundamentalClassGeneratorFrontier.lean:176` | allowlist, 14 names, checked | no | yes | benign |
| `RF/FundamentalClassInputReduction.lean:130` | allowlist, 7 names, checked | no | yes | benign |
| `RF/FundamentalClassMinimalHypotheses.lean:146` | allowlist, 15 names, **`` `name `` + `ns.append`** | no | yes | benign; all 15 resolve |
| `RF/FundamentalClassReduction.lean:45` | allowlist, 2 names, checked | no | yes | benign |
| `RF/FundamentalClassWellDefined.lean:51` | allowlist, 4 names, checked | no | yes | benign |
| `RF/LocalClassRealizationTransport.lean:99` | allowlist, 2 names, checked | no | yes | benign |
| `RF/LocalOrientationClassGeneratorFrontier.lean:92` | allowlist, 5 names, checked | no | yes | benign |
| `RF/NoncompactVanishingNucleus.lean:101` | allowlist, 9 names, **string** | no | yes | benign; all 9 resolve |
| `RF/PuncturedVanishingHypotheses.lean:160` | allowlist, 17 names, **string** | no | yes | benign; all 17 resolve |
| `DifferentialGeometry/Topology/Algebra/Module/InfiniteCyclicCriterion.lean:125` | allowlist, 12 names, **string** | no | yes | benign; all 12 resolve |
| `DifferentialGeometry/Topology/Homology/ClosedThreeManifoldH3Duality.lean:230` | allowlist, 17 names over two namespaces, **string** | no | yes | benign; all 17 resolve (two declared as `theorem` on its own line, `:48–49`, `:203–204`) |
| `PL/Section34PiercingPackageAxioms.lean:39` | `liftTermElabM`; allowlist, 64 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:66` | same shape, 20 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:94` | 20 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:122` | 20 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:150` | 20 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:178` | 20 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:206` | 20 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:234` | 20 names, checked | no | yes | benign |
| `PL/Section34VertexPreparationAxioms.lean:262` | 1 name, checked | no | yes | benign |

In total, 402 name checks: 197 in the 19 `open Lean in run_cmd do` sites and 205 in the
9 `Section34` sites. All 28 sites are at the end of their files, after the checked
declarations, so nothing later in the same file escapes them. A later file cannot be caught
by them either.

**Verdict A:** all 28 read the environment only, add nothing, and fail the build on
violation. They are sound tripwires but not audit evidence. They cover 402 intermediate
names, not the headline, and 9 sites depend on string names that an unknown constant would
pass vacuously (today all resolve). **No escalation beyond E2.**

---

## B. `set_option` and attributes

### B.1 `set_option` (7,584 sites, recounted with `git grep`)

| option = value | sites | kernel / soundness effect | class |
|---|---|---|---|
| `autoImplicit false` | 6,618 | none. It tightens: an unbound identifier in a signature is an error, not a new universally-quantified implicit. The lakefile already sets it globally. | statement-reading, protective |
| `autoImplicit true` | **2** | none for the kernel. It *can* change statement meaning: a typo in a binder becomes a fresh implicit variable. Sites: `External/Schoenflies/Compose.lean:14`, `External/Schoenflies/InitialReverseTransfer.lean:11`, both kept from upstream. All 6 of their declarations are **outside** the headline's cone *and* import closure (`CONE.csv`). | statement-reading; out of cone → no action |
| `relaxedAutoImplicit false` | 10 | none; tightening | protective |
| `backward.isDefEq.respectTransparency false` | **927** (SCAN: 921) | none (see below) | elaboration strength |
| `backward.isDefEq.respectTransparency true` | 21 | none; restates the default | elaboration strength |
| `backward.defeqAttrib.useBackward true` | **6** (SCAN: 12) | none. `dsimp` may also use `@[backward_defeq]` rfl-lemmas (`Lean/DefEqAttrib.lean:19–25`). All 6 are in `Topology/SphereSeparation/SphereCohomology.lean` (5) and `SphereComparison.lean:54`; 0 in cone. | elaboration strength |
| `debug.skipKernelTC`, `maxHeartbeats`, `maxRecDepth`, `synthInstance.*`, `pp.*`, `linter.*` | **0** | n/a | — |

The lakefile `[leanOptions]` sets `pp.unicode.fun` (cosmetic), `autoImplicit = false`
(protective) and `maxSynthPendingDepth = 3` (elaboration strength; Mathlib's own setting).
It also sets `weak.linter.mathlibStandardSet`, `linter.style.header = false` and
`linter.style.longLine = false`, all cosmetic. Nothing in the lakefile reaches the kernel.
DeGiorgi's history records `maxHeartbeats` / `synthInstance.maxHeartbeats` overrides that
were later *removed* (entry 2026-07-28), and a grep confirms 0 remain.

**`backward.isDefEq.respectTransparency`.** The option is registered at
`Lean/Meta/ExprDefEq.lean:47–51`, with its rationale at `:26–46`, default `true`. When it is
`true`, `Meta.isDefEq` checks non-instance implicit arguments at the caller's transparency
(instance-implicit arguments at `.implicit`). Setting it `false` restores the older behaviour
that *bumps implicit-argument unification to `.default`* transparency, so `simp`, `rw`,
`apply` and instance synthesis may unfold semireducible definitions when matching implicits.
Turning it off only makes the elaborator's *unifier* try harder:
- It is a `Meta`-level option. The kernel's definitional-equality checker has no
  transparency modes and no reads of `Options`: it re-checks every term the elaborator
  produces, whatever path found it.
- A proof accepted under `false` is still a closed term the kernel type-checks. A unification
  that succeeded only by unfolding still produced a term the kernel must accept on its own.

So this is an **elaboration-strength (performance and robustness) matter, not a soundness
one**. The pinned toolchain's own `Init` uses it (e.g. `Init/Data/List/Sort/Basic.lean:67`,
`Init/Data/BitVec/Bitblast.lean:2191`), and the pinned Mathlib contains
**6,909 occurrences in 2,120 files**. Placement: 282 of the 927 are file-level (no `in`);
563 sites either sit immediately before an in-cone declaration or are file-level in a file
with in-cone declarations. Because the setting can also be in force while a *statement*
elaborates, it could in principle pick a different but definitionally equal instance path.
It cannot produce a statement that is not definitionally what the source denotes. The
headline file does not set it.

### B.2 Attributes (`attribute […]` commands: 4,111; `@[…]` tags counted separately)

| attribute kind | count | sound-affecting? | note |
|---|---|---|---|
| `attribute [-instance] …` | 2,843 | no | removes instances, so elaboration can only fail more. Targets: `Tensor0SBundle.tangentSpaceNormedAddCommGroup` (2,537 + 52 qualified + 23 paired), `tensorRSSpaceNormedAddCommGroup` (173), `Bundle.continuousMultilinearMap.instNormedAddCommGroup` (31), `InnerProductSpace.toNormedSpace` (16), `Subtype.metricSpace`/`pseudoMetricSpace` (11) |
| `attribute [local instance] …` | 1,227 (1,226 + 1 with priority 10000) | no for the kernel. File/section-local, so it affects only the meaning of statements *in that file*; the headline file has none. 67 distinct target lists, dominated by structure-field projections (`PointedFlowData.topology/charted` 523, `PointedRiemannianManifold.topology` 210 + 125). `Classical.propDecidable` appears 22× (+1 at priority 10000, `Topology/PiecewiseLinear/MobiusManifold.lean:72`), which only affects which `Decidable` witness an `if` elaborates to. | statement-reading, local |
| `attribute [instance] …` (global, exported) | **33 + 3 `[reducible, instance]`** | no for the kernel. Global instances flow into every importer, including the headline. All 36 were read; each registers a **field projection of a project structure** (`X.topology : TopologicalSpace X.Carrier`, `.charts`, `.finite`, `vertexFintype`, …), or the tangent-space norm on `TangentSpace I x`. None can match `↥(Metric.sphere …)` or `EuclideanSpace ℝ (Fin n)`. 26 are in files in the headline's import closure. | statement-reading; checked, none reaches the headline's types |
| `attribute [simp]` / `[-simp]` | 1 / 3 | no | simp-set only |
| `@[simp]` | 4,874 | no | simp-set only |
| `@[reducible]` | 159 (68 files; 51 immediately precede an in-cone declaration) | no | changes elaborator unfolding (the `rfl`/`simp`/instance surface). The kernel ignores reducibility: `ReducibilityHints` only order its unfolding. Mostly local algebraic-instance scaffolding on quotients/Sobolev spaces. |
| `abbrev` | 2,723 | no | same as `@[reducible]` |
| `@[instance_reducible]` / `@[implicit_reducible]` | 79 / 11 | no | elaborator unfolding of instance-valued defs |
| `@[irreducible]` | **3** (all in cone) | no | can only make elaborator `rfl` *fail*; the kernel still unfolds. `Analysis/Spectral/Tensor/CovGrad/ConnectionDifference/JetTower.lean:202`, `Geometry/Flow/RicciFlow/Extinction/CurveShortening/Sobolev/InitialState.lean:625`, `Tensor/Coordinates/ModelBasis.lean:9` |
| `irreducible_def` | 10 (0 in cone) | no | Mathlib macro; value kernel-checked |
| `opaque` (with value) | **2** | no | `private opaque … := by …`: the value is kernel type-checked, and `collectAxioms` traverses `opaqueInfo` values (`CollectAxioms.lean:62`), so axioms stay visible. `Geometry/Compactness/CheegerGromov/Pointed/Compactness/Construction.lean:1266` (in cone), `Geometry/Flow/RicciFlow/Estimates/Distance/Barrier.lean:937`. The only effect is that the value cannot be unfolded downstream. |
| `@[reassoc]`, `@[ext]`, `@[fun_prop]`, `@[simps]`, `@[refl]`/`symm`/`trans`, `@[norm_cast]`, `@[elab_as_elim]`, `@[to_additive]`, `@[coe]`, `@[deprecated]` | 150 / 33 / 9 / 10 / 13 / 2 / 3 / 1 / 1 / 1 | no | generate lemmas or tag for tactics; generated lemmas are kernel-checked |
| `@[implemented_by]`, `@[extern]`, `@[csimp]` | **0** | — | confirmed by `git grep -w` (0 non-comment hits) |

**Global `attribute [instance]` sites** (all 36, read with `sed -n`):
- `Bundle/TensorProduct.lean:137, :167–170`
- `External/ClassificationOfSurfaces/Moise/GeometricTriangulation.lean:553–554`
- `External/ClassificationOfSurfaces/Moise/PlaneComplex.lean:350–353`
- `Geometry/Comparison/Distance/RadialIntegral.lean:25` (instance body at `Tensor/RSTensor/Defs.lean:33–47`: the model-space norm transported to `TangentSpace I x`)
- `Geometry/Comparison/Volume/Ball/Basic.lean:1147–1149, :1239–1241`
- `Geometry/Flow/RicciFlow/Perelman/KappaSolutions/TerminalSurfaceProduct.lean:48`
- `Geometry/Flow/RicciFlow/Surgery/Contract/MetricStep.lean:423`
- `…/Surgery/Contract/RoundDegreeInputRefutation.lean:27, :65`
- `…/Surgery/Topology/CutCap.lean:35`
- `…/Surgery/Topology/EventData.lean:170`
- `…/Surgery/Topology/HistoryLGeometry/Window.lean:322`
- `…/Surgery/Topology/MetricEvent.lean:111`
- `…/Surgery/Topology/StaticCap.lean:323`
- `Geometry/Metric/Sphere/Quotient/Descent.lean:73`
- `Tensor/Product/Bundle.lean:110`
- `Topology/Manifold/ClosedOriented.lean:21, :71` (structure at `:12–19`)
- `Topology/StandardModel.lean:34` (structure at `:21–32`)
- `Topology/ThreeManifold/CollaredSphereGluing.lean:114`
- `Topology/ThreeManifold/CutCap.lean:35`
- `Topology/ThreeManifold/PartialGraphRealization.lean:60`
- `Topology/ThreeManifold/StandardFactors.lean:31` (structure at `:23–30`)

**`@[implicit_reducible]` (all 11):**
- `Geometry/Compactness/CheegerGromov/Pointed/Convergence/Maps.lean:273, :284, :356, :368`
- `Geometry/Flow/RicciFlow/Compactness/Foundations/PointedMaps.lean:245, :256, :313, :325`
- `Geometry/Metric/TensorInner/FiberNorm/Norm.lean:25`
- `Topology/Manifold/ULift.lean:13`
- `Topology/StandardModel.lean:43`

**`@[reducible]` (first 30 of 159):**
- `Analysis/Parabolic/HarmonicMapHeatFlow/Energy.lean:37, :58`
- `Analysis/Sobolev/DirichletHs/Defs.lean:287`
- `Analysis/Sobolev/Embedding/Reverse/OrderPeeling.lean:1658, :1677`
- `Analysis/Sobolev/Embedding/Tensor/ContinuousRealization.lean:379, :397`
- `Analysis/Sobolev/Euclidean/Completeness/IteratedSobolevQuot.lean:290, :295, :300, :305, :310, :326, :331, :343, :414, :419, :457, :466`
- `Analysis/Sobolev/Hs/Defs.lean:315`
- `Analysis/Sobolev/Tensor/Chart/Wkp/Transport.lean:25`
- `Analysis/Sobolev/Tensor/Fine/Sobolev.lean:125, :131, :137, :143, :149, :166, :172, :186, :192`
- the remaining 129 as a count

**Notation (not asked, but it is the "reads as" surface).** 3,318 sites: 3,310 are
`local notation` (e.g. `local notation "V" => EuclideanSpace ℝ (Fin 2)`), 7 are global and 3
are scoped. None redefines a symbol in the headline statement (`≃ₜ`, `Metric.sphere`,
`EuclideanSpace`, `ℝ`, `𝓡`). One reading hazard: `Tensor/Exterior/Defs.lean:365` declares
`scoped notation:70 α " ∧ " β => DifferentialForm.wedge α β`, which shadows logical `∧`
wherever `DifferentialForm` is opened. That matters to a human reading statements in those
files, not to the kernel.

**Verdict B:** no option or attribute can change what the kernel accepts or hide an axiom.
`respectTransparency false` (927 sites), `useBackward` (6), reducibility tags and `opaque`
are elaboration-strength only. `autoImplicit true` appears twice, both vendored and out of
cone. `implemented_by`, `extern` and `csimp` are zero. Global instances were checked against
the headline statement's types and none applies. **No escalation.**

---

## C. Vendored code (`DifferentialGeometry/External/`)

`External/README.md` documents only DeGiorgi, Schoenflies and ClassificationOfSurfaces. Seven
directories carry a `MODIFICATIONS.md`. The upstream snapshots under `*/upstream/` are
`.tar.gz`, `.lean.txt`, `.json` or `.md`, never `.lean`, so they are not built. Cone counts
(declarations in cone / total) come from `CONE.csv`.

| project | upstream | in cone | modification classes | statement changes |
|---|---|---|---|---|
| **DeGiorgi** | scottnarmstrong/DeGiorgi `4c1b307` | 529 / 1,525 | relocation (imports); compatibility (Mathlib 4.33 renames, linter, `maxHeartbeats` overrides added then **removed**); proof refactors; **semantic**: redundant hypotheses and typeclass assumptions removed ("unchanged or generalized", 2026-08-21, 2026-08-28), `MemLp` removed from the Dirichlet uniqueness theorem, a Prop-valued `def` reclassified as `theorem`, definition/field renames, `NeZero` removed from the pairing theorem; **additions**: positive-test density, strong minimum principle, homogeneous weak-solution equivalence, weak-divergence pairing (2026-09-07) | generalizations and new native theorems inside the vendor directory |
| **Schoenflies** | alonamaloh/schoenflies-lean `05a43d2` | 4,015 / 4,973 | relocation; compatibility (4.33 renames, `letI`→`let`, whitespace); **semantic**: `autoImplicit true` removed from the 128-module closure with parameters bound explicitly; finiteness removed from `Graph.IsAcyclic.longest_path_{source,target}_is_leaf`, `Graph.IsDrawing.edge_radial_unique`, `Graph.IsDrawing.not_three_localDirs_on_edge` (all 4 out of cone); **`Infinite` removed from the ear-step predicates** (`FiniteTransfer.lean:1077–1100`, `EarStep`/`EarStepConstruction`). These are *definitions*. As read, the removed instance was unused by the body, so the predicate is unchanged on its old domain and newly defined elsewhere. Redundant `simp` attributes removed; `ArcSquareChain.lean` is an adapted extraction | generalizations; one definition's domain widened. The only upstream file retained is `ArcComplement.lean` (`upstream/selected-arc_05a43d2.tar.gz`), so there is **no local diff possible** for the rest |
| **ClassificationOfSurfaces** | mccorvie/classification-of-surfaces `e3c7230` | 1,111 / 1,401 | relocation; compatibility (`letI`→`let`, whitespace, header comments); proof refactors in `PlaneComplex`/`LineSubdivision` (`UPSTREAM.patch`); **semantic** in `UPSTREAM.patch`: unused `(_ : a ≠ b)` and `(_ : Function.Injective position)` hypotheses dropped; a 170-line block (`baryEval`, `PlaneComplex.realizationHomeomorph`, `PlaneComplex.toGeometricTriangulation`) deleted from `PlaneComplex`; `[NeZero n]` dropped from private `PolygonalCircle.natCast_eq_natCast_of_lt` (in cone); Brouwer ray/retraction generalized from `Plane` to an arbitrary inner-product space and unit ball, renamespaced (out of cone). **The four adapter modules** (`PrePolygonTriangulation`, `PrePolygonDeletion`, `TriangleMeshCrosscut`, `TriangleMeshGeometricFree`; `UPSTREAM.patch` from line 1036, plus `CROSSCUT_ADAPTATION.patch`, `DELETION_RECOGNITION.patch`, `TWO_EDGE_ADDITION.patch`) **re-target upstream arguments to `Schoenflies.PrePolygon` and `Schoenflies.inside`/`outside`**, replacing `PolygonalJordan J`, `J.interiorRegion`, `J.closedRegion`. Definitions such as `isInteriorArrangementTriangle` are restated over the new objects, and `TWO_EDGE_ADDITION.patch` adds new theorems (`PrePolygon.exists_prePolygon_closed_region_erase_triangle_of_two_edge_free`, in cone). | **semantic, retargeted: E1** |
| **CanonicalTopology** (+ `CanonicalTopologyProvenance`, docs only) | canonical-topology `4ca15d0de` / `f457fa93fe` (Ayush Khaitan) | 944 / 1,097 | relocation (namespace `Poincare`→`DifferentialGeometry`); proof-term ascription rewrites ("statement unchanged"); declaration-name normalization of 7 instances; private helpers promoted to public; **semantic**: `OneDimensionalSphere`, `SpherePuncture.unitSphere_ne_antipode`, `SphereRank`, `SphereCapDuality`, `OneDimensionalLocalCapDuality` generalized from `InnerProductSpace`+`FiniteDimensional` to `NormedSpace` (+`finrank = 1`); private `integralReducedZeroMap_oneDimSphere_neg` loses `FiniteDimensional`; `oneDimUnitSphere_eq_or_antipode` and `unitSphere_ne_antipode` are **in cone**; "native additions retained" inside External modules | generalizations |
| **RiemannMapping** | urkud/mathlib4 PR #33505 `d43061d` (Kudryashov) | 23 / 46 | extraction and relocation; compatibility (renames, `convert!`, `field_simp`, `module`/`public import`, **`import all Mathlib.Analysis.Complex.RiemannMapping`** at `External/RiemannMapping/RiemannMapIncrease.lean:9`, which exposes Mathlib-private declarations and has visibility effect only); duplicate upstream theorems replaced by merged Mathlib ones; **semantic**: the normalized disk seed's `x ∈ U` hypothesis replaced by an arbitrary point `x` | one generalization |
| **TauCeti** | Tau Ceti `3358033` | 4 / 8 | compatibility (Lean 4.34 module syntax removed); **proof** adaptation (Haar-measure transport inlined into equal-dimensional Sard, keeping the existing `MeasureTheory.addHaar_image_eq_zero_of_not_surjective_fderivWithin` name and signature; in cone); extraction of shared lemmas | none recorded |

**The 91 files with `Authors: Bennett Chow, OpenAI`.**
- **Where they are.** None is vendored. All are native:
  - `Topology/VanKampen/` (41)
  - `Topology/Manifold/` (20)
  - `Geometry/Comparison/Toponogov/` (10)
  - `Topology/FundamentalGroup/` (8)
  - `Topology/Algebra/Group/` (6)
  - `Topology/Embedding/` (2)
  - `Topology/Covering/` (2)
  - `Topology/LocallyPathConnected.lean`
  - `Geometry/Metric/CurveEnergy.lean`
- **What they cover.** The Seifert–van Kampen theorem and its machinery:
  - groupoid telescopes, homotopy grids, subdivision, covered paths;
  - pushouts and retract pushouts, free and amalgamated products;
  - cell attachment and its fundamental group, embedded cells and collars;
  - connected sums (neck, finite and parenthesized) and simply connected unions/covers.
- **Fundamental-group computations:** circle, spheres, real projective space, spherical
  quotients, products, basepoint change, homotopy invariance.
- **Free-product algebra:** amalgamated products, finite free-product induction, two-element
  free products, the "Poincaré standard" group presentation.
- **Smooth-manifold collar and transversality results:** compact and smooth bicollars,
  two-sided collars, boundary and normal atlases, codimension-one immersions, normal
  orientation covers, transverse flows and sections, signed clamps, local-diffeomorphism
  ranges.
- **Toponogov / hinge comparison and curve energy:** squared-distance convexity and support,
  hinge algebra, metric and Riemannian shortening.
- **Cone status.** 1,413 declarations, of which 875 (in 68 files) are in the headline's
  cone. This is the fundamental-group half of the route (simple connectivity propagating
  through surgery and connected sums). The co-authorship line marks model-authored code; it
  gets the same scrutiny as any native file and carries no external warrant.

**Verdict C:** every vendored modification is one of three kinds:
- relocation or import-path changes;
- toolchain compatibility (renames, linter, `letI`→`let`, `module` syntax);
- proof refactors — plus **statement changes that are all generalizations**: hypotheses or
  typeclass assumptions removed, and one predicate's instance argument dropped.

The exception is ClassificationOfSurfaces's four adapter modules, whose statements are
**re-targeted to project-native objects**. No change narrows a statement. The kernel rechecks
everything, so none of this threatens the headline's truth. By the escalation rule it is
still **escalated (E1)**: the in-cone vendored statements that changed (the adapter modules,
the CanonicalTopology `NormedSpace` generalizations, the Schoenflies ear-step predicates and
DeGiorgi's generalized theorems) have to be read as native statements. "Vendored" gives them
no upstream warrant. Before that reading can lean on upstream, fetch the Schoenflies upstream
at `05a43d2` and diff it.
