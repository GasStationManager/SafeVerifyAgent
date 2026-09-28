# Route walk 3: topological core of the smooth branch, and the Moise branch

Artifact `/home/user/differential-geometry` @ `7a48598d`, read-only, nothing compiled,
nothing committed. Continues `ROUTE-WALK.md` §6 (depth-5 frontier), parts "Smooth branch,
topological core" and "Moise branch". The analytic core of the smooth branch is another
reader's. Paths are relative to `DifferentialGeometry/` unless they start with `Mathlib` or
`.lake`. Every `file:line` below was opened in this pass (`sed -n`, `cat -n`, or `grep -A`
over the declaration). "Read" means the proof body was read as an argument. "Head" means
only the statement and the calls were read.

**Method note (applies to §4 and §7).** The headline takes no hypotheses and, per
`TRUST.md`, `#print axioms` is standard. So a named predicate that a route theorem takes as
a hypothesis cannot be left open in the kernel sense: the elaborator would reject the
headline. On this route every NOSUPPLIER `no_supplier` row I met is a false negative of the
same kind. The predicate is produced as the conclusion of an `∃`-statement that has a
named `_holds`/producer, or by an in-proof `have … := by refine ⟨…⟩`, which a name-level
scan cannot see. The risk the convention creates is therefore not an invisible `sorry`. It
is a named predicate whose *definition* is weaker than the literature theorem it names, so
that its discharge proves less than the name claims. For every literature-named predicate
on these two branches I read the definition against the standard statement (§4, column
"definition matches"). I found no weakened one.

---

## 1. The two arguments, as a mathematician would state them

### A. Topological core of the smooth branch (Perelman's endgame, topological half)

Input from the analytic half: a finite surgery trace `T` (`FiniteCutCapTrace`,
`Topology/ThreeManifold/CutCap.lean:189`) whose last stage is empty and whose discarded
components are all Poincaré-standard.

A surgery (`SphericalCutCapTransition M Q`, `CutCap.lean:138`) is modelled faithfully. There
are finitely many disjoint smoothly embedded tubes S²×[−2,2] in M (`CutCap.lean:28`). Remove
the open bands |t|<1 to get the core. Cap each of the 2k boundary spheres with a 3-ball
along an orientation-compatible attaching diffeomorphism (`SphericalCapping`,
`CutCap.lean:86`, including `boundary_orientation_reversing`). The capped manifold is
presented as Q ⊔ discarded (`presentation`, `CutCap.lean:144`), and every component of Q
meets the core.

1. **Reversing one surgery is connected sum.**
   `componentwise_isPoincareStandard_of_poincareControlled` (`CutCapPoincareStandard.lean:15`,
   read) proves that if every component of Q and every discarded component is standard, then
   every component of M is. The key step is `exists_diffeomorph_finiteConnectedSum_capComponents`
   (`CutCapConnectedSumSmooth.lean:13`, read):
   M ≅ ⊔_w #( capped components in group w ) # (S²×S¹)^{k_w}.
   It works on a graph whose vertices are the components of the capped manifold and whose
   edges are the tubes (ball pairs). `exists_finite_smooth_quotient_with_factor_lists`
   (`PairedBallFinite.lean:179`, read) inducts on the number of edges. A loop edge (both
   ends in one vertex) contributes N # S²×S¹ (`exists_quotient_homeomorph_loop`,
   `PairedBallLoop.lean:788`, head). Any other edge merges two vertices by connected sum
   (`exists_quotient_homeomorph_merge`, `PairedBallMerge.lean:546`, head). The quotient is
   identified with M itself by a bijective local diffeomorphism
   (`exists_pairedBallQuotient_diffeomorph`, `CapComponentDiffeomorph.lean:260`, read).
   Oriented standard pieces are closed under finite connected sum
   (`isOrientedPoincareStandard_capComponent_finiteConnectedSum`, `CappedPoincareStandard.lean:50`,
   read). This is the standard argument (Perelman III / Morgan–Tian ch. 18,
   Kleiner–Lott §§ 67–68): undo the surgeries, and each non-separating 2-sphere contributes
   an S²×S¹.
2. **Backward induction over the trace.** The last stage is empty, and a `Fin.reverseInduction`
   over step 1 (`CutCapPoincareStandard.lean:47`, read) gives stage 0. Stage 0 is the
   initial manifold (`:62`, read).
3. **Classification of a simply connected standard M**
   (`exists_diffeomorph_standardThreeSphere_of_isPoincareStandard`,
   `PoincareStandardClassification.lean:19`, read):
   - π₁(M) ≅ π₁(#Fᵢ) ≅ *ᵢ π₁(Fᵢ), by Van Kampen
     (`fundamentalGroup_finiteConnectedSum_freeProduct`, `VanKampen/FiniteConnectedSumFreeProduct.lean:277`).
   - A free product is trivial iff every factor is (`coprodI_subsingleton_iff`,
     `Algebra/Group/FreeProduct.lean:17`, read: `Monoid.CoprodI.of_injective`, Mathlib).
   - So each π₁(Fᵢ) is trivial, and each Fᵢ ≅ S³ with orientation
     (`exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor`,
     `PoincareStandardOriented.lean:62`, read).
   - A connected sum of S³s is S³ (`exists_diffeomorph_finiteConnectedSum_standardThreeSphere`,
     `PoincareStandardOriented.lean:86`, read: induction using transport of # and M # S³ ≅ M,
     `SphereCapFillingIsometry.lean:955`).
4. **"A spherical space form with trivial π₁ is S³".**
   `exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group`
   (`ThreeManifold/SphericalSpaceFormTrivial.lean:14`, read). A spherical space form is S³/Γ
   with Γ a finite subgroup of O(4) that preserves orientation and acts freely
   (`SphericalSpaceFormGroup`, `StandardFactors.lean:23`). The proof runs as follows:
   - π₁(S³/Γ) ≅ Γ (`fundamentalGroupManifoldEquiv`, `StandardFactors.lean:558`), from
     Mathlib's covering theory for a free, properly discontinuous action
     (`isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`, `.lake/…/Mathlib/Topology/Covering/Quotient.lean:244`;
     `IsQuotientCoveringMap.fundamentalGroupEquiv`, `…/Mathlib/Topology/Homotopy/Lifting.lean:762`)
     and S³ simply connected.
   - S³ simply connected (`sphereThreeSimplyConnectedSpace`, `FundamentalGroup/Sphere.lean:200`):
     Van Kampen on the two stereographic charts with path-connected overlap
     (`Sphere.lean:84`, read; `VanKampen/SimplyConnectedUnion.lean:34`, read).
   - π₁ trivial gives Γ trivial, so the covering map is bijective, a bijective local
     diffeomorphism, hence a diffeomorphism. It preserves orientation because the projection
     is positive (`StandardFactors.lean:572`).
5. **"S²×S¹ is not simply connected."** `exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle`
   (`StandardFactors.lean:584`) gives π₁(S²×S¹) ≅ π₁(S¹) ≅ ℤ:
   - the projection to the second factor is an isomorphism when the first factor is simply
     connected (`FundamentalGroup/Product.lean:54`, read);
   - S² is simply connected (`Sphere.lean:144`);
   - π₁(S¹) ≅ ℤ comes from Mathlib's covering ℝ → ℝ/ℤ (`FundamentalGroup/Circle.lean:40, :46`, read).

   Then `Multiplicative ℤ` is not a subsingleton (`PoincareStandardOriented.lean:58`), which
   excludes the S²×S¹ case.

Supporting facts on this branch:
- **Connected sum is well defined** up to oriented diffeomorphism, and is associative,
  commutative, has unit S³, and satisfies −(M#N) ≅ (−M)#(−N)
  (`connectedSumLaws_holds`, `ConnectedSum/OrientedLawsAssembly.lean:17`; `connectedSumOpposite_holds`,
  `OppositeSumOrientation.lean:185`). Chart independence is the disc theorem, proved in
  two steps: homogeneity (`BallChartTransportConnected.lean:115`) and Palais's germ
  realization for two charts at a common centre (`BallChartTransportCenter.lean:18`, read to
  the call of `exists_realizesGerm_of_contDiffOn_det_pos`). The gluing map is fixed as the
  antipodal map (`boundaryAttachment`, `ConnectedSum/Construction.lean:445`). So M # S³ ≅ M
  needs no Smale theorem, and `SmaleMunkresSphereIsotopy` is not on the route.
- **Orientation.** An unoriented presentation M ≅ #Fᵢ refines to an oriented one
  (`poincareStandardOrientationRefinement_holds`, `SphericalSpaceFormOrientationClosure.lean:324`).
  Reversing orientation keeps each factor standard: conjugate Γ by a reflection (`:307`), and
  use the antipodal map × id on S²×S¹ (`SphereTwoTimesCircleOrientationClosure.lean:13`).
- **Metric existence** (`nonempty_contMDiffRiemannianMetric_of_sigmaCompact`,
  `Geometry/Metric/Construction/Existence.lean:203`, read) uses Mathlib's partition-of-unity
  section theorem `exists_contMDiffSection_forall_mem_convex_of_local` over the convex set
  of positive-definite forms.
- **Orientability of a simply connected manifold**
  (`exists_compatible_orientation_of_simply_connected`, `Bundle/Orientation/Section.lean:69`,
  read): the orientation double cover is a covering map, and Mathlib's lifting criterion
  gives a section (`Topology/Covering/Sections.lean:5`, read, calling
  `IsCoveringMap.existsUnique_continuousMap_lifts`).
- **`ClosedOrientedManifold.uliftDiffeomorph` exists.** The full name is
  `DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph`
  (`Topology/Manifold/ULift.lean:249`, read). It wraps the generic `uliftDiffeomorph`
  (`ULift.lean:52`, read: `Homeomorph.ulift`, smooth in the singleton-chart atlas because
  the charts are identities). It preserves orientation by `rfl` (`ULift.lean:234, :254`).
  `standardThreeSphereLiftDiffeomorph` (`ThreeManifold/StandardSphere.lean:35`) is this
  map, applied to the round S³ with Mathlib's sphere charts.

### B. Moise branch: every compact topological 3-manifold is smoothable

The Lean follows the proof in **Moise's book** (*Geometric Topology in Dimensions 2 and 3*,
1977). The predicates carry that book's theorem numbers: `Moise251`, `252`, `264`, `303`–`308`,
`311`–`314`, `321`–`324`, `331`, `341`, `351`, `352`, `361`. I have not checked the numbering
against the book (E3). It is not Bing's 1959 proof (side approximation) and not Hamilton's
1976 proof (handle straightening). The ingredients are the loop theorem, tame shells,
pseudo-cells, approximation of graph neighbourhoods, approximation of 3-cells, and then
approximation on open sets.

1. **Triangulation from approximation** (`ChartGluing.lean`, read in full).
   `exists_atlasOn_union_of_plApproximation` does exist, at `ChartGluing.lean:25`. The previous
   reader looked for it outside this file.
   - Given PL atlases A on U and B on V, apply `PLApproximation` to the identity of O = U∩V,
     from B's structure to A's, with error φ = d(x, Oᶜ)/2. This gives a PL homeomorphism f
     of O close to id.
   - Extend f by the identity to a homeomorphism F of X. The extension is continuous because
     the error vanishes at ∂O (`:88–137`).
   - The atlas (A transported by F) ∪ B is PL-compatible, because the transition is
     e⁻¹∘f∘e′ on O (`:153–204`).
   - Compactness then gives a finite induction over chart domains
     (`exists_atlasOn_univ_of_plApproximation`, `:224`).

   This is the standard "fix one chart at a time" argument (Moise ch. 35; Bing).
   `PLApproximation` (`Approximation.lean:18`, read) says: a homeomorphism between open sets
   carrying PL atlases is φ-close to a homeomorphism that is PL in those atlases.
2. **Approximation between PL 3-manifolds** (`plApproximation_of_plApproximationManifold`,
   read by the previous reader). `PLApproximationManifold 3` comes from `Moise352`
   (`Endgame.lean:14`, read). The step: approximate h on U = univ with image equality
   (`exists_plh_approx_of_isOpen`, `Transition361.lean:372`, read →
   `Moise352.exists_approx_image_eq_of_isOpen`, `:283`, read). The approximant is a continuous
   bijection, so invariance of domain makes it a homeomorphism (`Endgame.lean:26–27`).
3. **`Moise352` from `Moise352Open`** (`moise352_of_inwardPush_of_open`, `OpenSourceReduction.lean:226`,
   read). A locally finite PL 3-manifold-with-boundary K is pushed into its own interior by
   a PL map p close to id with a PL left inverse (`Moise352InwardPush`, `SkeletonReduction.lean:65`;
   discharged by `moise352InwardPush_three`, `Moise352InwardPushProof.lean:15` →
   `IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isPLOn_injOn_leftInvOn_dist_lt`,
   `LocallyFiniteInwardPush.lean:16`, read to the stage invariant: a compact exhaustion,
   pushed stage by stage with error budget (1−2^{−i})ψ). Then approximate on the open
   interior and compose.
4. **`Moise352Open` from a §34 cell diagram** (`moise352Open_of_section34CellDiagram`,
   `Section34Endpoint.lean:88`, read).
   - `Section34CellDiagram` (`:59`, read) asks for matched, locally finite families of PL
     cells of dimension ≤ 3. The source family tiles U. Source and target families have the
     same face incidences and intersections, and each pair lies in a carrier of diameter
     < η.
   - Assembly (`exists_isPLHomeomorphInto_of_labelledCells`, `LabelledCellAssembly.lean:357`,
     read to the induction) inducts on cell dimension. Each step extends a PL homeomorphism
     of cell boundaries over the cells (`exists_isPLHomeomorphInto_extension_of_cell`, `:199`),
     then glues by local finiteness.

   This is Moise's cellular-approximation endgame.
5. **Constructing the cell diagram** (`section34CellDiagram`, `Section34Terminal.lean:19`, read).
   - (P0) `section34Control` (`Section34Control.lean:173`, head): a fine combinatorial
     triangulation 𝒦 of U whose simplex stars map under h into small sets H.
   - (33/34.1) `controlledGraphNeighborhood moise341` (`ControlledGraphNeighborhood.lean:58`,
     `:232`): a regular neighbourhood of the 1-skeleton, split into vertex balls and edge
     disks, plus a PL embedding f₁ of it close to h. This consumes Moise 34.1
     (approximation of an embedding of a PL 3-ball in ℝ³).
   - Face balls (`exists_section34FaceBalls`, `Section34FaceBalls.lean:624`, read): for each
     2-simplex s, a PL 3-cell containing h(rim s) whose boundary crosses the graph
     neighbourhood transversally and carries its homology.
   - Normalization (`section34NormalFamily`, `Section34Normalization.lean:93`, read): repeat
     compressions (`exists_section34Compression`, `Section34CompressionLeaf.lean:78`) and
     bigon slides (`exists_section34BigonSlide`, `Section34BigonSlide.lean:24`) while
     either applies. Each one lowers a rank (`exists_section34TerminalFaceBalls`,
     `Section34TerminalFaceBalls.lean:196`). At the terminal state the trace of each face
     ball on the frontier of the graph neighbourhood is a disjoint union of circles, each
     meeting each incident edge disk once (`Section34Trace`, `Section34Frame.lean`, read in
     the `Section34NormalPlus` definition).
   - Face disks (`exists_section34FaceDisks`, `Section34FaceDisks.lean:36`, head), residual
     balls filling the tetrahedra (`exists_section34ResidualBalls`, `Section34ResidualBalls.lean:33`,
     head), and recognition that the target cells tile with the source incidences
     (`section34TargetRecognition_of_tiling`, `Section34TargetRecognitionOfTiling.lean:796`,
     head).

   The wildness of h(face) is never approximated directly. The target 2-cells are disks
   inside the boundaries of PL face balls, chosen only to lie in small carriers. That is the
   Moise/Bing idea, and it is why the loop theorem is needed (next item).
6. **Moise 34.1 on a PL ball** (`moise341 = moise341_of_onNeighborhood moise331OnTube`,
   `Moise341Producer.lean:21`, read; `Section34Compact.lean:163, :292`, read). This is a
   compact copy of item 5 over ℝ³ (the `Section34Compact*` vocabulary). It rests on:
   - Moise 33.1 on tubes (`moise331OnTube`, `Moise341Producer.lean:14`), from 32.3 and 32.4
     (pseudo-cells, `Section32PseudoCell.lean:245, :260`) and 26.4 (orientable extended
     loop theorem: a π₁-compressible two-sided surface in the interior has a compressing
     disk, `ExtendedLoopTheoremStatement.lean:16`, read);
   - 26.4 from the loop theorem 25.2 (`moise252`, `LoopTheorem/Moise252Producer.lean:14`,
     read). That is a Shapiro–Whitehead tower argument: `orientableCoverReductionStatement`
     (`CoverReductionOrientableProducer.lean:208`), `generalPositionInDoubleBuffered`
     (`GeneralPositionInDouble.lean:877`) and `descentStepOrientableStatement`
     (`DescentStepOrientable.lean:212`), all hypothesis-free;
   - 30.7 on nested solid tori (`moise307`, `Section30Torus.lean:118`), also from 25.2.
7. **PL ⇒ smooth** (`plSmoothingModelCompact_three`, `PLSmoothingCompact.lean:411`).
   - Triangulate by a combinatorial 3-manifold (`exists_pLTriangulation_isCombinatorialManifold`,
     `Combinatorial.lean:263`, read: a finite PL piece, subdivided until the links are
     spheres).
   - Filter by derived neighbourhoods of skeleta. Each step attaches a PL handle whose index
     is the dimension of the simplex (`exists_pl_three_handle_filtration`,
     `DerivedNeighborhoodHandleFiltration.lean:18`, read; author Yuan Liao).
   - Build a smooth ∂-manifold stage by stage (`isSmoothHandleStage_step`, `PLSmoothingCompact.lean:245`,
     read to the k=1 case). Before gluing, a boundary-preserving self-homeomorphism θ makes
     the topologically embedded attaching disks smooth (`exists_homeomorph_smooth_disks_of_isClosedEmbedding`).
     This is 2-dimensional taming on the boundary surface.
   - 2-sphere recognition: a smooth surface homeomorphic to S² is diffeomorphic to S²
     (`nonempty_diffeomorph_sphere_of_homeomorph_sphere`, `:78` → `Homeomorph.nonempty_diffeomorph_sphere`,
     `Topology/Manifold/SphereDiffeomorph.lean:50`, read: triangulate in charts, then smooth
     the planar triangulation).
   - At the end the boundary complex is empty, so the manifold is boundaryless (`:368–409`).
   - `interiorChartedSpace` / `interiorIsManifold` (`Topology/Manifold/InteriorAtlas.lean:17, :33`,
     read) re-model it on ℝ³. `pullbackChartedSpace` / `instIsManifoldPullback`
     (`Homeomorph/Transport.lean:12, :47`, read) transport the structure along the
     homeomorphism.

   This is the classical "PL ⇒ smooth in dimension 3" argument.

---

## 2. Per-theorem records

Legend: **Lit.** = literature theorem; **Named** = Prop-valued hypothesis, and where it is
discharged; **Comp.** = computation not read (§5).

### A (topological core)

| decl (file:line) | statement | Lit. | calls | Named | notes |
|---|---|---|---|---|---|
| `SphericalCutCapTransition.componentwise_isPoincareStandard_of_poincareControlled` `ThreeManifold/CutCapPoincareStandard.lean:15` | discarded and next-stage components standard ⇒ every component of M standard | reversing a surgery along 2-spheres is # (Perelman III; Morgan–Tian ch. 18) | `exists_diffeomorph_finiteConnectedSum_capComponents` (`CutCapConnectedSumSmooth.lean:13`), `isOrientedPoincareStandard_capComponent_finiteConnectedSum` (`CappedPoincareStandard.lean:50`), `poincareStandardOrientationRefinement_holds` (`SphericalSpaceFormOrientationClosure.lean:324`), `componentwise_isOrientedPoincareStandard_closedOrientedUnion` (`PoincareStandardUnion.lean:11`), `componentwise_isPoincareStandard_iff_of_diffeomorph` (`PoincareStandardComponentTransport.lean:13`) | `hctrl : E.poincareControlled` comes from the trace (analytic side, via `controlled_extinct_trace`); `hnext` is the induction hypothesis | read; matches |
| `FiniteCutCapTrace.componentwise_…_extinct` `:47`, `isPoincareStandard_of_initialIdentification_…` `:62` | backward induction from the empty last stage | same | `Fin.reverseInduction`, `ConnectedComponents.isEmpty_iff_isEmpty` (Mathlib) | none | read |
| `exists_diffeomorph_finiteConnectedSum_capComponents` `CutCapConnectedSumSmooth.lean:13` | M ≅ ⊔_w #(capped comps in w) # (S²×S¹)^{k w} | graph-of-components form of undoing surgery | `PairedBallGluing.exists_finite_connectedSum_diffeomorph` (`PairedBallFinite.lean:373`), `exists_pairedBallQuotient_diffeomorph` (`CapComponentDiffeomorph.lean:260`), `exists_smoothBoundaryAtlas_puncturedFactor` (`PairedBallPuncturedAtlas.lean:43`) | none | read |
| `exists_finite_smooth_quotient_with_factor_lists` `PairedBallFinite.lean:179` (private) | strong induction on the number of edges; a loop gives `k+1`, a merge gives `L ++ K` | same | `exists_quotient_homeomorph_loop` (`PairedBallLoop.lean:788`, head), `exists_quotient_homeomorph_merge` (`PairedBallMerge.lean:546`, head), `connectedSumOrientedTransport_holds` (`OrientedTransport.lean:149`), `finiteConnectedSum_perm_orientedDiffeomorph` (`FiniteCongruence.lean:29`), `nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts` (`ChoiceIndependence.lean:11`) | none | read to `:330` |
| `exists_pairedBallQuotient_diffeomorph` `CapComponentDiffeomorph.lean:260` | the ball-pair quotient of the capped manifold ≅ M | the cap is glued exactly where it was cut | `capRaw_homeomorph_local` (`:208`), `IsLocalDiffeomorph.diffeomorphOfBijective` | `hcore`, `hseam` are smoothness side conditions supplied by the caller from `exists_finite_connectedSum_diffeomorph` | read |
| `exists_diffeomorph_standardThreeSphere_of_isPoincareStandard` `PoincareStandardClassification.lean:19` | simply connected standard M ≅ S³ | Perelman endgame / Kneser–Milnor bookkeeping | `fundamentalGroupMulEquivOfHomotopyEquiv`, `fundamentalGroup_finiteConnectedSum_freeProduct` (`VanKampen/FiniteConnectedSumFreeProduct.lean:277`), `coprodI_subsingleton_iff` (`Algebra/Group/FreeProduct.lean:17`), `…_of_isStandardFactor` (`PoincareStandardOriented.lean:62`), `…_finiteConnectedSum_standardThreeSphere` (`:86`) | none | read |
| `fundamentalGroup_finiteConnectedSum_freeProduct` `VanKampen/FiniteConnectedSumFreeProduct.lean:277` | π₁(#Lᵢ) ≅ *ᵢ π₁(Lᵢ) | Seifert–van Kampen for # | `finiteConnectedSumFreeProduct_of_connectedSumBased` (`:135`, read: list induction, `coprodIFinConsEquivCoprod`), `fundamentalGroup_connectedSum_freeProduct` (`:257`, read) → `fundamentalGroupEquiv_connectedSum` (`VanKampen/ConnectedSum.lean:142`, read: neck VK), `fundamentalGroupComplementEquiv` (`:90`: removing a 3-ball keeps π₁), `exists_embeddedCellConnectedSum_homeomorph_connectedSum` (`ConnectedSumNeckRealization.lean:593`) | `FiniteConnectedSumFreeProduct`, `connectedSumBasedFreeProduct` are defs discharged here | VK core `fundamentalGroup_isPushout` (`VanKampen/Based.lean:498`, head) is Brown's groupoid form over selected base points |
| `coprodI_subsingleton_iff` `Algebra/Group/FreeProduct.lean:17` | *ᵢGᵢ trivial ⇔ all Gᵢ trivial | elementary | `Monoid.CoprodI.of_injective`, `induction_on` (Mathlib) | none | read |
| `exists_orientedDiffeomorph_standardThreeSphere_of_isStandardFactor` `PoincareStandardOriented.lean:62` | standard factor with trivial π₁ is S³ | Γ trivial ⇒ S³; S²×S¹ has π₁ ℤ | `…_of_subsingleton_group` (`SphericalSpaceFormTrivial.lean:14`), `exists_fundamentalGroupMulEquivInt_sphereTwoTimesCircle` (`StandardFactors.lean:584`) | none | read |
| `exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group` `ThreeManifold/SphericalSpaceFormTrivial.lean:14` | Γ trivial ⇒ S³/Γ ≅ S³ (oriented) | see §1 A4 | `G.projection_eq_iff`, `projection_isLocalDiffeomorph.diffeomorphOfBijective`, `projection_positive` | none | read |
| `fundamentalGroupManifoldEquiv` `StandardFactors.lean:558` (def) | π₁(S³/Γ) ≅ Γ | covering-space theory | Mathlib `Covering/Quotient.lean:244`, `Homotopy/Lifting.lean:762`; `sphereThreeSimplyConnectedSpace` (`FundamentalGroup/Sphere.lean:200`) | none | read |
| `exists_diffeomorph_finiteConnectedSum_standardThreeSphere` `PoincareStandardOriented.lean:86` | #S³ ≅ S³ | S³ is the unit of # | `connectedSum_unorientedTransport_holds` (`BallChartTransportConnected.lean:175`), `nonempty_diffeomorph_connectedSum_sphere_right_unit` (`SphereCapFillingIsometry.lean:955`, head), `nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph` (`OppositeInvarianceObstruction.lean:52`) | none | read |
| `connectedSumLaws_holds` `ConnectedSum/OrientedLawsAssembly.lean:17` | # unit / commutative / associative / transport | well-definedness of # (disc theorem) | `sphereUnitLaws_holds` (`OrientedLaws.lean:319`), `connectedSumCommutative_holds` (`:108`), `connectedSumAssociative_holds` (`AssociativeFlattening.lean:1559`) ← `connectedSumFlatteningIsoCanonical_holds` (`:1441`), `connectedSumOrientedTransport_holds` (`OrientedTransport.lean:149`) ← `selfTransport_holds` (`BallChartTransportConnected.lean:172`) ← `ballChartTransport_of_center_eq` (`BallChartTransportCenter.lean:18`) | all discharged (see §4) | read to the leaves named |
| `poincareStandardOrientationRefinement_holds` `SphericalSpaceFormOrientationClosure.lean:324` | unoriented standard ⇒ oriented standard | orientation reversal of standard factors | `…_of_factorOrientationClosure` (`PoincareStandardFactorOrientationReduction.lean:12`) → `…_of_connectedSumOpposite_and_factorOrientationClosure` (`PoincareStandardFactorOrientation.lean:46`, read), `connectedSumOpposite_holds` (`OppositeSumOrientation.lean:185`), `sphericalSpaceFormOrientationClosure_holds` (`:307`, read), `sphereTwoTimesCircleOrientationClosure_holds` (`SphereTwoTimesCircleOrientationClosure.lean:13`) | discharged | read |
| `nonempty_contMDiffRiemannianMetric_of_sigmaCompact` `Geometry/Metric/Construction/Existence.lean:203` | σ-compact T2 ⇒ smooth metric | partition of unity | Mathlib `exists_contMDiffSection_forall_mem_convex_of_local`; `convex_posDefForms` (`:186`), `localFiber_contMDiffOn` (`:162`) | none | read |
| `VectorBundle.exists_compatible_orientation_of_simply_connected` `Bundle/Orientation/Section.lean:69` | simply connected base ⇒ compatible orientation | orientation double cover is trivial | `Covering.exists_unique_section` (`Topology/Covering/Sections.lean:5`, Mathlib lifting), `orientationCore_isCoveringMap` (not opened), `compatibleOrientation_of_section` (`:38`, read) | none | read |
| `ClosedOrientedManifold.uliftDiffeomorph` `Topology/Manifold/ULift.lean:249` (def) | M ≅ ULift M | bookkeeping | `uliftDiffeomorph` (`:52`, read) | none | exists; see §1 |

### B (Moise branch)

| decl (file:line) | statement | Lit. | calls | Named | notes |
|---|---|---|---|---|---|
| `exists_atlasOn_union_of_plApproximation` `PiecewiseLinear/ChartGluing.lean:25` | PL atlases on U, V ⇒ PL atlas on U∪V | Moise ch. 35 / Bing: adjust one chart by a PL approximation of the transition | `hA` applied at `:66`; `AtlasOn.transport`, `.union` (`Manifold/PartialAtlas.lean:95, :117`, read) | `hA : PLApproximation n`, from the caller | read; located |
| `exists_atlasOn_union_of_plApproximation_of_metrizable` `ChartGluing.lean:207` | the same after choosing a metric | Urysohn metrization | `TopologicalSpace.metrizableSpaceMetric` (Mathlib) | `hA` | read |
| `moise352_of_inwardPush_of_open` `OpenSourceReduction.lean:226` | InwardPush ∧ Open ⇒ `Moise352` | reduction of a ∂-manifold to its interior | `isPLHomeomorphInto_comp_of_leftInvOn` | `Moise352InwardPush` (`SkeletonReduction.lean:65`) → `moise352InwardPush_three`; `Moise352Open` (`OpenSourceReduction.lean:210`) → `moise352Open` | read |
| `moise352InwardPush_three` `Moise352InwardPushProof.lean:15` | one line to `LocallyFiniteInwardPush.lean:16` | collar push | stage lemmas (`InwardPushStages`, `StageInwardPush`, not opened) | none | read to the stage invariant `:57–70` |
| `plApproximationManifold_three_of_moise352` `Endgame.lean:14` | `Moise352 3` ⇒ `PLApproximationManifold 3` | Moise 35.2 ⇒ approximation of homeomorphisms | `exists_plh_approx_of_isOpen` (`Transition361.lean:372`), `isOpenMap_of_continuous_injective` (`Topology/InvarianceOfDomainManifold.lean:78`) | `h352` | read. Invariance of domain is vendored (E2) |
| `Moise352.exists_approx_image_eq_of_isOpen` `Transition361.lean:283` | approximation on open U with f(U) = h(U) | closeness gives surjectivity | `exists_locallyFinitePieceTower_of_isOpen`, `exists_continuous_pos_surjective_of_dist_lt`, `exists_continuous_pos_ball_subset_open`, `isOpen_image_of_continuousOn_injOn` | `h352` | read (E4) |
| `moise352Open_of_section34CellDiagram` `Section34Endpoint.lean:88` | cell diagram ⇒ `Moise352Open 3` | Moise §34/35 | `exists_isPLHomeomorphInto_dist_lt_of_cellDiagram` (`:21`) → `exists_isPLHomeomorphInto_of_labelledCells` (`LabelledCellAssembly.lean:357`) | `Section34CellDiagram` (`:59`) → `section34CellDiagram` | read |
| `exists_isPLHomeomorphInto_of_labelledCells` `LabelledCellAssembly.lean:357` | matched cell families ⇒ PL homeomorphism with f(cell) = cell | cellular extension by induction on dimension | `exists_isPLHomeomorphInto_extension_of_cell` (`:199`), `exists_isPLHomeomorphInto_row` (`:297`), `exists_isPLHomeomorphInto_union_of_locallyFinite_pieces` | none | read to the induction header |
| `section34CellDiagram` `Section34Terminal.lean:19` | `Section34CellDiagram` | Moise §34 | `section34NormalFamilyStatement` (`Section34Normalization.lean:174`), `exists_section34FaceDisks` (`Section34FaceDisks.lean:36`), `exists_section34ResidualBalls` (`Section34ResidualBalls.lean:33`), `section34TargetRecognition_of_tiling` (`Section34TargetRecognitionOfTiling.lean:796`), `section34SourceFace_iff_cutLe`, `carrier_subset_and_dist_lt_of_parent` | its conclusion; no hypotheses | read |
| `section34NormalFamily` `Section34Normalization.lean:93`; `section34NormalFamilyStatement` `:174` | fine triangulation + graph nbhd + terminal face balls ⇒ `Section34NormalPlus` | Moise §34 normalization | `section34Control` (`Section34Control.lean:173`), `controlledGraphNeighborhoodStatement` (`ControlledGraphNeighborhood.lean:232`) = `controlledGraphNeighborhood moise341` (`:58`), `exists_section34FaceBalls` (`Section34FaceBalls.lean:624`), `exists_section34TerminalFaceBalls` (`Section34TerminalFaceBalls.lean:196`), `exists_section34Compression` (`Section34CompressionLeaf.lean:78`), `exists_section34BigonSlide` (`Section34BigonSlide.lean:24`), `section34Trace_of_noOperation` | `Section34ControlStatement`, `ControlledGraphNeighborhoodStatement` (`Section34Statements.lean:14, :25`) discharged; `Section34Compression` / `Section34BigonSlide` are case hypotheses (an operation is available), not open results | read |
| `exists_section34FaceDisks` `Section34FaceDisks.lean:36`; `exists_section34ResidualBalls` `Section34ResidualBalls.lean:33`; `section34TargetRecognition_of_tiling` `Section34TargetRecognitionOfTiling.lean:796` | from `Section34NormalPlus`: face disks, residual 3-cells, tiling recognition | PL Schoenflies-type recognition | not opened below the signature | take `Section34NormalPlus` / `FaceDiskFamily` / `ResidualPlus`, supplied by the previous step | head |
| `moise341` `Moise341Producer.lean:21` | PL 3-ball embedding in ℝ³ ≈ PL embedding | Moise 34.1 | `moise341_of_onNeighborhood` (`Section34Compact.lean:292`, read) → `moise341OnNeighborhood` (`:163`, read to `:200`); `moise331OnTube` (`:14`) ← `moise323`, `moise324` (`Section32PseudoCell.lean:260, :245`), `moise264Orientable` (`LoopTheorem/Moise252Producer.lean:19`) | `Moise331OnTube` (`Section33TubeApproximation.lean:13`, read), `Moise323`/`Moise324` (`PseudoCell.lean:407, :422`, not opened), `Moise264Orientable` (`ExtendedLoopTheoremStatement.lean:16`, read) — all discharged | read |
| `moise252` `LoopTheorem/Moise252Producer.lean:14` | loop theorem, orientable case | Papakyriakopoulos loop theorem (Shapiro–Whitehead tower) | `moise252_of_lemmaTwoOrientable` (`CoverReductionOrientableProducer.lean:235`), `lemmaTwoBufferedOrientableStatement_of_generalPosition_of_descentStepOrientable` (`LemmaTwoOrientable.lean:71`), `generalPositionInDoubleBuffered` (`GeneralPositionInDouble.lean:877`), `descentStepOrientableStatement` (`DescentStepOrientable.lean:212`), `orientableCoverReductionStatement` (`CoverReductionOrientableProducer.lean:208`) | all hypothesis-free | head only; the tower bodies are frontier |
| `moise307` `Section30Torus.lean:118` | nested solid tori ⇒ cylindrical diagram in the shell | Moise 30.7 | `moise307_of_moise252`, `moise306_of_moise252`, `not_nullhomotopic_inclusion_of_nested_tori` (`NestedTori.lean:245`) | `Moise252` | read `:100–118` |
| `exists_pLTriangulation_isCombinatorialManifold` `Combinatorial.lean:263` | compact PL manifold ⇒ combinatorial triangulation | subdivide until links are spheres | `exists_pLPiece_univ`, `exists_isSubdivision_isCombinatorialManifold_succ` (not opened) | none | read |
| `exists_pl_three_handle_filtration` `DerivedNeighborhoodHandleFiltration.lean:18` | handle filtration from derived neighbourhoods | standard PL handle theory | `exists_derivedNeighborhood_filtration`, `isPLThreeHandleAttachment_derivedNeighborhoodCell` | none | read |
| `isSmoothHandleStage_step` `PLSmoothingCompact.lean:245` | smooth stage + PL k-handle ⇒ smooth stage | smooth handle attachment in dim 3 | `isSmoothHandleStage_of_attachment` (`:130`), `exists_homeomorph_smooth_disks_of_isClosedEmbedding`, `isSmoothHandleStage_adjunction_{zero,one,two,three}` | none | read to k=1. `IsSmoothHandleStage` (`Topology/Handle/SmoothStage.lean:15`, read) is "homeomorphic to a compact smooth ∂-manifold, boundary to boundary" |
| `nonempty_diffeomorph_sphere_of_homeomorph_sphere` `PLSmoothingCompact.lean:78` | smooth S ≅ₜ S² ⇒ S ≅ₘ S² | uniqueness of smooth structure on S² | `Homeomorph.nonempty_diffeomorph_sphere` (`Topology/Manifold/SphereDiffeomorph.lean:50`, read) | none | read |
| `interiorChartedSpace` / `interiorIsManifold` `Manifold/InteriorAtlas.lean:17, :33`; `pullbackChartedSpace` / `instIsManifoldPullback` `Manifold/Homeomorph/Transport.lean:12, :47` | re-model and transport an atlas | bookkeeping | `interiorChart`, `IsManifold.mk'` | none | read |

---

## 3. Escalations (ranked)

None is a gap. Every argument read above matches the standard one. These are the places
where the audit cannot rest on the name alone, or where the route relies on something
outside the native code.

**E1 (medium, audit method; affects NOSUPPLIER and TRUST use).** On this route, "undischarged
named predicate" cannot happen, and every NOSUPPLIER `no_supplier` row I met is a false
negative.
- `Section34GraphFrame` is the conclusion of the `∃` in `ControlledGraphNeighborhoodStatement`
  (`Section34Statements.lean:25–40`). It is produced by `controlledGraphNeighborhood`
  (`ControlledGraphNeighborhood.lean:58–230`).
- `Section34NormalPlus` is the conclusion of `Section34NormalFamilyStatement`
  (`Section34Normalization.lean:77–91`). It is produced by the tuple at `:166–171`.
- `Section34CompactFaceBallInvariants` is built in-proof by `have hinv₁ : … := by refine ⟨…⟩`
  (`Section34Compact.lean:182`).
- `Section34AlignedBandFilling` is built in-proof by `have halign` (`Section34CarrierFaceAlignedFilling.lean:62`).
- `disjointInl` / `disjointInr` (`ConnectedSum/AssociativeFlattening.lean:55, :59`, private
  abbrevs) are local disjointness side conditions, discharged by
  `exists_disjointOrientedBallChart_closedBall` (`AssociativeFlattening.lean:728`).
- `BrouwerFixedPoint` and `HasInvarianceOfDomain` are type classes supplied by instances
  (`Topology/FixedPoint/Brouwer.lean:30`; `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean:528`).

The real question under the "name, don't sorry" convention is whether each predicate's
*definition* says what its name claims. §4 answers it for every literature-named predicate
on the two branches.

**E2 (medium): invariance of domain, used on the Moise route, is vendored code conditional
on a Brouwer class.**
- Lean side: `Endgame.lean:27` and `Transition361.lean:307` call
  `isOpenMap_of_continuous_injective` / `isOpen_image_of_continuousOn_injOn`
  (`Topology/InvarianceOfDomainManifold.lean:78, :45`). These call
  `invariance_of_domain_open_map` (`External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean:464`)
  and `isOpen_range_of_isOpen_of_continuous_injective` (`:648`), under
  `variable [BrouwerFixedPoint E]` (`:166`) and `[HasInvarianceOfDomain E]`.
- The class `BrouwerFixedPoint` (`:59`) is documented upstream as *"This is assumed and
  used to prove invariance of domain"* (`:55–58`).
- It is discharged natively: `instance : BrouwerFixedPoint E` (`Topology/FixedPoint/Brouwer.lean:30`)
  ← `not_exists_retraction_closedBall_sphere` (`Topology/FixedPoint/NoRetraction.lean:14`).
  That theorem uses vendored `CanonicalTopology` sphere homology (`NoRetraction.lean:6–7`).
- `TRUST.md` E1 found that vendored `ClassificationOfSurfaces` and `CanonicalTopology`
  statements were modified. The statement at `InvarianceOfDomain.lean:464` reads as the
  standard one. Both files should nevertheless be read as native code, not taken on
  upstream warrant.

**E3 (low–medium): the literature mapping rests on identifiers only.**
- No docstrings on the route files (same as `ROUTE-WALK.md` E1).
- `Moise251`…`Moise361` look like theorem numbers in Moise (1977), chapters 25–36. I did
  not verify them against the book.
- The *shape* is recognizably Moise's book proof: loop theorem → extended loop theorem →
  tame shells and tori (ch. 30) → pseudo-cells (32) → graph neighbourhoods (33) → 3-cells
  (34.1) → open sets via a cell diagram (34/35.2) → chart gluing.
- It is not Bing's 1959 proof and not Hamilton's 1976 proof.

**E4 (low): a detour on the approximation route.**
- `plApproximationManifold_three` goes `Moise352Open` → `Moise352` (compact
  ∂-manifold K, by inward push, `OpenSourceReduction.lean:226`).
- It then applies `Moise352` only to an *open* U (`Transition361.lean:331` passes the
  polyhedral tower of the open U).
- It gets f(U) = h(U) by a closeness-implies-surjectivity argument
  (`exists_continuous_pos_surjective_of_dist_lt`).

Nothing is wrong with this. But `LocallyFiniteInwardPush` and its stage machinery are on
the headline's route only because of this detour, which inflates the cone.

**E5 (low): §34 is formalized twice.** There is a compact copy over ℝ³ for 34.1
(`Section34Compact*`, `Section34Compact.lean`) and an open copy on manifolds for the cell
diagram (`Section34*`). The two vocabularies are parallel. Both families appear in
NOSUPPLIER, and both are on the route: the open copy consumes 34.1 through
`controlledGraphNeighborhood moise341`. Findings about one family do not transfer to the
other automatically.

**E6 (low, positive): what is *not* on the route.**
- Smale's theorem (`SmaleMunkresSphereIsotopy`, `ConnectedSum/BoundaryAttachmentIsotopy.lean:80`)
  is off-route. Its discharger `smaleMunkresSphereIsotopy_holds` (`Surgery/Topology/SphereDiffeomorphismIsotopyConnected.lean:74`)
  is `in_cone=False` in `CONE.csv`. Connected sum uses the fixed antipodal gluing, and
  M # S³ ≅ M is proved by an isometric cap filling (`SphereCapFillingIsometry.lean:955`).
- The `cutCap*` reduction family with named hypotheses (`componentConnectedSumDecomposition`,
  `localReconstruction`, `Uncut/CappedDiscardedPresentationRealization`, …) is marked
  `in_cone=True`. That comes through off-route siblings (`PoincareControlledExtinction.isPoincareStandard`,
  `ROUTE-WALK.md` E6), not through the route theorem `componentwise_isPoincareStandard_of_poincareControlled`,
  which uses the paired-ball construction instead.

---

## 4. Named predicates met, and where they are discharged

**NOT discharged: none.**

For the reason, see the method note: on a hypothesis-free headline this list is empty by
construction, and the substantive check is the "definition matches" column.

| predicate (def file:line) | taken by | discharged at | definition matches literature? |
|---|---|---|---|
| `SphericalCutCapTransition.poincareControlled` (`ThreeManifold/PoincareStandard.lean:78`) | `CutCapPoincareStandard.lean:16` | the trace's `poincareControlled` (analytic side) | yes: every discarded component is standard |
| `isPoincareStandard` (`PoincareStandard.lean:20`), `isStandardFactor` (`StandardFactors.lean:594`), `SphericalSpaceFormGroup` (`StandardFactors.lean:23`) | throughout | defs | yes: # of S³/Γ (Γ ⊂ SO(4) finite, free) and oriented S²×S¹; empty # = S³ (`ConnectedSum/Finite.lean:12`) |
| `poincareStandardOrientationRefinement` (`PoincareStandardOrientationRefinement.lean:13`) | `CutCapPoincareStandard.lean:27`, `CappedPoincareStandard.lean:47` | `_holds` (`SphericalSpaceFormOrientationClosure.lean:324`) ← `factorOrientationClosure_holds` (`:320`) ← `sphericalSpaceFormOrientationClosure_holds` (`:307`), `sphereTwoTimesCircleOrientationClosure_holds` (`SphereTwoTimesCircleOrientationClosure.lean:13`), `connectedSumOpposite_holds` (`OppositeSumOrientation.lean:185`) | yes |
| `isOrientedPoincareStandardSumClosed` (`PoincareStandardOriented.lean:158`) | `CappedPoincareStandard.lean:61` | `_holds` (`PoincareStandardSumClosure.lean:25`) ← `connectedSumLaws_holds` | yes |
| `connectedSumLaws`, `binaryConnectedSumLaws` (`ConnectedSum/SumLaws.lean:50, :24`); `sphereUnitLaws`, `connectedSumCommutative`, `connectedSumAssociative`, `connectedSumOpposite`, `connectedSumOrientedTransport`, `connectedSumUnorientedTransport`, `connectedSumOrientedChartTransport`, `connectedBallChartTransport` (`FiniteLaws.lean:110, 120, 126, 132, 81, 72, 91, 17`); `SelfTransport` (`SumLaws.lean:420`); `ConnectedSumFlatteningIsoCanonical` (`AssociativeFlattening.lean:712`) | # well-definedness chain | `OrientedLawsAssembly.lean:12, :17`; `OrientedLaws.lean:108, :319`; `AssociativeFlattening.lean:1441, :1559`; `OrientedTransport.lean:144, :149`; `BallChartTransportConnected.lean:169, :172, :175`; `OppositeSumOrientation.lean:185` | yes (standard # laws; disc theorem via Palais) |
| `FiniteConnectedSumFreeProduct`, `FiniteConnectedSumStatement`, `connectedSumBasedFreeProduct` (`VanKampen/FiniteConnectedSumFreeProduct.lean:92, :85, :80`) | `PoincareStandardClassification.lean:38` | `:277`, `:135`, `:257` | yes: π₁(#) = free product |
| `BallChartTransport` (`Manifold/BallChartTransport.lean:103`) | disc theorem | `ballChartTransport_of_orientedBallCharts` (`BallChartTransportConnected.lean:153`) | yes: an ambient diffeo carrying one chart to the other on the radius-2 ball |
| `PLApproximation` (`PiecewiseLinear/Approximation.lean:18`) | `ChartGluing.lean:25`; `PLSmoothingCompact.lean:59` | `plApproximation_three` (`Moise352Producer.lean:27`) | yes: Moise's approximation of homeomorphisms between open PL sets |
| `PLApproximationManifold` (`PiecewiseLinear/Manifold.lean:156`) | `ApproximationManifold.lean:81` | `plApproximationManifold_three` (`Moise352Producer.lean:24`) | yes |
| `Moise352` (`Transition361.lean:256`) | `Endgame.lean:14` | `moise352_three_of_open` (`Moise352OfOpen.lean:14`) | yes: PL approximation of an embedding of a locally finite PL ∂-manifold |
| `Moise352Open` (`OpenSourceReduction.lean:210`) | `:226` | `moise352Open` (`Moise352Producer.lean:18`) | yes (open-set form) |
| `Moise352InwardPush` (`SkeletonReduction.lean:65`) | `:226` | `moise352InwardPush_three` (`Moise352InwardPushProof.lean:15`) | yes: collar push into the interior with a PL left inverse |
| `Section34CellDiagram` (`Section34Endpoint.lean:59`) | `:88` | `section34CellDiagram` (`Section34Terminal.lean:19`) | yes: matched locally finite PL cell structures with small carriers |
| `Section34NormalFamilyStatement` (`Section34Normalization.lean:77`), `Section34ControlStatement`, `ControlledGraphNeighborhoodStatement` (`Section34Statements.lean:14, :25`) | `Section34Terminal.lean:35`; `Section34Normalization.lean:93` | `Section34Normalization.lean:174`; `section34Control` (`Section34Control.lean:173`); `controlledGraphNeighborhoodStatement` (`ControlledGraphNeighborhood.lean:232`) | yes |
| `Moise341` (`MoiseChain.lean:96`) | `ControlledGraphNeighborhood.lean:58` | `moise341` (`Moise341Producer.lean:21`) | yes: approximation of a 3-cell embedding in ℝ³ (34.1) |
| `Moise341OnNeighborhood` (`Section34Compact.lean:155`) | `:292` | `moise341OnNeighborhood moise331OnTube` (`:163`) | yes |
| `Moise331OnTube` (`Section33TubeApproximation.lean:13`) | `Section34Compact.lean:163` | `moise331OnTube` (`Moise341Producer.lean:14`) ← `moise323`, `moise324`, `moise264Orientable` | yes: graph-tube approximation (33.1) |
| `Moise264Orientable` (`ExtendedLoopTheoremStatement.lean:16`) | `Section33TubeApproximation.lean:302` | `moise264Orientable` (`LoopTheorem/Moise252Producer.lean:19`) ← `moise252` | yes: a π₁-compressible two-sided surface has a compressing disk |
| `Moise252` (`MoiseChain.lean:33`) | `moise264_orientable`, `moise307_of_moise252` | `moise252` (`Moise252Producer.lean:14`) | yes: loop theorem, orientable |
| `Moise307` (`MoiseChain.lean:125`); `Moise323`, `Moise324` (`PseudoCell.lean:407, :422`) | `moise323_of_moise307`; `moise331OnTube_of_…` | `Section30Torus.lean:118`; `Section32PseudoCell.lean:260, :245` | yes for 307; 323/324 defs not opened (frontier) |
| `PLSmoothingCompact`, `PLSmoothingModelCompact` (`PLSmoothingCompact.lean:37, :45`), `PLManifoldTriangulation` (`Polyhedron.lean:96`) | `PLSmoothingCompact.lean:52, :59` | `Moise352Producer.lean:30`; `PLSmoothingCompact.lean:411`; `Combinatorial.lean:275` | yes |
| `IsSmoothHandleStage` (`Topology/Handle/SmoothStage.lean:15`) | `PLSmoothingCompact.lean:245` | induction `:383–393` | yes (a stage up to homeomorphism) |
| `Section34Compression`, `Section34BigonSlide`, and the compact analogues | `Section34TerminalFaceBalls.lean:200` and the compact twin | none needed: case hypotheses of a terminating rewrite | n/a (not results) |

---

## 5. Computation not read

1. `CutCap.lean:19, :71–72`: `norm_num`, `linarith` on tube levels.
2. `PairedBallFinite.lean:153–159`: the `List.Perm` rearrangement of factor lists.
   `CapComponentDiffeomorph.lean` seam coordinates: `norm_num [SelfAttachment.directSeamDomain]`.
3. `StandardFactors.lean:26–29, :591`: `by decide` for the sphere-orientation dimensions.
   `PoincareStandardOriented.lean:58–60` (ℤ is not a subsingleton).
4. `FundamentalGroup/Sphere.lean:134–142, :190–198`: finrank arithmetic for the orthogonal
   complements of the north vectors.
5. `ChartGluing.lean:88–137`: ε/2 continuity estimates, `linarith`.
6. `Transition361.lean:305–330`: `min`-based error bookkeeping.
7. `LocallyFiniteInwardPush.lean:57–80`: the geometric error budget (1−2^{−i})ψ, `norm_num`.
8. `PLSmoothingCompact.lean:258–300`: `fin_cases k` handle-index case split, `simp` on
   attaching regions.
9. `Section34Terminal.lean:160–195`: `simp [section34Dim]`, ULift bookkeeping.
   `Section34CompactVocabulary.lean:518–520`: `omega` for rank descent.
10. Instance resolution for `uliftChartedSpace` (a local instance at `ULift.lean:22`) when
    `ClosedOrientedManifold.ulift` is used outside that file. This is elaboration, not text.

---

## 6. Remaining frontier (unread bodies, highest priority first)

- Vendored, on the Moise route (E2):
  - `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean:166–464`;
  - `Topology/FixedPoint/NoRetraction.lean:14` and the `External/CanonicalTopology/Topology/Homology/*`
    it imports;
  - `External/Schoenflies/*` and `External/ClassificationOfSurfaces/Moise/PolygonalSchoenflies`,
    used by `NestedJordanCurves.lean`, `PseudoCellCentralTrace.lean`, `SphereDiffeomorph.lean`.
- Loop theorem bodies: `LoopTheorem/DescentStepOrientable.lean:212`,
  `GeneralPositionInDouble.lean:877`, `CoverReductionOrientableProducer.lean:208`,
  `LemmaTwoOrientable.lean:71`. There are 1,270 in-cone declarations under `LoopTheorem/`.
- Pseudo-cells: `PseudoCell.lean:407, :422` (defs of `Moise323`/`Moise324`),
  `Section32PseudoCell.lean:245` (`exists_reducedDisk_of_crossesPseudoCell`).
- §34 leaves: `Section34FaceDisks.lean:36` body, `Section34ResidualBalls.lean:33` body (the
  PL 3-cell recognition; the 3D PL Schoenflies machinery via `SchoenfliesInput`,
  `HeightSlabSurgery.lean:54`, `SphereCellPush.lean:63`),
  `Section34TargetRecognitionOfTiling.lean:796` body, `Section34CompressionLeaf.lean:78`,
  `Section34BigonSlide.lean:24`, `exists_section34FaceBall_of_neighborhood`,
  `exists_section34CutFrame`.
- Compact §34: `Section34Compact.lean:163–290` below `exists_compactCutAndGraph`,
  `exists_compactFaceEnvelopes`, `exists_compactFaceShellBalls`,
  `exists_compactFaceBallsGeneralPosition`, `compactTraceHomology`.
- PL ⇒ smooth: `isSmoothHandleStage_adjunction_{zero,one,two,three}`,
  `exists_homeomorph_smooth_disks_of_isClosedEmbedding`, `SurfaceTriangulationSmoothing`.
- A, connected sum: `PairedBallLoop.lean:788` and `PairedBallMerge.lean:546` bodies
  (`SmoothSelfAttachment` ≅ N # S²×S¹), `exists_smooth_quotient_step_atlas`
  (`PairedBallQuotientSmooth.lean:130`), `capRaw_homeomorph_local`
  (`CapComponentDiffeomorph.lean:208`), `Analysis/ODE/Flow/Planar/LinearGermRealization`
  (`exists_realizesGerm_of_contDiffOn_det_pos`), `SphereCapFillingIsometry.lean:955` body.
- VK core: `VanKampen/Based.lean:498` body (Brown's groupoid pushout over selected objects),
  `ConnectedSumNeckFundamentalGroup`, `EmbeddedCellCollar`
  (`fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar`),
  `FundamentalGroup/HomotopyEquiv.lean`.

---

## 7. Verdicts on the `Section34*` NOSUPPLIER rows

| row (NOSUPPLIER status) | on the route? | discharged? | where |
|---|---|---|---|
| `Section34GraphFrame` (`Section34Frame.lean:550`, no_supplier) | yes (open §34: `ControlledGraphNeighborhoodStatement` → `section34NormalFamily`) | **yes, false negative** | conclusion of `controlledGraphNeighborhood` (`ControlledGraphNeighborhood.lean:58–230`), inside an `∃` |
| `Section34NormalPlus` (`Section34Frame.lean:612`, no_supplier) | yes (`Section34NormalFamilyStatement`) | **yes, false negative** | conclusion tuple in `section34NormalFamily` (`Section34Normalization.lean:166–171`); `section34NormalFamilyStatement` (`:174`) |
| `Section34CompactFaceBallInvariants` (`Section34CompactVocabulary.lean:517`, no_supplier) | yes (34.1: `moise341OnNeighborhood`) | **yes, false negative** | `have hinv₁ … := by refine ⟨…⟩` (`Section34Compact.lean:182`) |
| `Section34FaceBallInvariants` (`Section34FaceBallVocabulary.lean:117`, conditional) | yes | yes | `exists_section34FaceBalls` (`Section34FaceBalls.lean:624`) and the terminal descent |
| `Section34FaceDiskFamily` (`Section34Frame.lean:648`, conditional) | yes | yes | `exists_section34FaceDisks` (`Section34FaceDisks.lean:36`) |
| `Section34ResidualPlus` (`Section34Frame.lean:670`, conditional) | yes | yes | `exists_section34ResidualBalls` (`Section34ResidualBalls.lean:33`) |
| `Section34Exterior` (`Section34Frame.lean:585`, conditional) | yes (a clause of `NormalPlus` and `FaceBallInvariants`) | yes | `section34Exterior_of_subset` (`Section34FaceBalls.lean:649`) |
| `Section34Compression`, `Section34BigonSlide` (conditional) | yes, as **case hypotheses** | not an open result | consumed by `exists_section34TerminalFaceBalls` (`Section34TerminalFaceBalls.lean:196`); their negation is what the terminal state records |
| `Section34CompactCompression`, `Section34CompactBigonSlide` (conditional) | yes, the compact twins | same | the compact terminal descent (`Section34Compact.lean:195`) |
| `Section34CompactFaceDiskFamily`, `Section34CompactResidualPlus`, `Section34CompactTrace` (conditional) | yes (34.1) | yes, per NOSUPPLIER's chain | `Section34CompactFaceDisks.lean:26`, `Section34CompactResidualBalls.lean:97` (heads not opened in this pass) |
| `Section34AlignedBandFilling` (`Section34AlignedBandFilling.lean:8`, no_supplier_in_cone) | yes (depth ≈17 under the face-ball construction) | **yes, false negative** | `have halign` (`Section34CarrierFaceAlignedFilling.lean:62`) |

Verdict: every `Section34*` row I passed is on the route and discharged. The three
`no_supplier` rows and the one `no_supplier_in_cone` row are name-scan false negatives,
caused by `∃`-packaged conclusions and in-proof `have`s. None is an open result hidden
behind a name.
