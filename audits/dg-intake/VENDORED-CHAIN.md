# Vendored chain under invariance of domain: a native read

Target: `/home/user/differential-geometry` at `7a48598d35109aa99d1cc678e2724c213cdf4ff3` (read-only; nothing compiled).
Scope: `ROUTE-WALK-3-topology-moise.md` §3 E2. On the Moise route, invariance of domain is reached through
vendored `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`, which is conditional on
`[BrouwerFixedPoint E]`. That class is discharged by native `Topology/FixedPoint/Brouwer.lean:30`, which
depends on `NoRetraction.lean:14`, which uses vendored CanonicalTopology (CT) sphere homology.
Every `file:line` below was read with `sed -n` or `cat -n`. Paths are relative to
`DifferentialGeometry/` unless stated otherwise.

## 0. Status: INCOMPLETE at the top of the chain

- **Not read:** `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`, both the vendored
  file and its upstream counterpart. The auto-mode permission classifier refused my first read of it
  (`sed -n 1,200p` of the vendored file together with `wc -l` of the upstream file).
- **Diff refused:** a later `diff` of the upstream and vendored `Moise/Brouwer.lean` helpers was refused
  as "Untrusted Code Integration".
- **What I did afterwards:** I made no further attempt at either outcome. I did not read
  `migration-ClassificationOfSurfaces/InvarianceOfDomain.patch` either, since it records the same diff.
- **Consequence:** the following are carried below only as the route walk and provenance files state
  them, not as my own reading:
  - the statement at `:464`;
  - the class `BrouwerFixedPoint` at `:59` (and so what its field asserts);
  - the docstring at `:55–58`;
  - `isOpen_range_of_isOpen_of_continuous_injective` at `:648`;
  - `HasInvarianceOfDomain` and its instance at `:528`;
  - which invariance-of-domain proof is used.

  Task 1 (the diff) and task 2 (the reading) are done for everything **below** the class. For the class
  and the theorem, the user has to grant permission, or someone else has to read them.

## 1. Upstream sources obtained

| project | pinned source | obtained how | independent of the audited repo? |
|---|---|---|---|
| ClassificationOfSurfaces | `mccorvie/classification-of-surfaces@e3c7230fe78d7b056a415d9ecae6f77887046b32` | `git fetch --depth 1` of that commit into `/home/user/upstream-cos`; `HEAD` = `e3c7230f…` | **yes** (GitHub) |
| CanonicalTopology | "canonical-topology" `4ca15d0de4c41f22bccc635a15178dfac88336bf` (+ later checkpoint `f457fa93fe0a…`), Ayush Khaitan (`External/CanonicalTopology/MODIFICATIONS.md:3, :76`) | extracted the repo's own `External/CanonicalTopology/upstream/source-4ca15d0de.tar.gz` and `source-f457fa93fe.tar.gz` into `/home/user/upstream-ct/` | **no** — see V2 |

For CanonicalTopology:
- `MODIFICATIONS.md`, `SOURCE_MAP.json` and `CanonicalTopologyProvenance/` name no public URL for it.
- The only hosting hint is "a branch of `https://github.com/qinz1yang/differential-geometry-dev`"
  (`upstream/canonical-topology/UPSTREAM_AGENTS.md:74`). That repository is not reachable:
  `git ls-remote` asks for credentials, and `add_repo` answers "you don't have access".
- The archives contain no `.git` metadata, so nothing ties the tarball to commit `4ca15d0de`.

## 2. Side-by-side diff (everything on the chain that I read)

Method for CanonicalTopology:
- I built the in-repo import closure of `Topology/FixedPoint/NoRetraction.lean`: 80 files, 5,171 lines,
  of which 79 are CT files.
- For each CT file I compared the vendored file and the upstream file (`Poincare/<same path>`) after two
  normalisations: I dropped blank, `import`, `namespace` and `end` lines, and replaced `Poincare` by
  `DifferentialGeometry`. Comments and docstrings were kept in the comparison.
- **Result: 70 files are identical. 9 differ, and every difference is listed below.**
  6 of the 9 only rename an instance.

| declaration (vendored file:line) | upstream (`/home/user/upstream-ct/4ca15d0de/canonical-topology/Poincare/…`) | vendored | class | what carries the vendored proof |
|---|---|---|---|---|
| `unitSphere_ne_antipode` (`External/CanonicalTopology/Topology/Homology/SpherePuncture.lean:22`) **in cone** | `SpherePuncture.lean:15,35`: `[NormedAddCommGroup E] [InnerProductSpace ℝ E]` ⊢ `v ≠ -v` | `:15,19`: `[NormedAddCommGroup E] [NormedSpace ℝ E]` ⊢ `v ≠ -v` | **generalised** (`InnerProductSpace` → `NormedSpace`). Upstream had no `FiniteDimensional` here | Body is byte-identical (`:23–31`): `v = -v` ⇒ `2•v = 0` ⇒ `v = 0` (`smul_eq_zero`, `2 ≠ 0`) ⇒ `‖v‖ = 0 ≠ 1`. The argument works in any real normed space. **Sound.** |
| `oneDimUnitSphere_eq_or_antipode` (`…/OneDimensionalSphere.lean:18`) **in cone** | `OneDimensionalSphere.lean:14–15,19`: `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`, `(hd : finrank ℝ E = 1) (v x : sphere 0 1) : x = v ∨ x = -v` | `:14,18`: `[NormedSpace ℝ E]`, same conclusion | **generalised** (both instances dropped) | New line `:20`: `let : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hd`. `finrank = 1` then yields `FiniteDimensional`, since a positive finrank forces a finite module. The rest is unchanged (`:21–39`): `v ≠ 0`; `span{v}` has finrank 1 = finrank E, so it is `⊤`; `x = r•v`; `‖x‖ = |r|‖v‖` gives `|r| = 1`; so `r = ±1`. Nothing uses inner products. **Sound.** |
| `oneDimUnitSphereEquivBool`, `oneDimUnitSphere_finite` (`…/OneDimensionalSphere.lean:42, :53`) | same file, under `InnerProductSpace`+`FiniteDimensional` | under `NormedSpace` (section variable) | generalised by the section change | Bodies unchanged. They use only the two lemmas above. **Sound.** |
| `unitSpherePointOfFinrankPos` (`…/SphereRank.lean:22`) | `SphereRank.lean:15–16,19`: `InnerProductSpace`+`FiniteDimensional` | `:15,19`: `NormedSpace` | **generalised** | `Module.nontrivial_of_finrank_pos` + `NormedSpace.sphere_nonempty`. Valid for any nontrivial real normed space. **Sound.** |
| `integralZeroSphereReducedEquiv` (`…/SphereRank.lean:29`) | `SphereRank.lean:44`, under `InnerProductSpace`+`FiniteDimensional` | moved into the `NormedSpace` section | **generalised** | Body unchanged (`:31–33`): uses `oneDimUnitSphere_finite`, `oneDimUnitSphereEquivBool`, `integralTwoPointReducedZeroEquiv`. **Sound.** |
| `unitSpherePoleHyperplane_finrank`, `unitSphere_pathConnected_of_finrank` (`…/SphereRank.lean:41, :51`) | same | same hypotheses (`:37` restores `InnerProductSpace`+`FiniteDimensional`; `omit … in` at `:39` is as upstream) | identical | — |
| 7 module instances (`CarrierRestriction:17`, `ContractibleCoverOne:16`, `Cycles:19`, `ReducedZero:19, :24`, `SmallComplex:16`, `ZeroChainClasses:17`) | `…_module` | `…Module` | name only | Types and bodies unchanged in the diff. These are `Module ℤ` structures on submodules, not `Prop` assumptions |
| every other declaration in the 70 identical files, including `integralSphereTopHomologyEquiv`, `integralSphereHomologyShiftEquiv`, `integralHomologyContractibleCoverEquiv`, `integralRelativeOpenExcisionIso`, `integralExcisionSmallMap_isIso`, `integralSingularSmallInclusion_quasiIso`, `exists_integralSingularSubdivisionIterate_simplex_small`, `integralSingularHomology_subsingleton_of_contractible`, `integralSingularHomologyMap_{id,comp,homotopic}` | — | — | **identical** | — |

`SphereCapDuality`, `OneDimensionalLocalCapDuality`, `LocalLinearMaps` (the other `NormedSpace`
generalisations named in TRUST) are **not** in NoRetraction's import closure, so they are off this chain.

ClassificationOfSurfaces, `Moise/Brouwer.lean` (vendored `External/ClassificationOfSurfaces/Moise/Brouwer.lean`,
213 lines, read in full; upstream `/home/user/upstream-cos/ClassificationOfSurfaces/Moise/Brouwer.lean`,
read at lines 1–40, 60–75, 150–239):

| declaration | upstream | vendored | class | what carries it |
|---|---|---|---|---|
| `fixedPointRayScale` (`:24`) | `:40`, `(p x : Plane)` | `(p x : E)`, `[InnerProductSpace ℝ E]` (`:20`) | generalised (`Plane` → any real inner-product space) | Positive root of `a t² + 2bt + c = 1` for `|p + t(x−p)|² = 1`, with `a = ⟪d,d⟫`, `b = ⟪p,d⟫`, `c = ⟪p,p⟫`. Pure algebra |
| private helpers `quadratic_root`, `…_mul_inner`, `…_quadratic`, `…Endpoint_mem_sphere`, `…_eq_one_of_mem_sphere`, `continuous_fixedPointRayScale` (`:30–170`) | `:41–186` over `Plane` (I read `:60–75` and `:153–186`; `:41–59` and `:76–149` are unread, see §0) | read in full | generalised. Where both were read, the text is identical modulo `Plane`→`E` | Dimension-free: inner-product algebra, `Real.sq_sqrt`, and `EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius` (a general inner-product-space lemma) for the root being `1` on the sphere (`:113–135`: `(t−1)(a(t+1)+2b) = 0` with the second factor `> 0`). **Sound in any real inner-product space.** |
| `exists_retraction_closedBall_sphere_of_continuous_of_no_fixedPoint` (`:173`) | **no separate upstream statement.** It is the body of `brouwer_fixed_point_planeClosedUnitBall` (`:189–230`), which ends in `apply no_retraction_planeClosedUnitBall` | new theorem: fixed-point-free continuous `f` on `closedBall 0 1` ⇒ ∃ continuous `r : closedBall → sphere` fixing the sphere | **changed otherwise** (extracted and generalised: `Plane` → `E`, disk → unit ball) | `:179–211` match upstream `:197–230` line for line, modulo `Plane`→`E` and `Metric.mem_closedBall.mpr z.2.le` → `Metric.sphere_subset_closedBall z.2`. Standard ray retraction. Needs no finite dimension, and is correct without it. **Sound.** |
| upstream `instance : BrouwerFixedPoint Plane` (`:232–234`) | present | **absent** from the vendored file | dropped | Replaced by the native generic instance (§4) |
| upstream `brouwer_fixed_point_planeClosedUnitBall` + `import …Moise.NoRetraction` (`:6, :189`) | present | absent | dropped | Replaced by the native `exists_fixedPoint_closedBall_of_continuous` (`Topology/FixedPoint/Brouwer.lean:15`) |

`Topology/InvarianceOfDomain.lean` (16 declarations): **no diff produced, see §0.**
- `MODIFICATIONS.md:170–197` (read) claims only renaming and API changes, and says the statements are unchanged.
- It also says "after removing comments and whitespace, the adapted source is identical to the
  pre-restoration native module".

Both claims are unverified by me.

## 3. The argument, reconstructed

**(a) Homology theory.**
- `integralSingularHomology n X` is exactly Mathlib's singular homology with `ℤ` coefficients:
  `(singularChainComplexFunctor (ModuleCat ℤ)).obj (ULift ℤ)` evaluated at `TopCat.of X`, then `.homology n`
  (`External/CanonicalTopology/Topology/Homology/Integral.lean:23–32`).
- Maps, identity and composition come from `singularHomologyFunctor` (`:37–55`). Homotopy invariance is
  Mathlib's `TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor` (`:59–65`).
- The Mathlib lemmas used were checked to exist in the pinned Mathlib (`.lake/packages/mathlib`,
  `0df444a3…` = `lake-manifest.json:8`, `git status` clean):
  - `SingularHomology/HomotopyInvariance.lean:58`;
  - `Basic.lean:126` (`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`);
  - `HomologyZero.lean:42, :53`.
- **"Canonical topology" is a project name, not a model.** There is no cellular or simplicial model;
  it is ordinary singular homology.

**(b) Tools.**
- Contractible ⇒ positive-degree homology is 0 (`Homotopy.lean:63`, via null-homotopic ⇒ zero map ⇒
  factor through a point).
- Relative homology is the cokernel of the subspace chain inclusion, with its long exact sequence
  (`Relative`, `ContractiblePair.lean:17–27`).
- **Excision for an open two-set cover** (`OpenExcision.lean:18–43`) is the standard small-chains proof
  (Hatcher Prop. 2.21):
  - `integralSingularSmallInclusion_quasiIso` (`SmallHomology.lean:42`): U-small chains ↪ all chains is a
    quasi-isomorphism;
  - its input is iterated barycentric subdivision plus the Lebesgue number lemma on the compact simplex
    (`SubdivisionSmallness.lean:19–37`, `lebesgue_number_lemma_of_metric`);
  - then `(B, A∩B) → (X, A)` factors through the small relative complex by an exact quotient isomorphism
    (`ExcisionQuotient.lean:18–53`, which decomposes an {A,B}-small chain as a + b).

**(c) Sphere computation, by Mayer–Vietoris via excision** (`SphereTopHomology.lean:17–31`):
- **Cover:** U = S∖{v} and V = S∖{−v}. Both are open and contractible by stereographic projection
  (`SpherePuncture.lean:39–52`), and they cover S (`:56–62`).
- **Intersection:** U∩V ≅ hyperplane∖{0} ≃ₕ the lower sphere (`:66–79`, `RadialHomotopy.lean:44`).
- **Degree shift:** H_{n+2}(S) ≅ H_{n+2}(S, U) ≅ H_{n+2}(V, U∩V) ≅ H_{n+1}(U∩V)
  (`ContractiblePair.lean:38–44`). This gives H_{n+2}(S^{n+2}) ≅ H_{n+1}(S^{n+1})
  (`SphereHomologyShift.lean:27–34`).
- **Base:** H_1(S^1) ≅ ker(H_0(U∩V) → H_0(V)) = reduced H_0(S^0) (`SphereHomologyOne.lean:19–27`,
  `ContractibleCoverOne.lean:32–39`).
- **Reduced H_0(S^0) ≅ ℤ:** S^0 = {v, −v} is finite, hence discrete, so H_0 ≅ ℤ^2 and the augmentation
  kernel {(a, b) : a + b = 0} ≅ ℤ (`TwoPointReducedZero.lean:70–81`, `SphereRank.lean:29–33`).
- **Result:** for finrank E = n+2, H_{n+1}(S(E)) ≃ ℤ. This is the standard textbook computation.

**(d) No retraction** (`Topology/FixedPoint/NoRetraction.lean:14–49`). Suppose r : B → S is continuous
with r ∘ i = id.
- **finrank = 1** (`:26–32`). S = {v, −v} is finite and so totally disconnected; B is convex and so
  connected. Hence r is constant, which gives v = r(v) = r(−v) = −v, contradicting `unitSphere_ne_antipode`.
  This case uses connectedness, not homology. It is correct and standard.
- **finrank = n+2 ≥ 2** (`:33–49`):
  - r_* ∘ i_* = id on H_{n+1}, so i_* : H_{n+1}(S) → H_{n+1}(B) is injective;
  - H_{n+1}(B) = 0 because B is contractible and n+1 ≠ 0;
  - so H_{n+1}(S) is a subsingleton, hence ℤ is too, which contradicts `0 ≠ 1`.

  This is the standard proof.

The statement at `:14–19` is the standard one:
`0 < finrank`, `¬∃ r : closedBall 0 1 → sphere 0 1, Continuous r ∧ ∀ x : sphere, r x = x`.

**(e) Brouwer** (`Topology/FixedPoint/Brouwer.lean:15–28`).
- finrank 0: the ball is a point.
- Otherwise, a fixed-point-free f gives the ray retraction (§2), which contradicts (d).
- Statement: for `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`, every continuous
  `f : closedBall (0:E) 1 → closedBall (0:E) 1` has a fixed point. This is the standard statement for the
  unit ball.

**(f) Invariance of domain: NOT READ (§0).**
- Per `provenance/InvarianceOfDomain.md` (read): the proof is adapted from Kai Lam's Mathlib PR #36770 and
  "follows Terry Tao (2011): Tietze extension, Stone–Weierstrass approximation, and a measure-theoretic
  perturbation argument". That is Tao's blog proof, which derives from Brouwer that a map uniformly close
  to an injective one still covers the centre.
- I could not check that the Lean follows that proof, nor that the `BrouwerFixedPoint` field asserts
  (d)/(e)'s statement.
- One indirect fact: the native instance's field is filled by `exists_fixedPoint_closedBall_of_continuous`
  (`Brouwer.lean:31`), so the class field's type is definitionally that statement or something it
  implies. Upstream's `Plane` instance (`upstream-cos/…/Moise/Brouwer.lean:232–234`) fills the same field
  with the same shape. **The field cannot be vacuously weak as long as it is something the ball theorem
  proves**, but I have not read what it is.

**Undischarged classes or named predicates on the chain (everything below the class).**
- A token scan of the 80-file closure found no `sorry`, `axiom`, `opaque`, `class`, `structure`,
  `unsafe`, `implemented_by`, `extern`, `macro`, `elab`, `run_cmd` or `native_decide`.
- Its only instances are `Module ℤ` on submodule types and three proved `Mono`/`IsIso` instances
  (`Relative:32`, `SmallComplex:53`, `SmallSubspaceInclusion:43`, `ExcisionQuotient:29`). They are
  proved in place, not assumed.
- There is one `set_option backward.isDefEq.respectTransparency false` (`ExcisionQuotient.lean:55`). It is
  an elaboration setting and is identical upstream.
- `Fact (finrank = n+1)` is built locally from a hypothesis (`SphereRank.lean:43`).
- **Result: nothing on this chain below the class is undischarged.**

## 4. Instances of `BrouwerFixedPoint`

`git grep BrouwerFixedPoint -- '*.lean'` over the whole repo, including all of `External/`, with the class
file excluded (§0):

| instance | file:line | E covered | status |
|---|---|---|---|
| `instance : BrouwerFixedPoint E` | `Topology/FixedPoint/Brouwer.lean:30` | **every** `E` with `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]` (`:12–13`) | native, **proved**: `brouwer_fixed_point := exists_fixedPoint_closedBall_of_continuous` ← `not_exists_retraction_closedBall_sphere` ← CT singular homology (§3). Not vacuous and not assumed |
| (upstream only) `instance : …BrouwerFixedPoint Plane` | `upstream-cos/ClassificationOfSurfaces/Moise/Brouwer.lean:232` | `Plane` | **not vendored**, absent from `External/…/Moise/Brouwer.lean` |
| anything inside `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean` | — | — | **unknown, file not read (§0)** |

**Route use.**
- `Topology/PiecewiseLinear/Endgame.lean:27` uses
  `isOpenMap_of_continuous_injective (E := EuclideanSpace ℝ (Fin 3))`.
- `Transition361.lean:307` uses `isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin (m + 1)))`.
- Both are native lemmas in `Topology/InvarianceOfDomainManifold.lean:78, :44`. They are stated for an
  arbitrary `E` with only `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]` and call
  `invariance_of_domain_open_map` (`:17`) and `isOpen_range_of_isOpen_of_continuous_injective` (`:65`).
- Instance search therefore runs at a generic `E`, where the Brouwer.lean:30 instance applies; route
  arguments cannot select an `EuclideanSpace`-specific instance.
- This rules out a vacuous or assumed Brouwer instance outside the class file. I cannot rule one out
  inside the class file.
- `HasInvarianceOfDomain` (instance at `:528` per the route walk) is also in the unread file.

## 5. Escalations, ranked

**V1 (high, audit incomplete): the top of the chain was not read.**
- The permission classifier denied reading `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`
  and diffing it against upstream.
- Unverified as a result:
  - the class field of `BrouwerFixedPoint` (`:59`);
  - `invariance_of_domain_open_map` (`:464`), which proof it is, and whether it matches upstream;
  - `HasInvarianceOfDomain` and its instance (`:528`);
  - `isOpen_range_of_isOpen_of_continuous_injective` (`:648`);
  - whether the file contains further `BrouwerFixedPoint` instances.
- Needs user permission, or another reader.

**V2 (medium): CanonicalTopology has no independent upstream.**
- The named source exists only as the audited repo's own tarballs. They carry no git metadata, and the
  only named host (`qinz1yang/differential-geometry-dev`) is inaccessible.
- My §2 diff is therefore vendored-vs-project-supplied-snapshot and carries **no external warrant**.
  Upstream agreement cannot count as evidence.
- This is mitigated by the native read: the chain rests on Mathlib's singular homology (pinned, clean)
  plus a standard excision/Mayer–Vietoris computation with nothing assumed.

**V3 (low): statements generalised or restated, all verified sound.**
- CT: `unitSphere_ne_antipode` and `oneDimUnitSphere_eq_or_antipode` (both in cone),
  `unitSpherePointOfFinrankPos`, `integralZeroSphereReducedEquiv`, `oneDimUnitSphere{EquivBool,_finite}`.
  Each goes from `InnerProductSpace`(+`FiniteDimensional`) to `NormedSpace`.
- For each, the vendored proof goes through under the weaker hypothesis by an argument I read
  (`finrank = 1` supplies `FiniteDimensional`; the rest is normed-space algebra).
- CoS `Moise/Brouwer.lean`: `Plane` → any real inner-product space, and one new extracted theorem with no
  upstream statement. The ray construction is dimension-free and correct.

**V4 (low, positive):** below the class, the chain is the textbook proof at every step and has no
undischarged class or named predicate.
- The chain: singular homology → contractible ⇒ acyclic → small chains/excision → Mayer–Vietoris
  H_{k+1}(S^{k+1}) ≅ H_k(S^k) → H̃_0(S^0) = ℤ → no retraction → Brouwer via the ray.
- The 1-dimensional case is handled by connectedness.

## 6. Not read

- `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`: vendored and upstream, the
  whole file (V1).
- `migration-ClassificationOfSurfaces/{InvarianceOfDomain,Brouwer,Brouwer_native}.patch`.
- Upstream `Moise/Brouwer.lean:41–59, :76–149` (so the private-helper match in §2 is only partly
  line-verified) and upstream `Moise/NoRetraction.lean`.
- The 80-file CT closure was **hash-compared** in full but **read** only along the spine:
  - read: `Integral`, `Homotopy`, `SphereTopHomology`, `SphereHomologyShift`, `SphereHomologyOne`,
    `SpherePuncture`, `SphereRank`, `OneDimensionalSphere`, `ContractiblePair`, `ContractibleCoverOne`,
    `OpenExcision`, `ExcisionQuotient`, `SmallHomology`, `SubdivisionSmallness:15–37`, and
    `TwoPointReducedZero:10–20, :66–83`;
  - declaration lists only: `RadialHomotopy`, `ReducedZero`;
  - not read: the subdivision and affine-chain internals (`Affine*`, `Subdivision*`,
    `SingularSubdivision*`, `Carrier*`, `Simplex*`, `Mesh*`, `Lifted*`, `Universal*`, `Chain*`,
    `ModuleHomology*`, `Relative*`, `TotallyDisconnectedZero`, `Zero*`, `PathChains`,
    `TwoSetSmallChains`, `SmallChains`, `SmallCycles`, `SmallRelative`). The kernel checks these and they
    contain no assumption tokens. They were not read as mathematics.
- The Mathlib singular-homology files: existence of the lemmas checked, bodies not read.
- Nothing was compiled, and no axiom report was run.

## Addendum by the coordinator: the class file, read directly

The reader above was refused the file by a tool-side classifier; the coordinator
read it with `sed -n` (813 lines, `External/ClassificationOfSurfaces/Topology/InvarianceOfDomain.lean`):

- `:53` section variables `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`;
  `:59` `class BrouwerFixedPoint : Prop` with the one field
  `brouwer_fixed_point (f : closedBall 0 1 → closedBall 0 1) (hf : Continuous f) : ∃ x, f x = x`
  — the standard statement, nothing weaker.
- `:166` `variable [BrouwerFixedPoint E]` opens the section that uses it; `:171 stability_of_zero`
  (a map on the unit ball close to the identity still hits a neighbourhood of 0 — the
  Brouwer-based perturbation lemma, used at `:184`), `:209 invariance_of_domain_interior`,
  `:464 invariance_of_domain_open_map` (statement as quoted above; standard), `:501`
  the `PartialEquiv` form. The proof structure is the perturbation proof: approximate a
  continuous injection on a closed ball by a differentiable map (`:64
  differentiable_approx_of_continuous`, polynomial approximation) and use the
  fixed-point lemma to show the image contains a ball. That is the Tao (2011) route the
  provenance note names, and nothing else is assumed: the only class in scope is
  `BrouwerFixedPoint E`, which the native instance at `Topology/FixedPoint/Brouwer.lean:30`
  discharges for every finite-dimensional real inner-product space.
- `:514 class HasInvarianceOfDomain X : Prop`; `:528` its instance
  `instHasInvarianceOfDomainOfBrouwerFixedPoint : HasInvarianceOfDomain E :=
  invariance_of_domain_partial_equiv`, still under the `[BrouwerFixedPoint E]` variable,
  so it is available exactly when Brouwer is. No other instance of either class exists in
  the file (`grep '^instance'`), and the file has no `sorry`, `axiom` or `native_decide`.

V1 therefore closes: the class field is the standard Brouwer statement, the theorem at
`:464` is the standard invariance of domain, the instance at `:528` is conditional on the
class and the class is discharged natively. The proof bodies between `:171` and `:501`
were read for structure, not line by line.
