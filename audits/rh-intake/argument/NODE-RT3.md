# NODE-RT3: `OneCharU` steps (2) and (3), read as an automorphy-lifting argument

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `U3/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/`
- `DTC/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/`
- `CDS/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/CurveDVRSpecialization/`
- `GML/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/`

"The Lean says" means I read it; *(inferred)* means it is my reading. Nothing was compiled.

## 0. Answers in brief
- **(a) The ring is Galois-side.** It is a genuine universal ring of *normalised lifts* of r̄ = Ψ̄⊕1⊕Ψ̄⁻¹. It is defined by
  representability (`Univ`/`GRepresents`), with a minimal-ramification condition away from l and a Kisin-style ordinary
  condition at l. It is **not** a Hecke or trace algebra. So "every point is automorphic" is a real R = T-type theorem, and the
  algebra in step (1) is formal. The real theorem sits in step (3), together with two companions: R is finite over O, and the
  adjoint Selmer group vanishes at automorphic points.
- **(b) Step (3) follows the Skinner–Wiles scheme.** It is carried out over an auxiliary abelian CM field L, for U(2) and U(3)
  simultaneously, with:
  - Hida families (the universal ordinary determinant ring B; J = the kernel to a unitary Hida Hecke algebra);
  - a dimension count plus "propagation" through the reducible locus, so that every component is "good" (pro-modular);
  - a gluing of two runs with different auxiliary primes p;
  - descent from L to K.

  There is no Taylor–Wiles patching. The hypotheses are l odd, l ∤ h_K·disc K, and l − 1 ∤ 2e, which is p-distinguishedness.
  There is no l > e condition. I know of no published theorem of this generality for a three-character residual
  representation of U(3).
- **(c) LemmaM is a multiplicity inequality.** The ring S is graded by torus weights in [−2, 2]. Suppose that:
  - the char-0 tangent in weight −1 is controlled by the weight −1 equations;
  - the weight-0 part is finite over O;
  - at every two-signed point the tangent space is at most 1-dimensional (the torus orbit).

  Then length(cot_{−1}) ≤ 2·Σ over orbits of v(a(τ)), for a weight-0 function a vanishing at the base point. The proof is a
  Rees-algebra Hilbert-function (Euler characteristic) count. This is the **upper-bound** direction, and it is legitimate. The
  inequality concerns R itself; automorphy is needed only to feed the congruence number NN. The toy R = O[[X,Y]]/(X(XY − lⁿ)),
  whose weight-0 part is {(a,b) : a ≡ b mod lⁿ}, gives n ≤ 2n. I found no counterexample.
- **(d) The decomposition is recognisable, and nothing in it is vacuous.** The parts that exceed the literature are:
  1. AutEnd3Alt: residually reducible ordinary modularity for U(3), uniform in l;
  2. FinPt/FinEnd: no characteristic-l deformation with non-residual charpoly on a finite-index subgroup;
  3. RigidityFirstCase: adjoint Bloch–Kato vanishing at automorphic points congruent to Eisenstein.

## 1. Statement (what is being deformed)

### Residual representation (`U3/RhoKApply.lean:16-79`, `U3/GRepresents.lean:35-44`)
- **Group.** Γ = G_ℚ. r̄ = `rbar c.O η Ψ` = `r0 η (barChar Ψ)` is valued in the unitary C-group `GG 3`, a semidirect product of GL₃
  with ℤˣ. η is the quadratic character with ker η = G_K (`Dat.η_ker`).
- **Character.** Ψ = `Chr.Psi l e (dirG ψ)`. On inertia at l, Ψ = cyc^e·τ (`Dat.Ψ_I`). The coefficients are the residue field
  of c.O, a finite extension of ℤ_l.
- **Restriction to G_K.** It is Ψ̄⊕1⊕Ψ̄⁻¹. The map is `rhoK`, the GL₃-part restricted to ker η.
- **Lifts.** `GLift` = a continuous hom to `GG 3 R` reducing to r̄, for R a complete local O-algebra with residue field k.

### Ring (`U3/ConjStable.lean:49`, `U3/RhoKApply.lean:69-71`, `U3/GRepresents.lean:81-105`)
- `D.Ring U g₁ = SRing D.Kill D.ι_cont U (D.loc.It U) D.cc g₁ = Univ (NormCond c g₁ (BoxCond Kill ι U It))`. This is the
  representing object for lifts satisfying three conditions:
  1. **Normalised(c, g₁).** The entries are fixed at complex conjugation c and at a marked element g₁. *(inferred)* This
     rigidifies the reducible r̄, replacing framing. It leaves the diagonal torus acting.
  2. **Kills(Kill).** `Kill` = {g in an inertia group at a place not above l with r̄(g) = 1} (`RhoKApply.lean:63`). So the lift is
     trivial on ker(r̄|I_v) for v ∤ l. This is a *minimally ramified* condition.
  3. **At l.** The restriction to G_{ℚ_l} (via ι) factors through U.R/It, where U.R is the local universal lift ring.
- **The ideal It** (`PadicHodgeTheory/IsInertiaInfiniteCyclotomic.lean:93-133`). It starts from `ordIdeal`:
  - charpoly(ρ(s)) = ∏(X − ψ_a(s)) for s ∈ inertia ∩ ker η ∩ ker τ;
  - ∏_a (ρ(s_a) − ψ_a(s_a)) = 0.

  It is then saturated by `del` = l·dd₀·dd₁ (which inverts l and the genericity elements), and the radical is taken (`Icr`).
  Finally It is the intersection of the minimal primes through the split point r0. So It is the union of the components of a
  reduced, l-saturated **ordinary local deformation ring with fixed inertial characters (ψ_a) = (cyc^e τ, 1, cyc^{−e} τ⁻¹)**,
  that is HT weights (e, 0, −e), through the base point. This is Kisin-style. It is neither Fontaine–Laffaille nor a
  pseudo-deformation ring.
- **Existence.** `exists_ring` (`U3/RingEx.lean:109-153`) builds the ring from the general `exists_univ` (Mazur, using
  Φ_l-finiteness of the quotient group) and from `Loc.locGood`, a hypothesis bundle that says the local ring is formally smooth
  at the base point with prescribed graded dimensions (`ConjStable.lean:22-37`, `locDims` = 1, 2, 3, 4, 2 in weights −2..2).
- **Model** (`ConjStable.lean:54-90`). This is a graded presentation A ↠ S.R with kernel generated by `Eqns` (F weight −1,
  r+1 of them; G weight −2; E weight 1; E′ weight 2; Z weight 0). `M.len = cotLen x 𝒜 (−1) Q.F`, the length of the
  weight −1 cotangent of S at the base point.

**Answer to (a).** The ring is defined from Galois deformations, not from automorphic forms. Ш ↪ (weight −1 tangent) is
formal (`vlen_le`, `U3/VlenLe.lean:52-67`). It uses `shaCoc` (`ConjStable.lean:107-112`): weight −1 cocycles that vanish on
Kill and are coboundaries on the decomposition group at l. All non-formal content therefore lies in the upper bound and in the
automorphy of points.

## 2. Argument

### Step (2): `model_upper` and LemmaM

**`model_upper`** (`U3/ModelUpper.lean:103-150`) derives LemmaM's hypotheses as follows:
- M2 from `FinA` (the weight-0 subalgebra of S.R is finite over O);
- M1 (tangent spanning in weights −1, −2, 0) from `PtHyp.rigid0`;
- M3 and M4 from `PtHyp`;
- M5 with a = E₀₀ + E₁₁ + E₂₂ − tr r0(σ), which has weight 0, vanishes at the base point, and equals trDiff at points.

**LemmaM, the version actually used** (`CommutativeAlgebra/OrbitVanishingLocal.lean:111-118`). The `Formalism/...GradedPowerSeriesLemmas.lean:221`
version cited by the parent is a different statement and is not the one `model_upper` consumes.
- **Setting.**
  - O is a complete DVR of characteristic 0, and K is an algebraically closed field with a valuation v extending v_O.
  - A is a ℤ-graded O-algebra. Its 𝒜₀ is complete local, it is generated over 𝒜₀ by elements of weights ±1, ±2, and
    nonzero-weight elements vanish at x.
  - Q is a system of equations.
- **M1.** At x, A is smooth with graded tangent dimensions (r, s, r′+1, s′+1, m) in weights (−1, −2, 1, 2, 0). The F's
  (r+1 of them) span the weight −1 cotangent rationally, and G and Z span weights −2 and 0.
- **M2.** (𝒜₀ mod I) is finitely generated over O.
- **M3.** For every fixed non-base point x₁, reducible deformations with B ≠ 0 or with C ≠ 0, having the same diagonal, do not both
  occur.
- **M4.** At every two-signed point, any two tangent vectors are linearly dependent.
- **M5.** a(ξ) ≠ 0 at two-signed points.
- **Conclusion.** Finite covering sets T of the orbits exist, cotLen is finite, and for **every** covering T,
  cotLen₋₁ ≤ 2·Σ_{ξ∈T} v(ξ(a)).

**Proof** (`GML/MainCotSpan.lean:32-80`, `GML/AlgMemCoef.lean:92-200`, read):
1. Smith-normalise the F's into ϖ^{c_i}y_i plus one element in the saturated square (`sm_holds`). Then cotLen = Σc_i.
2. Cut down to a chart (`cut_holds`).
3. Build a three-variable Rees/graded "HidaSetting" X over 𝒜₀.
4. Compare eventual Hilbert functions (`chi`):
   - `low_holds`: 2^{r+r′}Σc_i ≤ χ;
   - `chain` (a is a nonzerodivisor modulo the chart kernel);
   - `up_holds`: χ ≤ 2^{r+1+r′}·Σ v(ξ a), counting points of the 1-dimensional two-signed locus.
5. Divide by 2^{r+r′}. **The factor 2 is 2^{r+1+r′}/2^{r+r′}**: the weight ±1 generators enter the filtration squared
   (`sq_mem_neg`/`sq_mem_pos` in `ts_valid`).

**Mathematical content** *(inferred)*:
- The F-spanning part of M1 says the char-0 Selmer group in weight −1 vanishes (Bloch–Kato for Ψ⁻¹-type twists:
  `bloch_kato_nonpositive_weight`, `DTC/FPtHypU.lean:29-32`).
- Hence over K a point with B ≠ 0 must have C ≠ 0. A weight −1 polynomial with no positive-weight variable is linear in the X_i,
  and the F's have full-rank linear part.
- So the weight −1 module lives on the two-signed curve, and its length at the base point is bounded by the degree of the
  divisor (a) on that curve.
- Since 𝒜₀ is finite (M2), ξ(a) is integral and v ≥ 0. Non-continuous K-points cannot contribute negative terms.

**Direction.** This is the direction that needs a real argument (Selmer ≤ congruences). The argument here is **algebraic, about
R**: it uses only char-0 rigidity (M1/M4) and finiteness (M2). It is not Ribet's construction, and it is not a numerical
criterion on T. It differs from Wiles–Lenstra because it bounds by Σ_τ v(a(τ)) (a norm) rather than by the congruence module η.
Checks:
- In the 2-point toy, A = O[[X,Y,U]] (weights −1, +1, +2) with F = (X(XY − lⁿ), X³U): cot = n and Σ = n, so n ≤ 2n.
- In the 3-point non-complete-intersection toy, F = (X₁(X₁Y − l), X₂(X₂Y − l), X₁X₂Y): cot = 2 and Σ = 2.
- Attempts to make cot large while Σ stays small broke M2 (an infinite torsion weight-0 part) or M4 (non-reduced or
  2-dimensional branches).

**Where the inputs come from.**
- **M4** comes from `PtHyp.rigid` (`U3/Rigid0.lean:16-20`): at every TwoPt the tangent is coboundaries. This in turn comes from
  `Af.BlochKatoSelmerVanishes l (adRep ρ_f)`, i.e. **adjoint Selmer vanishing at every two-signed point**, supplied by:
  - `RigidityFirstCase` (`DTC/RigEnd3.lean:28-33`; type I points, assuming they are automorphic). It is proved from
    `AdjointLiftingTheorem` (`DTC/AutomorphicPointGalois.lean:35-39`: adjoint vanishing at automorphic points of Hida
    determinant rings, n ≤ 4) via `rigIUE_alt` (`DTC/ERigIU.lean:80`).
  - `RigiditySecondCase` (type II, from modularity of W).
- **Order of dependence.** Automorphy of points comes first, then rigidity, then LemmaM. M4 is indeed a multiplicity-one input,
  and it is obtained *from* step (3).

### Step (3): automorphy of every point, `hA : AutomorphyUnramifiedCoefficientsAlt`
- **The target** (`DTC/AutomorphyUnramifiedCoefficients.lean:16-26`) provides `Marked g₁`, `FinA` (the weight-0 subalgebra is
  finite over O) and:
  - `AutBAlt`: every Q̄_l-point of the entry algebra of type I (irreducible on G_K) is `IsAutCsdA` after twisting by
    cyc̄⁻¹. That is, it is attached to a regular algebraic polarized cuspidal π on GL₃/K (`IsAutCsdA.lean:11`).
  - `LemWAlt`: for type II points the 2-dimensional piece W is modular.
- **The source** is `automorphyUnramified_of_locPrints_kisin_gdEnd` (`DTC/AutomorphyU3OfEndoscopy.lean:27-62`) ← `GdEndAlt`
  (`DTC/AutEnd3AltAlt.lean:35-40`).
  - Every point of S is moved to an `OrdPt` over a finite DVR A (`exists_ordPt_of_point`, not opened). OrdPt
    (`CDS/RatTorsionFree.lean:21-27`) means: reduction r̄, continuous, normalised, trivial on inertia away from l where η and Ψ are
    trivial, and `CondT`-ordinary at the place B | l.
  - **`AutEnd3Alt`**: every such OrdPt that is irreducible on every open subgroup of G_K is automorphic.
  - **`FinEnd`**: there is a finite-index U such that for every characteristic-l complete local A and every OrdPt r over A,
    charpoly r(g) = charpoly r̄(g) on U ∩ ker η. *(inferred)* This is "R/λ is finite", the finiteness of the trace algebra.
- **`GdEndAlt`** ← `gdEnd_of_frame_linkedEnd_downCsdK_descent` (`DTC/GdEndOf.lean:22-85`).
  - `GdFrameEx` (`CDS/HostFrameEx.lean:75-79`) supplies an abelian CM field L, a "frame" Φ, and a `GalLink` (`:22-50`, a precise
    dictionary between G_L, the frame group and the places above l), plus `SeedClause` (a CM/endoscopic seed point).
  - `LinkedEndEAlt` (`DTC/PlDefs.lean:12-20`) gives FinPt for n = 3 and AutPtAlt for n = 3 and n = 2 over L.
  - The result descends to K.
- **`LinkedEndEAlt`** ← `linked_endomorphism_dense` (`DTC/LinkedEndE.lean:18-67`). Its inputs are `ModUAlt`, `LevEx`, `LamEx`,
  `ProModularRingExists`, `UnitaryThreeAutomorphyDense` and `Seed2Alt` (automorphic seed points for n = 3 and n = 2), and then
  `twoRuns_alt`.
- **`twoRuns_alt`** (`DTC/TwoRuns.lean:80-110`, read in full).
  - For each auxiliary "CReal" setting R (an auxiliary prime R.s.p), `modularity_linked_ends` (`DTC/PrLinkedEnd.lean:22-42`)
    gives an ideal J of the determinant ring with `ModIn J` and classicality.
  - It uses `ModUAlt` (a Hida ideal), `LamEx` (a weight-space Λ) and `dimOf`/`degEq` (the components of B/J have the expected
    dimension).
  - `absMain` (`CDS/AbsMain.lean:12-30`) applies `components_good_rank_two/three` (the "propagation theorem": every component is
    good), yielding `goodPtOf` and `finPtOf`.
  - Each run gives automorphy "off" the place v0 of that run (`AutOffN`). Two runs with different p are glued (`glueN`).
- **`ModUAlt`** (`DTC/PointTheoremBaseObject.lean:44-48`). For every Hida setting over a CM field L without ζ_l, with n ≥ 1, a
  residual r, a universal ordinary determinant ring B and weight algebra Λ, there exists J with:
  - `RingProps` (B/J finite and torsion-free over Λ);
  - `Dense` (classical points are dense);
  - `PointTheoremBaseObject` (`:28-34`): **every automorphic arithmetic point with ordinary flag and distinct κ_i lies in V(J)**,
    the R → T direction;
  - purity and classicality of arithmetic points of B/J (the control theorem);
  - `TwistOk`, `P1core` and `P3core`.

  It comes from `HidaUAlt` via `hida_unitary_of_printed_hida` (`DTC/THidaU.lean:38-50`), whose J is the kernel to a unitary
  Hida Hecke algebra (`exists_hecke_ideal`, not opened). Its hypothesis is `HypothesesH'`.
- **`HypothesesH'`** (`DTC/AfDesc.lean:17-22`) extends classical theorem bundles. `LiteratureRankNHypothesis`
  (`DTC/LitAut.lean:59-63`) lists local Langlands/BZ facts, Jacquet–Shalika, Clozel purity, Artin reciprocity, and `RowT`.
  It contains **no Hida theory, no R = T, and no adjoint-vanishing theorem**. So those are claimed proved in the tree.
- **`RowT`** (`AutomorphyLifting/WeakOfAtt.lean:47`; `Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:42-75`)
  gives Galois representations for polarized regular algebraic cuspidal π on GL_a over CM fields:
  - semisimple;
  - compatible away from l, with full WD matching only in "tor/mono0" cases and Frobenius-semisimplified tame matching when
    the residue field is ℚ_p with p > 16a²;
  - crystalline with the right HT weights at spherical places above l;
  - pst with WD matching in "nice" cases.

  **No ordinary-at-l clause** (π ordinary ⇒ ρ|G_v upper-triangular with prescribed characters) appears in RowT. The ordinary
  local–global compatibility needed for J ≤ ker x and for Galois determinants on the Hida Hecke algebra must therefore be
  proved inside `exists_hecke_ideal`/`hecke_ideal_point_properties` (not opened).

**Comparison with Skinner–Wiles** *(inferred)*:

| SW ingredient | Here |
|---|---|
| Hida families | `ModUAlt`/`HidaUAlt` over an auxiliary CM field L |
| base change to make the Eisenstein locus manageable | `GdFrameEx`/`GalLink` (L chosen with frame conditions Ok/Big; `SeedClause`) |
| connectivity: every component through the reducible locus meets a modular one | "linked ends", `components_good_rank_two/three` |
| pro-modularity of components, dim R ≥ dim Λ | `dimOf`/`degEq` |
| p-distinguished | `GD`: l − 1 ∤ 2e makes cyc^e, 1, cyc^{−e} distinct mod l |
| l odd | `GD.l_odd` |

What has no SW counterpart:
- (ii) Taylor–Wiles patching: **absent**. It is replaced by Hida-family dimension counting and propagation. This is consistent
  with SW, which also needs no patching.
- The 3-dimensional reducible locus with three characters, handled by running n = 2 and n = 3 together (the endoscopic W⊕1
  branch is covered by the n = 2 run).
- (iv) Ordinary local–global compatibility at l, as noted above.

**Weights.** e ranges up to x^{401} with l small. In Hida families this matters only through classicality and control at
weight (e, 0, −e), which is weight-independent for ordinary forms. Nothing in the statements requires l > e.

## 3. Children

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `AutEnd3Alt` / `GdEndAlt` | `DTC/AutEnd3AltAlt.lean:20,35` | every ordinary, minimally ramified, normalised lift of Ψ̄⊕1⊕Ψ̄⁻¹ over a finite DVR, irreducible on open subgroups of G_K, is polarized-cuspidal automorphic (after cyc⁻¹), uniformly in l odd with l − 1 ∤ 2e | gives AutBAlt | **core**, beyond the literature (Thorne 2015 and Allen–Newton–Thorne treat ρ̄ = ρ̄₁⊕ρ̄₂ with extra Selmer and size conditions) |
| 2 | `FinEnd` ← `FinPt` (via `finPtOf`, propagation) | `CDS/RatTorsionFree.lean:29`; `CDS/PropagationTheoremGL2.lean:74` | char-l ordinary deformations have residual charpoly on a finite-index subgroup ⇒ the trace algebra is finite over O (M2) | finiteness | **core** (*inferred*: equivalent to R/λ finite; usually a consequence of R = T) |
| 3 | `RigidityFirstCase` ← `AdjointLiftingTheorem` | `DTC/RigEnd3.lean:28`; `DTC/AutomorphicPointGalois.lean:35` | adjoint Bloch–Kato Selmer vanishing at automorphic points of S (and of Hida determinant rings, n ≤ 4) | M4 | **core** (cf. Allen 2016 and Newton–Thorne, which need residual hypotheses; here ρ̄ is reducible) |
| 4 | `ModUAlt` ← `HidaUAlt` ← `exists_hecke_ideal` | `DTC/PointTheoremBaseObject.lean:44`; `DTC/THidaU.lean:38` | Hida Hecke ideal J ⊂ B with control, density, classicality and R → T (automorphic points ⊂ V(J)) | existence of automorphic points | core, *standard in spirit* (Hida, Geraghty), but proved in the tree from RowT, which lacks an ordinary-LGC clause |
| 5 | `modularity_linked_ends`, `absMain` (`components_good_rank_two/three`) | `DTC/PrLinkedEnd.lean:22`; `CDS/AbsMain.lean:12` | every component of B is good / pro-modular | SW connectivity step | **core** (not opened past the statement) |
| 6 | `twoRuns_alt` | `DTC/TwoRuns.lean:80` | two runs with distinct auxiliary p are glued into full automorphy | glue | glue (read) |
| 7 | `GdFrameEx`, `SeedClause`, `UnitaryThreeAutomorphyDense`, `Seed2Alt` | `CDS/HostFrameEx.lean:58,75`; `DTC/LinkedEndE.lean:19` | an auxiliary CM field L with frame, and automorphic seed points | base change and seeds | core (not opened) |
| 8 | `LemmaM` = `Alg.M.main_holds` | `CommutativeAlgebra/OrbitVanishingLocal.lean:111`; `GML/MainCotSpan.lean:32`; `GML/AlgMemCoef.lean:92` | cotLen₋₁ ≤ 2Σ_T v(ξ a) under M1–M5 | step (2) | core, proved; mechanism read down to `low_holds`/`up_holds`/`chain` (bodies of those three not opened) |
| 9 | `Loc.locGood` (`LocalPublishedTheorems`) | `U3/RingEx.lean:153`; `ConjStable.lean:34` | the local ordinary ring It is smooth at the split point with graded dims 1, 2, 3, 4, 2 | Model/chart | definition to unfold (a hypothesis bundle) |
| 10 | `exists_ordPt_of_point` | `DTC/AutomorphyU3OfEndoscopy.lean:34` | points of S (condition It) are OrdPts (condition CondT at B) | bridges two local conditions | glue? (not opened) |

## 4. Oddities
1. **Two LemmaM's.** `Formalism/SharpRestriction/.../GradedPowerSeriesLemmas.lean:221` (cited by the parent) has a different
   M4: regular local of Krull dimension 1. `model_upper` uses `UpperTheory.V.Alg.LemmaM` (`OrbitVanishingLocal.lean:111`), where
   M4 says the tangent dimension is ≤ 1. The parent's rendering of M4 belongs to the unused version.
2. **Two different local conditions at l.** The ring uses It (components through r0 of a saturated ordinary ideal). The
   automorphy theorem uses `OrdPt`/`CondT` at a place B. The bridge `exists_ordPt_of_point` is unopened. If It allows points
   not of type CondT, AutBAlt would not cover them.
3. **FinEnd quantifies over all characteristic-l complete local A,** including R/λ itself. It is equivalent to finiteness of R
   over O. It is listed as a hypothesis-level property of the frame, proved by propagation. This is where I would look first
   for a gap: in the case of interest, l divides the congruence, and R/λ has non-reduced structure (toy: k[[X,Y]]/(X²Y)). Its
   charpoly on a finite-index U is residual only if the weight-0 products B·C contribute nothing to charpolys on U. I did not
   check this, even in the toy.
4. **No ordinary-at-l local–global compatibility in `RowT`** (WeightsConjBis.lean:42-75), yet `PointTheoremBaseObject` needs
   automorphic points with ordinary flags. Either it is proved inside `exists_hecke_ideal`, or the flag is assumed on ρ. In
   `PointTheoremBaseObject` it is a hypothesis (`HasFlag`), so the ordinary LGC is pushed to whoever produces the points.
5. **Covers / ∀ T.** LemmaM's bound holds for every covering T, and T may contain repeats. This only weakens the bound, so it is
   harmless.
6. **Vacuity.**
   - The base point exists (`Model.base`).
   - If there are no two-signed points, the lemma forces cotLen₋₁ = 0. That is a strong, non-vacuous claim: Ш⁺ = 0.
   - Ш is not replaced by something zero by definition. `shaCoc` is the correct Ш-type cocycle set.
   - No `True` hypotheses were seen in the chain I read, apart from `GCond.noCondition` for the local universal ring, which is
     correct.
7. **The factor 2 is a filtration artefact** (squares of weight ±1 generators in the Rees filtration). The toys suggest the
   truth is ≤ 1·Σ.

## 5. Coverage
Read:
- PROTOCOL; SUMMARY §10; NODE-ONECHARU (all); NODE-VWIN not reread in detail.
- `DTC/FOneCharU.lean` (all); `U3/GRepresents.lean:1-145`; `U3/ConjStable.lean` (all); `U3/RhoKApply.lean:1-80`; `U3/ULocEx.lean` (all);
  `U3/RingEx.lean:105-153`; `U3/Rigid0.lean` (all); `U3/ModelUpper.lean:100-150`; `U3/VlenLe.lean:40-67`.
- `PadicHodgeTheory/IsInertiaInfiniteCyclotomic.lean:1-140`.
- `AutomorphicCases/AutomorphyUnramifiedCoefficients.lean:1-40`; `DTC/AutomorphyUnramifiedCoefficients.lean`; `DTC/IsAutI.lean`;
  `DTC/AutomorphyU3OfEndoscopy.lean:1-63`; `DTC/AutEnd3AltAlt.lean` (all); `CDS/RatTorsionFree.lean:1-45`; `AutomorphyLifting/IsAutCsdA.lean:1-30`.
- `DTC/GdEndOf.lean:1-85`; `DTC/PlDefs.lean`; `CDS/HostFrameEx.lean` (all); `CDS/PropagationTheoremGL2.lean:60-95`; `DTC/PrDesc.lean`;
  `DTC/LinkedEndE.lean` (all); `DTC/TwoRuns.lean` (all); `DTC/PrLinkedEnd.lean` (all); `CDS/AbsMain.lean:1-30`.
- `DTC/PointTheoremBaseObject.lean:1-48`; `DTC/HidaU.lean`; `DTC/THidaU.lean:25-50`; `DTC/AfDesc.lean:1-40`; `DTC/LitAut.lean` (all);
  `AutomorphyLifting/WeakOfAtt.lean:1-60`; `.../WeightsConjBis.lean:1-100`.
- `DTC/FPtHypU.lean:10-45`; `DTC/RigEnd3.lean:1-45`; `DTC/ERigIU.lean:80-90`; `DTC/AutUpA.lean:80-100`; `DTC/AutomorphicPointGalois.lean:35-40`.
- `CommutativeAlgebra/OrbitVanishingLocal.lean:1-125`; `GML/MainCotSpan.lean` (all); `GML/AlgMemCoef.lean:1-200`;
  `Formalism/.../GradedPowerSeriesLemmas.lean:1-245`.

Not opened:
- `exists_hecke_ideal`, `hecke_ideal_point_properties`, `nonempty_unitaryHeckeData`;
- `components_good_rank_two/three`, `finPtOf`, `dimOf`, `degEq`;
- `exists_ordPt_of_point`, `finA_of_end`;
- `low_holds`/`up_holds`/`admissibility_holds`;
- `Loc.locGood`, `exists_univ`;
- `UnitaryThreeAutomorphyDense`, `Seed2Alt`, `GdFrameEx` proof;
- `AdjointLiftingTheorem` proof, `RigiditySecondCase` proof;
- `model_lower`, `sha_inj` bodies.
