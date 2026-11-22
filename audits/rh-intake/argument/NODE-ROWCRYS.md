# NODE-ROWCRYS: the l-adic clauses of `Row0b` (`AboveB.crys`, `AboveB.nice`): statement, proof route, inputs, live bundle, purity

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my own reading. Nothing was compiled or run.

Abbreviations:
- `GR/` = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- `GG/` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/`
- `CD/` = `GR/IntegralStructures/CrystallineDescent/`
- `ECL` = `TPS/EveryCharacterOfLiteratureOfVWin.lean`
- `GLC` = `GR/IntegralStructures/InertCharpoly/GaloisLocalGlobalOfLocalGlobalCompatibility.lean`

## 0. Verdict

**No ESCALATE.**

1. **The clause is claimed for every π, not only geometric ones.**
   - `Row0b` claims `crys` and `nice` for **every** regular algebraic polarized cuspidal π on GL_a over every CM field, for every prime l, with no bound on the weights.
   - For essentially every π, the proof obtains r as an **l-adic trace limit** (`LimFinOdd`) of geometric seeds. Even rank goes through two stable-range theta lifts to odd rank.
   - So the clause does rest on limits. The GoodR family of `G2a` is therefore **not** geometric-only.
2. **The limit argument is the correct one.**
   - The congruent forms U′ are required to have the **same weight as U at every embedding not over w₀ or v′** (`SameWtOff`).
   - The limit is asserted crystalline only at places w apart from w₀ and v′.
   - At those places the in-tree closure theorem `closedAtL` is used. It is a Kisin / Berger-type statement: a limit of semistable representations with **fixed** HT multiplicities J is de Rham with jumps J, and it is crystalline if the approximants are. Its proof fixes the jump bound N = max|J| and works with Breuil–Kisin lattices.
   - Every w is covered by choosing (w₀, v′) among three pairwise-apart places above l, then identifying the different limits by Chebotarev / Brauer–Nesbitt (`joinU_of`).
   - So the exact-weight objection (unbounded weights in a family) does not apply.
3. **`nice` at an unramified (Tor, N = 0) parameter.**
   - It is obtained by solvable CM base change to a field where the component is spherical, then the spherical clauses, then descent of de Rham, pst and jumps (`R1`).
4. **Task 4: the root uses the in-tree Row0b, not Published Caraiani.**
   - The root's `car` is `O.caraianiLocalGlobalDual : UpperTheory.One.M.Row` (ECL:216, 618), filled with `galoisLocalGlobalStrong_recParameter` (`Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:8, 11`).
   - The field's name says "Caraiani", but its type is the in-tree Row0b.
   - The Published `CaraianiLocalGlobalDual` appears only in `HypothesesBridge.main` and its caller `localLanglandsGL_and_prN_of_lit`. ECL never references either.
5. **Task 5: purity on the `ConclusionG6` path is not Galois purity.**
   - It is the **Jacquet–Shalika bound** q^{-1/2} < |α| < q^{1/2} for Satake parameters of cuspidal constituents (`OpenB`), together with half-integrality (`OpenB.exp_eq`), which forces |α| = 1.
   - That bound is proved in-tree (`tempered_of_true_cuspidal_alt` → `jacquetShalikaBound`).
   - No Ramanujan, Clozel or Caraiani temperedness is needed there.
   - `Published.ClozelPurity` in this tree is Clozel's purity **lemma for the infinity type**, not local temperedness.

| Q | Answer | Status |
|---|---|---|
| 1 | §1 | read |
| 2 | §2: crys/dR ← CoreAll ← Core ← LimFinOdd (seed + congruence + `closedAtL`), theta for even rank, base change | proved; chain read to `closed_of_cover`; seed, congruence and BK-frame lemmas statement only |
| 3 | §3: all inputs proved in-tree; none is a hypothesis; none is stronger than the literature | read (statements) |
| 4 | the TPS bundle, `car := One.M.Row` = Row0b | read |
| 5 | Jacquet–Shalika bound, a datum field `adm7_alt` | read |

## 1. Statement (Task 1)

**`Row0b Rc`** (`GR/TypeConditions/WeightsConjBis.lean:69-73`):
- Data: every CM field E, every prime l, every ι : \bar{ℚ}_l ≅ ℂ, every a ≥ 1, every cuspidal π on GL_a(𝔸_E) with χ such that π is regular algebraic and `PolarizedPair π χ`.
- Conclusion: there exist r : G_E → GL_a(\bar{ℚ}_l), wt and HT with `PropsB Rc π ι r wt HT`.
- `Rc = recT` = `IsRecT` (`GR/IntegralStructures/Development.lean:18`).

**Weights** (`PropsB.weights`, WeightsConjBis.lean:60-61):
- HT τ is the multiset {(a−1)/2 − z : z ∈ infinity type of π at ι∘τ}.
- It is fixed once, by `exists_weights` (GLC:127-148).
- There is no size or regularity restriction beyond "regular algebraic". The application's enormous weights are in scope.

**Above l** (`PropsB.above`, :64-67). For every period datum P with `Nonempty (LocTied l P AI)`, every place w, and every bridge Bw with `Pst.Induces Bw`, the condition `AboveB` (:39-52) holds.
- `Pst.Induces Bw` forces l ∈ w (`mem_of_induces`, used at GLC:115). So w | l.
- **`crys`** (:43-46). If σ = π_w is spherical, then:
  - r|_{G_w} is crystalline (`IsCrysAt`) and de Rham;
  - at each τ inducing w, its HT jumps equal HT τ.
- **`nice`** (:48-52). Take σ = π_w and any rc with `IsRecT`. Suppose either rc(σ) is `Tor` (commutators of W_w act trivially, `WeightsConjAlt.lean:27`), or w ≅ ℚ_p with a = 1 or p > 16a², and rc(σ) is tame and `Sqf`. Suppose also N = 0. Then:
  - r|_w is de Rham and **pst**;
  - its HT jumps are HT τ;
  - `AwayB(wdAt(r|_w), rc(σ))`. In the Tor case this means WD(D_pst(r|_w)) = rc(σ). In the tame case it means N = 0 and equal inertia charpolys.
  - In the Tor case the equality is proved from equal charpolys of every Weil element plus N = 0 on both sides (`eq_of_mono0_charPol`, GLC:119). *(inferred)* This is equality of Frobenius-semisimple WD representations. `wdAt` was not opened; NODE-GALREP reads `wdOf` as Frobenius-semisimplified.

`Row0b` is the projection of `Row0` (`WeightsConjAlt.lean:51-89`; `Row0.row0b`, WeightsConjBis.lean:84-86). That projection weakens `Away` to `AwayB` by restricting the tame clause to big p.

**In the literature.**
- `crys` matches BLGGT, "Local–global compatibility for l = p, I": π_w unramified ⇒ crystalline with the right HT weights, for all l.
- `nice` in the Tor case is the pst/WD part of BLGGT II / Caraiani 2014, restricted to abelian parameters with N = 0.
- Neither is stronger than the literature.

## 2. Argument (Task 2)

### 2a. How `crys` and `nice` are assembled

The constructor is `galoisLocalGlobal_of_placeClassCompatibility` (GLC:157-171), called via GLC:192-193 from `rest` (`GR/IntegralStructures/Development.lean:24-25`).
- **`crys` field** (GLC:166-168). It is `crys C` (GLC:150-153): a Satake parameter B at w gives `C.2 .crys` and `C.2 .dR`, where C : `CoreAll`.
- **`nice` field** (GLC:169-171) is `above H1 H2` (GLC:108-125).
  - In the Tor case it uses `H1 : R1` (`Development/AbelianVarietyTheory/Statements/EllipticCurveLevels/IsQg.lean:13-26`).
  - In the tame case it uses `H2` (`R2`-type, IsQg.lean:31-47), from `localGlobalCompatAtIwahoriFixed_of_unlinked` (not opened).
- For the unramified π_w that `G2a` needs, the Tor case applies. Independently, `crys` applies directly because π_w is spherical.

### 2b. R1 (Tor, N = 0) reduces to the spherical clauses

`galoisCompat_unlinkedSupport_of_spherical` (`GR/SphericalGaloisCompatibility/ToralDeRham/GaloisCompatUnlinkedSupportOfSpherical.lean:69-82`) proves R1 from `CoreAll`.
- **de Rham with exact jumps.** `deRham_of_plainTor` (:27-67) proceeds in three steps:
  1. A solvable CM extension M with PM = BC(π) spherical at u | w (`exists_sph_lift_of_toral`, :36-38).
  2. `CoreAll .dR` for PM at u (:40).
  3. `deRham_descends` and `jumps_descend` (:41-44, :66). The infinity type matches through `hlift.inf` (:65).
- **pst and WD charpolys.** These come from `toralAbove_of_holds` with `CoreAll .crys` and `.phi` (:76-82). *(inferred)* That is: potentially crystalline over M, plus Frobenius on D_cris equal to the Satake data.

This is the standard solvable-base-change argument (BLGGT style).

### 2c. CoreAll ← Core ← LimFinOdd

- **`CoreAll`** (`GG/CyclicStrongAtCusp.lean:96`) is `Ex .all ∧ ∀ c, SphericalLevelCondition .all c` (:88-92).
  - At every w with Satake parameter B, for every `Weak` r, `SphAt c` holds for c ∈ {unr, dR, crys, phi} (:78-86).
  - `Weak` = continuous ∧ `AttC` (`GG/IsWeight.lean:18-19`). `AttC` includes `IsSSRep` (`Development/AutomorphicArithmetic/AutomorphicVarieties/AutomorphicForms/BlochKatoSelmerVanishes.lean:77-82`). So r is unique up to isomorphism.
  - `ClauseAt .dR` gives de Rham and jumps J whenever J is the infinity-type multiset (IsWeight.lean:35-40).
- **`coreAll_of_core`** (`SP/CoreAllOfCore.lean:24-36`) passes in two steps from `Core` to `CoreAll`, by twisting and base change / descent (unopened theorems):
  - from csd, `Good`, split places
  - to polarized, all fields, all places.
- **`Core`** is `toCore` (`CD/LimOddOfLimFinOdd.lean:53-62`). The chain is: `LimFinOdd` → `LimOdd` → `LimU` (`limU_of_limOdd`, `CD/LimOddOfLimWU3.lean:48-54`) → `joinU` → `joinAll` (even rank) → `joinGL` (descent) → `joinUp` → `joinEnd`.

**`LimFinOdd = LimWU4 Odd`** (`GG/LimWU4OfLimWU3.lean:57-76, 107`). It covers:
- every U on a definite U(a), a odd, of any level, with l split (`FieldOK`);
- every pair w₀, v′ of places above l that are apart.

For each such datum there is a semisimple r with:
- Frobenius = Satake at good places;
- **`CrysDRU U ι r w` at every w | l that is spherical and apart from w₀ and v′.** `CrysDRU` (`GG/LatticeDataThicknessBound.lean:36-44`) means crystalline, de Rham, and HT jumps given by U's weight at w.

**`limWU4_of`** (`GR/TraceLimits/LimFinOddOf.lean:16-195`, read in full) uses two inputs:
- **seed** `SeedWU4` (LimWU4OfLimWU3.lean:15-35). For U′ of type `TyEll` at w₀, of the given level off w₀ and v′, it gives r_{U′}. That representation is crystalline with U′'s jumps at w ∈ Y apart from w₀ and v′ (:34). It comes from `GeoOne`.
- **congruence** `CongUW4` (:37-55). The Hecke eigensystem of U is a limit (`PolyApprox`) of eigensystems of such U′ with `SameWtOff ι w₀ v′ U U′`, the same level off w₀ and v′, and the seed conditions.
  - `SameWtOff` (`GG/CuspFormLimitTwoPlaces.lean:27-29`) says: at every embedding τ not over w₀ or v′, U and U′ have the same weight.
  - "Over" is `OverPl`, :21-22.
  - `Apart` is "different place of F⁺" (`Development/AbelianVarietyTheory/Statements/EllipticCurveLevels/ClosedAtLConclusionOfMem.lean:16-17`).

The steps of the proof:
1. `exists_trace_limit` and `exists_limit_rep` (:118-127) produce r with `LinApprox r (ρ '' A)`.
2. The `CrysDRU` conclusion (:166-172) is `crysDRU_of_linApprox closedAtL …` applied to the approximants. Each approximant carries `sameWtAt_of_off …` (same weight as U **at w**) and its seed `CrysDRU` at w.
3. `crysDRU_of_linApprox` (`SP/BlowUpFibreSemilocal.lean:67-97`) feeds `closedAtL` with J = jumps of U's weight. It checks that each approximant is semistable (crystalline ⇒ sst) with those jumps, via `SameWtAt` (:80-82).

**`closedAtL`** is proved (`SP/ClosedAtL.lean:25-117`). Its statement `ClosedAtL` (ClosedAtLConclusionOfMem.lean:105-118) says: if r is semisimple and `LinApprox r C`, and every ρ ∈ C is semistable at w with HT jumps J (fixed), then r|_w is de Rham with jumps J, and crystalline if all ρ are crystalline.
- It reduces to `closed_of_cover` (`Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ClosedOfCover.lean:159-301`).
- That proof does the following:
  - sets **N := max |J|** (:168-175);
  - builds Breuil–Kisin frames of bounded height N for each lattice layer (:183-186);
  - takes a limit frame (:188);
  - shows that the limit is de Rham and crystalline when the layers are (:189-193);
  - recovers the HT multiset of the limit from power sums of a Hodge–Tate operator along the tower (:194-300).
- This is the Berger "limites de représentations cristallines" / Kisin-closedness mechanism, and it uses the fixed weights essentially.

**Covering every w** (`joinU_of`, `CD/JoinEndHolds.lean:19-62`).
- `FieldOK` supplies three pairwise-apart places w₁, w₂, w₃ above l (:44).
- For each w | l it picks u, v among them, apart from w (:48-55). It applies `LimU` with (w₀, v′) = (u, v) and gets s crystalline at w with U's jumps (`key`, :25-43).
- `IsoOne` (Chebotarev / Brauer–Nesbitt) identifies s with the fixed r, and `ClConj` transports the clause (:58-61).

### 2d. Even rank: theta lift and peeling

`allCoreQ_of` (`GR/ThetaParseval/CoreAtQIffRowQ.lean:216-220`) sends even n to `SubtractQ` (:195-198), proved by `subtractQ_of` (:200-210). The core step is `atPlaceQ` (:103-174):
- `TwoUp` gives two lifts U₁, U₂ to odd rank n+t. Each has parameter (U ⊗ κ) ⊕ Hecke characters, with disjoint character sets ψ₁, ψ₂ (:107-108).
- Odd-rank `RowQ` gives r₁ and r₂ (:112-113).
- The charpoly identity r₁ ⊕ ψ₂ ≅ r₂ ⊕ ψ₁ (:128-130) and `PeelAll` give an n-dimensional summand s (:141).
- Its clause at w (crystalline, jumps) follows from r₁'s clause with jumps (U's jumps + m) ∪ {−p₁ i} (:148-158), by taking the summand and twisting back by κ (`hcl`, `hCT`, :165-178).
- So even rank also inherits exact weights from odd-rank limits.

### 2e. The geometric seed

`geometric_realization_of_weight_one` (`GR/IntegralStructures/GeometricFlagBases/GeometricRealizationOfWeightOne.lean:18-25`) builds a representation from l-adic cohomology of a Hecke tower (NODE-GALREP §1c).
- Its crystallinity is `Seam.crysStep_holds := crysStep_of cstSmooth.1` (`GR/CrystallineTowers/Closed.lean:7-9`; `CrysStep` at `…/HodgeTrAt.lean:112-115`).
- `CstSmooth` = `SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi` (`Development/WeilBound/CoreStatements/PadicHodgeComparison/EtaleCohomologyComparison/CstSmooth.lean:18`).
- `SmoothModelCrystalline` (`…/SemistableModelSemistable.lean:46-48`): étale cohomology of a good smooth model over O_K is B_cris-admissible. That is Faltings/Tsuji C_cris.
- It is proved in-tree from `HT.etSideS = Top.etSide_sm_holds` (`GR/CrystallineTowers/ClosedHT.lean:15`). I did not open the body.

### 2f. Which representations are geometric and which are limits (G2a's GoodR)

- **Geometric directly:** only the seed U′ (odd a, `TyEll` type at w₀, special fields).
- **Limits:**
  - every U at odd rank, through `LimFinOdd`;
  - even rank, through theta to odd rank;
  - general CM fields and polarizations, through base change / descent.
- GoodR (NODE-GALREP §2c) is built from Row0b-type representations of the constituents π_j of Labesse base-change parameters. These are generic regular algebraic csd π, so **they are limit representations**.
- `G2a` uses `nice` + `CrysIffWD` (NODE-G2A). By §2b–c that rests on `CoreAll` at a spherical place, which holds with exact weights for the reason in §2c.

## 3. Children and inputs (Task 3)

| # | name | file:line | statement | role | weight / status |
|---|---|---|---|---|---|
| 1 | `galoisLocalGlobal_of_placeClassCompatibility`, `above`, `crys` | GLC:108-171 | CoreAll + R1 + R2 ⇒ Row0 | assembles `crys`/`nice` | glue; read |
| 2 | `galoisCompat_unlinkedSupport_of_spherical`, `deRham_of_plainTor` | `…/ToralDeRham/GaloisCompatUnlinkedSupportOfSpherical.lean:27-82` | CoreAll ⇒ R1 (Tor, N = 0: dR, pst, WD) | solvable BC + descent | standard (BLGGT); read; `toralAbove_of_holds`, `deRham_descends` statement only |
| 3 | `coreAll_of_core` | `SP/CoreAllOfCore.lean:24` | Core ⇒ CoreAll | twist / BC / descent | standard; read (callees unopened) |
| 4 | `toCore`, `joinU_of` | `CD/LimOddOfLimFinOdd.lean:61`; `CD/JoinEndHolds.lean:19-62` | LimFinOdd ⇒ Core; three apart places | covers every w | core; read |
| 5 | `limWU4_of` | `GR/TraceLimits/LimFinOddOf.lean:16-195` | Seed + Cong ⇒ limit r crystalline with U's weights off w₀, v′ | trace limit | **core**; read |
| 6 | `closedAtL` → `closed_of_cover` | `SP/ClosedAtL.lean:25`; `…/InertiaEigenvalues/ClosedOfCover.lean:159` | limit of sst reps with fixed HT ⇒ dR with the same HT; crystalline preserved | the closure theorem | **core**, standard (Berger 2004 / Kisin 2008); proved; BK-frame lemmas (`exists_frame_sst`, `limit_frame_exists`, `crys_of_frame`, `CoverTrace.trace_pow_eq`) statement only (wrapper files read) |
| 7 | `seedFinOdd_of_geoOne`, `congFinOdd_of_ex wtLacEx_holds` | `GR/IntegralStructures/Development.lean:28` | seeds; congruences with weights changing only at w₀, v′ | inputs to 5 | **core, unread**. *(inferred)* `CongUW4` is a p-adic family on a definite unitary group with weight varying at the places over w₀, v′ only |
| 8 | `subtractQ_of`, `atPlaceQ` | `GR/ThetaParseval/CoreAtQIffRowQ.lean:103-210` | even n from two odd theta lifts by peeling | parity | core; read; `TwoUp` (TLiftK) per NODE-GALREP |
| 9 | `crysStep_holds` ← `cstSmooth` | `GR/CrystallineTowers/Closed.lean:7-9` | C_cris for good smooth models | seed crystallinity | standard (Faltings, Tsuji); proved in-tree, statement only |
| 10 | `Inp.pst` = `deRham_potentiallySemistable` | `GR/IntegralStructures/CrystallineInputs/Crys.lean:32` | `Published.DeRhamPotSemistable`: dR ⇒ pst (`…/AutomorphicForms₂/DeRhamPotSemistable.lean:13-17`) | in `Inputs` | standard (Berger 2002); proved in-tree, statement only |
| 11 | `inp_holds` | `GR/IntegralStructures/CrystallineInputs/InputsOf.lean:11-20` | JS, GK, BZ, exhaustion, Zelevinsky, unitary dual, Arthur–Clozel | `Inputs` | standard; proved terms |

**Published statements on this path.**
- No `Published.*` Prop enters Row0b's proof as a hypothesis. Each one used (`DeRhamPotSemistable`, `ArthurClozelStrongTC`, `JacquetShalikaRigidity`, …) is proved by a named theorem.
- Kisin / Berger closure, Faltings–Tsuji C_cris and Berger's dR ⇒ pst are all **proved in-tree**. I read their statements; I did not verify their bodies.
- Caraiani, BLGGT, Shin, Kottwitz and Morel do not occur as Published inputs on this path.
- **Nothing is stronger than the literature:**
  - `ClosedAtL` concludes only dR + jumps (+ crystalline), which is weaker than Kisin's sst-closedness.
  - `Row0b`'s l-adic clauses are within BLGGT l = p I/II.

## 4. Live bundle (Task 4)

The root (read):
- `everyCharacter := everyCharacter_of_row galoisLocalGlobalStrong_recParameter` (`…/CharacterBoxes/MainConclusion.lean:10-11`).
- `everyCharacter_of_row h = every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ …` (:7-8).
- `OpenLiteratureStatements` has exactly three fields (ECL:215-218): `caraianiLocalGlobalDual : UpperTheory.One.M.Row`, `localLanglandsExists`, `galoisRepOfPolarizedPairLit : One.M.Row`.

How `car` is consumed (read):
- `literature_automorphy O` sets `car := O.caraianiLocalGlobalDual` (ECL:609, 618). It is used as `aut` (ECL:641).
- `localLanglandsGL_and_purity_at_member_alt` (`TPS/LocalLanglandsGLAndPurityAtMember.lean:18-26`) passes `A.car` to `T.published_inputs_combined_alt_alt` = `HypothesesBridge.locComp_of_isRc_classMapD_cenLoc` (`TPS/PublishedInputsCombined.lean:18-42`). That theorem's 12th hypothesis is `One.M.Row`, and it sets `car := carU_of_finite_gl_recT hFin hLL (hCSD.1 hCLGD)` (:30).
- The same field feeds `localGlobalAboveL := carU_above_l_of_literature O` (ECL:461-462, 688).
- Its caller is `exists_hyp_n_of_geometric_galois_compat` (`TPS/ThetaLiftHypothesesOfNonvanishing.lean:24-28`).

The sibling route:
- `HypothesesBridge.main` (`SP/PublishedInputsCombined.lean:26-46`) takes `Published.CaraianiLocalGlobalDual` and builds the **different** type `NRows.Hypotheses₂`.
- It is called only via `T.published_inputs_combined` (`SP/PublishedInputsCombinedStatement.lean:17-18`) from `localLanglandsGL_and_prN_of_lit` (`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalLanglandsOfLiterature.lean:21-28`).
- ECL contains no occurrence of `Published.CaraianiLocalGlobal`, `LitAut` or `localLanglandsGL_and_prN_of_lit` (grep).

**So the root's above-l input is Row0b, proved in-tree.**

## 5. Purity (Task 5)

`ConclusionG6` uses `PurityStringWeight'` (`TPS/HeckeCharEqOfLAdicRealisation.lean:24-32`). It is proved by `sixth_weight_purity_alt_alt` (`TPS/SixthWeightStatement.lean:11-12`; `TPS/SixthWeightPurity.lean:18-86`, read). The proof:
1. Chebotarev gives a split good Frobenius σ (:22-39).
2. The χ₁-eigenvalue ε^j·χ₁(σ) is a root of the block's charpoly, hence equals some Satake α of a constituent π_k (:57-74).
3. `frobEig_openB_and_norm_one_of_isBCV` (`TPS/PartFrobEigNormO.lean:11-59`) gives `OpenB q α`: q^{-1/2} < |α| < q^{1/2} (`…/StringRepresentations/AllCuspidalOpenBound.lean:12`).
4. |α|·q^{x} = q^{y} with y − x ∈ ½ℤ forces x = y (`OpenB.exp_eq`, `…/RankOneOfLong.lean:11-12`). This gives d − 1 − 2j = t − 1 (:84-86).

Where `OpenB` comes from:
- It comes from `GalN.tempo' hT` with `hT : adm7_alt D` = `AllCuspidalOpenBound` (`TPS/CuspidalGaloisUnramified.lean:31`). That is `TempAt` at every w for csd regular algebraic cuspidal constituents (AllCuspidalOpenBound.lean:22-25).
- `TempAt` means "tempered if a = 1, and the JS bound at unramified w". **It is not Ramanujan.**
- `temp` is a field of `RowsAAlt` (`TPS/PartsGive.lean:21`). Both suppliers found (`TPS/NOProd.lean:24-35, 39-41`) use `tempered_of_true_cuspidal_alt`, which calls `PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound` (:33). That is the Jacquet–Shalika 1981 bound.
- I did not trace which of the two suppliers the root uses.

The `clo := regularAlgebraicPurity_of_clozel hCP hCC` field (`TPS/PublishedInputsCombined.lean:31`; ECL:493-494):
- It concerns the **infinity type**. `Published.ClozelPurity` (`…/GaloisGeometry₂/ClozelPurity.lean:10-14`) says the infinity type is pure: z ↦ w₀ − z under complex conjugation. This is Clozel's purity lemma.
- `RegularAlgebraicPurity` (`…/RegularAlgebraicPurity.lean:14-18`) adds "cohomological".
- It is proved in-tree (ECL:329-330 → `WeilBound/…/ClozelPurity/Bridge.lean:6`).

`PropsU.sizeAway` (`GG/CyclicStrongAtCusp.lean:118-120`) is a Galois-side purity clause of the stronger `RowU`. It is not part of Row0b and not on this path.

## 6. Oddities

1. **Misleading field name.** `OpenLiteratureStatements.caraianiLocalGlobalDual` (ECL:216) has type `One.M.Row`, the in-tree Row0b, not the Published Caraiani statement imported at ECL:10. `galoisRepOfPolarizedPairLit` (:218) is also `One.M.Row`. A reader of names would think Caraiani is assumed; it is not.
2. **`AboveB` quantifies over all places w.** It applies only above l, through `Pst.Induces` (GLC:115). It is not vacuous, given `Nonempty (LocTied …)` (NODE-G2A §1).
3. **The `nice` tame case** needs w ≅ ℚ_p with p > 16a². Since w | l, this means l > 16a², so it is essentially unused for large a. The Tor case (unramified, principal series with N = 0) is what `G2a` needs.
4. **The unread core inputs to the limit argument** are `CongUW4`/`congFinOdd_of_ex` and the seed. A reviewer should check that congruent forms with weight varying **only** at the places over w₀ and v′, at fixed level elsewhere, are produced honestly. The correctness of the exact-weight conclusion depends on `SameWtOff`, and that is part of `CongUW4`'s statement (read). So any problem would sit inside `wtLacEx_holds`, not in the closure step.
5. **Jumps over w₀ and v′.** `closedAtL` is applied with J defined at all τ, but the approximants are checked only at τ inducing w (`BlowUpFibreSemilocal.lean:80-82`). That is consistent: jumps over w₀ and v′ are never claimed for the limit.

## 7. Coverage

Read:
- PROTOCOL; NODE-G2A, NODE-GALREP, NODE-LIVEPATH, NODE-WHERECONG (all).
- `GR/TypeConditions/WeightsConjBis.lean` (all); `WeightsConjAlt.lean` (all).
- `GR/IntegralStructures/Development.lean` (all); `RowSrc.lean` (all); GLC (all).
- `IsQg.lean` (all); `ToralDeRham/GaloisCompatUnlinkedSupportOfSpherical.lean` (all); `…/SphericalGaloisCompatibility/GaloisCompatUnlinkedSupportOfSpherical.lean` (all).
- `GG/CyclicStrongAtCusp.lean` (all); `GG/IsWeight.lean` (all); `BlochKatoSelmerVanishes.lean:60-95`.
- `CD/ToCoreK.lean`, `CD/LimOddOfLimFinOdd.lean`, `CD/LimOddOfLimWU3.lean`, `CD/JoinEndHolds.lean`, `CD/JoinAll.lean` (all); `PatchOneAlt.lean` (def list).
- `GG/LimWU4OfLimWU3.lean` (all); `GR/TraceLimits/LimFinOddOf.lean` (all); `SP/ClosedAtL.lean` (all); `ClosedAtLConclusionOfMem.lean:14-20, 95-140`; `ClosedOfCover.lean` (imports, theorem list, 159-301); four BK `*Statement.lean` wrappers; `SP/BlowUpFibreSemilocal.lean:67-97`.
- `GG/CuspFormLimitTwoPlaces.lean:15-40`; `GG/LatticeDataThicknessBound.lean:25-55`.
- `ThetaParseval/AllCoreOf.lean:1-30`; `CoreAtQIffRowQ.lean:60-224`.
- `GeometricRealizationOfWeightOne.lean`; `CrystallineTowers/Closed.lean`; `ClosedHT.lean:1-23`; `HodgeTrAt.lean:100-140`; `CstSmooth.lean`; `SemistableModelSemistable.lean:30-58`.
- `CrystallineInputs/InputsOf.lean`; `Crys.lean:1-40`; `DeRhamPotSemistable.lean` (grep 13-17); `SP/CoreAllOfCore.lean`.
- `TPS/PublishedInputsCombined.lean`; `SP/PublishedInputsCombined.lean`; its Statement file; `TPS/LocalLanglandsGLAndPurityAtMember.lean`; `TPS/ThetaLiftHypothesesOfNonvanishing.lean:1-45`; `LocalLanglandsOfLiterature.lean:15-40`.
- ECL:210-222, 327-330, 459-462, 493-494, 600-625, 641, 680-692, 805-814; `MainConclusion.lean`.
- `TPS/HeckeCharEqOfLAdicRealisation.lean:15-40`; `TPS/SixthWeightStatement.lean`; `TPS/SixthWeightPurity.lean` (18-89); `TPS/PartFrobEigNormO.lean`; `AllCuspidalOpenBound.lean:1-35`; `RankOneOfLong.lean:11-15`; `TPS/NOProd.lean:18-60`; `TPS/PartsGive.lean:13-30`; `ClozelPurity.lean:8-22`; `RegularAlgebraicPurity.lean:12-24`.

Greps run:
- `def (CoreAll|Core|Weak|ClauseAt|R1|R2|InScope|PlaceOK|Ex)`; `namespace GlobalTheory.RoadU|GalCut`;
- `def (LimFinOdd|LimOdd|LimU|SeedFinOdd|CongFinOdd|TwoUpOK|JoinU)`; `limFinOdd_of`; `joinU_of`; `joinAll_of`; `TwoUp|SubtractQ`; `def Apart|FieldOK|ApartAll`;
- `crysDRU_of_linApprox|CrysDRU|ClosedAtL|SameWtOff|SameWtAt`; `steps_holds|Steps`; `crysStep_holds|CrysStep|cstSmooth|CstSmooth|EtSideS|etSideS|SmoothModelCrystalline`;
- `def AttC|FrobEig|algSat`; `theorem pst`; `coreAll_of_core`;
- `published_inputs_combined(_alt_alt)?|locComp_of_isRc_classMapD_cenLoc|HypothesesBridge.main`; `localLanglandsGL_and_(purity_at_member_alt|prN_of_lit)`;
- in ECL: `car|One.M.Row|Caraiani|Clozel|purity` and `Published.CaraianiLocalGlobal|LitAut|localLanglandsGL_and_prN_of_lit|literature_automorphy`;
- `everyCharacter_of_row`; `galoisLocalGlobalStrong_recParameter`;
- `PurityStringWeight|purity_string_weight`; `ClozelPurity|RegularAlgebraicPurity|ClozelCohomological`; `frobEig_openB_and_norm_one_of_isBCV`; `adm7_alt`; `AllCuspidalOpenBound`; `OpenB|exp_eq`; `structure RowsAAlt`; `temp :=`.

Not opened:
- the bodies of `seedFinOdd_of_geoOne`, `congFinOdd_of_ex`/`wtLacEx_holds`, `exists_trace_limit`, `exists_limit_rep`;
- the BK-frame lemmas (`BKLim.*`, `CrTop.crys_of_frame`, `CoverTrace.trace_pow_eq`);
- `toralAbove_of_holds`, `deRham_descends`, `jumps_descend`, `exists_sph_lift_of_toral`;
- the callees of `coreAll_of_core`; `localGlobalCompatAtIwahoriFixed_of_unlinked` (the R2 / tame case);
- `etSide_sm_holds`; `deRham_potentiallySemistable`; `jacquetShalikaBound`; `wdAt`;
- which of the two `AllCuspidalOpenBound` suppliers is live; whether `LocalLanglandsHypothesesOfLiterature` is reachable by some other route from the root (ECL does not reference it).
