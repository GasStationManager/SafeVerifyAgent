# NODE-GALREP: `Row0b`, `galoisLocalGlobalStrong_recParameter`, `GoodR`, `NoChiOff`

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `GR/` = `Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `SR` = `Formalism/SharpRestriction/LevelLetterCocycles/SumRepresentations.lean`
- `DN` = `Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean`
- `GC` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean`

"The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.

## 0. Answers in brief

- **(a) Row0b is weaker than the literature statement.** It is weaker than Chenevier–Harris / Caraiani "full local–global compatibility", and the word "Strong" in the name misleads.
  - The scope is right: every CM field, every l, every polarized regular algebraic cuspidal π of GL_a over it, at any level.
  - It gives ρ that is continuous and semisimple, with Hodge–Tate weights from the infinity type and conjugate symmetry of the weights.
  - Compatibility away from l is required only when the local parameter is abelian with N = 0, plus a tame inertia charpoly clause. This is up to Frobenius-semisimplification.
  - Above l it gives crystallinity at spherical places, and de Rham / potentially semistable with WD matching only in "nice" cases.
  - It has no purity clause and no general ramified local–global compatibility.
- **(b) The proof has a Harris–Taylor / Chenevier–Harris shape and is closed.**
  - Descent from GL_a to a unitary group (trace formula).
  - A geometric construction (`GeoOne`) for odd rank, built from l-adic cohomology of a scheme with Hecke correspondences.
  - The theta lift `TLiftK` handles even rank by lifting to odd rank d ≫ n, in place of Chenevier–Harris's eigenvariety parity trick.
  - Trace-limit / congruence steps (`LimFinOdd`).
  - Arthur–Clozel cyclic base change, which is proved in the tree.
  - The import closure of `RowSrc.lean` is 66,168 files. A text search found no `axiom`, `sorry` or `admit`, and no use of `galoisLocalGlobalStrong_recParameter` except its own file and `GaloisRepresentationsOfThetaLift.lean`. **So it is not circular.** At the root, `OpenLiteratureStatements` is *filled by* this theorem; nothing flows back into it.
- **(c) GoodR and NoChiOff are discharged, and NoChiOff is not a theta converse theorem.**
  - **GoodR** has no l-local content: Galois representations of every eigensystem x in X_i, with charpoly(Frob_w) equal to the Hecke polynomial at split good w. Its ∃ is the `Conclusion41` field of the datum's facts. *(inferred)* It is built from the A-parameter of x, via base change and Speh strings, with Row0b-type Galois inputs.
  - **NoChiOff** is proved by `UnrNoChi.main` from GoodR plus `ConclusionG6`.
  - `ConclusionG6` says: if r_x has a χ₁-eigenline, then the A-parameter of x contains the block ⟨1, μη, t⟩. That is a Galois-side argument (§3c).
  - Z is tied to "A-parameter contains μ⊠S_t" by the **structure field `D7.Z_tie`**. The theta-image identification is a separate fact, `ConclusionZ`.
- **(d)** See §5.

## 1. Statement

### 1a. Row0b (`GR/TypeConditions/WeightsConjBis.lean:69-73`)
```lean
def Row0b : Prop := ∀ E Ω [CM E] (l) (ι : Qbar l ≃+* ℂ) (a ≥ 1) (π : CuspSub E a) (χ : HChar E⁺),
  (CG.mk π).IsRegAlg → PolarizedPair π χ → ∃ r wt HT, PropsB Rc π ι r wt HT
```
`PolarizedPair` (`Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DualIsConjByOne.lean:53-55`) has two parts:
- the sign condition χ_v(−1) = (−1)^a at every real place;
- π^∨ ≅ π^c ⊗ (χ∘N), i.e. polarized in the sense of BLGGT.

`PropsB` (`WeightsConjBis.lean:54-67`) has these clauses:
- `cont` and `ss`: continuous and semisimple.
- `away`. For every finite w ∤ l and **every** rc with `Rc h rc` (that is, `IsRecT`: any map obeying the LLC laws `LawsT`, `GR/../LocalLanglands/IsRecTOfIsRec.lean:56-76`) and every local component σ, it requires `AwayB (wdOf r|_w) (rc(algNorm σ))`. `AwayB` (`:26-31`) consists of:
  - equal dimension;
  - **if rc(σ) is "Tor"** (Weil-group commutators act trivially, i.e. abelian image, `WeightsConjAlt.lean:27`) **and has N = 0, then the WD representations are equal**;
  - if w ≅ ℚ_p with p > 16a², and the parameter is tame, square-free (`Sqf`) and has N = 0, then N = 0 on the Galois side and the inertia charpolys agree.
  - `wdOf` takes the Frobenius-semisimplified WD representation (`IsWDOf`/`IsFrobSS`, `…/WeilDeligneParamMonodromyEqZeroIff.lean:340-353`). Its junk default is the trivial representation when no WD representation exists.
- `weights`: the HT multiset is ((a−1)/2 − z) over the infinity type; `weights_conj` gives the symmetry under complex conjugation.
- `above` (`AboveB`, `:39-52`) has two parts:
  - `crys`: at w | l with σ spherical, r|_w is crystalline and de Rham with the right HT jumps;
  - `nice`: when rc(σ) is "Tor", or is tame and square-free over a big ℚ_p, and has N = 0, r|_w is de Rham and pst, and its WD representation (from D_pst) satisfies `AwayB`.

`recT` is `fun h rc => IsRecT h rc` (`GR/IntegralStructures/Development.lean:18`).

**Comparison with the literature.**
- Unramified places are covered, since the parameter is then abelian with N = 0, so Frobenius traces equal Hecke eigenvalues.
- Ramified places are covered only partially: principal-series-like with N = 0, or tame and square-free inertia charpolys.
- The above-l clause is the crystalline / Fontaine–Laffaille-type part, plus restricted pst cases.
- There is no Caraiani-type statement for N ≠ 0, and no purity (that is a separate `ClozelPurity` / `TemperedCuspidal`).
- So Row0b is weaker than Chenevier–Harris + Caraiani. The quantifier "∀ rc obeying `LawsT`" is mildly stronger: compatibility must hold for every candidate LLC map, not only the true one. That only matters if `LawsT` failed to pin rc down on Tor parameters *(inferred: `one`/`langlands` force it)*.

### 1b. TLiftK (`GR/ThetaParseval/HalfIndexLattices/TLiftK.lean:12-23`)
Fix:
- a CM field E and a hermitian space X of dimension n;
- skew-hermitian W = δ·I_d for all d ≥ d₀(X);
- splitting characters χ_X, χ_W, with χ|_{𝔸_{E⁺}^×} = η^n resp. η^d, and their exponents;
- an automorphic representation U of U(X) with weights λ satisfying d + m_W ≤ 2λ_k.

Then there is an automorphic U′ on U(W) satisfying `IsLift` (`ThetaParseval/SchurStep.lean:103-113`):
- weights λ′ given by an explicit Adams-type shift;
- at every split place, the local components are related by a nonzero intertwiner of Weil representations (`LocPair`).

In words: **nonvanishing of the global theta lift in the stable range, with local theta at split places.** This is Rallis's tower / stable-range nonvanishing.

It is proved as `tLift_of_tools_k tools_holds_k …` (`GR/ThetaParseval/ThetaKernels/TPGHolds.lean:36-58`). The inputs are doubling and the Siegel–Weil formula (`siegelWeilStd_k`), Eisenstein continuation, compactness, the Weil representation and Lie-algebra steps. All are named theorems, none is a hypothesis.

### 1c. GeoOne (`GR/IntegralStructures/GeometricFlagBases/HodgeTrAt.lean:79-90`)
Take:
- a CM field E of a special shape (`FieldOK E l d`, with √−d ∈ E);
- **odd** rank a;
- an automorphic U on U(a) (`AutOffT`, type `TyEll` at w₀ | l, spherical off S).

Then there is a Galois representation ρ (`VBase`) satisfying:
- Eichler–Shimura `ESAt` at almost all good w ∤ l: the Frobenius eigenvalues are the normalised Satake parameters;
- crystalline with jumps at suitable w | l;
- a Frobenius-killing `PhiKilled` at w | l.

`HTower` (`Development/AbelianVarietyTheory/Definitions/Divisors/IdTower.lean:9-37`) has:
- a scheme Z/k with correspondences Y_g ⇉ Z;
- Hecke operators `hop` on total l-adic cohomology Htot (an inverse limit of ℤ/l^k cohomology tensored with ℚ_l, `PullHlComp.lean:216-239`);
- the Galois action `galTot`;
- generalised eigenspaces V.

This is a genuine "cohomology of a variety with Hecke correspondences" construction.

## 2. Argument

### 2a. Proof skeleton of `galoisLocalGlobalStrong_recParameter` (two levels)
```
RowSrc.lean:6         galoisLocalGlobalStrong_recParameter := galoisRepresentations_of_thetaLift tLiftK
GaloisRepresentationsOfThetaLift.lean:6   := galoisLocalGlobalStrong_of_geometry_lift geoOne_holds up
Development.lean:30   := Row0.row0b (galoisLocalGlobal_of_geometry_lift geo up)
Development.lean:27   := rest (coreAll_of (seedFinOdd_of_geoOne geo) (congFinOdd_of_ex wtLacEx_holds) up)
Development.lean:20   coreAll_of := Inp.coreAll_of_core (toCoreK up congPhi_holds descOffT (limFinOdd_of seed cong))
Development.lean:24   rest C := galoisLocalGlobal_of_localGlobalCompatibility C (galoisCompat_unlinkedSupport_of_spherical C) (…Iwahori…)
```

Level 1, the pieces:

1. **`Core`** (`GaloisGeometry/CyclicStrongAtCusp.lean:92`) says: for conjugate self-dual π in scope, a "Weak" r exists, with clauses at spherical places (`.unr` Frobenius, `.dR`, `.crys`, `.phi`). It comes from `toCoreK` = `toCore (twoUpOK_of_k hT)` (`IntegralStructures/CrystallineDescent/ToCoreK.lean:7-9`), whose inputs are:
   - `TwoUpOK` (`ThetaParseval/AllCoreOf.lean:18-22`): even rank n is handled by the theta lift to odd d;
   - `ClosedPhi` (`congPhi_holds`);
   - `DescOffT`: descent from GL_a/E to an automorphic U on a unitary group with matching at split places and weights (`MatchOfMatchOffTEmpty.lean:24-38`). It is proved by `desc_of speh … weakAll` (`BaseChangeDescent/BcBackOffT.lean:24-29`), a trace-formula comparison;
   - `LimFinOdd` (`limFinOdd_of seed cong`, `TraceLimits/LimFinOddOf.lean:197`), *(inferred)* l-adic limits of trace functions, the Chenevier–Harris-type step. `SeedFinOdd` comes from `GeoOne` and `CongFinOdd` from the weight congruences `wtLacEx_holds`.
2. **`coreAll_of_core : Inputs → Core → CoreAll`** passes from csd to polarized π by twisting. `Inputs` = `inp_holds` (`CrystallineInputs/InputsOf.lean:11-20`) contains Jacquet–Shalika, Gelfand–Kazhdan, BZ finiteness, Langlands exhaustion, Zelevinsky, the generic unitary dual and **Arthur–Clozel cyclic base change** (`strongTC_holds = strongOf liftUnr ramSph`, `LiftFactorization/FirstQuadraticSquareHolds.lean:23`). Each is a closed theorem.
3. **`galoisLocalGlobal_of_localGlobalCompatibility`** (`InertCharpoly/GaloisLocalGlobalOfLocalGlobalCompatibility.lean:192`) assembles `PropsB` from `CoreAll`, `R1` and Iwahori-level compatibility (`:174-189`).

Level 2, `geoOne_holds` (`GeometricFlagBases/WeightOneGeometricRealization.lean:11`):
- It is `geometric_realization_of_weight_one weight_one_geometric_realization`.
- Its only external input is `HolomorphicLefschetzFormula`, proved as `lefschetz_fixedPoint_finite_etale_correspondence`.
- `geoOne_of_parts steps_holds (kodaira_spencer_of_weight_one hW) planEx_holds` (`GeometricRealizationOfWeightOne.lean:18-25`) splits into three parts:
  - `Steps` (crystalline / jump / Φ steps on the cohomology of an HTower);
  - `KSAll` (Kodaira–Spencer: the Hodge numbers of the tower match the automorphic weights);
  - `PlanEx` (`PackExOf.lean:82-90`, `planEx_holds = exists_unitaryGroupDatum_of_vector_exponent_spectral …`). For each U it produces a `Plan`: a prime p, a `Datum p`, an `HTGroup p`, a `Link`, a level N, Hecke eigenvectors g with eigenvalues θ, and congruences `CongP` linking the Hecke eigenvalues at w to the Satake parameters of U.
- *(inferred)* `Plan` = a PEL/Shimura-type datum and its integral model; `CongP` + `ESStep` = the Eichler–Shimura congruence relation; `HolomorphicLefschetzFormula` is the point-counting / trace input.

**How much of the edifice is proof terms.** The chain is closed down to named theorems. I did not find any `Published.*` Prop that is taken as a hypothesis on this path; for example `ArthurClozelStrongTC`, `DefiniteN` and `DepthZeroTypeInertia` are each proved by a theorem. I did not open the bodies of `steps_holds`, `KSAll`, `planEx_holds`, `limFinOdd_of`, `desc_of`, `strongOf` or `tLift_of_tools_k`. Whether "Shimura variety, Kottwitz counting, Eichler–Shimura" is really what is there (as opposed to a different geometric object) is **not verified**.

### 2b. Circularity
Lean forbids a theorem from using itself. The import closure of `GR/IntegralStructures/RowSrc.lean` (66,168 files) mentions the theorem name only in its own two files, and a text search found no `axiom`, `sorry`, `admit` or `@[extern]` in it. `BuildAid/D1–D5` only add names to the library-suggestion deny list. The root's `⟨h, recTExists, h⟩` and `car : One.M.Row` (`TPS/LocalRepresentationTheoryHypotheses.lean:42`) consume Row0b; they do not feed it.

### 2c. GoodR (`DN:1220-1233`) and where it comes from
`GoodR N i r := ∀ x ∈ X_i, IsHeckeGalois N i x (r x)`. For each x this means:
- r_x : G_E → GL_{nV}(O_i) is continuous and semisimple over Frac O_i;
- at every split w outside l, S and Q, charpoly(r_x(Frob_w)) = heckePol(x, w).

There are no conditions at l; those are separate hypotheses `LocBound` and `G2` (`SR:120-126`: crystalline with the automorphic HT weights for l ≠ g₀, g₁).

The ∃ r with GoodR is the first conjunct of `Conclusion41` (`SR:145-153`), a field of `provisionFirst D` supplied by `I.Conclusion1 (Parts.main_alt_alt D) …` (`TPS/PartsGive.lean:71-72`; `TPS/PreAtMem.lean:59`). Its inputs on the datum:
- `adm1 = admBC`: every automorphic point P of U(N) has a parameter Pa (`IsBCV`, `DN:1270-1277`), a multiplicity-free list of csd cuspidal π_j ⊠ S_{d_j} with exact matching at split places, Satake matching at inert places and infinitesimal character. It comes from `base_change_automorphic_of` (`…/IrreducibilityOfTheoremThree.lean:29-38`) ← `SphericalInertData.Conclusion1` ← `Conclusion1_alt_alt_alt DefiniteN … ascComp` (`TPS/Auxiliary.lean:16-21`). `DefiniteN` (`Foundations/BaseChangeIdentities/Narrow.lean:28-34`) is **Labesse's weak base change for definite U(n)** to an isobaric sum of discrete csd representations. `AscComp` (Mœglin–Waldspurger: discrete = Speh) turns these into Speh blocks. All are proved terms (`baseChangeN`, `definiteN_of`).
- `adm2`: Galois representations for csd regular algebraic cuspidal π over E with WD matching **at all w** (`SR:287-305`). This is a statement about the datum, coming from `RowsAAlt.a2`.
- `OLarge` (an integral model over O_i).
- *(inferred)* r_x = ⊕_j ρ_{π_j} ⊗ (centred ε-string of length d_j), which is exactly the `CentredStringDecomposition` used below.

So **GoodR is "Row0b-type representations for the cuspidal constituents of the endoscopic / Speh A-parameter of x, summed"**. The endoscopic input is Labesse + Mœglin–Waldspurger on *definite* unitary groups, not Arthur / Mok / KMSW in general. I did not trace `adm2` all the way to Row0b.

### 2d. NoChiOff (`GC:68-70`): statement and proof
The Lean says: for all x ∈ Xs with x ∉ Z_i, every u ∈ K^{nV} fixed by r_x ⊗ χ₁⁻¹ is 0. At the use site Xs = `Set.univ` (`IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`), so this is not vacuous.

It is discharged by `GlobalTheory.UnrNoChi.main` (`IE/NoCharacterOffsetUnramified.lean:34-51`). Its hypotheses are `Facts D nch`, l > lStar, l ≠ g_k, `HG` (Zgood ≠ ∅, `DN:1341`), GoodR, π ∈ Z, and `IsRankRPart`.

Proof:
1. An invariant u of r_x⊗χ₁⁻¹ is a χ₁-eigenvector of r_x.
2. `galois_condition_six_of` (`…/GaloisConditionFiveExtraOf.lean:28-32`) = `(D.Z_tie i x).2 ∘ ConclusionG6` puts x ∈ Z.
3. `ConclusionG6` (`SR:268-275`): if HG and GoodR hold and r_x has a χ₁-eigenline, then x ∈ ZN, and every parameter of x is cuspidal-iso.
4. `ZN` (`DN:1292-1294`) = {x : some point P over x has a parameter Pa containing ⟨1, μ·η_T⁻¹, t⟩}, i.e. the A-parameter contains the twisted μ⊠S_t.
5. `D7.Z_tie : ∀ i x, x ∈ nd.Z i ↔ x ∈ ZN` is a **field of the datum structure** (`Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:280`). Each construction has to prove it (e.g. `l_Z_tie`, `…/NZTypeG.lean:436`; not opened).

`ConclusionG6` is proved by `prvG6_of_admissible'` → `ClosingSixth.conclusionG6_of_adm_alt` (`TPS/PrvG6OfAdm.lean:16-19`) → `prvG6_of_realisation_mu_res_count_numerics` (`TPS/MemZAndCuspOfSteps.lean:106-110`). The proof of `mem_ZN_alt` (`:18-58`) goes:
1. Take a point P over x (`pt_surj`) and its parameter Pa (`admBC`).
2. **CentredStringDecomposition**: r_x has the charpoly of ⊕_k R_k ⊗ (ε-string of length d_k), where R_k is the Galois representation of block k.
3. **ResidueCount**: there are multisets A_k with Σ_k d_k·A_k = {r} + {1}^t. This is residual bookkeeping: r̄_x = ρ̄ (irreducible of dimension r, `RbEx`) ⊕ t characters, the same for all x in the localisation (cf. `G3` in `SR:128-140`).
4. **EigenCharTwist**: the χ₁-line lies in some R_k ⊗ ε^{−a}.
5. **PurityStringWeight + Numerics**: a = 0, rank 1, and d_k = t.
6. **HeckeCharEqOfLAdicRealisation + MuCharacterCondition**: the character of that block is μη_T⁻¹, so the block ⟨1, μη⁻¹, t⟩ ∈ Pa and x ∈ ZN.
7. `isCuspIso_of_hasParamX` (`:59-105`): when Pa = Sig ++ [μ-block], ResidueCount forces Sig to be a single cuspidal block of rank r.

All the step lemmas are closed theorems (`centred_string_decomposition`, `purity_string_weight`, `hecke_char_eq_of_l_adic_realisation`, `muChar_holds_alt`, `eigencharacter_of_summand_charZero`, `resCount_of_valRing_ssList_ssRank …`, `stringRankOneLength_and_multisetSumSingleton`). I did not open their bodies.

**So NoChiOff is Galois → parameter bookkeeping in a residually "ρ̄ ⊕ characters" localisation, plus purity / weight numerics. It is not Rallis / Mœglin / Adams-type converse theory.** The parent's inference "every form with the χ₁⊠S_t block is in the theta image" is not what NoChiOff says. That content is `ConclusionZ` (`SR:277-283`): on ZgoodN the theta map is injective with image the sum of eigenspaces, and the multiplicities add up to dM. It is supplied as `h.z` ← `reducedMultiplicity_of_inputs hL D I R` (`TPS/PreAtMem.lean:65`; not opened). **The deep converse-theta input of the core route sits there, and in `Z_tie`, not in NoChiOff.**

## 3. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `geoOne_holds` (`steps_holds`, `KSAll`, `planEx_holds`) | `GR/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean:11`; `GeometricRealizationOfWeightOne.lean:18-25` | odd-rank U on U(a): ρ from cohomology of a Hecke tower, Eichler–Shimura at good w, crystalline at l | geometric construction | **core, unread**; standard in kind (Kottwitz / Harris–Taylor) |
| 2 | `tLiftK` ← `tLift_of_tools_k`, `tools_holds_k` | `GR/ThetaParseval/ThetaKernels/TPGHolds.lean:36-58` | stable-range theta lift U(n) → U(d) is nonzero, with weights and split-place local theta | parity reduction | standard (Rallis tower, Siegel–Weil); unread |
| 3 | `limFinOdd_of`, `congFinOdd_of_ex`, `seedFinOdd_of_geoOne` | `TraceLimits/LimFinOddOf.lean:197`; `CongruenceOddLevel/CongFinOddOfLvLac.lean:15`; `ZetaCharacterDivisibility/MainFin.lean:13` | l-adic limits / congruences of trace data | non-regular / limit step *(inferred)* | core, unread (Chenevier–Harris analogue) |
| 4 | `descOffT` ← `desc_of` | `BaseChangeDescent/BcBackOffT.lean:24-31` | GL_a/E csd → U(a) form, matching at split places | descent | standard (Labesse); unread |
| 5 | `strongTC_holds` | `LiftFactorization/FirstQuadraticSquareHolds.lean:23` | Arthur–Clozel cyclic base change | input to CoreAll | standard; unread |
| 6 | `DefiniteN` ← `baseChangeN`; `ascComp` | `Foundations/BaseChangeIdentities/Narrow.lean:28-71`; `TPS/Auxiliary.lean:16` | Labesse base change of every π on definite U(n); discrete = Speh | gives `admBC`, used by GoodR and NoChiOff | standard (Labesse; Mœglin–Waldspurger); unread |
| 7 | `ConclusionG6` ← `prvG6_of_realisation_mu_res_count_numerics` | `TPS/MemZAndCuspOfSteps.lean:18-110` | χ₁ ⊂ r_x ⇒ A-parameter ∋ μη⁻¹⊠S_t | NoChiOff | core; read, step lemmas unread |
| 8 | `ConclusionZ` ← `reducedMultiplicity_of_inputs` | `SR:277`; `TPS/PreAtMem.lean:65` | theta image on ZgoodN = sum of eigenspaces, multiplicities add | the real converse-theta content | **core, unread** |
| 9 | `D7.Z_tie` (`l_Z_tie`) | `…/RhoDetPrimeEqMuTildeMulChiPow.lean:280`; `…/NZTypeG.lean:436` | Z_i = ZN as sets | identifies the theta-defined Z with the parameter-defined ZN | **core, definition to unfold** |
| 10 | `Conclusion41` / `adm2` / `OLarge` | `SR:145`, `SR:287`, `SR:110` | ∃ GoodR family; Galois representations for csd cuspidal π over the host field with WD matching at all w | GoodR supplier | core; supplier not traced to Row0b |
| 11 | `UnrNoChi.main` | `IE/NoCharacterOffsetUnramified.lean:34` | GoodR + G6 ⇒ NoChiOff ∧ UnrOut (Xs = univ) | discharge | glue (read) |

## 4. Oddities

1. **"Strong" is a misnomer.**
   - Row0b requires equality of WD representations only when the parameter is abelian with N = 0, plus tame inertia charpolys. Above l it requires crystallinity at spherical places and restricted pst cases. It contains no purity clause.
   - That is weaker than Caraiani. But SR `adm2` (`SR:287-305`) asks for **WD equality at every w, including w | l, plus temperedness**. If adm2 is ultimately fed from Row0b, a strengthening must happen somewhere. I did not find where.
2. **The `away` clause quantifies over every rc with `IsRecT`.** It is vacuous if no such rc exists. `RecTExists` is proved separately (`recTExists_of_published_inputs`, `TPS/LocalLanglandsGLAndPurityAtMember.lean:21`), so this is fine, but it should be noted.
3. **Junk defaults.**
   - `hop` = 0 when no correspondence operator exists (`IdTower.lean:28-29`).
   - `wdOf` = the trivial representation when no WD representation exists (`…ParamMonodromyEqZeroIff.lean:352-353`).
   - Neither looked exploited in what I read, but `GeoOne`'s proof should be checked to see that it never lands on these defaults.
4. **GeoOne covers only odd a and special fields** (`FieldOK`, √−d ∈ E, `NonSplitSet T`). Everything else goes through the theta lift and the limit steps. This is unlike the published route, which uses quadratic base change and eigenvarieties for parity.
5. **The deep automorphic content of the core route moved out of NoChiOff.**
   - NoChiOff is an argument by residual counting and purity. It needs (a) `admBC` for every point (Labesse + Mœglin–Waldspurger; multiplicity-freeness `Nodup` is built into `IsBCV`), and (b) the residual shape ρ̄ ⊕ t characters with ρ̄ irreducible (`RbEx`, `ResidualIrreducibility`).
   - The converse-theta statement is hidden in `ConclusionZ` and in the datum field `Z_tie`. Both need opening.
6. `ConclusionG6` also needs Numerics with r ≥ 2 and t ≥ 2 from `D.R` (`MemZAndCuspOfSteps.lean:43-49`). These hold for the chain's ranks.
7. I saw no `True`/`trivial` slots in the files I read.

## 5. Judgement (task d)

- **Row0b.** Proved in the tree by a closed chain of recognisable shape (descent, geometric construction, theta parity lift, limits, Arthur–Clozel). It is not circular and has no axioms or sorries in its closure (by text search). The statement is weaker than the literature's "strong" local–global compatibility. The bodies of the geometric and limit steps are unread, so "recognisable mathematics" is established at the level of statements only.
- **GoodR.** Discharged as a datum fact (`Conclusion41`). In kind it is an instance of Galois representations for the cuspidal constituents of Labesse base change on definite U(N), summed with Speh strings. It is not vacuous: it is required for all x ∈ X_i. It is not traced to Row0b in full.
- **NoChiOff.** Proved from GoodR plus `ConclusionG6`, a Galois-side bookkeeping argument whose step lemmas are closed theorems. It is not vacuous (Xs = univ) and not circular. It is not the deep input; the deep input is `ConclusionZ` + `Z_tie`.
- **Ranked children to open next:** (1) `ConclusionZ` ← `reducedMultiplicity_of_inputs` and `l_Z_tie`; (2) `planEx_holds` / `steps_holds` (what variety, which congruence relation); (3) `limFinOdd_of`; (4) the `adm2` supplier (WD equality at all w, including w | l).

## 6. Coverage

Read:
- context: PROTOCOL (Explainer); SUMMARY §11; NODE-LINKN; NODE-ROOT; NODE-VWIN (grep plus §1, 5); NODE-RT3 (grep plus 186-205);
- `GR/TypeConditions/WeightsConjBis.lean` (all); `WeightsConjAlt.lean:1-60`; `LocalLanglands/IsRecTOfIsRec.lean:1-110`;
- `IntegralStructures/Development.lean` (all); `RowSrc` (grep line);
- `HalfIndexLattices/TLiftK.lean`; `ThetaKernels/TLiftK.lean`; `TPGHolds.lean:1-60`; `SchurStep.lean:95-130`; `AllCoreOf.lean:1-40`; `CrystallineDescent/ToCoreK.lean`;
- `GeometricFlagBases/HodgeTrAt.lean` (all); `WeightOneGeometricRealization.lean`; `GeometricRealizationOfWeightOne.lean`; `GeoOneOfParts.lean`; `PackExOf.lean` (all);
- `Divisors/IdTower.lean`; `IsCorrOpOfAvg.lean:1-12`; `PullHlComp.lean` (grep 216-239); `…ParamMonodromyEqZeroIff.lean:330-380`; `MonodromyZero…:495-505`; `DualIsConjByOne.lean:45-55`;
- `CyclicStrongAtCusp.lean:1-100, 195-215`; `GaloisLocalGlobalOfLocalGlobalCompatibility.lean:170-200`; `ArthurClozelStrongTC.lean:10-20`; `FirstQuadraticSquareHolds.lean`; `InputsOf.lean`; `BcBackOffT.lean`; `MatchOfMatchOffTEmpty.lean:1-60`;
- `DN:1195-1345`; `GC:55-90`; `SR` (definition list, 100-175, 240-360); `NoCharacterOffsetUnramified.lean` (all); `GaloisConditionFiveExtraOf.lean:1-60`; `ResidualIrreducibilityFormsEquivalent.lean` (all);
- `TPS/PrvG6OfAdmStatement.lean`; `TPS/PrvG6OfAdm.lean`; `TPS/MemZAndCuspOfSteps.lean` (all); `TPS/CFacts.lean:30-60`; `TPS/GaloisPreconditions.lean`; `TPS/PreAtMem.lean` (all); `TPS/PartsGive.lean:32-80`; `TPS/PublishedInputsThirdLayer.lean`; `TPS/LocalLanglandsGLAndPurityAtMember.lean`; `TPS/Auxiliary.lean`; `TPS/EveryCharacterOfLiteratureOfVWin.lean:255-275`; `TPS/ThetaLiftHypothesesOfNonvanishing.lean:15-40`;
- `BaseChangeIdentities/Narrow.lean:1-75`; `IrreducibilityOfTheoremThree.lean:10-60`; `SphericalInertData.lean:15-55`; `RhoDetPrimeEqMuTildeMulChiPow.lean:270-285`; `BuildAid/D1–D5`;
- import-closure script over `RowSrc` (text search for axiom / sorry / self-reference).

Not opened:
- the bodies of `steps_holds`, `KSAll`, `planEx_holds`, `lefschetz_fixedPoint_finite_etale_correspondence`, `limFinOdd_of`, `desc_of`, `strongOf`, `tLift_of_tools_k`, `baseChangeN`, `ascComp`;
- the step lemmas of `ConclusionG6`;
- `reducedMultiplicity_of_inputs`, `l_Z_tie`, `Parts.main_alt_alt`, `RowsAAlt.a2`'s supplier;
- `Datum`, `HTGroup`, `Link`, `KS`.
