# NODE-MODU3: the residually reducible modularity theorem for U(3), read as a specialist

Paths are relative to `.../scratchpad/art/lean/src/Development/AutomorphicArithmetic/AutomorphicVarieties/`.
Abbreviations:
- `DTC/` = `ModularityArgument/ThresholdArguments/DenseThresholdCases/`
- `CDS/` = `CurveDVRSpecialization/`
- `FSV/` = `FrobeniusSmoothVectors/`
- `PM/` = `PatchingModules/`
- `WGC/` = `WeilGroupCharacters/`

"The Lean says" means I read it. *(inferred)* means it is my reading. Nothing was compiled.

## 0. Answers in brief

### Correction to the parent (NODE-RT3)
There **is** Taylor–Wiles patching. It is not done at the residual point. It is done **at nice primes**, as in
Skinner–Wiles. `P1core`/`P3core` (the "a nice pro-modular point makes every component through it pro-modular" step) are
proved by `Pa.pFromAut` (`PM/AutomorphicDetection/PfromAut.lean:9`). That proof uses:
- Taylor–Wiles data `TWGrp`/`TWPl`;
- the Hecke-side input `HasAut` (Hecke algebras at Taylor–Wiles level);
- a patching core `Raw` (`PM/PatchedSupportCompletions.lean:207`);
- the bounds `FirstOrderDualArithmeticBound` and `TaylorWilesObstructionBound`.

### (a) What the pieces are
- **R** = `UniversalOrdinaryDeterminantRing` (`WGC/UniversalOrdinaryDeterminantRing.lean:154`). It is a Chenevier-determinant
  deformation ring of D̄ = det(⊕χ̄ᵢ) over G_L.
- **Ordinarity.** It is imposed by the trace identity tr(h·∏ᵢ(gᵢ − ψᵢ(gᵢ))) = 0 for all h ∈ G_L and all gᵢ in the
  decomposition group at v | l (`Pair.Ord`, `:145`). The characters ψ_{v,i} are part of the data.
- **𝕋** is the ordinary Hecke algebra of `ratU L n`, with level Iwahori-type at v0 and coefficients τ₀. It is localised at
  the maximal ideal `a` given by the residual Hecke polynomial. *(inferred)* `ratU L n` is meant to be a definite unitary
  group; I did not check definiteness.
- **J** = ker(R ↠ 𝕋).
- **If the localised module is 0**, then J = ⊤ by definition (`HeckeAlgebras/IsTheta.lean:46`;
  `DTC/ExistsHeckeIdeal.lean:52`).

### (a) Seeds: 𝕋_𝔪 ≠ 0 is proved, not assumed
- **n = 2.** The seed is a cusp form over ℚ congruent to the Eisenstein series E_k(1, φθ), where θ has order l and prime
  conductor w with w ≡ 1 mod l and φ(w) = 1. Then L(1−k, φθ) ≡ L(1−k, φ)(1 − φ(w)w^{k−1}) ≡ 0 mod λ
  (`DTC/BirthEG.lean:231`, `DTC/FinOrderOfKills.lean:297`).
- **n = 3.** The seed is the adjoint (Gelbart–Jacquet) lift of that cusp form, base-changed to L (`DTC/SymUse.lean:27`,
  `DTC/UnitaryThreeInputsOfLiterature.lean:29`).
- **Unconditional.** No L-value hypothesis on Ψ itself is needed. The Selmer case distinction never arises, because J ≠ ⊤
  is forced by the seed (`ModIn.seed`).

### (b) Dimension count
- **dim Λ = 1 + n·d**, where d = [L⁺:ℚ] = Σ_v d_v. Λ is the local weight space of inertial characters at l, so no Leopoldt
  defect enters.
- **Lower bound for R.** The Euler-characteristic inequality `EC` gives local presentations with
  (#variables + 1 − #relations) ≥ 2d + 2 for n = 2. That is dim Λ plus the 1-dimensional torus. Components therefore meet in
  codimension 1 (Hartshorne connectedness, `FSV/ChainedBot.lean:51`).
- **Upper bound for the reducible locus.** The `Frame.Ok` hypotheses bound the rank of several H¹ groups by C₀, and
  `Big` requires d > 3C₀ + 7.
- **How C₀ is bounded.** L is taken in the cyclotomic ℤ_l-tower over an abelian field. C₀ is bounded uniformly up the tower
  by **Ferrero–Washington** (μ = 0), which is *proved in the tree* (`GaloisLibrary/FerreroWashingtonIndex/`, 62 files,
  unread). This is exactly how "L abelian" is used.

### (c) Strata of the reducible locus
- **TI** (irreducible type) primes are the target.
- **TE** (endoscopic W⊕1, with block {Ψ, Ψ⁻¹} ⊕ {1}) primes are handled by the n = 2 run plus chains of "thick" links
  (`P23'` ← `P3core`).
- **Triangular (reducible) primes** are never required to be modular.
- **Every TI component reaches the reducible fibre.** It contains a closed point of BB, a non-split residual extension
  (`FSV/MonMemPow.lean:81`).
- **Polarisation excludes the other 2+1 patterns** *(inferred)*.

### (d) Hypotheses on l
- l is odd.
- l − 1 ∤ 2e. This gives Ψ̄² ≠ 1 at every v | l (`f3`).
- Ψ̄ ≠ ω^{±1} and ωΨ̄^{±2}δ ≠ 1 (`f2b`, `f2c`).
- ω ∉ ⟨Ψ̄⟩ on G_L (`f5`).
- l ∤ h_K·disc K.
- **Missing:** there is no l > 3 and no l ∤ n. Taylor–Wiles at nice points for GL₃ in characteristic l = 3 is where I would
  look.

### (e) Can I reconstruct it?
Yes, as a Skinner–Wiles architecture extended to n = 3. The step I would bet against is `P3core`/`Raw`, applied to chains
of **endoscopic** nice points. These are points whose characteristic-l curve representation is W ⊕ 1, so the patching there
is residually reducible (Thorne-type). The chains are linked through non-semisimple "thick" primes. Nothing in the
literature covers this over k((T))-points.

## 1. Statement

### 1.1 `exists_hecke_ideal` (`DTC/ExistsHeckeIdeal.lean:70-84`)
```lean
theorem UpperTheory.V.Hi.exists_hecke_ideal : Af.HypothesesH' → ∀ l L Ω [IsCMField L] (s : HidaSetting l L Ω) n, 1 ≤ n →
  ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) ι (B : UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), ∃ J : Ideal B.B, R.IsJ B K J
```

**Residual data `Resid`** (`WGC/UniversalOrdinaryDeterminantRing.lean:109-117`):
- distinct characters χ̄ᵢ of G_L, with D̄ = det diag(χ̄ᵢ) polarised;
- local residual characters ψ̄_{v,i};
- fixed values on l-power torsion of the local abelianisations.

**R = B** (`:138-161`). It is universal for pairs (D, ψ):
- D is an n-dimensional determinant of G_L reducing to D̄;
- the ψ_{v,i} lift ψ̄_{v,i};
- polarisation `P` holds;
- **ordinarity `Ord`** holds: tr(h·∏ᵢ(gᵢ − ψ_{v,i}(gᵢ))) = 0;
- **minimality `I`** holds: tr(h(g − 1)) = 0 for g in tame inertia where r̄ is trivial.

**Λ** (`:168-176`). It is universal for inertial characters κ_{v,i} lifting ψ̄|_I. Its dimension is 1 + n·Σ_v [L_v:ℚ_l].

**𝕋** (`HeckeAlgebras/CoefficientRepTrivialOnUnramified.lean:75-176`; `IsTheta.lean:110-178`).
- `HSet`: Γ = `ratU L n` → G(𝔸^{l,∞}) × ∏_{v|l} GL_n(L_v).
- `MK` = the localisation (at eigenvalues `a`) of the ordinary part `X.Ord` of l-adic forms of weight θ : T(ℤ_l) → Λˣ.
- Hecke operators: spherical T_w at split w ∉ S, and U_{v,j} at v | l.
- `IsRes` says the eigenvalues `a` reduce to the residual Hecke polynomial and to the U_p-eigenvalues of ψ̄.

**`IsJ`** (`IsTheta.lean:46-51`) is one of:
- MK = ⊥ and J = ⊤; or
- there is a surjective f : B ↠ 𝕋_K with D_univ ↦ the Hecke determinant (`IsUniv`), Λ-linear, and J = ker f.

**Proof** (`:28-69`, read). If MK = ⊥, take J = ⊤. Otherwise:
1. `coreDet_alt` gives a 𝕋-valued determinant with ordinary characters.
2. `core_hecke_of_automorphic_hecke_dense_weight` gives, at a dense set of `Good` points (arithmetic weight with distinct
   characters), a Galois representation with a **flag at each v | l** (`hO.pt … e3`).
3. Hence the 𝕋-determinant satisfies `Ord` (`heckeDeterminant_satisfies_deformation_relations_alt`), by Zariski density.
4. The universal property gives f.
5. f is surjective (`deformationRing_to_heckeAlgebra_surjective`), because 𝕋 is generated by Frobenius traces.

**Where ordinary local–global compatibility comes from.**
- `AutomorphicHeckeSet` (`DTC/UnitaryPointProperties.lean:48`) requires the field `atL : AtLT ι … (σl v)`
  (`ModularityArgument/OrdinaryJacquetModules/AtLOf.lean:17`).
- `AtLT` says: if σ_v ≅ PS(ω) with the ωᵢ distinct on units, then ρ|_{G_v} has D_pst/WD charpoly equal to rec(σ_v) and the
  prescribed HT weights.
- `AtLOf` derives `AtLT` from RowT's potentially-semistable clause.
- The flag itself (ordinary ⇒ upper triangular) is then obtained in `OrdinaryJacquetModules/` (`flagJ`, `FlagOfRel.lean:108`;
  `coreOrd`; `extChar`). *(inferred)* This is the usual weak-admissibility argument: U_p-ordinary implies Newton = Hodge,
  which splits the filtration (Geraghty-style).
- **So the parent's worry is answered.** Ordinary local–global compatibility is derived, from pst local–global
  compatibility, which is published (BLGGT/Caraiani), plus a local p-adic Hodge argument that is proved in the tree. I did not
  read `FlagOfRel`.

**Control theorem.** `HidaUAlt` (`DTC/HidaU.lean:12`) packages J with `HidaPropsAlt` (`DTC/PointTheoremBaseObject.lean:32`):
- `RingProps`: B/J is finite and torsion-free over Λ;
- `Dense`;
- `PointTheoremBaseObject`;
- purity and classicality at arithmetic points;
- `TwistOk`;
- plus `Pa.HasAut` (Hecke algebras with Taylor–Wiles level).

These are proved in `DTC/THidaU.lean:38-48` from:
- `ring_props_of_is_j_unitary_hecke_data`, `dense_of_…`, `hecke_ideal_point_properties`, `level_of_is_j…`;
- the Hecke-data existence `nonempty_unitaryHeckeData` (`DTC/HdEx.lean:20`). This supplies `IsWt.free`, i.e. the ordinary
  module is free over Λ. *(inferred)* That is Hida's control theorem for definite U(n) (Geraghty §2).

None of these bodies were opened.

**`PointTheoremBaseObject`** (`:26-31`). It takes the ordinary flag as a **hypothesis** on ρ, together with the regularity
condition ψᵢ ≠ ψⱼ·ε.

### 1.2 Seeds
- **`ModIn.seed`** = `IdealSpecializationPoint J` (`CDS/SecondThirdPrimeConditionTransferAlt.lean:59`): there is an absolutely
  irreducible point φ with J ≤ ker φ.
- **Its source** in `modularity_linked_ends` (`DTC/PrLinkedEnd.lean:30,37`) is `hs J hJ.pt`. That is, a seed automorphic
  point plus `PointTheoremBaseObject` gives the specialisation point. The seed is built in `linked_endomorphism_dense`
  (`DTC/LinkedEndE.lean:56-66`) from:
  - `UnitaryThreeAutomorphyDense` (`DTC/SymUse.lean:27`): for infinitely many m ≡ j mod (l−1), an irreducible-on-open-subgroups
    r : G_L → GL₃ that `IsSeedAlt` (`DTC/IsSeed.lean:25`), meaning it is continuous, irreducible, polarised, has residual
    characters (Ψ, 1, Ψ⁻¹) restricted to G_L, has the right type away from l, is ordinary at l with weights (m, 0, −m), and
    is automorphic after a twist;
  - `Seed2Alt` (`DTC/SdStmt.lean:14`), the same for n = 2.
- **Proof of `Seed2Alt`** (`DTC/FinOrderOfKills.lean:297-420`, read in part). It uses `PropEGP`
  (`AutomorphyLifting/PrimeIndexConstruction/MixSeedPAlt.lean:30`; proved at `DTC/BirthEG.lean:231`):
  - for φ ≠ 1 split at an auxiliary prime w and θ of order l and conductor w, with k large of the right parity, there is
    `EisRep ι φ θ k ρ`, a cusp form whose Galois representation is residually 1 ⊕ φ;
  - the proof uses φ₀(w) = 1 and l | w − 1 (`hφw`, `hdvd`);
  - ρ is twisted by Ξ⁻¹, with Ξ = cyc^m χ′;
  - irreducibility on G_L uses `D.sq`;
  - θ dies on G_L (`θL`), so the seed is unramified at w over L.
- **n = 3.** `unitary_three_automorphy_dense_of_prints_and_row` applies `adjoint_lift_from_eisenstein_of_propagation` (an
  adjoint/Gelbart–Jacquet lift) to this ρ. *(inferred)* The residual representation of Ad⁰ is Ψη, 1, Ψ⁻¹η. On G_L, where
  η = 1, this is Ψ, 1, Ψ⁻¹.
- *(inferred)* This is the Ribet / Billerey–Menares auxiliary-level Eisenstein trick. It is unconditional, so 𝕋_𝔪 ≠ 0
  always. If Ш⁺ ≠ 0 nothing changes in the argument; the case distinction in the brief does not arise.

### 1.3 Propagation (`CDS/PropagationTheoremGL2.lean:51-60`, `CDS/AbsMain.lean:12-30`)
```lean
def PropagationTheoremGL2 := ∀ l O F C₀, F.Ok C₀ → F.Big C₀ → ∀ (S : Space O F 2) (M : Ideal S.B),
  S.FinLam M → P1' S M → SeedIn S M → AllGood S M
def PropagationTheoremGL3 := … S₂.FinLam M₂ → AllGood S₂ M₂ → ∀ (S : Space O F 3) M,
  S.FinLam M → P1' S M → P23' S M → SeedIn S M → AllGood S M ∧ OffFin S
```

**`Space`** (`FSV/LeAdicClosure.lean:157-170`). S.R is the universal ring of `NRep`s (`:27-32`). An `NRep` is a matrix lift
r : G_L → M_n(R) of diag(Ψ̄^{w(i)}), with w = (1, 0, −1) for n = 3, satisfying:
- the polarisation r(g*) = J r(g)ᵀ J;
- a normalisation at g0 (where Ψ̄(g0)² ≠ 1);
- the matrix ordinary identity ∏ᵢ(r(gᵢ) − ψᵢ(gᵢ)) = 0.

It comes with:
- S.B = the closure of the torus-invariant monomials together with the ψ's. *(inferred)* This is the determinant/GIT
  quotient, and Φ : B_univ ↠ S.B.
- S.A = S.B[entries].

**Strata of primes** (`:94-108`):
- **OffTri**: neither the strictly lower nor the strictly upper entries all vanish.
- **TI** = OffTri, and for n = 3 the "odd" entries (those linking the middle character to Ψ^{±1}) do not all vanish.
- **TE** = OffTri with those odd entries all zero. This is the endoscopic shape W ⊕ 1.
- **Coin**: two of the local characters coincide on N_v.
- **Thick**: TE together with a non-split ordinary modification that links the blocks (`:264`).

**Nice prime** (`PropagationTheoremGL2.lean:16-21`): a prime of dimension 1 and characteristic l, OffTri, with no
coincidences.

**`P1'`**: if a nice TI prime p is good (M ≤ π p), then every prime below p is good.

**`P23'`**: goodness propagates along chains of nice TE primes joined by thick primes.

**`AllGood`**: every TI prime of S.A is good. `GoodPtOf` turns this into `GoodPt`: every absolutely irreducible lift over a
domain factors through B/J.

## 2. Argument (as mathematics)

1. **Auxiliary field** (`GdFrameEx` ← `FSV/GdEx.lean:8`, `FSV/FrameEx.lean:126-160`).
   - L is a CM abelian field. It is obtained from an abelian V-field by adjoining the m-th layer of the cyclotomic
     ℤ_l-extension. It contains K and the θ-field, and it contains no ζ_l.
   - The l-rank of the class group of L(Ψ̄, μ_l) is ≤ C₀ uniformly in m (`b0`, `FSV/RankLeOfCardLe.lean:137`, via `FW.main`,
     i.e. Ferrero–Washington).
   - Take m = 3C₀ + 7, so d ≥ l^m > 3C₀ + 7 (`Big`).
   - `Frame.Ok` (`FSV/ContinuousCoboundaries2.lean:176-210`) is then proved from published Galois cohomology
     (`GC.Hypotheses₂`: Tate local and global duality, Euler characteristics, Poitou–Tate, Greenberg–Wiles,
     `UnramifiedOrthogonality`). It includes:
     - `ec`, the Greenberg–Wiles Euler-characteristic inequality;
     - `b1`, `b1p`, `h1`: H¹ ranks ≤ C₀;
     - `f4`, `f4'`: H¹ ≠ 0 for Ψ̄⁻¹δ and Ψ̄⁻²δ;
     - `cl`: a class-group exponent;
     - `gen`: generators of inertia.
2. **Hida ideal.** `ModUAlt` gives J for n = 2 and for n = 3, with:
   - B/J finite and torsion-free over Λ, so every minimal prime has dimension 1 + nd (`DimT`, via `dimOf`);
   - `P1core` and `P3core` (from `pFromAut`; see step 6).
3. **Reach the reducible fibre** (`l41`, `FSV/MonMemPow.lean:81`). Every torus-homogeneous minimal prime η of S.A with
   η ⊉ triP lies in a maximal ideal x ∈ BB. BB is the set of points over m_B, i.e. with residual determinant, that are not
   upper triangular. *(inferred)* x is a non-split residual extension.
4. **Local structure at x** (`sharp2`, `FSV/ChainedBot.lean:51-80`).
   - `pres` writes the completed local ring L.R as O′[[N]]/(N′ elements), with N + 1 − N′ ≥ 2d + 2. This uses `EC`.
   - Hartshorne connectedness (`c1ch`) then shows that any two minimal primes are chained through pairwise intersections of
     dimension ≥ 2d + 1.
   - All minimal primes are TI (n = 2).
   - `exists_nice_prime_above_of_large_dim` (`CDS/ExistsNicePrimeAboveOfLargeDim.lean:7`): a prime of dimension ≥ nd + 1 that
     contains a Λ-finite ideal lies under a nice prime.
5. **Global propagation** (`components_good_rank_two`, `CDS/ComponentsGoodRankTwo.lean:129-163`, read).
   - `GlobData`: TI is open, Good is closed, and the Core is BB, which is preconnected (`preconnected_rank_two`).
   - Local charts `ld` carry the threshold D1 = 2d + 1.
   - The seed component (`SeedIn` → `seedpt`) is good.
   - At each x, two good-or-not components meeting in dimension ≥ 2d + 1 have a nice prime above their intersection. Good
     passes up to that nice prime (closedness) and down to every component below it (`P1'`).
   - Preconnectedness of the core carries goodness to every x, and so to every TI component.
   - For n = 3 (`PropagationTheoremGL3.lean:213`, statement only), the endoscopic components are added through `P23'`
     (chains of TE nice primes with thick links) and the n = 2 result (`AllGood S₂ M₂`).
   - The same theorem yields `OffFin`, hence `FinPt`, hence `FinEnd`.
6. **Nice primes are pro-modular** (`PM/ChebotarevFamilies/PFromAutOf.lean:30-133`, read).
   - Given a chain of points xᵢ that are NiceI or NiceE, `Choice` picks Taylor–Wiles primes (Chebotarev, using N3) adapted
     to all xᵢ at once.
   - `ArPl` realises them.
   - `HasAut` supplies Hecke algebras at Taylor–Wiles level.
   - `FirstOrderDualArithmeticBound` bounds the dual Selmer group by n·d + n·q. *(inferred)* This is the numerical
     coincidence for U(n): dim = n[L⁺:ℚ].
   - `TaylorWilesObstructionBound` bounds the obstructions.
   - `Raw` then patches and concludes `ChainConcl`: if x₀ is linked to a stable modular prime, every stable or thick prime
     under x_h contains J.
   - NiceI (`WGC/UniversalOrdinaryDeterminantRing.lean:255`) = N1 (distinct ordinary characters, ψᵢ ≠ ψⱼε) + TypeI
     (irreducible on G′) + N3 (separable Frobenius on open sets) + N4 (H⁰(ad ⊗ ε) = 0 on D0). NiceE is the same with
     TypeE = W ⊕ W′ with both blocks irreducible and no G′-homomorphisms between them.
   - N4 holds for **all** points (`ModIn.n4`, `n4Of`). *(inferred)* This comes from a choice of the auxiliary prime v0. That
     is why there are two runs, glued by `twoRuns_alt`.
7. **Glue and descend**: `twoRuns_alt` (read by the parent), `finPtDown`, `GdEndOf`.

**Comparison** *(inferred)*:
- Steps 1–6 for n = 2 are Skinner–Wiles (1999): base change into a Ferrero–Washington tower, connectedness of complete
  intersections, nice primes, Taylor–Wiles at nice primes, and an auxiliary-level Eisenstein seed.
- For n = 3 the novelties are:
  - the endoscopic stratum and thick links (`P23'`/`P3core`), with patching at residually-reducible nice points;
  - `preconnected_rank_three` for the 3-character unipotent fibre;
  - FlagPt, the ordinary condition on a determinant giving a genuine flag for n = 3.

## 3. Children (ranked by where I would look)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `Raw` / `P3core` via `chain_of` | `PM/PatchedSupportCompletions.lean:207`; `PM/ChebotarevFamilies/PFromAutOf.lean:30` | Taylor–Wiles patching along chains of nice points, including **TypeE** (W ⊕ 1) points linked by thick primes, over k((T))-curves | **core**, beyond the literature (cf. Thorne 2015 and ANT, which need Ext/Selmer-dimension conditions; I found none in NiceE) |
| 2 | `components_good_rank_three` | `CDS/PropagationTheoremGL3.lean:213` | 3-dimensional propagation through the TE and thick strata, and OffFin | **core**, not opened |
| 3 | `preconnected_rank_three` | `FSV/ExistsNonzeroLowCocycle.lean:144` | the core BB is preconnected for three characters | core, not opened |
| 4 | `Choice`, `TaylorWilesObstructionBound`, `b1Ar` | `PM/AutomorphicDetection/*` | Taylor–Wiles primes and Selmer bounds at nice points | core; **small-l risk** (l = 3 = n) |
| 5 | `FW.main` / `FW.ferreroWashington` | `GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104`; `Imports.lean:3` | bounded l-rank of class groups up the cyclotomic ℤ_l-tower over abelian fields | standard (Ferrero–Washington 1979), **proved in tree**, 62 files unread |
| 6 | `flagJ` | `ModularityArgument/OrdinaryJacquetModules/FlagOfRel.lean:108` | an ordinary determinant at an irreducible arithmetic point gives a flag with characters in the given order | core-ish, not opened |
| 7 | `nonempty_unitaryHeckeData`, `ring_props_…`, `hecke_ideal_point_properties` | `DTC/HdEx.lean:20`; `DTC/HeckePolyCoeffZero.lean:18` | Hida's control theorem and freeness for U(n) over L | standard (Hida, Geraghty), proved in tree, not opened |
| 8 | `PropEGP`, adjoint lift | `DTC/BirthEG.lean:231`; `DTC/UnitaryThreeInputsOfLiterature.lean:29` | Eisenstein-congruent cusp forms at auxiliary level; their Gelbart–Jacquet lift | standard (Ribet/Billerey–Menares; Gelbart–Jacquet) |
| 9 | `sharp2`/`pres`, `l41`, `exists_nice_prime_above_of_large_dim` | `FSV/ChainedBot.lean:51`; `FSV/MonMemPow.lean:81`; `CDS/ExistsNicePrimeAboveOfLargeDim.lean:7` | complete-intersection presentation, connectedness, nice primes | standard (Skinner–Wiles §3–4), statements read |
| 10 | `frame_ex` / `ok_link` | `FSV/FrameEx.lean:52,126` | the existence of L with `Ok ∧ Big` | glue plus published cohomology |

## 4. Oddities

1. **J = ⊤ is allowed.** `IsJ` permits J = ⊤ when MK = ⊥, and then `DimT` and `RingProps` hold vacuously. Non-vacuity rests
   entirely on `ModIn.seed`, which is genuinely produced (§1.2). Without the seed, `AbsMain`'s hypotheses could be met
   trivially, but `seed` blocks that.
2. **The parent's "no patching" is wrong.** Patching is at nice primes (`PM/`). The directory is literally named
   `PatchingModules`, and it contains `TaylorWilesObstructionBound`.
3. **No condition l > 3 or l ∤ n.** `Frame.Ok.l_odd` and `Ax.odd` are the only constraints on l. For n = 3 and l = 3,
   Taylor–Wiles at nice points (adequacy, the choice of Taylor–Wiles primes, H¹ of the image with coefficients in ad) is
   where a standard condition would normally sit. I did not open `Choice` to see how it copes.
4. **`f5` (ω ∉ ⟨Ψ̄⟩ on G_L) needs a case analysis.** It can fail if Ψ̄|_{G_L} = ω^e with gcd(e, l−1) = 1. For ψ = 1,
   `PsiEven` forces e to be even, which saves it. For ψ ≠ 1 it needs L not to trivialise ψ̄. It is proved (`h_f5` in
   `ok_link`), but not read.
5. **The ordinary condition on determinants is the Skinner–Wiles/Thorne trace form.** For n = 3 its equivalence with a
   genuine flag at irreducible points is a lemma (`FlagPt`/`FlagJ`). Read literally, for a reducible degenerate ρ (for
   example ρ|_{G_v} scalar) the trace condition need not give a flag. It is only claimed at irreducible arithmetic points,
   where the HT weights are distinct.
6. **Euler characteristic as a hypothesis.** `EC` is an inequality stated for every finite representation of an abstract
   profinite Γ inside `Frame.Ok`. For the actual Γ it is discharged from published Greenberg–Wiles results (`GC.ec`).
   Nothing about it is vacuous.
7. **Definiteness of `ratU L n` was not checked.** Algebraic modular forms with a finite-level `FinLevel` need G(ℝ) compact.

## 5. Coverage

### Read
- PROTOCOL; SUMMARY §10–11; NODE-RT3 (all); NODE-ONECHARU §0–1; NODE-LINKN and NODE-CONGMOD (grep only).
- `DTC/ExistsHeckeIdeal.lean` (all).
- `WGC/UniversalOrdinaryDeterminantRing.lean:1-310`.
- `HeckeAlgebras/CoefficientRepTrivialOnUnramified.lean:1-200`; `HeckeAlgebras/IsTheta.lean:30-240`.
- `CDS/AbsMain.lean`; `DTC/PrLinkedEnd.lean`; `CDS/SecondThirdPrimeConditionTransferAlt.lean` (all);
  `CDS/PropagationTheoremGL2.lean` (all); `CDS/ComponentsGoodRankTwo.lean` (all).
- `FSV/ContinuousCoboundaries2.lean:100-215`; `FSV/LeAdicClosure.lean:1-280`; `CDS/HostFrameEx.lean:1-83`; `FSV/GdEx.lean`;
  `FSV/FrameEx.lean:35-160`; `FSV/RankLeOfCardLe.lean` (all).
- `GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:1-30,95-119`.
- `GaloisCochains/GLinkQuot.lean:1-40`; `LevelCohomology/HcDefs.lean:1-80`.
- `DTC/THidaU.lean`; `DTC/PointTheoremBaseObject.lean`; `DTC/HidaU.lean`; `DTC/CoefIsCoef.lean`.
- `DTC/UnitaryPointProperties.lean:40-55`; `DTC/AuTeichEx.lean`; `OrdinaryJacquetModules/AtLOf.lean`;
  `CoreOrdAlt.lean:20-165`; `FlagJ.lean:10-25`.
- `DTC/LinkedEndE.lean`; `IdeleGenerators/SlopeTestRemainingChoices.lean:130-175`; `DTC/SymUse.lean`; `DTC/SdStmt.lean`;
  `DTC/IsSeed.lean`; `DTC/FinOrderOfKills.lean:280-420`; `MixSeedPAlt.lean:1-60`; `DTC/BirthEG.lean:225-280`;
  `DTC/UnitaryThreeInputsOfLiterature.lean` (grep).
- `PM/TaylorWilesObstructionBound.lean:20-175`; `PM/AutomorphicDetection/PfromAut.lean`;
  `PM/ChebotarevFamilies/PFromAutOf.lean` (all); `PM/PatchedSupportCompletions.lean:181-221`.
- `FSV/ChainedBot.lean:1-80`; `FSV/MonMemPow.lean:81-95`; `CDS/ExistsNicePrimeAboveOfLargeDim.lean:1-30`.

### Not opened (bodies)
- `Raw`, `Core`, `Choice`, `ArPl`, `b1Ar`, `b2Ar`;
- `components_good_rank_three`, `preconnected_rank_two/three`, `globProp`, `locProp`, `pres`, `l41` body;
- `nonempty_unitaryHeckeData`, `ring_props…`, `hecke_ideal_point_properties`, `coreDet_alt`, `core_hecke_…`;
- `flagJ`, `FW.cyc` internals, `h_f5`, `GC.ec`/`b1`/`h1`;
- `EisRep`, the adjoint lift;
- `seedpt`, `seedOf`, `finPtOf`, `dimOf`, `degEq`.
