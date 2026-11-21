# NODE-KILLAT: `KillAt` (twisting kills the ρ-block Selmer group) and the local-at-l exponents

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- `LLC/` = `Formalism/SharpRestriction/LevelLetterCocycles/`
- `CEC` = `LLC/JointConditionsZpowers/CommutingEndomorphismCondition.lean`
- `BKP` = `LLC/BlochKatoPhases.lean`
- `IHF` = `LLC/IntegralHeckeForms.lean`
- `TWG` = `LLC/TwGood.lean`
- `GSA` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean`
- `DDR` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsDualDualRep.lean`
- `TP` = `Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean`
- `LT` = `LLC/LiftingTheory.lean`

"The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.

## 0. Answers in brief

**(a) Mechanism.**
- The Lean uses neither of the two mechanisms the task proposes in pure form.
  - It is not the cyclotomic ℤ_l-tower, and not a "character of order prime to l kills H¹" argument.
- It uses a **finite, multivariable, tamely ramified anticyclotomic "Iwasawa tower"**, made effective by Taylor–Wiles/Kolyvagin-style auxiliary primes.
  - Choose 2R split auxiliary primes P (Chebotarev, prescribed Frobenius).
  - Twist by characters ψ of Δ = (ℤ/l^M)^{2R}, l-power order, ramified only at those primes.
  - The Selmer group of the whole Λ_M = O[Δ]-family has a **square** presentation matrix Φ.
  - The Selmer length at ψ equals v(ψ(det Φ)). This identity is proved in-tree (`length_selT`).
  - Killing the residual Selmer group by the choice of P gives "μ = 0": det Φ has a unit coefficient on a monomial of degree ≤ 4rR, with the bound uniform in M.
  - Evaluating at a well-chosen point of large l-power order then gives normalised length ≤ ν_l + ε.
- No torsion-ness of an infinite Iwasawa module is needed, and no weak Leopoldt. Everything is at a finite level, and the "μ = 0" comes from residual Chebotarev killing.
- The "small cyclotomic quantity" ν_l is v_l-type. It vanishes unless l divides a fixed host integer QS, and Σ_l ν_l·log l ≤ log QS + log(tr).

**(b) Existence at every l.**
- The existence is qualitative and per l: for each ε > 0, take M large (`exists_good_of_conditions`, `TWG:239`, via `Classical.epsilon`).
- No bound on the size of the conductor Q appears in `GoodTw`.
- The pigeonhole/Behrend remark refers to `Formalism/BehrendSets` (2-power cyclotomic orders). That code is not on this route.

**(c) Local lengths.**
- The local length is an explicit number: len0 = (2[E_λ:ℚ_l]m + 1)·e′, with e′ = ⌈C_A(2 + 2hN/l + log_l(2hN+1))⌉.
- The theorem behind it is an **integral p-adic Hodge lifting lemma** proved in-tree from Wach-module theory, with C_A = 23. It says:
  - for a surjection T₁ → T₂ of crystalline lattices with HT weights in [−M, h],
  - every integral Bloch–Kato cocycle on T₂ times l^{e} lifts to T₁ modulo coboundaries,
  - with e = 2⌊H·l/(l−1)² + 3 + log_l(H+1)⌋ + Σ_{jumps j} v_l(j) + (M/(l−1)+1) + v_l((M/(l−1)+1)!).
- This is the Legendre-type arithmetic the task predicted.
- Budget: Σ_{l≤lStar} log l·f·m·(1 + hB/l + log_l hB) ≈ f·m·b·log lStar, with lStar ≈ m·b/poly(x).
  - Since L = log b, this is ≤ C·f·m·b·L, which is inside the LinkN term C·f·m·b·L² by a factor L.

**(d) Judgement.**
- (1) Recognisable mathematics, with in-tree proofs: Greenberg–Wiles, Chebotarev killing of residual Selmer, a Λ-adic determinant presentation, and Weierstrass-type evaluation. The uniform-in-l use is qualitative, so it is safe.
  - What carries real weight is the set of hypotheses about the family. They are listed in §5.
  - The strongest of them is residual absolute irreducibility of ρ̄ and the Hodge/self-duality conditions **for every twisted l ≤ X″**.
- (2) A Wach-module theorem in the non-Fontaine–Laffaille range. It is not in the literature in this explicit form as far as I know. It is plausible, and proved here from in-tree Wach "admitted" facts that I did not open.

## 1. Statement

### 1a. `KillAt` (`CEC:45-51`)

The Lean says, for ρ a family of r-dimensional representations:

> ∀ twisted local index i (`TwLoc`, i.e. muAt(w_i) ≠ mu0):
> (∀ π ∈ Zgood_i: sFin(ρ_π) ∧ sPi(ρ_π) ≤ nuL(l_i) + epsL(l_i))
> ∧ t·Σ_{v∈Q_i} len_O O/(ζ_v − 1) ≤ epsL(l_i).

The terms are:
- epsL(l) = 1/l² (`TP:51`).
- nuL(l) = `KStar.Tree.nuOf l (cyc) (t·r)` (`TP:53-57`). This is a cyclotomic v_l-quantity. It is 0 unless l | QS (`RootsOfUnity/NuRecord.lean:37-50`), and Σ_l ν_l·log l ≤ log QS + log(tr) (`sum_nu_le`, same file).
- sPi is the normalised length of the Bloch–Kato Selmer group of ρ_π⊗χ₁⁻¹ (NODE-LINKN).

### 1b. `chosenTwist_annihilates_selmerGroups` = `twist_kills_selmer` (`IE/ChosenTwistAnnihilatesSelmerGroups.lean:8-32`)

The statement is NChTie ∧ TwGoodAt ∧ SignatureChoiceCondition ⇒ KillAt.

The proof is glue (read in full):
- `SignatureChoiceCondition` (`CEC:33-43`) gives a signature s with goodS and sPi(ρ_π) ≤ sLen(s, k′, Q, ψ_w).
- `partAT` inside `GoodTw` gives sLen ≤ ν + ε_T(s) with Σ_s ε_T ≤ 1/l².
- `partD` gives the tame clause.

### 1c. What sLen is (`BKP:120-197`)

- Trep(i, s, k, ψ) is the representation (ρ_s ⊗ χ_s⁻¹ ⊗ ψ) ⊗ K_k/O_k on G_E. Here:
  - ρ_s = `X.rhoS i s` is the r-dimensional source representation;
  - χ_s = chi1;
  - O_k = `X.Ok i k` contains a primitive l^k-th root of unity `zk`.
- selT is the Selmer group of Trep in H¹(G_E, ·) with these local conditions (`bkCond`, `Formalism/GaloisCohomology/Statement.lean:162-167`):
  - at λ | l: the image `bk` of integral **finite (crystalline) cocycles** of ρ_s⊗χ_s⁻¹;
  - at Spl ∪ Q (places over g₀, g₁, pD, and the auxiliary set Q): relaxed;
  - elsewhere: unramified.
- sLen is length_{O_k}(selT) / v_{O_k}(l). This normalisation is what lets a bounded O_k-length become tiny as k grows.

### 1d. `GoodTw` (`IHF:219-231`)

It is a conjunction of:
- **PsiOk** (`BKP:289-297`). Q consists of split, degree-1, unramified places, disjoint from S0 ∪ A ∪ the theta levels. Also: k′ ≥ 1; ψ is continuous; **anticyclotomic** (AntiHom cc); ψ takes values in ⟨ζ_{l^{k′}}⟩; ψ is **ramified exactly at Q**; ψ is **trivial on decomposition groups above l**.
- **IdxAt**: the twisted theta lattice is not much bigger than the untwisted one (index ≤ + ε_B).
- Lattice inclusion.
- **partAT**: sLen ≤ ν + ε_T(s) for every good signature s.
- **partC**: twisted theta values θ(ψ) ≠ 0, and −N0 ≤ v(θ(ψ)) ≤ c0 + ε, where c0 is the valuation of the untwisted sum.
- **partD**: t·Σ_Q tameVal(ψ) ≤ ε.
- `TwGoodAt` (`TWG:196`) asks this at every twisted place w for (C.twI w, C.Q w, C.k′ w, C.ψ′ w). `TwConjAt` (`TWG:210`) asks that the conjugate place gets the same pack, with the opposite side.

### 1e. How the twist meets ρ_π

`SignatureChoiceCondition` is proved in `IE/PsiAtPsiAt.lean:22-37` (`JointSix.main`) from:
- `PtFam`, `TriplesGood`, `SameTwist`, `GoodPtRow`, `ResAbsIrr`, Chebotarev;
- the tame clause via `conductorRoot_sub_one_length_le_tameValue`.

*(inferred)* The ρ-block of each π ∈ Zgood at a twisted place **is** ρ_s⊗ψ_w. The type-μ(y) part at a place of residue characteristic l consists of theta lifts twisted by that place's own ψ_w. The ψ_w are glued across places through `NChTie.psi_eq` (`Formalism/LocalRingCardinality/DataNChTie.lean:19-23`): there is one global character ψ0_w with values in LL for each place, conjugation-invariant.

## 2. Argument for KillAt

Chain: `exportAt_of_bundles` (`IE/RealizationOfPublished.lean:27`) → `twistAllPowers_of_galoisCohomology_classField` (`IE/TwistAllPowersOfGaloisCohomologyClassField.lean:21-29`) → `twistTheorem_allPowers_of_selmer_supLattice` (`IE/TwistTheoremAllPowersOfSelmerSupLattice.lean:24-41`).

1. **Λ-adic presentation** (`ThmS`, `GSA:46-49`, ← `selmerPresentationMatrix_of_galois_cohomology`).
   - Put Λ = O[(ℤ/l^M)^ι], where ι indexes the auxiliary places P and d gives the coordinates of the tame characters.
   - The Selmer module of Tgl⊗κ, with κ the universal character, is ≅ ker(Φ) on (K/O)^a for a square a×a matrix Φ over Λ with no unit entries.
   - The proof uses Poitou–Tate, cohomological dimension 2, local and global Euler characteristics, and local Tate duality. Its inputs are named published theorems. I did not open the body.
2. **Specialisation** (`twisted_selmer_lengths_eq_determinant_valuation`, `IE/TwistedSelmerLengthsEqDeterminantValuation.lean:330-385`, read).
   - length_{O_k} selT(ψ) = v_{O_k}(ψ(det Φ)).
   - It uses that ψ is trivial at l, so the local condition at l is unchanged (`le_bk`, `bk_le`).
3. **Residual killing ⇒ μ = 0** (`ResidualBoundOddPrimes`, `GSA:56-65`, ← `residual_bound_of_parts`, `IE/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21-31`, read).
   - `EqDim` (`DDR:65`): dim Sel(ρ̄) = dim Sel(ρ̄*) for the propagated BK conditions. This is a Greenberg–Wiles parity, `residual_selmer_finrank_eq_dual`.
   - `StepAB`: auxiliary primes with prescribed Frobenius, from Chebotarev.
   - `ChooseH` + `SpanOdd`/`SpanTwo` (`DDR:47-63, 142-147`): the Chebotarev images of the pairings of residual Selmer classes are independent. Hence corank 0 (or 1 when ν > 0).
   - `FirstHalf` (`DDR:85-92`): at the inl places, H⁰ = H¹ = H² = 0 for the whole family, so relaxing there is free.
   - `Recip`: Poitou–Tate reciprocity at the inr places.
   - `ResBound` (`DDR:133-140`): at corank 0, det Φ has a **unit** coefficient on a monomial of degree ≤ 4rR. The proof, `IE/ResidualSelmerDeterminantOrderBound.lean:324-352` (read), restricts to a line K[X]/X^{l^M} and shows that X^{4rR+1} does not divide det; that is the first-order-kernel step.
   - At ν > 0, including l = 2 (`ThmC`, `boundModTwoUniformizerAtTwo_of_chebotarev`), the bound is a coefficient of valuation ≤ v(l^ν), via the adjugate.
4. **Evaluation** (`exists_level` → `exists_level_order_exponents_small_valuation_determinants`, statement read at `IE/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321-345`).
   - Choose k ≤ M and exponents e_q with l^{e_q}/φ(l^k) ≤ ε, and set u_q = ζ_{l^k}^{l^{e_q}}.
   - Then the normalised v(F(u − 1)) ≤ μ/e + ε for every F that has a degree-≤ Dd coefficient of valuation ≤ μ.
   - This is a non-archimedean dominant-monomial (Weierstrass-type) argument, uniform over all Galois conjugates ψ^a with (a, l) = 1.
5. **Assembly** (`admissibleIndexBoundAllPowers_of_conditions`, `IE/AdmissibleIndexBoundAllPowersOfConditions.lean:92-224`, read). The same ψ simultaneously gives:
   - partAT (from 2–4);
   - partC (theta values: `PropE`, an Euler-factor distribution relation, `GSA:31-44`);
   - partB/IdxAt;
   - partD (tame: |Q| ≤ 4R and tameVal ≤ ε).

**Why it is uniform in weight.** The twist is trivial at l, so the hard local condition at l is never deformed. All of the work is residual or Λ-adic away from l. Large HT weight enters only through the hypotheses of `SetHyp` and `adm1`/`adm2` (§5).

## 3. Local-at-l lengths (task c)

1. **Definitions** (`LLC/JointConditionsZpowers/LocalErrorBoundPlaces.lean:20-28`).
   - eA(C_A, l) = ⌈C_A(1 + 2hN/l + 1 + log_l(2hN+1))⌉, with hN = ⌊hB⌋ and hB = b + Sc + etaSz + t + 2 (`TP:22`).
   - lenA(λ) = (2[E_λ:ℚ_l]m + 1)·e′.
   - `canon` (`CEC:240-262`) sets len0 := lenA at split l, and explicit lenRowB/lenRowCD at inert l.
2. **The theorem behind len0.** `EmbeddingTypes.aux₃` (`LLC/EmbeddingTypes.lean:311-315`) gives vcc ≤ boundSplit, which is built from e′, sPi, Ш, v_l h_E and the tame terms. Its key hypothesis is `LiftExponentColumn e′` = `LiftExponentAtPlaces`:
   - for every surjection F: L₁ → L₂ of lattices in subquotients of sums of the local family representations,
   - every integral finite cocycle c on L₂ satisfies l^{e′}·c ∈ image(finite cocycles of L₁) + coboundaries (`LatHom.LiftF`, `Formalism/WeaklyAdmissibleFiltrations/Statement.lean:265`).
3. **Supplier.** `lifting_condition_of_crystalline_lift` (`LLC/JointConditionsZpowers/LiftingConditionOfCrystallineLift.lean:72-148`, read) applies `LiftTheoremAllCases` in case A (K unramified, l ≠ 2, HT window [−M, h]).
   - ePA(l, M, H, jumps) = 2·eWA + eUA (`LT:17-27`).
   - eWA = ⌊H·l/(l−1)² + 3 + log_l(H+1)⌋.
   - eUA = Σ_{j∈J} v_l(j) + ⌊M/(l−1)⌋ + 1 + v_l((⌊M/(l−1)⌋+1)!).
   - Then ePA ≤ C_A(1 + H/l + 1 + log_l(H+1)).
   - `LiftTheoremAllCases D HW F 23 32 32` is proved by `lifting_all_parts_of_admitted` (`LLC/BaseChangePreservesUnitaryOf.lean:4818`) from the Wach-module facts `LiftingTheory.admitted` (adm1–23: Wach lattice freeness and characterisation, Γ-semisimplicity of N/Q^yN with eigenvalues χ^{−(a+j)}, extension and descent).
   - Those facts are discharged unconditionally by `liftingTheorem_wachModuleLemma_hypotheses_admitted`. Its body I did not open; neither did I open the contents of `HWOf`.
4. **Case B** (ramified / cyclotomic, `LiftKOf.lean`). The exponent is ePB = 2(2Hs + v_l((2H)!)) + eU ≤ 32(H·s + 1). This is the source of the l = 2, 3 / small-l bound C·f·m·b·log x *(inferred)*.
5. **Reconstruction.** For a crystalline lattice with Wach module N(T), N/π^?N is controlled by q = φ(π)/π, with v(q) ≈ 1/(l−1) on the relevant annulus.
   - The defect between torsion and integral H¹_f is the power of l needed to clear t^H/q^{…} denominators: ≈ H/(l−1)·(l/(l−1)) + log_l H.
   - Together with the ∏ j over the jumps (Σ v_l(j)), this is the same Legendre count as v_l(H!).
   - It is a theorem about local Galois cohomology of crystalline lattices, not just the index of an explicit lattice. It is stated for all surjections in the family.
6. **Budget.**
   - Over l ≤ lStar, with lStar = m·b/(n t²(N+t)L² + k n²(Sc+t+L)) (`LevelStarExponents`), and with Σ_λ[E_λ:ℚ_l] = [E:ℚ]:
     Σ_l log l·3C_A·f·m·(2 + 2hB/l + log_l hB) ≤ C·f·m·(θ(lStar) + hB·log lStar + π(lStar)·log hB) ≈ C·f·m·b·L,
     because log lStar ≤ log b = L (`Scale.b = exp L`, `CoeNeZeroOfNotMem.lean:288`).
   - This is inside dZ0·C·f·m·b·L² (`TP` aux₃) by a factor of L. For l > lStar the term is 0 (`LargePrimeLengthVanishing`).

## 4. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `selmerPresentationMatrix_of_galois_cohomology` (ThmS) | `IE/SelmerPresentationMatrixOfGaloisCohomologyStatement.lean:9`; def `GSA:46` | Λ-adic Selmer ≅ ker of a square matrix | Iwasawa-type presentation | core; body unread (Poitou–Tate, Euler characteristic) |
| 2 | `twisted_selmer_lengths_eq_determinant_valuation` | `IE/TwistedSelmerLengthsEqDeterminantValuation.lean:375` | length at ψ = v(ψ(det Φ)) | specialisation | standard (Fitting/determinant); read |
| 3 | `residual_bound_of_parts` + `resBound` + `chooseH` + `stepAB` + `eqDim` | `IE/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21`; `IE/ResidualSelmerDeterminantOrderBound.lean:324` | auxiliary primes kill residual Selmer ⇒ unit monomial of degree ≤ 4rR | "μ = 0" | core; Taylor–Wiles/Rubin-style; components 2 of 5 read |
| 4 | `boundModTwoUniformizerAtTwo_of_chebotarev` (ThmC) | `IE/BoundModTwoUniformizerAtTwoOfChebotarevStatement.lean:9` | corank-1 case: valuation ≤ v(l^ν) | l = 2 and self-dual residual case | core; unread |
| 5 | `exists_level_order_exponents_small_valuation_determinants` | via `IE/IsAuxiliaryPlaceFamilyAtLevelMono.lean:343` | dominant-monomial evaluation | choose ψ | standard; body unread |
| 6 | `JointSix.main` (SignatureChoiceCondition) | `IE/PsiAtPsiAt.lean:22` | ρ-block of π = ρ_s⊗ψ | ties sPi to sLen | core; hypotheses `PtFam`, `ResAbsIrr`, `SameTwist` unread |
| 7 | `SetHyp`, `adm1` (`IsotypicValuationAtRing`), `adm2` (`ValuationStabilityAtRing`) | `BKP:327-330, 351-392` | self-dual; no HT jumps in [−1, t]; crystalline at l; ρ̄ absolutely irreducible (span = matrix algebra); H⁰ vanishing at every place | residual inputs for every twisted l | **core, hypotheses** (discharged via `admT4_of_rational_rows`, unread) |
| 8 | `lifting_condition_of_crystalline_lift` | `LLC/JointConditionsZpowers/LiftingConditionOfCrystallineLift.lean:72` | LiftExponent with e′ = eA | local length | glue; read |
| 9 | `lifting_all_parts_of_admitted` + `liftingTheorem_wachModuleLemma_hypotheses_admitted` | `LLC/BaseChangePreservesUnitaryOf.lean:4818`; `IE/LiftingTheoremWachModuleLemmaHypothesesAdmittedStatement.lean:9` | Wach-module lifting exponent ePA ≤ 23(…) | weight/l bound | **core, unread**; definition to unfold: `HWOf` |
| 10 | `exists_good_of_conditions` | `TWG:239` | choice by ε, consistent across conjugates | glue | read |

## 5. Oddities

1. **"Killed by choosing the twist" is real mathematics, not a redefinition.** The ε comes from normalising by v_{O_k}(l) = φ(l^k). A bounded λ-invariant becomes length/φ(l^k) → 0. ν is a genuine H⁰-type obstruction.
2. **The weight of the argument sits on hypotheses about ρ_s at every twisted l ≤ X″ ≈ e^{x^{ε/3}}:**
   - residual absolute irreducibility (`ValuationStabilityAtRing`: the span of ρ̄(G) is everything);
   - no HT jumps in [−1, t] (`NoJump`);
   - self-duality;
   - crystallinity at l.
   - For an r ≥ 100-dimensional source representation, residual irreducibility at **all** l up to X″ is a "big image at every prime" statement. Its discharge (`admT4_of_rational_rows`, `ResAbsIrr`) is the next thing to open.
3. **The Selmer condition is relaxed at Spl ∪ Q** (`bkCond`). It is "the Bloch–Kato Selmer group" only away from those places. That is harmless for the congruence bound, because the cocycles of `CutCoreUnit` are relaxed there too *(inferred; not traced)*.
4. **The conductor Q is unbounded.** Its norms satisfy ≡ 1 mod 2l^M with M → ∞ as ε → 0. No size constraint was seen. If any analytic estimate elsewhere depends on the level of the ψ-twisted lifts, this would conflict. I saw ψ only in l-adic lattice statements.
5. **`GreenbergWiles` is passed but unused** (`_`) in `residual_bound_of_parts`. EqDim is derived from the other duality inputs instead.
6. **The Behrend sets are not on this route** (`Formalism/BehrendSets/StatementE.lean`: 2-power Frobenius orders, thick sets).
7. I saw no `True`/`trivial` placeholders, except for a literal `True ∧` at the start of `SetHyp` (`BKP:328`), which is vacuous but harmless.

## 6. Coverage

Read:
- PROTOCOL; SUMMARY §11; NODE-LINKN (all); grep of NODE-CONGMOD, NODE-ACCOUNT, NODE-DIV.
- `CEC:1-262`; `IE/ChosenTwistAnnihilatesSelmerGroups{,Statement}.lean`; `TWG:89-274`; `IHF` (all); `BKP:82-450`.
- `IE/ToricLatticeDenominators` (`TorsionBlocks`):140-191; `IE/RealizationOfPublished.lean`; `IE/TwistAllPowers…ClassField.lean`; `IE/TwistTheoremAllPowersOfSelmerSupLattice.lean`.
- `GSA:1-80`; `DDR:1-170`; `IE/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean`; the statement files of children 1, 3 and 4; `IE/ResidualSelmerDeterminantOrderBound.lean:324-352`; `IE/TwistedSelmerLengthsEqDeterminantValuation.lean:325-387`.
- `IE/AdmissibleIndexBoundAllPowersOfConditions.lean:92-226`; `IE/IsAuxiliaryPlaceFamilyAtLevelMono.lean:318-345`.
- `TP:1-200`; `NuRecord.lean:1-60`; `LocalErrorBoundPlaces.lean`; `EmbeddingTypes.lean:20-66, 173-323`; `QuotientHomNonvanishingBound.lean:120-175`; `DecompositionData.lean:250-270`; `WeaklyAdmissibleFiltrations/Statement.lean:230-290`.
- `LiftingConditionOfCrystallineLift.lean:60-150`; `LT:1-80, 586-663`; `BaseChangePreservesUnitaryOf.lean:4810-4860`; `LiftKOf.lean`; `LocalConstantsFromAdmitted….lean`; `IE/PsiAtPsiAt.lean:1-40`; `DataNChTie.lean:11-23`; `Choice.lean:150-190`; `LevelStarExponents` lStar; `BehrendSets/StatementE.lean:1-80`.

Not opened:
- the bodies of ThmS, ChooseH/SpanOdd, StepAB, EqDim, ThmC and `exists_level_order_exponents…`;
- the Wach "admitted" proofs and `HWOf`;
- the PtFam/ResAbsIrr/SetHyp dischargers;
- PropE (twisted theta values);
- the inert-row lengths (lenRowB/CD);
- the l = 2, 3 file `NRowTwo`.
