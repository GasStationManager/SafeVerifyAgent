# NODE-LINKN: the congruence-module bound behind `LinkN`

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- `LLC/` = `Formalism/SharpRestriction/LevelLetterCocycles/`
- `DN` = `LLC/DataN.lean`
- `TP` = `Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean`
- `B23` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean`
- `QH` = `LLC/QuotientHomNonvanishingBound.lean`
- `GC` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean`

"The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.

## 0. Answers in brief

**(a) The node is deep, not elementary.** There are two layers. Only one of them is a finite-group projector.
- The type part Z is cut out by a **theta map**: Z = jL⁻¹(range θ′\*) (`Formalism/LocalToGlobal/IndefiniteReal/PartsOrth.lean:122-128`). It lies inside the "block" subspace ZHL. ZHL consists of the Hecke eigenforms whose Hecke polynomial at every good place is divisible by ∏_{c<t}(1 − νq^cX) (`Columns/HeckeSp.lean:507,577,660`). These are the forms whose Galois representation contains χ⊗(1 ⊕ ε ⊕ … ⊕ ε^{t−1}). Equivalently their A-parameter contains a Speh block μ⊠S_t (`muPart = ⟨1, muC i, t⟩`, `DN:1257`). In short, Z is a sum of Hecke eigenspaces: theta lifts of A-parameter ρ_0 ⊞ μ⊠S_t.
- Zgood ⊆ Z is a further cut by a level type of the finite group G = ∏_k GL_r(F_{g_k})^f (`DN` `restN_card_levelGroup_eq`). That part is elementary. The α = |G|·(type idempotent) of `CommutingEndomorphismCondition` (`CommutingEndomorphismCondition.lean:13-20`) costs v_l|G|, and Σ_l log l·v_l|G| = log|G| ≤ C·x^C·L (`LinkNOfGd.lean:59`).
- The cost of separating Z from the other eigensystems X∖Z of the Hecke-localised lattice Mt_i is the genuine Hida-type congruence ideal vcc(π) = len O/ccAt(T, Z, π) (`DN:225`, `DN:29`). So etaW splits as Σ mult·(Hida congruence + v_l|G|) (`adm1`, `TP:133-136`).

**(b) The mechanism is a Wiles-type Fitting-ideal argument, not a pseudo-character one.**
- ρ_π (dimension nV = r + t) is ρ ⊕ χ_1 ⊕ … ⊕ χ_t with χ_c = χ_1ε^{−(c−1)} (`IsOrthogonalIdempotentDecomposition`, `IdempotentChoiceDepthZero.lean:18-60`). So the user's guess is right: these are theta/Speh-type lifts whose Galois representation is ρ plus a cyclotomic chain of characters. ρ itself is not abelian.
- The bound is vcc ≤ len(cocycles of the ρ-block) + Σ_c len(cocycles of block c) (`CutDetOrd.main`).
- The proof applies a determinant lemma: for a presented module, if all generic block determinants of the relations lie in I, then len O/I ≤ Σ len(solution modules). This is "Fitt₀ ⊆ I ⇒ len O/I ≤ len M".
- The key input is `NoChiOff`: no form outside Z has χ_1 inside its Galois representation.
- Each block is then bounded:
  - ρ-block: Bloch–Kato Selmer group of ρ⊗χ_1⁻¹, which is sPi;
  - block c = 1: unramified homomorphisms, bounded by v_l(h_E);
  - block c ≥ 2: Ш¹(ℚ_l/ℤ_l(−(c−1))), plus tame costs.

**(c) Direction.**
- The Lean needs len(congruence) ≤ len(Selmer), and that is what it proves. In the Eisenstein case this is the half of Mazur–Wiles proved by Ribet's lattice made quantitative through Fitting ideals (Wiles 1990; also Bellaïche–Chenevier Ch. 1, Skinner–Urban).
- That half is "class group ≥ congruence module". It does not need the analytic class number formula or the other half of the main conjecture.
- So the user's worry names the right theorem but not a gap. The direction used is the established one. What is deep sits in its hypotheses, which (§6) are carried uniformly over l and huge weight.

**(d) Where b comes from.** The size b = e^{x^ε} is the **Hodge–Tate weight scale**, entering through the local-at-l terms.
- Per place λ | l the local length is ≤ (2·nLam·m + 1)·C(1 + hB/l + log_l hB), with hB = b + Sc + etaSz + t + 2 (`admA`, `TP:162-165`; `eP`, `TP:28`; `hB`, `TP:22`).
- At l = 2 and 3 the bound is midF = C·f·m·b·log x + C·x^C·L² (`B23:33-34,52-53`; `NRowTwo.lean:16-43` uses ⌊2b⌋).
- Summing log l·[E:ℚ]·m·b/l over l ≤ lStar gives ≈ f·m·b·log lStar per eigen-system. Multiplying by the multiplicity bound dZ0 gives the LinkN shape.
- For l > lStar the local term is 0 (`StarE`, Bd with b = 0, `B23:21-23`).
- Several other terms are kept negligible by hypothesis:
  - the Q-term: `KillAt` forces t·Σ_Q len ≤ 1/l² (`CommutingEndomorphismCondition.lean:45-51`);
  - sPi: `KillAt` gives sPi ≤ nuL + 1/l², a cyclotomic v_l-type quantity;
  - vdel and the polynomial errors: BB ≤ C·f·n·t²·nV·L² (`BBLe`), which is ≪ b only because b is super-polynomial.

**(e) Judgement.**
- The skeleton is recognisable and coherent: Fitting-ideal Ribet–Wiles, cocycles sorted by GMA blocks, blocks identified with Selmer and class groups.
- Two places go beyond the literature in uniformity. Both are hypotheses fed from elsewhere:
  - `KillAt`: the ρ-block Bloch–Kato Selmer group is killed down to nuL at every twisted l. It is obtained by *choosing the twist* (`chosenTwist_annihilates_selmerGroups`, `GoodTw`).
  - The local-at-l exponent bounds ~ weight/l for weight ≈ e^{x^ε} and l as small as 2.
- The Galois-representation inputs (`GoodR`, `NoChiOff`) are standard in kind but required for every eigensystem in the localised lattice.

## 1. Statement

### 1a. `UpperTheory.GalC.final_alt_alt` (`TPS/CFinal.lean:19`)

The Lean says: `final_alt_alt : GlobalTheory.NLink.Final.mainTheorem`. Here (`TPS/MainTyzTer.lean:22`):

> Hypotheses₂ → PublishedInputsThirdLayerAlt → GeometricGaloisRepCompatibility → SerN → DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ hL cDep, LinkedAt(… Closed (BoundAtTwoThreeFamilyFonAlt)) → LinkedAt(… Closed (LinkN)).

So it is a **transfer theorem**. From the bound at l = 2, 3 (`BoundAtTwoThreeFamilyFonAlt`, supplied by `at23_family_alt`, `TPS/At23OfAll.lean:19`) and the Galois inputs, it produces LinkN on the whole family.

Proof (`TPS/LinkNFam.lean:37-86`):
1. `exists_good_cut_facts_tie4` gives a good cut. It needs Chebotarev (`prN.cheb`), local finiteness, local Tate duality and the local Euler characteristic formula.
2. `galois_preconditions_at_mem` gives the Galois preconditions.
3. `linkN_of_twGood_galoisPreconditions` combines them with:
   - `exists_const_tieChi_bound_of_facts` (the constants C, CT);
   - `conclF_of_family_facts_and_bound_at_two_three` (`TPS/ImportsFurtherTailStatement.lean:11`);
   - `linkN_along_family_of_localBounds` (`IE/LinkNAlongFamilyOfLocalBoundsStatement.lean:7`, which is `LinkFam.main`): ConclF ⇒ LinkN;
   - `linkN_of_gd` (`.../HeckeGaloisCriteria/LinkNOfGd.lean:38-80`), which passes back from the cut family. It absorbs log|G| ≤ C1·x^{C1}·L into C·f·m·b·L².

### 1b. `ConclF` (`B23:124-143`)

The intermediate statement. For each datum there is hub data X (Galois representations r, ρ; local lengths len0; error BB) such that, at every twisted local index i and every π ∈ Zgood_i:

  vcc_i(π) ≤ sPi(ρ_π) + Σ_{λ|l} len_i(λ) + VVr(l) + v_l(h_E) + BB_i + 1/l²   (`Bd`, `B23:17-19`; `StarAD`)

The pieces are bounded as follows:

| condition | range of l | bound |
|---|---|---|
| `StarE` | l > lStar | len = 0 and BB = 0 |
| `admA`, `admB`, `MediumInert…` (`TP:162-189`) | middle l | len ≤ C(nLam + 1)·m·eP(l) etc. |
| `BBLe` | — | BB ≤ C·f·n·t²·nV·L² |
| `KillAt` | — | sPi ≤ nuL + 1/l² |
| `StarF`/`BoundAtTwoThree` | l ∈ {2, 3} ∪ small | Bd with midF |
| `adm1` (`TP:133`) | — | etaLoc ≤ Σ mult·(vcc + v_l\|G\|) |
| `MultLe` | — | Σ mult ≤ rank = dZ0 |

### 1c. `GlobalTheory.CutCoreUnit.main` (`IE/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`)

The hypotheses, as I read them:
- Artin reciprocity;
- `GoodR`: for every x ∈ X_i there is a continuous r_x : G_E → GL_{nV}(O_i), semisimple over K, with charpoly(Frob_w) equal to the Hecke polynomial at split w (`DN:1220-1233`);
- `IsOrthogonalIdempotentDecomposition` (below);
- π ∈ Z;
- `NoChiOff`: for x ∉ Z, r_x⊗χ_1⁻¹ has no nonzero invariant vector (`GC:68-70`);
- `UnrOut`;
- conditions at the places S and Q;
- at w | l: LocBound with exponent 0 for the ρ-block; the χ_c-cocycles (c ≥ 2) lie in BD; the χ_1-cocycles are unramified;
- finiteness of sPi and of Ш.

Conclusion: vcc(π) ≤ sPi + Σ_{0<e<t} len Ш¹(E, ℚ_l/ℤ_l(−e)) + v_l(h_E) + t·Σ_{q∈Q} len O/(ζ_q − 1).

**The decomposition** (`IdempotentChoiceDepthZero.lean:18-60`):
- There are idempotents eB (rank t) and e1 (rank 1) in the O-span of r(G) with Hecke coefficients.
- At π, r_π ≅ ρ_π ⊕ ⊕_{c=1}^{t} χ_c via S.e.
- There is an inertia element g0 at a place over l whose cyclotomic value ε(g0) has order exactly l − 1 mod l.
- X0 acts on the t-block by χ_c(g0). The roots rr_c of its characteristic polynomial are adjoined to T, giving T′ free of rank t! over T.
- Eel = ∏_{c≥2}(X0 − rr_c·eB) is the rank-1 projector onto the χ_1-line. It satisfies Eel² = del51·Eel with del51 = ∏_{c=2}^{t}(rr_1 − rr_c), and **IsUnit(del51(π′))** is required.

## 2. Argument

### 2a. From etaW to vcc

1. etaW(j, w) is the length at w of Tl/cutZ, where Tl is the orthogonal projection of the integral level lattice onto Z_l and cutZ = Z_l ∩ lattice (`LiftLat.lean:116`; `RowLat.lean:153,155`).
2. The Lean ties etaJ j w = Σ_{i∈locs j w} etaLoc i (NODE-CONGMOD).
3. Here Mt_i is the Hecke-localised piece of the type-μ lift lattice MtLat(μ, j) (`DN` `prMt_lat`, `T_local`).
4. etaLoc = len(MtUp/MtLow) is the congruence module of the eigensystem set Zgood in Mt_i (`DN:205-220`).
5. Use an endomorphism α that commutes with Hecke, acts as |G| on Zgood eigenspaces and as 0 on Z∖Zgood (the finite-group type projector, integral after multiplying by |G|). Combine it with Hecke elements f ∈ T that vanish on X∖Z (these generate ccAt). Together they kill the complement and act on π by an element of (|G|)·cc(π).
6. Hence etaLoc ≤ Σ_π mult·(vcc(π) + v_l|G|) (`adm1`; `EtaBound`/`CongruenceSingleEndomorphism`, `LLC/CongruenceSingleEndomorphism.lean:87-109`).
7. This step is standard: congruence module ≤ Σ congruence ideals for a semisimple Hecke action.

### 2b. vcc ≤ cocycles (`CutDetOrd.main`, `IE/LengthHeckeValueIdealLeDeterminantBound.lean:59-140`)

1. Let A be the O-algebra generated over T′ by the matrices r_{x′}. Put yg(γ) = r(γ)⊗χ_1⁻¹·Eel − Eel. This is the column that measures how far the χ_1-line moves under γ. Let Y be the A-module spanned by the yg(γ).
2. Choose finitely many generators γ_q. Let Rel be the relations θ ∈ A^g with Σθ_q·yg(γ_q) = 0 at every x′.
3. For every relation system, the generic block determinant is the value at π′ of an element of T′ (`BlockDetPoly.main`, using `CharpolyCoeffsInSubalgebra`).
4. That element vanishes at every x′ lying over X∖Z. By `NoChiOff`, the χ_1-line of r_x is not invariant, so some yg(γ)η ≠ 0 (`exists_ne_zero`). The relation matrix therefore has a kernel there and its determinant is 0 (`det_generic_eq_zero`).
5. So the element lies in ccOff, using freeness of T′ over T (`value_mem_ccOff`).
6. The determinant lemma (`IE/DeterminantLemmaDiscreteValuationRingQuotientLenStatement.lean:6`) then gives len O/ccOff ≤ Σ_blocks len{solutions in (K/O)^{d_j g} killed by Rel}.
7. Those solution modules are cocRho and cocChi c: continuous 1-cocycles G_E → K/O ⊗ (ρ⊗χ_1⁻¹), resp. → K/O ⊗ (χ_{c+1}/χ_1) (`GC:28-42`).
8. *(inferred)* This is Wiles's Fitting-ideal form of Ribet's lemma: the Fitting ideal of the extension module is contained in the congruence ideal.

### 2c. Bounding each block (`CutCoreUnit.main`, lines 56-114)

- **ρ-block.**
  - Restriction at w | l lies in the local lattice (LocBound 0, together with `localCocycles_aboveEll_inCut_unitDelta`).
  - At places outside S ∪ Q ∪ {l} the cocycles are unramified (`LocalGlobalSelmer.main` + UnrOut).
  - Coboundaries vanish because del51 is a unit.
  - So the block is ≤ len of the Bloch–Kato Selmer group of ρ⊗χ_1⁻¹, which is sPi (`QH:857-860`).
- **Block c = 0** (twist χ_1/χ_1 = 1): unramified homomorphisms that are trivial at l, so ≤ v_l(h_E) (`UnramHom.length_le_classNumber`, which uses Artin reciprocity).
- **Block c ≥ 1** (twist ε^{−c}).
  - Peeling the tame set Q costs len O/(ζ_q − 1) per q (`Cut.Peel.main`).
  - At S the quadratic or polynomial relations kill inertia.
  - At l the cocycles lie in BD.
  - So the cocycle is in Ш¹(ℚ_l/ℤ_l(−c)) (`length_cyclotomic_block_cocycles_le_sha`).
- Adding up gives the stated inequality.

## 3. What ρ_π is, and the classical check (task c)

**ρ_π.**
- ρ_π = ρ ⊕ χ_1(1 ⊕ ε⁻¹ ⊕ … ⊕ ε^{−(t−1)}), with ρ of dimension r (the Galois representation of the source of the theta lift).
- Through `SignatureChoiceCondition` (`CommutingEndomorphismCondition.lean:33-43`), sPi is compared with the Bloch–Kato length of a Hecke character ψ′ attached to the chosen twist. So *(inferred)* ρ is itself induced from, or controlled by, CM characters.
- The congruences that are counted are between a Speh-type lift and forms outside Z. Their cocycles live in the extensions χ_1 → ρ and χ_1 → χ_c. The second kind is the ε^{−(c−1)}-twist, which matches Ш(−e) with e < t.

**Classical check.** Take k fixed, level 1, Eisenstein series E_k, and I the Eisenstein ideal.
- Ribet–Wiles give len T/I ≤ len Cl(ℚ(μ_l))^{(ω^{1−k})} through the same Fitting argument. The input is that cusp forms congruent to E_k have irreducible ρ_f, which is the analogue of NoChiOff.
- With len T/I ≥ v_l(B_k/2k) (constant term), this yields "l^n | B_k ⇒ #class ≥ l^n".
- So the step the Lean uses is the proved half. The remaining depth of Mazur–Wiles (the reverse inequality, via the class number formula) is not used.
- The direction is therefore right. The worry "upper bound on the congruence module = deep main-conjecture direction" does not apply. The bound is "congruence ≤ Selmer", and Ribet's lattice made quantitative is exactly that.

## 4. Sizes (task d)

| term | size per eigen-system | source |
|---|---|---|
| local lengths at split l ≤ lStar | Σ_{λ\|l}(2·nLam·m + 1)·C(1 + hB/l + log_l hB), with hB ≥ b | `admA`, `TP:162`; `eP`, `TP:28` |
| inert l | C(nLam+1)·r·(hB/(l−1)^{jA+1} + …) + C·nLam·m·eP | `admB`, `MediumInert…`, `TP:167-189` |
| l = 2, 3, small | midF = C·f·m·b·log x + C·x^C·L² | `B23:33,52`; `NRowTwo.lean` |
| BB (vdel, h0, cB) | ≤ C·f·n·t²·nV·L² (polynomial) | `BBLe`; `localErrorBoundDecomposition` |
| sPi | ≤ nuL + 1/l² (cyclotomic, ~log) | `KillAt` |
| tame Q | t·Σ_Q len ≤ 1/l² | `KillAt` |
| Ш, v_l(h_E) | carried separately (VVr, vhE), summed with weight log l | `TP:55,70,117` |

- Weighted by log l and summed over l ≤ lStar, the local term gives ≈ [E:ℚ]·m·b·Σ log l/l ≈ f·m·b·log lStar. With multiplicity ≤ dZ0 this gives the LinkN term dZ0·C·f·m·b·L².
- So b enters as the **weight**: the forms have Hodge–Tate spread of order b (`BandPlaceWeightApproximation`: weights s with |l·s − b| small, `TP:191-194`). The local integral p-adic Hodge defect costs about weight/l at each place over l.
- Uniformity in l holds because each term is explicit in l and vanishes for l > lStar outside a controlled exceptional set (`ExcOK`, `B23:25-27`).

## 5. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `CutDetOrd.main` + `determinantLemma_…` | `IE/LengthHeckeValueIdealLeDeterminantBound.lean:59`; `IE/DeterminantLemma…Statement.lean:6` | len O/cc ≤ Σ_blocks len(cocycles) | Ribet–Wiles via Fitting | standard (Wiles 1990; Bellaïche–Chenevier Ch. 1); proof read, lemma body not |
| 2 | `IsOrthogonalIdempotentDecomposition` / `GoodCongruenceObjects` | `IdempotentChoiceDepthZero.lean:18`; `QH:458` | GMA blocks via a g0-eigen-idempotent; del51 a unit, or length vdel | makes the blocks | core hypothesis; see Oddity 1 |
| 3 | `GoodR`, `NoChiOff` | `DN:1220-1233`; `GC:68` | Galois representations for **all** x ∈ X_i; complement forms have no χ_1 | Galois input | standard in kind (Row0b family); NoChiOff ⇔ every form with χ_1⊠S_t is in the theta image *(inferred)*: Rallis/Mœglin-type; not traced |
| 4 | `KillAt` ← `chosenTwist_annihilates_selmerGroups` | `CommutingEndomorphismCondition.lean:45`; `IE/ChosenTwistAnnihilatesSelmerGroupsStatement.lean:7` | sPi ≤ nuL + 1/l² at every twisted l | kills the ρ-block | **core, unread**: Bloch–Kato vanishing for the chosen twist (`GoodTw`) |
| 5 | local-length bounds (`admA`/`admB`/Medium/SmallInert, `starInequality_rowsAD_of_global_theorems`, `onAt_eq_two_bounds_of_setup`) | `TP:162-194`; `IE/StarInequalityRowsAD…:7`; `NRowTwo.lean:7` | local cocycle defect at λ \| l ≤ C·m·(1 + hB/l + log_l hB) | where b enters | **core, unread**: integral p-adic Hodge theory (Wach/Fontaine) at weight ≈ e^{x^ε}, l ≥ 2 |
| 6 | `UnramHom.length_le_classNumber`, `length_cyclotomic_block_cocycles_le_sha`, `Cut.Peel.main`, `LocalGlobalSelmer.main` | used in `CutCoreUnit.main:73-109` | block c = 0 ≤ v_l h_E; c ≥ 1 ≤ Ш(−c); tame peel | identify blocks | standard (CFT; definitions of Ш); bodies not read |
| 7 | `adm1`/`EtaBound`/`CommutingEndomorphismCondition` | `TP:133`; `CongruenceSingleEndomorphism.lean:87`; `CommutingEndomorphismCondition.lean:13` | etaLoc ≤ Σ mult·(vcc + v_l\|G\|) | module ⇐ ideals; finite-group layer | standard |
| 8 | `linkN_of_gd`, `LinkFam.main`, `conclF_of_family_facts_and_bound_at_two_three` | `LinkNOfGd.lean:38`; `IE/LinkNAlong…:7`; `TPS/ImportsFurtherTailStatement.lean:11` | assembly into LinkN | bookkeeping | glue (first read, others statement only) |

## 6. Oddities

1. **The unit version needs t < l.**
   - `IsUnit(del51(π′))` with ord(ε(g0) mod l) = l − 1 forces (l − 1) ∤ k for 1 ≤ k ≤ t − 1, i.e. t < l. With t ≈ x^{398.5} (ACCOUNT), `CutCoreUnit.main` can only serve l > t.
   - For smaller l the general `GlobalCore`/`GoodCongruenceObjects` route pays vdel = Σ_{0<k<t}(s0 + v_l k) (`DN:228`). That is ≈ t·log t, times 4nV. It is absorbed into BB ≤ C·f·n·t²·nV·L².
   - That is harmless only because b = e^{x^ε} is super-polynomial (`ParametersPolynomiallyBounded`, `EmbeddingTypeJumps.lean:260`). The "≈ f·m·b" is really f·m·b + poly(x).
2. **sPi ≤ nuL is very strong.** The Bloch–Kato Selmer group of an r-dimensional, large-weight ρ⊗χ_1⁻¹ is killed down to a cyclotomic v_l-number at *every* twisted l, small l included. The Lean obtains it by choosing the twist. This is the real reason twisted places exist *(inferred)*: the twist is chosen so the ρ-block Selmer vanishes. Unread.
3. **NoChiOff must hold for all non-Z eigensystems in Mt_i.** Z is the theta image. Any form with the χ_1⊠S_t block that is not in the theta image would break the argument. I did not find where NoChiOff is discharged.
4. **`final_alt_alt` is only a transfer theorem.** The l = 2, 3 bound is supplied separately (`at23_family_alt`), using `Hypotheses₂` "prints" constants 6000 and 30000 (`NRowTwo.lean:44-46`).
5. I saw no `True`/`trivial` placeholders in the files I read.

## 7. Coverage

Read:
- PROTOCOL (Explainer); NODE-CONGMOD (all); NODE-ONECHARU:1-40; grep over the ROOT, ACCOUNT, DIV, WRITEUP and VWIN nodes; SUMMARY §10.
- `TPS/HypothesesNonemptyOfUnramifiedExponents.lean` (all); `TPS/CFinal.lean`; `TPS/LinkNFam.lean` (all); `TPS/MainTyzTer.lean:22`; `TPS/BoundAtTwoThreeFamilyFon.lean:15-34`; `TPS/At23OfAll.lean`; `TPS/NRowTwo.lean:1-46`.
- `LinkNOfGd.lean:10-80`; `B23` (all); `TP:1-200`; `CommutingEndomorphismCondition.lean:1-200`; `EmbeddingTypeJumps.lean` (def list, 41-49, 111-116, 260).
- `CongruenceSingleEndomorphism.lean:60-140`; `DN:20-35, 60-240, 1220-1260`; `QH:271-284, 380-384, 430-500, 857-862`; `IdempotentChoiceDepthZero.lean` (all).
- `GC:1-90`; `IE/GlobalCongruenceCountOfRootDifferenceUnit.lean` (all); `IE/LengthHeckeValueIdealLeDeterminantBound.lean` (all) and its Statement file; `IE/DeterminantLemma…Statement.lean:6` (statement).
- `RowLat.lean:40-160, 195-260`; `LiftLat.lean:1-160`; `IndefSide.lean:120-175`; `PartsOrth.lean:55-128`; `CxLemmas.lean:505-540`; `HeckeSp.lean:500-512, 570-580, 640-665`; `GoodPartHermitianSpec.lean:25-45`; `NuInf.lean:9`; `TwGood.lean:150-235`.

Not opened:
- the bodies of the determinant lemma and `BlockDetPoly.main`;
- the block lemmas of child 6;
- `chosenTwist_annihilates_selmerGroups` and `GoodTw`;
- the local-length suppliers (child 5);
- where NoChiOff and GoodR are discharged (`galois_preconditions_at_mem`, `exists_good_cut_facts_tie4`);
- `LinkFam.main`;
- the definition of MtL (full forms space vs block part).
