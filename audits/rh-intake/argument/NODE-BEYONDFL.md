# NODE-BEYONDFL: zero local defect at lStar < l < b (outside the Fontaine–Laffaille range)

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my own reading. Nothing was compiled.

Abbreviations:
- `BS` = `Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/BaseSizes.lean`
- `APE` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/AdmissibleParameterEventually.lean`
- `IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- `UL` = `IE/AdmissibleOfLargeResidueChar.lean` (this file holds `GlobalTheory.UseLoc.main`)
- `TL2` = `Formalism/SharpRestriction/LevelLetterCocycles/TableLineDegreeTwo.lean`
- `HWR` = `Formalism/FrobeniusContraction/HighestWeightResidueAvoids.lean`
- `PD` = `IE/ExistsLocalSlotDataOffExceptionalPrimes.lean` (`position_data_exist`)
- `TOP` = `IE/TwistedLatticeCohomologyTheoremTOP.lean`
- `RB` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ResBound.lean`
- `MMA` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean` (`TopData`)
- `CIC` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/CentralIdemCoeff.lean`
- `APJ` = `Formalism/SharpRestriction/LevelLetterCocycles/AdmissibleParameterJ.lean`
- `EXC` = `IE/ExcludedPrimesFewAndSmallAlongFamily.lean`
- `EBA` = `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean`

## 0. Verdicts

**No ESCALATE.** The local claim is a new, in-tree integral comparison, type (ii): a lattice-level "torsion-crystalline = Bloch–Kato" theorem for widely spaced weights. It holds under a residual genericity condition, which is what "position data" means: Sen weights mod l stay away from the short window that holds the character block.

It is not mechanism (i). Nothing uses a CM or induced shape of ρ locally. `TopCore` is stated for an arbitrary crystalline ρ over an unramified K.

My toy test (GL₂(ℚ_l), one character ψ of weight u ≫ l against χ₁) is consistent with the Lean. The configurations where the Breuil–Mézard / Serre-weight analysis produces an extra residual admissible class are exactly the ones the residue-avoidance hypothesis T3 removes (§2e).

| Q | Answer | Status |
|---|---|---|
| 1 | Defect = length of span(cut cocycles at w ∣ l) modulo the divisible Bloch–Kato H¹_f(G_w, V/T). The claim is that this length is 0 (`LocBound … 0`). The weights at each embedding are: a block of t consecutive weights; m "lows" within etaSz of the block; k−1 "cloud" weights in one window of length ≈ Sc + etaSz around a base size W0 ≈ b (or w″, or bT+b′/x). The top weight h ≈ b + Sc + 2etaSz + 3, which is far above l. | proved and read (assembly); shape lemmas statement only |
| 2 | (ii). `TopCore` (TL2:193-212): admissible ⇔ H¹_f; for χ_c, c ≥ 2, admissible ⇔ coboundary; for χ₁, admissible ⇔ unramified. The conditions are the position hypotheses. The arithmetic condition on l is l > lStar and l ∉ Exc. | `UseLoc.main`, `position_data_exist`, `TOP`, `resBound_dsum`, `AdmBound.main`: read. The mod-l (φ,Γ)/Sen counting `card_cocycles_independent_mod_coboundaries_le`, `realD`, `exactLocalConditions_topCore`, `jump_position_conditions_at_letter`: statement only |
| 3 | Plausible. On the toy case it agrees with the weight part of Serre's conjecture for GL₂(ℚ_l) (§2e). | my computation, not Lean |
| 4 | `BhattScholzeIntegral`: matches Bhatt–Scholze (crystalline ℤ_l-lattices ↔ prismatic F-crystals; existence plus full faithfulness, no weight bound). `LocalTateDualityK`, `LocalEulerCharK`: standard. `BlochKatoLocal` is passed and discarded. Fontaine–Laffaille and Wach modules are **not** published inputs here: Wach data are built in-tree from Bhatt–Scholze. | read (statements) |
| 5 | Confirmed: \|Exc\| ≤ (\|TT\|+2)(Sc+3η+t+8b/lStar+9), elements ≤ 3b, and the charge ≤ 1.164·10⁶(C+1)²Ub¹⁸ ≤ b. | `excOK_at` read in part, `card_exc_le` read, `sum_exc` statement and opening read |

## 1. Statement

**`CongBound_at D L`** (BS:87-93). For every local index i with ℓ := l_i:
- if lStar < ℓ, ℓ ≠ g_k for every k, ℓ ∉ Exc, `WeightTie`, `HG`, and GoodR(r) hold,
- then for every π ∈ Z_i and every rank-r part ρ of r(π) (`IsRankRPart`: r(π) ≅ ρ ⊕ χ₁ ⊕ … ⊕ χ_t over K, BS:57-66),

  vCC(π) ≤ sPi(π, ρ) + shaSum + vClass + epsQ.

The terms are as follows.
- vCC = min over f ∈ cc_i of v_ℓ(f(π)). This is the Hida congruence ideal (BS:68-69).
- sPi = normalised length of the global ρ-block Selmer group selPi (BS:71-72).
- shaSum = Σ_{0<e<t} len Ш(e) (BS:74-75).
- vClass = v_ℓ(h_E) (BS:77).
- epsQ = t·Σ_{P∈Q} v(ζ_P − 1) (BS:82-83).

There is **no local-at-ℓ term**. That is the "lamG = 0" of NODE-LARGETW.

**`lStar`** (`Formalism/LocalRingCardinality/DataParams.lean:38-40`):

lStar = m·b / ( n t²(N_m + t) L² + k n²(Sc + t + L) ), with b = e^{L}.

**`Exc`** (BS:21-32):
- sgPlus = ⌊2b/lStar⌋.
- baseSizes = {b, w″(n)} ∪ {bT(t) + ⌊b′/x⌋ : t ∈ TT}.
- window(W) = [W − etaSz − 2sgPlus − 3, W + Sc + 2etaSz + 2sgPlus + 4] ∩ ℤ.
- Exc = {ℓ prime : lStar < ℓ and ℓ divides some n ∈ window(W) for some W ∈ baseSizes}.

**The local object.** `UseLoc.main` (UL:24) concludes three things at each w ∣ ℓ.
1. `LocBound i w hw r univ (WpO ρ π) 0`. `LocBound` (CIC:138-141) says: length of span(cutCoc) / (span ∩ HfD) ≤ 0. Here:
   - cutCoc (CIC:122-133) is the set of local cocycles G_w → W_ρ ⊗ (K/O) obtained from the GMA/Ribet lattice construction (an FG stable submodule Y with a map φ : Y → W, evaluated on E_j);
   - HfD (`Formalism/WeaklyAdmissibleFiltrations/StatementTor.lean:126-127`) is the image of the rational H¹_f cocycles in V/T, plus coboundaries.

   So the defect is the length of the cokernel "Ribet classes / divisible Bloch–Kato H¹_f(G_w, W_ρ ⊗ K/O)", and the claim is that it is 0. The proof (UL:32-47) shows span ⊆ HfD, using `mem_finite_part_of_lift` (statement only).
2. For c ∈ [2, t], the χ_c/χ₁ cut cocycles are coboundaries (BD).
3. For c = 1 they are unramified (Z1urD).

**HT weights at ℓ** (BS:42-55 `param`; APJ:18-30; PD:58-68).
- At each embedding the multiset is, relative to the block:
  - **block**: {0, …, t−1}, the characters χ_c = χ₁ε^{−(c−1)};
  - **lows**: e_j − b_a + c0 for a < m, so m weights;
  - **cloud**: e_j + v_a + c0 for a < k−1, so k−1 weights.
- The Lean says (PD:58-64; `lowJumps_and_cloud_in_windows_along_family`, statement read):
  - lows lie within etaSz of the block centre (t−1)/2 and at distance ≥ 2b/lStar + t/2 + 3 from it;
  - the cloud lies in [W0, W0 + Sc + etaSz + 1] (oriented by `up`), for one W0 ∈ baseSizes per embedding.
- So there are **two short windows** (low window of length ≈ etaSz containing the block, and cloud window of length ≈ Sc + etaSz) separated by a gap ≈ W0 ≈ b. The top h satisfies h ≤ b + Sc + 2etaSz + 3 (PD:70-77).
- For lStar < ℓ < b, the cloud weights are ≈ (b/ℓ)·ℓ with b/ℓ ≤ x^{O(1)}. They exceed ℓ by a factor up to x^{O(1)}, so this is outside FL. They stay below ℓ²/4 because σ < ℓ/4.
- σ := sg = ⌊Σ_{j≥0} h_{c+j+1}/ℓ^{j+1}⌋ ≈ h/(ℓ−1) (HWR:40-41). The Lean proves σ ≤ 2b/lStar (PD:78-91).

## 2. Argument

**(a) Assembly** (`NLinkE.main_alt_alt`, APE:30-57, read).
1. `position_data_exist` gives, for ℓ > lStar, the facts 5 ≤ ℓ, t+1 < ℓ, ℓ ∉ {q, d, small}. For ℓ ∉ Exc it also gives position data.
2. Unramifiedness of the host at ℓ follows (APE:42).
3. Bhatt–Scholze gives the Wach-type data (HW, F, Cm) (APE:52).
4. `blochKatoTop_of_localTateDuality_eulerChar` gives `aux₃ = TopTheoremLocal` (APE:53). This is `TopCore` for every prime ℓ ≥ 5, every unramified K and every irreducible λ (TL2:398-401).
5. `UseLoc.main` (APE:54) gives the zero defect.
6. `congruenceBound_extended_of_rationalBound` and `globalCongruenceCount_of_rootDifference_unit` (statements only) turn this into vCC ≤ Selmer + Ш + h_E + epsQ. That is the Ribet/GMA step of NODE-LINKN, now with no local correction.

**(b) What "position data" is** (TL2:25-31; HWR:67-74). For each Frobenius-orbit index c ∈ ℤ/n of embeddings, take (h_c, w_c, η_c, typ_c, U_c) such that:
- U_c ⊂ [1, h_c − 1], and the block [w_c, w_c+t−1] ⊂ [1, η_c] when typ = G (respectively ⊂ [h_c − η_c, h_c − 1] when typ = Bd);
- **T1**: η_c + 4σ_c + 6 < ℓ. The low window has FL length.
- **T2**: every low weight is at distance > σ_c + 2 from every block weight.
- **T3** (`ResidueAvoidance`): every cloud weight x satisfies x mod ℓ ∉ [−2σ_c−2, η_c+2σ_c+3] mod ℓ (h_c − x for typ = Bd).
- U_c + w_c is exactly the jump set JW.

*(Inferred)* Write x = a + (ℓ−1)m with m ≤ σ. Then x ≡ a − m (mod ℓ). So T3 makes x mod (ℓ−1) stay ≳ σ away from the window residues. This is a base-ℓ digit genericity condition: the residual characters (and mod-ℓ Sen weights) of the cloud are distinct from those of the low window, with margin.

In PD:94-108, T3 is derived from ℓ ∉ Exc. The Lean says ℓ ∉ Exc ⇒ no m in window(W0) has ℓ ∣ m (PD:97-100). Then `jump_position_conditions_at_letter` (statement only) converts this. T1 comes from 2etaSz + 8b/lStar + 7 < ℓ (PD:105). **This is the arithmetic condition defining Exc.**

**(c) TopCore** (TL2:193-212). Its hypothesis is `TopHyp` (TL2:180-191): ρ is crystalline with HT multiset U, the χ_c are crystalline with weight w_c + c − 1, and the position hypotheses hold. Then for every finite O-module X:

(1) For z a cocycle in T₀ ⊗ X twisted by χ₁⁻¹, the following are equivalent:
- z is **admissible**: for all large a, the extension of O/λ^a(χ₁) by T₀⊗X is ≅ L₁/L₂ for lattices L₂ ⊂ L₁ in a direct sum of crystalline reps with HT multiset U + block and char. poly ≡ charpoly(ρ)·Π(X − χ_c) mod λ (`AdmQ`, TL2:93-98; `IsAdmCoc`, TL2:172-178);
- z ∈ H¹_f(T₀ ⊗ X) (`InHfX`, TL2:140-151).

(2) For c ≥ 2: admissible ⇔ coboundary.

(3) For c = 1: admissible ⇔ unramified.

There is no weight-length restriction beyond PositionHyps.

**(d) Proof of TopCore** (TOP:44-82; RB:36-131; `IE/ExistsIndependentAdmissibleCocyclesResidue.lean:209-227`; `IE/AdmissibleCocyclesCardLeSumDims.lean:73-81`, all read). It is a dimension count.
- **Real.** Every residual admitted object has a model in a mod-ℓ (φ,Γ)-module category over k((X)) with cyclotomic Γ (`realD`, `real_of_presented`; statement only).
- **Vanish / FreeH.** Residual H⁰ = H² = 0, so H¹(T) is free of rank r·n (via Euler characteristic and Tate duality).
- **FSummand.** H¹_f is a direct summand of rank dsum = Σ_c #{u ∈ U_c : u < w_c}.
- **FinAdm.** H¹_f ⊆ admissible classes.
- **ResBound.** Independent residual admissible classes number ≤ dsum. This is `AdmBound.main`. Admissible cocycles are represented by Herr-complex pairs (b, g) inside a maximal residual model lattice. A Sen-weight count of that lattice uses T1–T3 and `LemmaPsi`, and gives ≤ dsum (`card_cocycles_independent_mod_coboundaries_le`, statement only).
- **Conclusion.** Admissible = H¹_f (`cls_eq_H1fX`).

*(Inferred)* T3 is used exactly to keep the cloud's residual Sen eigenvalues off the window. Then the cloud contributes no extra residual admissible classes.

**(e) Toy test (mine).** Take K = ℚ_ℓ (n = 1), t = 1, w = 1, η = 1, U = {u}, h = u + 1. Here ρ = ψ is a crystalline character of Lean weight u. The Lean convention is weight(ε) = −1 (RB:129).
- In standard weights, after twisting, the extension is 0 → ψ₀ (weight 0) → E → ψ_d (weight d = u − 1) → 0. So H¹_f(V′) = H¹_f(ℚ_ℓ(−d)) = 0, and dsum = 0 agrees.
- TopCore then says: no nonsplit residual E (sub 1, quotient ω^d·unr) is a subquotient of crystalline lattices with HT {0, d}.
- The fibre product L₁ = {(x, t, y) ∈ L ⊕ T ⊕ O : p(x) ≡ y mod λ}, with L₂ = λL ⊕ T ⊕ λ^a O, realises "for all a" as soon as one crystalline lift of E with HT {0, d} exists. So the claim is equivalent to: no such lift exists.
- Write d − 1 = d₀ + d₁ℓ. Breuil–Mézard (Kisin, Paškūnas) says a lift exists iff the Serre weight σ_{ℓ−3−d₀−d₁} ⊗ det^{d₀+d₁+1} is a JH factor of Sym^{d−1}.
- Using 0 → Sym^{d₀} ⊗ Sym^{d₁}^{Fr} → Sym^{d−1} → Sym^{ℓ−2−d₀} ⊗ det^{d₀+1} ⊗ Sym^{d₁−1} → 0, this happens only for d₀ ∈ [ℓ−2−d₁, ℓ−2].
- Then u mod ℓ = d₀ + 2 ∈ [−d₁, 0] mod ℓ, and σ ≥ d₁, so T3 **excludes it**. Example: ℓ = 101, d = 151 is allowed by T3 and has no lift (weights σ₅₀, σ₄₈⊗det, σ₅₀⊗det⁵⁰ against the needed σ₄₈⊗det⁵¹).
- The residual-character degeneracies (d ≡ 0, ±1 mod ℓ−1, which give the très ramifiée phenomenon in the other orientation) are also in the T3 range.

So the toy case agrees with known results. It does not test n > 1, r > 1, or irreducible ρ.

## 3. Children

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `UseLoc.main` | UL:24 | cut cocycles ⊆ HfD; χ_c coboundary; χ₁ unramified | zero defect | core; read (assembly) |
| 2 | `TopCore` / `TopTheoremLocal` | TL2:193, 398 | admissible ⇔ H¹_f under PositionHyps | the new comparison | core definition; read |
| 3 | `twistedLatticeCohomology_theoremTOP`, `stmtAt_of_real` | TOP:67, 44 | TopCore from Real, Vanish, FreeH, FSummand, FinAdm, ResBound | proof skeleton | core; read |
| 4 | `resBound_dsum` → `AdmBound.main` → `card_cocycles_independent_mod_coboundaries_le` | `IE/ExistsIndependentAdmissibleCocyclesResidue.lean:209`; `IE/AdmissibleCocyclesCardLeSumDims.lean:73`; `IE/CardCocyclesIndependentModCoboundariesLeStatement.lean:8` | residual admissible classes ≤ dsum via mod-ℓ Herr/Sen count | heart of beyond-FL | **core; last link statement only** |
| 5 | `realD`, `real_of_presented`, `wachLattice_usedProperties_of_admitted` | `IE/ExistsPresTensor.lean:556`; `IE/ExistsModThOfPres.lean:72` | residual models exist for admitted objects | Wach/(φ,Γ) reduction | core; statement only |
| 6 | `position_data_exist` | PD:21 | ℓ > lStar, ℓ ∉ Exc ⇒ PositionHyps with σ ≤ sgPlus | defines Exc's role | core; read; `jump_position_conditions_at_letter`, `lows_cloud_windows` statement only |
| 7 | `exactLocalConditionData_at_place`, `unramifiedEnlargement_cut_cocycles_blochKato`, `mem_finite_part_of_lift` | `IE/…Statement.lean:7` | puts the GMA cocycles into TopCore form | glue to the global setting | statement only |
| 8 | `BhattScholzeIntegral` | `Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BhattScholzeIntegral.lean:12-29` | crystalline ℤ_ℓ-lattices realised by prismatic F-crystals; full faithfulness | Published input | standard (Bhatt–Scholze 2023) |
| 9 | `excOK_at`, `card_exc_le`, `sum_exc` | EXC:32; EBA:576, 611 | Exc finite, small, ≤ 3b; charge ≤ C·Ub¹⁸ | budget | glue; read in part |

## 4. Oddities

1. **TopCore is a new theorem, not a citation.** It is a lattice-level comparison for weights up to ≈ ℓ·x^{O(1)} (< ℓ²/4). Its only conditions are residual genericity and an FL-length low window. As far as I know, the literature has results of this kind only for weights in roughly [0, ℓ] (Gee–Liu–Savitt) or for special shapes. Its correctness rests on child 4/5 (mod-ℓ Sen counting), which I read at statement level. The toy test is consistent with it. Expert check: is "Σ residual admissible ≤ #negative weights" true in dimension > 2, for inert K, with generic cloud?
2. `BlochKatoLocal` is a hypothesis of `blochKatoTop_of_localTateDuality_eulerChar` but is discarded (`intro _`, `IE/BlochKatoTopOfLocalTateDualityEulerChar.lean:28`). This is harmless.
3. The genericity mod ℓ is applied to the weights themselves, not mod (ℓ−1). By the digit identity in §2b this is the right condition *(inferred)*.
4. Crystallinity of ρ_π at w ∣ ℓ, and the shape of the weights, come from `admG2`/`admG3`/`WeightTie`. I did not open them.

## 5. Coverage

Read:
- PROTOCOL; NODE-LARGETW (all); grep of KILLAT, CONGMOD, LINKN.
- BS:1-166; APE:16-58 and Statement; DataParams:38-40.
- UL:1-54; TL2:21-31, 150-300, 398-460; HWR:1-83; ResidueAvoidanceOfPrimes (grep).
- PD:1-118 and Statement; TOP:1-84; `IE/BlochKatoTopOfLocalTateDualityEulerChar.lean` (all) and Statement.
- `IE/ExistsWachFunctorComparisonOfBhattScholze.lean` (all) and Statement; BhattScholzeIntegral (all); RationalDualityOfAllCoefficients:55-80.
- RB:1-134; MMA:20-90; `IE/ExistsIndependentAdmissibleCocyclesResidue.lean:1-30, 200-229`; `IE/AdmissibleCocyclesCardLeSumDims.lean` (all) and Statement.
- CIC:100-145; StatementTor:120-135; APJ:14-50; B23:18-30; EXC:1-140; EBA:570-625; `IE/ExistsPresTensor.lean:556-560`.

Greps:
- `UseLoc`; `exists_localPositionData_off_exceptional_primes`; `def PositionHyps|JW|JumpConditions|lStar`;
- `def (sgN|InWinN|ResidueAvoidance|GlobalTheory)`; `def (TopCore|aux₃|adm20|cutCoc|LocBound|HfD|WpO)`;
- `CaseA`; `twistedLatticeCohomology_theoremTOP`; `structure TopSit|def (Vanish|Real|…)`;
- `ResidueAvoidance|LemmaSN|FrobContractsSharp` (files list); `resBound_dsum|realD|real_of_presented`;
- `structure TopData|def T1|T2|T3|dsum|LemmaPsi`; `ExcOK`; `sorry|axiom|admit` in the key files (none; only the word "admitted").

Not opened: the bodies of children 4 (last link), 5, 7; `jump_position_conditions_at_letter`; `lows_cloud_windows`; `exactLocalConditions_topCore`; `LemmaPsi`; `admG2`/`admG3`.
