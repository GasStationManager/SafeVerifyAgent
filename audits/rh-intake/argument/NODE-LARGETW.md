# NODE-LARGETW: does the twisted-place machinery cover the live Tw = W1 (unbounded residue characteristics)?

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.
Abbreviations:
- `FLS` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/FiniteLevelAndSecond.lean`
- `EUS` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUnlocalizedSaturatedState.lean`
- `SYM` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TwistDataAgreeAcrossCoefficientsSymm.lean`
- `ABH` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AmbientBaseHeq.lean`
- `EGP` = `Formalism/SharpRestriction/LevelLetterCocycles/ExistsGoodPlacesEveryConjugate.lean`
- `EET` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsExtTwistedPlaces.lean`
- `CQF` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CmQuadraticFormEqAlternatingForm.lean`; `NBC` = `…/AutomorphicMembership/NotBaseCondFalse.lean`
- `CT2` = `Formalism/LocalToGlobal/IndefiniteReal/CutTuples2.lean`; `CSC` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConstructionStartingChoicesOfFineAdelicData.lean`
- `B23` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/BoundAtTwoThreeFamily.lean`; `TP` = `Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean`
- `BS` = `Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/BaseSizes.lean`; `APE` = `…/ThirdPlaceSeries/AdmissibleParameterEventually.lean`
- `EBA` = `Formalism/SharpRestriction/LevelLetterCocycles/ExportBoundOfAdmissible.lean`; `MPO` = `Formalism/SharpRestriction/LevelLetterCocycles/MemPrimesOverOfMem.lean`
- `IFT` = `…/ThirdPlaceSeries/ImportsFurtherTail.lean`; `RI3` = `Formalism/SharpRestriction/LevelLetterCocycles/ResidualIrreducibleOfTheoremThreePrime.lean`

## 0. Verdicts

**No ESCALATE.** The machinery is written for an arbitrary finite twisted set. Every cost at a twisted l is either zero above lStar or bounded by a summable/global quantity. The key budget inequality, `point_bound`, is proved for **every finite set S of primes** (EBA:893-1004, read).

The premise of question 2 is wrong. There is no single ψ and no CRT over the twisted l. One pack (Q_i, k_i, ψ_i) is chosen **per twist index i**, each at its own prime l_i, by an induction that only keeps the Q_i pairwise disjoint (SYM:97-120, 182-202, read).

| Q | Answer | Status |
|---|---|---|
| 1. Size of W1; circularity | **No quantitative bound on #W1 or on max resChar was found, and none is consumed.** Finiteness only: `{v ∣ TwistedAt}.Finite` (SYM:133) and W1 ⊆ {resChar ∈ T.pl}, where T.pl ⊇ P₁ and P₁ is an existential finite set fixed by the pre-chain (`large₂`, CQF:100-107). **No circularity.** W1 is computed in pass 1 with T = untw (ψ = 1). Pass 2's W1 is proved equal to it (EET:91-103 `key`; FLS:112 `hWt`). So twisting creates no new nonzero-index places. | proved and read (the glue); `nonzeroForcedContentPlaces_agree_over_enlargement` and `DatExt` statement only |
| 2. One ψ for all l? | **No.** `ExportAt` (ABH:36-40) supplies, at each index i separately, ∀ A ∃ (Q, k′, ψ′) with GoodTw at every coprime power (EGP:180-189). `nonempty_seed_of_kept` (SYM:133-210) chooses the packs one index at a time, each Q avoiding the earlier ones (`exists_disjoint_choice`, SYM:97-120). The only cost carried per index is ε = twEps = 1/l_i² (TP-TwGood:107). It enters as sPi ≤ ν_l + 1/l², tame ≤ 1/l² (KillAt, CEC:45-51), Σ ε_B ≤ 1/l² (GoodTw IdxAt, IHF:219-231) and 2/p² in ON. Σ_l log l·C/l² < ∞, and Σ_l ν_l log l ≤ log QS + log(tr) (`sum_nu_le`). Q, k′ and ord ψ are unbounded and enter no budget (as NODE-ORDER found). | proved and read (choice); GoodTw existence per l = `goodTwistExistsAllCoprimePowers`, supplied by `series_realization_of_published_alt` (not opened) |
| 3. Local lengths, large weights | Split at lStar = m·b/(n t²(N+t)L² + k n²(Sc+t+L)) (DataParams:38-40). **l ≤ lStar**: Wach/Legendre exponent eP = C(1 + hB/l + log_l hB); the total over **all** l ≤ lStar is ≤ 1000(C+1)³·f·m·b·L² (`sum_small`, EBA:18-19). **l > lStar, l ∉ Exc ∪ {g₀, g₁}**: `CongBound_at` (BS:87-95) has **no local-at-l term**: vcc ≤ sPi + Ш + v_l(h_E) + epsQ, for every such l, unbounded. **Exc** = primes > lStar dividing an integer in short windows around the base sizes (BS:21-32). It has ≤ (|TT|+2)(Sc + 3η + t + 8b/lStar + 9) elements, each ≤ 3b (B23:25-27), and is paid by `sum_exc`. l = 2, 3, small: midF. l ∈ {q, d}: midG, with q, d ≤ lStar. l = g_k: StarH. For l > lStar the host is unramified at l (APE:23) and t+1 < l (statement of `exists_localPositionData_off_exceptional_primes`). | point_bound and the case split read; `CongBound_at` proved (`NLinkE.main_alt_alt`, APE:30-58, read), but its local input (`UseLoc.main`, the position data, the Wach comparison) was read at statement level only |
| 4. Residual irreducibility | Yes. For every local index i, whatever l_i is: if l_i ∈ BB(r, g₀) then l_i ∉ BB(r, g₁) by disjointness, and `irreducibility_of_good_tuple` is applied at that g_k (RI3:173-215, read). Nothing restricts l. | proved and read (glue); good-tuple body not read |

## 1. Statement

The question is: given the live MuDef (CT2:188-198, read; Tw ⇔ W1, where W1 = nonzero untwisted index, dual index or F0), do the following hold at **every** twisted local index i, with no bound on l_i?
- KillAt (CEC:45-51, read: ∀ i with TwLoc);
- GoodTw (IHF:219-231, read);
- residual irreducibility;
- the ConclF/LinkN local bounds.

Each of these hypotheses is quantified ∀ i with TwLoc D i (TP:77). None carries an "l ≤ X″" guard.

## 2. Argument

**(a) Order of construction (Q1).**
1. Pass 1 has T = `TwDat.untw B pl` (CQF:196-200, read: Q = ∅, k = 0, ψ = 1, with pl free).
2. `FirstG`/`ExportF`/`Pass` (NBC:53-66, read) are `EvLgG` statements. They hold for every T with P₁(pre-chain, fields) ⊆ T.pl (`large₂`, CQF:100-107).
3. `untwisted_adelic_data_saturated_over_fixed_field` (statement read) produces z with W1(z) ⊆ {resChar ∈ T.pl}. `exists_pre2_of_fine_of_resChar_mem` (CSC:195-237, read) then sets Wt := W1.
4. The seed is chosen from the pass-1 export (FLS:85-87).
5. Pass 2: `exists_ext_twisted_places` (EET:82-112, read) builds z′ over (B′, T′). It proves v ∈ Wt ⇔ v′ ∈ z′.W1 for v below v′ (`key`, EET:91-103). That uses `hExt.W1` (from `DatExt`, CoefAEqOfHeq:171-175) for the index/dual-index part, and `nonzeroForcedContentPlaces_agree_over_enlargement` for the F0 part.
6. FLS:112 transports this to P′.Wt.

So the set is fixed before the twist. The twist is trivial off W1 (`TwFrom`, EUS:89-98), and the pass-2 nonzero-index set is the same set.

**(b) Per-index choice (Q2).**
1. For each twisted r, `key` (SYM:146-168) moves the pass-1 per-index existence `hp` to D₁.
2. For each index i, `hch` (SYM:182-190) gives a pack whose Q avoids A(i) ∪ B.
3. `exists_disjoint_choice` (SYM:97-120) inducts over the finite image s(twisted places) and makes the Q_i pairwise disjoint (`Seed.sep`, EUS:79).
4. The l_i are never combined. *(Inferred)* Chebotarev is used separately at each l_i, inside `goodTwistExistsAllCoprimePowers` (KILLAT §2).

**(c) Budget over an arbitrary twisted set (Q2, Q3).**
- `export_bound_of_admissible` (EBA:1023-1054, read) is the live supplier: `LinkFam.main` (LinkNAlongFamilyOfLocalBounds:11-17, read) → `stmtF_holds` (EBA:1160).
- It sets S := resChar(twisted places in L.supp) (EBA:1033) and applies `point_bound` (EBA:893):

  6 + nuBudget + log h_E + log|G| + Σ_{l∈S} log l·lamG(l) ≤ 2000(C+1)³·f·m·b·L²  for every finite set S of primes.

- lamG(l) (MPO:259-263, 528-529) takes these values:
  - l ∈ gset: C x^C η;
  - l small or l = 3: midF;
  - l ∈ {q, d}: 2C f m b;
  - **l > lStar and l ∉ exc: 0**;
  - otherwise bbB + lenB(l).
- The proof (EBA:905-1004) splits S into five classes and bounds each class by a lemma that holds for any subset: `sum_g`, `sum_23`, `sum_qd`, `sum_small`, `sum_exc`.
- **Arithmetic check.**
  - Σ_{l≤lStar} log l·bbB ≈ lStar·C f n t² nV L² ≈ C f m b·nV/(N+t), using the definition of lStar. This is O(f m b), inside f m b L².
  - Σ_{l≤lStar} log l·lenB ≈ f m(θ(lStar) + hB log lStar + …) ≈ f m b L.
  - The exc sum is ≤ 1.164·10⁶(C+1)² Ub¹⁸, and Ub¹⁸ ≤ b (`U_pow_eighteen_le_b`, `big_le_b`, EBA:501-550: x^{O(1)}·e^{18x^{ε/4}} ≤ e^{x^ε}).
  - None of these terms depends on #S or on max S. The sizes r ≤ x⁵ and Y = (k e^{x^ε})⁸ enter only the choice of g₀, g₁ (NODE-ORDER §2b), which is independent of W1.
- `StarE` (B23:21-23) and `LargePrimeLengthVanishing` (TP:196-200) provide the zero above lStar. They come from `CongBound_at` via `RowE.main` (LocalBoundZeroAtLargePrimesOfCongruenceBound.lean:100-172, read). The ν, ε, Ш and v_l(h_E) pieces are summed globally: nuBudget, log h_E, Σ' vvTerm.

**(d) Residual irreducibility (Q4).** `theorem_three_prime_holds` (RI3:173-215) case-splits on l_i ∈ BB(r, g₀). BB(r, g) is finite: it is {g} together with primes l with l^{4 v_l(g^d − 1)} > g^d. Disjointness (from `typePrimesN`, NODE-ORDER) therefore covers every prime, including l > g^r and l = g_k.

## 3. Children

| # | Name | file:line | Statement | Role | Weight |
|---|---|---|---|---|---|
| 1 | `point_bound` | EBA:893 | Σ_{l∈S} log l·lamG ≤ 2000(C+1)³ f m b L², for every finite S | uniform budget over twisted l | core; proof read |
| 2 | `CongBound_at` ← `NLinkE.main_alt_alt` | BS:87; APE:30 | for l > lStar, l ∉ Exc ∪ {g_k}: vcc ≤ sPi + Ш + v_l h_E + epsQ | zero local cost at large l | **core**; assembly read; `UseLoc.main`, `exists_localPositionData_off_exceptional_primes`, `exists_wachFunctor_comparison_of_bhattScholze` statement only |
| 3 | `nonempty_seed_of_kept`, `exists_disjoint_choice` | SYM:133; SYM:97 | per-index packs with disjoint Q | twist choice | glue; read |
| 4 | `goodTwistExistsAllCoprimePowers` (inside ExportAt) | EGP:180; ABH:36 | ∀ A ∃ (Q, k′, ψ′) with GoodTw at index i | per-l Selmer killing | core; supplier `series_realization_of_published_alt` not opened (see NODE-KILLAT) |
| 5 | `exists_ext_twisted_places` (+ `DatExt`, `nonzeroForcedContentPlaces_agree_over_enlargement`) | EET:82 | pass-2 W1 = pass-1 W1 | no new twisted places | read; the two inputs statement only |
| 6 | `theorem_three_prime_holds` | RI3:173 | ρ̄ is absolutely irreducible for every l_i | Q4 | read (glue) |
| 7 | `sum_small`, `sum_exc`, `card_exc_le` | EBA:18, 611, 576 | sums over l ≤ lStar and over Exc | arithmetic | statements read, bodies partly |

## 4. Oddities

1. **The real large-l content is the zero local defect for lStar < l ≲ b.**
   - HT weights are ≈ hB ≥ b, while lStar ≈ b/x^{O(1)}. So for primes in (lStar, b) ∖ Exc the weights far exceed l, which is outside the Fontaine–Laffaille range. Yet `CongBound_at` claims no local-at-l term there.
   - Its justification is the "position data": weights placed in short windows around a few base sizes, with l dividing no integer in those windows. It is supplied through `UseLoc.main` and a Bhatt–Scholze/Wach comparison. I read these at statement level only.
   - This is a non-standard local claim and the place for expert scrutiny. It is uniform in l, so it is **not** a W1-coverage gap.
2. The NODE-KILLAT budget "Σ_{l≤lStar} … ≈ f m b L, inside by a factor L" is confirmed, and it is independent of W1: `sum_small` sums over all l ≤ lStar.
3. The unit-GMA route (`CutCoreUnit.main`, which needs t < l; NODE-LINKN oddity 1) is available at every l > lStar, because the position statement gives t + 1 < l there.
4. No explicit bound on #W1 or Σ_{W1} log N v exists. A reader expecting one ("bounded height") will not find it. The design makes it unnecessary.
5. `pde`/`pde′` are not excluded in `CongBound_at`. I did not check how a twisted l = pde above lStar is handled (via δ′), but no clause excludes it.

## 5. Coverage

Read:
- PROTOCOL; NODE-TWSET, KILLAT, ORDER, TWIST, LINKN, CONGMOD, VWIN (all).
- CT2:180-206; CSC:185-237 and its Statement file.
- FLS:1-128; EUS:55-118 (Seed, TwFrom, MvB); ExistsSeed.lean (all); SYM:60-212.
- ABH:20-60; EGP:170-190; DataN.lean:440-470; TwGood.lean:85-120.
- CQF:70-107, 190-200; NBC:47-70.
- StartStateUntwistedEmptyLocal.lean:18-63; UntwistedAdelicDataSaturated…Statement:11; EET:1-112; CoefAEqOfHeq:171-175; PositionOfIntro:50-80.
- B23:1-147; TP:14-60, 155-245; DataParams:30-50; BS:1-95; JumpDictionary:95-125.
- LocalBoundZeroAtLargePrimesOfCongruenceBound(+Statement):100-175; IFT:20-110; AdmissibleParameterEventually(+Statement):20-58.
- EBA:1-30, 495-560, 893-1083 (and its declaration list); MPO:249-263, 528-529; LinkNAlongFamilyOfLocalBounds(+Statement).
- RI3:160-219; AdmissibleThreePrime:54-62; CEC:45-51; IHF:219-231; ExistsLocalSlotData…Statement:11.

Greps run:
- `exists_pre2_of_fine_of_resChar_mem`; `nonempty_seed_of_kept`; `def ExportAt|def twEps|def NonzeroIndexPlace|def TwistedAt`; `goodTwistExistsAllCoprimePowers`;
- `LargePrimeLengthVanishing|def lStar|StarE`; `CongBound_at|WeightParam`; `eventually_congBound_of_facts`; `NLinkE`; `LinkFam`; `def lamG|def lamB|def admitted`;
- `sum_nu_le|epsL_sum`; `exists_ext_twisted_places`; `def DatExt`; `def StepW`; `def EvG|EvLgG`;
- cardinality greps `(Tw|W1|Wt|twPl|TwPl).(n)card` (only `twPl.card ≤ 2` in an auxiliary construction, `IntertwinersExistScalarUpdateInvariant.lean:266`, not the live set).

Not opened:
- bodies of `UseLoc.main`, `exists_localPositionData_off_exceptional_primes`, `exists_wachFunctor_comparison_of_bhattScholze`, `series_realization_of_published_alt`, `nonzeroForcedContentPlaces_agree_over_enlargement`, `datExt_of_hypotheses`, `sum_bb`/`sum_eP`, `irreducibility_of_good_tuple`.
