# NODE-E1LOOSE: three loose ends on E1 (theta-image index) and the determinant identity

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled or run.

Abbreviations (new; others as in NODE-INDEXBUDGET / WHERECONG / LIVEMULT):
- `RIC/` = `Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/`
  - `JWM` = `RIC/JWMggWMem.lean`, `LQD` = `RIC/LevelsQDesc.lean`, `AMO` = `RIC/AlgebraMapOlInjective.lean`, `REZ` = `RIC/RestrictionEqZeroIffMemVanishingFiltration.lean`, `FLP` = `RIC/FirstLengthLePrimeBound.lean`, `LPF` = `RIC/LiftIndexPowFourLeDegree.lean`, `TSL` = `RIC/TheoremZeroSplitOfLocal.lean`, `LSD` = `RIC/LogSupSumLeOfNonvanishingDetLimit.lean`, `TZB` = `RIC/TheoremZeroBundledOfLift.lean`, `TZL` = `RIC/TheoremZeroBundledOfLengths.lean`, `WPS` = `RIC/WeightedPrimeSumBound.lean`
- `BLB/` = `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BaseLengthBound/` (`TSG` = `TaylorSpanGeneratorsAlt.lean`, `ASM` = `Assembly.lean`)
- `HT/` = `ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/` (`HAR` = `HtArith.lean`, `DPR` = `DiscProduct.lean`, `HDB` = `HDiscB.lean`, `HDA` = `HDiscA.lean`, `HAG` = `HDiscAG.lean`, `HDD` = `HDiscDefs.lean`, `HIE` = `HeightIntegralEstimates.lean`)
- `WA` = `Formalism/SharpRestriction/Divisibility/WeightAlgebra.lean`; `WFm` = `Formalism/SharpRestriction/Divisibility/WeightFamilies.lean`
- `ONL` = `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `IWD/` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/`; `CPI` = `IWD/ColumnParamsInstanceData.lean`; `RFZ` = `IWD/ReFaceZeroPartConventionsChosenAgain.lean`; `SZP` = `IWD/ScalarsZeroPartConventionFixedPlace.lean`; `PAU` = `IWD/PartAtUpdSReFace.lean`
- `QRP` = `Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/RecursivePageLatticeBound.lean`
- `HDL` = `Development/AbelianVarietyTheory/Proofs/HeightProofs/HeightInequalityDefiniteLiftIndex.lean`

Status tags: **[proved, read]**, **[proved, stmt]** (the proof exists, but I read only the statement), **[hyp]** (a hypothesis passed down), **[not found]**.

## 0. Verdicts

**No ESCALATE.** All three loose ends close.

| | Answer |
|---|---|
| **A** | (1) There is no curve in the geometric sense. The object is the generic 0-dimensional complete intersection Z = {s₁ = … = s_d = 0} ⊂ D(s₀) (d = dimY), cut out by d+1 *generic* linear combinations s_i = Σ_k T_{ik}w_k of the weight-wL forms. It lives over the Gauss-valuation DVR O_λ(T) := O_λ[T]_(λ) (AMO:14-24, 182-183; REZ:123, 201, 230, 235). Relative to Spec O_λ(T), its integral closure is an arithmetic curve. The binomial factor arises because the restriction map sends a weight wF+T·wL form to its Taylor jet of order < a0 = T−d along Z (REZ:281-282, 372-373). That jet module is filtered by J^k/J^{k+1}, and the pieces sum to #{α : \|α\| < T−d} = C(T−1,d) copies of the sections on Z. Hasse derivatives in the generic coefficients T_{ik} pick out each graded coefficient integrally, up to a unit (`TaylorHasse`, `Column`; TSG:30-36, 52-57). So each copy costs at most Ila. **[proved, read at the top; bodies of `taylorHasse_holds`, `filtration_length_bound` not opened]** (2) The local inequality is 2·Ila ≤ ord_λ Δ + 2·N_λ(ta′) − t (HAG:28-32, 55-57; HDA:20-23). Here N_λ(ta′) = Σ_{w\|λ} f_w·ord_w(ta′) is the λ-part of the divisor of one auxiliary nonzero weight-wF section ta′. The term t ≥ 0 is the order of the discriminant of the integral closure, and it is dropped in the favourable direction. Globally Σ_λ N_λ·log Nλ is the finite part of the height Hgt(ta′) (DPR:26-29). **[proved, read]** (3) The global bound is an exact product formula for Δ = a/b (DPR:21-131), followed by Hadamard. The size arithmetic closes, and with **large slack**: the index part of r(λ) is ≲ rk·f·m·b·de2·O(1/PPv) + rk·b/T, well below the allocated rk·f·m·b·de2. The tightness of E1 lies in its other pieces, J0 (`EJ ≤ 32·x^ε·f·m·b·L`) and the bad-place constants (ONL:765-866), not in the discriminant budget. Two corrections: (i) the live instance uses **Bx = 0** (LPF:291, 309), so the T-floor is PPv⁴·dimY³·k·f/(m·de2) with no x^{Bx}; (ii) the CM lower bound is paid at weight \|ka\| ≈ CK·k·f·b (≫ x·b), but only by rz ≤ 44·dimY²·rk/T "deep" forms. That is how it avoids swamping f·m·b (§2A.3). |
| **B** | **ON does not use DIVinN, and there is no circularity.** The live ON producer `onto_path_alt` introduces the DIVinN premise as `_` and never uses it (TPS/OntoPath.lean:23). Its nine inputs (TPS/OntoPath.lean:18-19; TPS/OntoXOfPrints.lean:28-46) mention neither DIVinN nor LinkN. `ev_prem` is a pure logical wrapper: it turns p → ∃C… into ∃C, Ev(p → q) by case split on p (`Development/AbelianVarietyTheory/Proofs/DivisorProofs/PartitionSelectionEvaluation.lean:12-19`). In the other direction, the LinkN, VWin and DIVinN producer files do not mention SurjectiveOntoX, ON, BoundsMu or HasIndexBound (grep, §5). DIVinN is produced at `topDesWin` (`Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:29`) from LinkN, HypV and SmallLevelRankEq only. **Correction to WHERECONG §3.** E1 is free of the *congruence* pieces, but its J0 part is not free of Galois input. ON takes `ExponentStatement` (TPS/OntoPath.lean:60, 74), and that is supplied from CuspUAlt (Galois representations of polarised cuspidal forms), BaseChangeDefiniteUnitaryGroup, Bhatt–Scholze crystalline lattices and Chebotarev (TPS/OntoXOfPrints.lean:45). |
| **C** | **All three links trace, and the identities are carried correctly.** (i) The transport keeps **κ = R.kap** literally (RFZ:30; CPI:155 `rfl`). It replaces λ by `zeroLam` (SZP:94-95), which agrees with λ wherever the relevant eigenspace is nonzero. The Rallis identities thmB/thmA/GalD are *re-proved* for the new datum by congruence lemmas, and these are trivial on zero subspaces (PAU:24-48, 44-64). Lattices and maps are unchanged (`updS` = `{R with lam3 := lam}`, `upd6 R.kap R.lam` = R; `Formalism/LocalToGlobal/IndefiniteReal/WeakCharacterisationWithError.lean:60-61`, `…/LinksStage.lean:205`). `reFace` changes only the definite-side fields (Dc, Sp, Zsc) (`…/StableIffCarrierEq.lean:55-57`). (ii) The point record's Holds originates in `primRows3_of_parts`. The chain is `holds_of_ties_alt` (LTD `RationalDataSizedFamily.lean:12-27`, `.prim := h.1` from `primRows3_typesSep3_alt`), then WeightCaseCondition, then the starting record field (`IWD/ConstructionStartingChoicesOfFineAdelicData.lean:217, 233`). Later records carry it by `holds_tr`, a relabelling transport whose statement I read. (iii) selI = (σ …).B.Q for the **one** raw selection σ that `classSel` returns. That same σ carries both hPA and rRows (TPS/ShapeOf.lean:25; TPS/ColumnChoiceWithTies.lean:61; TPS/NonemptyHypsOfAllRows.lean:40-63). hPA for that σ comes from `of_wit_alt` over linked bundles (TPS/HermWCellLastMulMulVecEqOfInWb.lean:20-32). |

## 1. Statements

**A. Objects** (all read):
- O_p = `Op X la N` = the localisation of O_λ[T_{(i,k)} : i ≤ d, k < N] at the Gauss prime. It is a DVR with uniformiser the image of ϖ_λ (AMO:14-24, 31, 46-53). K_p = Frac(O_p) = K_λ(T). R_p = K_p ⊗ (forms at λ) (AMO:55, 77).
- s_i = `sec i` = Σ_k T_{(i,k)}·w_k, the generic linear combinations of the N short weight-wL forms (AMO:182-183). secPow(α) = Π s_{i+1}^{α_i} (AMO:188).
- Lw = R_p[s₀⁻¹]. Frac0 = its weight-0 subalgebra. Jid = (s₁/s₀, …, s_d/s₀). OsK = Frac0/Jid (REZ:123, 165-167, 201, 230, 235). *(inferred)* With d = dimY = f·(pq + C(p,2) + C(q,2)) (WFm:54-56), the dimension of the product of f flag-type unitary Shimura varieties, OsK is the coordinate ring of a generic 0-dimensional linear section, a finite K_λ(T)-algebra.
- WK(wF, a) = HK(wF)/J^a·HK. These are weight-wF sections on D(s₀) modulo the a-th power of the ideal of Z, i.e. jets of order < a along Z (REZ:281-282). The map ρ_K: F ↦ F/s₀^T sends weight wF+T·wL forms to WK (REZ:360-373).
- `LenBase` (FLP:17-22): len_{O_p}(AA_T / ⟨ρ_K(w^α s₀^{T−\|α\|} th′_i) : \|α\| < a0, i < del⟩) ≤ C(T−1,d)·Ila. Here AA_T ⊆ WK is the integral (ballO) part. It is proved, closed: `lenBase_all` → `length_base_t0` → `lenBase_holds` → `lenBase_of_taylorHasse taylorHasse_holds` (TZB:9-11; BLB `LenBaseHolds.lean:10-13`; ASM:27-37).
- `localIdx` (JWM:70-145): idx_λ(M_ka ∩ U, Θ ∩ U) ≤ e·dim U + C(T−1,d)·T·cp·Σ_ζ e_ζ f_ζ v(ζ) + C(T−1,d)·Ila + gaussC(zc, λ) + len_λ(Qm/⟨th_i⟩). The proof is one application of the abstract `levelsQDesc` (LQD:9-42) with ρ = the jet map, Zm = ker ρ (`ker_rhoN`), len(Zm/Zl) ≤ gaussC (`len_Zm_le`), hA = LenPole and hN = LenBase.

**A. Local discriminant** (`disc_at`, HAG:28-112, read):
- g_c is a local multiplier with ord_w(g_c) = ord_w(ta′) at every place w | λ of the c-th component (HAG:44-46). The admissible set is {y : g·y integral} (HAG:47-51).
- `HDiscLat.lattice_main` gives disc(b)·Π N(g_c)² = unit·ϖ^{2nn+t}, where nn = len(admissible span / span b) = Ila (HAG:55-57, 66-71).
- Hence ord_λ Δ = 2·Ila + t − 2·N_λ with N_λ = Σ_c Σ_{w\|λ} f_w·ord_w(ta′) (HAG:58-60, 78-112). Here Δ = det[Σ_c Tr(b_k b_l)] (HDD:28-32).

**A. Global** (`disc_product`, DPR:21-29, read): an exact identity

  [K:ℚ]⁻¹·Σ_λ (ord_λ Δ + 2N_λ)·log Nλ = mean_σ(mSgP_σ(a,b) − 2N_σ) − h₀(Ω) + 2·Hgt(ta′),

for Δ = a/b with a, b ∈ K[T] and Ω·b·V² = a·U² (DPR:72-76). It is the product formula for Gauss norms of polynomials (DPR:44-47, 95-103), with the archimedean side as a sphere mean, i.e. a Mahler measure (DPR:104-108).

**A. `disc_global`** (HDB:24-82, read): the left side above is

  ≤ del·log del + 2Σ_k mean_σ log sup_σ(th′_k) + 2D·aG·(log(N+1) + ½) + 2·Hgt(ta′).

- Hadamard (`disc_hadamard`, HDB:62) bounds mSgP − 2N_σ.
- `sphere_height_lower_bound` gives −h₀(Ω) ≤ 2D·aG·(log(N+1) + ½) (HDB:71-80). This is a standard lower bound for the height of a nonzero polynomial, not a CM input.

**A. `heights_arith`** (HAR:7-130, read): pure real arithmetic. From the chain h7a/h7b/h7c (auxiliary heights HL, Hde, HF) and hdi/hdn it yields

  2·SI ≤ δ·log δ + 2·Ssum + (8/3)·D(D+4)·δ·Prw·L + 2(D+4)(D+1)·δ·(2G + 6PH)·L,
  SN/i ≤ g₀·((D+1)·δ·(2G + 6PH)·L + (4/3)·D·δ·Prw·L) + δ·Pet,

with D = dimY, δ = del, L = \|wL\| and PH = 2(PP0′ + PN + … + Prw) + G. **Every term other than δ log δ and Ssum is ∝ δ·L.**

**A. Top layer:**
- `theorem_zero_of_named_inputs` = `theorem_zero_split_of_lengths lenBase_all lenPoleL_all` (TZB:18-19; TZL:18-20).
- It proves `Conclusion1OfComb` (WPS:117-142), which is the *same* statement for every 1 ≤ j ≤ m with β = rk·f·m·b·de2. QAt is needed only for j < m. At j = m, rq = 0 (TSL:62-68).
- It is applied at I4R:47 with the Heights from `heights_definite` (HDL:288). That proof builds the same `Data` record. Its CM input is `HtLAM` at weight n96·wL: meanLogSup(g) ≥ −PP0′·n96·\|wL\| for nonzero integral combinations of n96-fold products of the w's (HIE:106-110). `LamConst` (`Formalism/LocalToGlobal/ProjectiveLattices/AxHLAM.lean:69-70`) requires PP0′·n96·\|wL\| ≥ PP0·(1 + log(n96·\|wL\|))·n96·\|wL\|.

**A. QAt supplier** `qAt_run` (QRP:35-62, read):
- It is closed, modulo `quotientBound_of_kill_detect_constantRoom`, `cmFamilyFunctionals_detect_lowCoefficients` and `arithmeticCMKnownTheorems_proof` (**[proved, stmt]**: `…/ThetaShiftProofs/*Statement.lean:9-10`).
- *(inferred)* Mathematically it is a Siegel-lemma bound: CM-point functionals detect the low Fourier–Jacobi coefficients that MggK kills.

**B. Objects:**
- `IndefiniteRealisationConstantBounds.onto : hN → ON` (TPS/IndefiniteRealisationChoice.lean:72-82). It is instantiated with hN := DIVinN Fm (:94).
- `SurjectiveOntoX` := Closed FamHyp (fun Fm CH ⇒ DIVinN Fm → ∃C0, eventually, More p → ∀C ≥ C0, ON) (TPS/ExportSt.lean:47-48).

**C. Objects:** `twArgs_exists` (CPI:153-169); `reFace_zero_parts` (RFZ:17-35); `zeroLam` (SZP:94-95); `HypsAlt.hPA` (TPS/Hyps.lean:32-33).

## 2. Argument

### 2A. The discriminant budget as a paper proof

**A.1 The section and why only C(T−1,d) is lost.**
1. Choose N short forms w_k of weight wL with no common zero (`Column`: at every point ζ of the integral model some w_k/s₀ is a unit; TSG:52-57).
2. Take d+1 generic combinations s_i = Σ T_{ik}w_k over K_λ(T) (AMO:182-183). The ring K_λ(T) has the Gauss DVR O_λ(T), whose residue field is k_λ(T), so reduction mod λ of a generic choice stays generic.
3. Any weight-(wF + T·wL) form F gives F/s₀^T ∈ HK(wF). Its class in WK(wF, a0) = HK/J^{a0}HK is its Taylor jet along Z of order < a0 (REZ:281-282, 372-373).
4. Filter WK by J^k. A class in J^k has a Taylor representation x ≡ Σ_{\|α\|=k} (s/s₀)^α·cf_α mod J^{k+1} (`TaylorRep`, TSG:24-28).
5. The Hasse derivative ∂^{(α)} in the variables T_{·,jj} applied to x reduces on Z to (w_jj/s₀)^α·cf_α (`TaylorHasse`, TSG:30-36). Hasse derivatives of integral elements are integral for the Gauss valuation, and some w_jj/s₀ is a unit at each point (`Column`). Hence integrality of x forces integrality of each cf_α on Z.
6. So the integral jets form a direct sum of C(T−1,d) = #{α : \|α\| < T−d} copies of the integral sections A0 of Z (`monoCount_holds = sum_antidiagonalTuple`, ASM:25). Each copy has index ≤ Ila relative to the span of the th′_i.
7. The kernel of the jet map, Zm (forms vanishing to order ≥ a0 along Z), is handled separately. It is the zK/detPoly piece gaussC (`ker_rhoN`, `len_Zm_le`; JWM:111, 139).
8. Pole orders are the Net/LenPole piece.

This is a "generic hyperplane section + Hasse derivative" argument, not Noether normalisation with a lossy restriction. The loss is exactly the number of monomials, and ShareRd (proved, NODE-MIRABOLIC §2d) makes C(T−1,d)·del ≤ rk.

**A.2 The local inequality.** At λ:
- Let ta′ be a nonzero weight-wF section and g_c an element with div_w(g_c) = div_w(ta′) for every w | λ (HAG:44-46).
- The admissible lattice is A = {y : g·y integral over O_λ(T)}, and b_k = restricted th′_k ∈ g⁻¹·O. Then

  disc(b) = [A : ⟨b⟩]²·disc(A) and disc(A) = N(g)⁻²·disc(O_int),

  hence ord_λ Δ = 2·Ila − 2·N_λ(ta′) + t with t = ord_λ disc(O_int) ≥ 0 (HAG:55-60, 105-112).
- The "correction" is +2·N_λ(ta′), the λ-adic divisor of one auxiliary section on Z. It is small because Σ_λ N_λ·log Nλ is the finite part of the Faltings-type height Hgt(ta′) of that one section. It is bounded by `h_seven` and `sum_logHeight_upper_bound` in terms of sup norms, the CM lower bound (HtLAM) and log(N+1). Every one of those terms is ∝ del·\|wL\| (HAR:22-27).
- Dropping t ≥ 0 is the correct direction.

**A.3 Global bound and size arithmetic.** Let R = C(T−1, D), δ = del, d = rk M_ka, D = dimY, L = \|wL\|, κ = \|ka\|, F′ = \|wF\|, PP = PPv. Combining HDB/HAR with `sumGP4`/`pvs_core4` (LPF:141-158, 289-403), the bound to prove is

  R·(ΣIla + T·c/(2·iet)·ΣNet) + rz·p·κ + 2·rq·PPv·κ ≤ d·f·m·b·δ₂.

The inputs:
- 2A ≤ δ·lδ + 2SS + c₁D²δPH·L, with SS ≤ δ·G·F′;
- F′ ≤ (D+2)L + 5fr²T and T·L ≤ 2κ (H4, WA:398-399);
- κ ≤ CK·k·f·b (SetC, WA:351);
- Rδ ≤ d (ShareRd);
- rz ≤ rq + 22D²d/T and rq ≤ 22D²d/T (ShareRho*);
- PP³T² ≤ b (H4, WA:400);
- **T ≥ PP⁴·D³·k·f/(m·δ₂)** (H3 with Bx = 0, LPF:291, 309; WA:417).

Term by term, as checked by hand against LPF:199-285:
- **weight terms of A**: R·δ·(G(D+2) + D²PH)·L ≤ d·(…)·2κ/T ≤ d·(…)·2CK·k·f·b·m·δ₂/(PP⁴D³kf) = d·m·b·δ₂·O(CK/(PP³·D)).
- **the T-proportional term of A** (5G·fr²·T from F′, together with δ·log δ ≤ d·Pd·T, LPF:278): ≤ d·PP³·T ≤ d·b/T, since PP³T² ≤ b (ps0, LPF:254-268). This is ≪ d·f·m·b·δ₂.
- **CM lower-bound term** (deepC, TSL:13-34):
  - Cd = rz·(2Gc + Prw + PP0(1 + log κ) + 1.5(Pd + PO))·κ, the cost ρ·log Bop of `deepCore` (LSD:590-641).
  - Bop comes from LAMwAt through `transference_successive_minima` (TSL:32). *(inferred)* A nonzero integral form has sup ≥ e^{−pκ}, so the dual coordinate functionals have norm ≤ e^{pκ}·poly.
  - Sign: this is a positive cost in an *upper* bound for Σ gaussC·log N, which is correct.
  - Size: Cd ≤ d·44·PD·D²·κ/T (LPF:199-206) ≤ d·44·CK·m·b·δ₂/(PP³·D), and with 4·CK ≤ PP²·f (hCK) this is ≤ (11/(PP·D))·d·f·m·b·δ₂.
  - **Answer to the brief's worry.** The weight here is κ ≈ CK·k·f·b, not a = x·b, and the per-form cost p·κ is ≫ f·m·b. But only rz ≲ 44D²·d/T forms pay it, and T ≥ PP⁴D³kf/(mδ₂) cancels the k·f in κ. The heights-side CM input (HtLAM) is paid at weight n96·\|wL\| per unit of del·\|wL\|, i.e. with the same 1/T dilution.
- **QAt term**: 2rq·PPv·κ ≤ d·44·PPv·D²·κ/T, the same order as Cd.
- **Net term**: T·c·g₀ ≤ 1 (H3) makes it ≤ R·δ·(poly·L + Pη) ≪ d·f·m·b·δ₂.

So the proved index remainder is Σ_λ r·log Nλ ≲ d·f·m·b·δ₂·max(O(1/(PP·D)), 1/(T·f·m·δ₂)): **slack is a positive power of x**. The constant-level closure lemmas `levels_real`, `total_le_of_bounds` and `four_term_sum_bound_of_parameters` were not opened, but every dominant term above is visible in LPF:188-285.

The *allocation* is what is tight:
- ON charges 2·Rb/(\|U\|·D) with Rb = 2·nZ·f·m·b (ONL:765-772, 846-848). That is the "+12" inside (4C² + 25C + Cb + 12)·x^ε·f·m·b·L + EJ, with EJ ≤ 32·x^ε·f·m·b·L, all ≤ CE·E1u (ONL:829-864).
- Over m layers the total is ≈ f·m²·b·x^{O(ε)} ≈ x^{3+O(ε)}·b, which is budget size as in NODE-ACCOUNT.
- Of the E1 constants, the J0 term EJ (coefficient 32) and the bad-place constants C, Cb fill the allowance. The discriminant budget's real share is smaller by a power of x.

**Parameter sanity** *(inferred, using NODE-ACCOUNT sizes)*:
- f ≈ 2x^{2+8ε}, r ≈ k ≈ x^{4.5}, so D = dimY ≈ f·r²/2 ≈ x^{11}.
- Zb = f·r·L ≈ x^{6.5}, PPv = C·Zb^A, and log dim S_ka ≈ D·log κ ≈ x^{11+ε} must be ≤ Pd ≤ PP, so A ≥ 2.
- The window PP⁴D³kf/(mδ₂) ≤ T ≤ √(b/PP³) is nonempty for large x, because b = e^{x^ε} is superpolynomial.

### 2B. DIVinN premise on ON: unused, and no cycle

1. W4F supplies `ra.onto hN` with hN : DIVinN (NODE-WHERECONG). The record field comes from `row_rRows_of_parts_alt`. That theorem receives `Ind.EvWC (fun Fm => DIVinN Fm) summandNormBound` and strips it with `ev_prem` (TPS/RowRRowsOfParts.lean:21-36, 57, 61).
2. EvWC p q means "p Fm → ∃C₀, eventually q" (`…/Divisors/BaseRankDimension.lean:90-91`). `ev_prem` only moves the implication inside (PartitionSelectionEvaluation.lean:12-19). It neither discharges nor uses p.
3. The EvWC is produced in `row_rRows_stage0_alt` (`TPS/TupAllUsedAtPart.lean:46-64`). The chain is `eventually_norm_bound_of_more_points hOnto` (:64) → `onto_at_chosen_alt` (TPS/OntoAtChosen.lean:13-18), which threads the premise into SurjectiveOntoX generically.
4. SurjectiveOntoX is proved by `onto_x_of_all_estimates` = `onto_path_alt`. There, `intro eps Fm CH _ H _`: the last `_` is the DIVinN hypothesis, discarded (TPS/OntoPath.lean:22-23). The remaining body (:24-76) uses only Runs, Rationality, Geometric, RankAtPlaces, Twist, Share, BadPlaces, Exponent and Page.
5. The producer of these nine is `ontoX_of_hypotheses_alt_alt` with Published inputs + CuspUAlt + RecTExists (TPS/OntoXOfPrints.lean:28-46). It is reached at the root through `ontoX_and_lamLow_of_unitaryGroupHypotheses' P` (TPS/HypothesesNonemptyOfUnramifiedExponents.lean:44; `TPS/SurjectiveAndLowWeightOfUnramifiedExponents.lean:16-19`).
6. In the same root theorem, LinkN is produced separately: `hNrow := final_alt_alt P.nLink prN … hN` (:47-48). Its type `NLink.Final.mainTheorem` has no ON or SurjectiveOntoX argument (TPS/MainTyzTer.lean:22).
7. DIVinN is formed only in `topDesWin` from aN (LinkN), aZ and hV, and consumed by aD (LinkDIVt) (DesWin.lean:11-31). LinkN is an independent field `hN` there.

So the dependency is one-way (Galois side → E2 only), and E1's index bound is unconditional. The type `DIVinN → ON` is a vacuous strengthening of the hypothesis.

### 2C. The witness links

**(i) Transport in `twArgs_exists`.**
- The lemma (RFZ:17-35, proof read) sets kap := R.kap (`rfl`, :30) and lam := zeroLam R F (l6m of the new scale). zeroLam = λ unless (v = v₀ ∧ W_{i,p} = 0) or (v ≠ v₀ ∧ ¬PartAt) (SZP:94-95). Under the hypothesis hZ ("EE_p ≠ 0 ⇒ W_{i,p} ≠ 0 ∧ PartAt off v₀", CPI:153), λ is unchanged on every p with EE_p ≠ 0 (RFZ:25-26; SZP:97-103).
- The identities are re-proved, not assumed:
  - thmB (ΘΘ* = κ·Πλ on each part): `thmB_zeroLam` via `isKap_congr`. On a part with partE σ = ⊥ the identity holds because x = 0 (PAU:24-35, 44-49).
  - thmA: `isLamP_congr`, same mechanism (PAU:37-48, 52-57).
  - GalD: `cx_galD_scal` with `zeroLam_off` (PAU:60-64).
  - Positivity: `zeroLam_pos` (SZP:122-127).
  - Assembly into PrimRows3: `prim_updS`, which copies every non-scalar field from the old PrimRows3 (`IWD/FurtherRowsUpdatedScalars.lean:14-26`).
- `reFace_prim` carries the result to the re-faced datum (`IWD/ReFacePrim.lean:13-19`). reFace keeps P0, ψ0, P1, ψ1 and replaces only Dc, Sp, Zsc.
- updS changes only lam3, since toRealDat.upd6 R.kap R.lam is R. So M_j, θ_j, the metrics and the maps are literally those of R.
- **Status:** a consistent rescaling on zero-dimensional parts only. **[proved, read]**

**(ii) The point record's Holds comes from primRows3_of_parts.**
- WeightCaseCondition is produced by `w_of_weight_residue_char` → `atDat_holds_alt` (LTD `WeightSetResidueCharacteristic.lean:20-62`). It applies `rational_data_sized_family_alt` = `holds_of_ties_alt` to a copy y of the datum and returns via `holds_of_copy` (:30-62; `IWD/CopyLIntegral.lean:50-52, 100`).
- `holds_of_ties_alt` sets prim := h.1, where h comes from `real_data_weight_vector_family_core_alt` = `primRows3_typesSep3_alt`, whose `hPrim := primRows3_of_parts …` (LTD `RationalDataSizedFamily.lean:12-27`; LTD `RealDataWeightVectorFamilyCore.lean:18-37`).
- The starting record stores it as `intersectionNumber_baseChange := hH` (`IWD/ConstructionStartingChoicesOfFineAdelicData.lean:217, 233`).
- Later stages move it with `holds_tr` / `cp_holds` / `holds_transfer` along SameGrp relabellings. These are built from `primRows3_tr` (`…/WeakCharInertPartRealAdelicDataTransport.lean:201-205`; statement of `primRows3_tr` at `…/Wp3ApplyEqSqMulSubSqMul.lean:127`).
- The only other PrimRows3 constructors found are prim_updS, reFace_prim and the of_wit and bundle projections (grep, §5).
- **Status:** origin [proved, read]; relabelling transports [proved, stmt]. I did not identify which of the four transport sites (IWD files at :118, :158, :178, :188) the live t.r passes through. Every RowsAre record must carry Holds of its own z.R, z.F by type (`…/NonzeroPlacesOverPrimes.lean:47-50`).

**(iii) selB is the linked bundle's b.B.**
- `goal_of_shape_of_hyps` instantiates TopShapeAlt's universally quantified selB as `selectionBundleOfRawSelection h.σ`, which is `(σ Fm hc x hx i).B` (TPS/ShapeOf.lean:24-30; TPS/ColumnChoiceWithTies.lean:61).
- In the same call it passes h.hPA and h.rRows. Both fields of HypsAlt are typed against that σ (TPS/Hyps.lean:22-33).
- σ, hPA and rRows come together from one `classSel` over the conjunction RowL.and … (TPS/NonemptyHypsOfAllRows.lean:40-63). Upstream, the hPA row is `linkedAt_hPA` → `of_wit_alt` for every linked bundle b. It uses `w.y.eq : realPackageOfBundle b = realPackageOfRealInput y` (TPS/HermWCellLastMulMulVecEqOfInWb.lean:20-32), and the PrimRows3 there typechecks definitionally against x.R = newR z.R lam err.
- **Status:** [proved, read]. The PrimRows3, the covol/ON/L6 rows and the package that BoundsMu uses therefore all concern (σ…).B.Q.Rl, the zeroLam-updated datum whose lattices and maps are those of the point record.

## 3. Children

| # | name | file:line | statement | role | status / weight |
|---|---|---|---|---|---|
| 1 | `lenBase_holds` ← `lenBase_of_taylorHasse` ← `taylorHasse_holds` | BLB `LenBaseHolds.lean:10`; ASM:33; BLB `TaylorHasse.lean:160` | jet module index ≤ C(T−1,d)·Ila | binomial loss | proved; top read, `taylorHasse_of`/`filtration_length_bound` not opened; core |
| 2 | `levelsQDesc` (→ `localStepLevelsQ`, `localStepDescent`) | LQD:9 | abstract filtration index bound | assembly of r(λ) | proved; statement and top read; glue |
| 3 | `HDiscLat.lattice_main` | used HAG:55 | disc(b)·N(g)² = unit·ϖ^{2·len + t} | disc = idx²·disc | proved, stmt; standard |
| 4 | `disc_product` | DPR:21 | product formula identity for Δ = a/b | global | proved, read; standard |
| 5 | `disc_hadamard`, `sphere_height_lower_bound` | used HDB:62, 73 | Hadamard; lower bound for the height of a nonzero polynomial | archimedean side | proved, stmt; standard |
| 6 | `heights_arith` | HAR:7 | arithmetic combination into Heights | numerics | proved, read; glue |
| 7 | `deepCore` + `transference_successive_minima` | LSD:590; TSL:32 | Gauss content ≤ ρ·log\|disc\| + Σ_σ(ρ·log Bop + ΣE) | CM-cost carrier | deepCore proved, read; transference stmt only; standard (Banaszczyk-type) |
| 8 | `qAt_run` ← `quotientBound_of_kill_detect_constantRoom`, `cmFamilyFunctionals_detect_lowCoefficients` | QRP:35 | QAt | quotient piece | proved; children stmt; core |
| 9 | `heights_definite`, `HtLAM`, `LamConst` | HDL:288; HIE:106; AxHLAM:69 | top-layer Heights, CM at weight n96·wL | j = m | proved; statement and setup read |
| 10 | `pvs_core4`/`sumGP4` | LPF:141, 289 | numerics close at Bx = 0 | size | proved, read (dominant terms); 3 sub-lemmas not opened |
| 11 | `onto_path_alt`, `ontoX_of_hypotheses_alt_alt` | TPS/OntoPath.lean:18; TPS/OntoXOfPrints.lean:28 | SurjectiveOntoX, premise unused | B | proved, read |
| 12 | `reFace_zero_parts`, `zeroLam`, `*_zeroLam`, `prim_updS`, `reFace_prim` | RFZ:17; SZP:94; PAU:44-64 | Holds transported, κ kept, λ changed only on zero parts | C(i) | proved, read |
| 13 | `holds_of_ties_alt` ← `primRows3_typesSep3_alt` ← `primRows3_of_parts` | LTD RationalDataSizedFamily:12; LTD RealDataWeightVectorFamilyCore:18 | origin of the record's Holds | C(ii) | proved, read |
| 14 | `holds_tr` / `primRows3_tr` | WeakCharInert…:201; Wp3Apply…:127 | Holds is invariant under SameGrp relabelling | C(ii) | proved; holds_tr read, primRows3_tr stmt |
| 15 | `goal_of_shape_of_hyps`, `selectionBundleOfRawSelection`, `classSel` | TPS/ShapeOf.lean:24; ColumnChoiceWithTies:61; NonemptyHypsOfAllRows:58-63 | one σ feeds hPA, rRows and selB | C(iii) | proved, read |

## 4. Oddities

1. **The INDEXBUDGET "x^{Bx}" is not there on the live instance.** sumGP4 is called with `H3 … 0 …` and rewrites x⁰ = 1 (LPF:291, 309). The T-floor margin is PPv⁴·dimY³, which is polynomially large, so this is harmless.
2. **The discriminant budget is not tight; its allocation is.** The proved Σ r·log N is below rk·f·m·b·de2 by at least ~PPv·dimY/11. NODE-INDEXBUDGET and NODE-ACCOUNT put E1 in the tight "m·B0" bucket because of the *allocation* 12·f·m·b and EJ (32·x^ε·f·m·b·L). The second of these, J0 / `LiftExponentAtTwisted`, is the genuinely budget-sized part of E1.
3. **E1 does have Galois input,** through J0. `ExponentStatement` uses CuspUAlt, BaseChangeDefiniteUnitaryGroup, Bhatt–Scholze and Chebotarev (TPS/OntoXOfPrints.lean:45). This corrects WHERECONG §0, §3 row "index at Tw" ("no Galois input"). None of the seven congruence/Selmer pieces is involved, and none of them depends on ON.
4. **"Generic curve" is a misnomer.** Z is 0-dimensional over K_λ(T). It is an arithmetic curve only over Spec O_λ(T). Krull–Akizuki (`PublishedIntClos`) is applied to that.
5. `zeroLam` sets λ = e^{l6m} on zero parts and at (v = v₀, W = 0). Whatever value it picks there is irrelevant to thmA/thmB/GalD, which are vacuous on 0. It could matter only for statements that read λ on a zero part, such as L6 sums over all p. I did not check whether L6/BoundsMu sum λ over p with EE_p = 0. If they do, the choice l6m (the new scale's L6 constant) is presumably exactly what makes `scal_zeroLam` hold (PAU:70-75, read to the signature) *(inferred)*.
6. ON's premise-carrying type (`hN → ON`) is a vacuous strengthening. It is harmless but misleading for readers. The same holds for FUN (`fun0`): its producer `hfun` comes straight from the FunctionalCondition row (TPS/TupAllUsedAtPart.lean:50, 64). I did not open the FUN producer to check that it also ignores the premise.

## 5. Coverage

Read:
- PROTOCOL; NODE-INDEXBUDGET, MIRABOLIC, WHERECONG, LIVEMULT, ACCOUNT, WHYHALF (all).
- JWM:1-191; LQD:1-85; FLP (all); TZB (all); TZL:1-25; WPS:117-142; TSL:1-68; LSD:560-700; LPF:141-424.
- AMO:1-195; REZ:120-380; BLB `LenBaseHolds.lean`, TSG:1-60, ASM (all); `…/OrbitalBoundsConclusion/LengthBaseT0.lean`.
- HT: HAR (all), DPR (all), HDB (all), HDA (all), HAG (all), HDD (all); HIE:106-114; AxHLAM:69-75.
- WA:330-434; WFm:24-31, 54-56; WA:265; ONL:765-866; QRP (all) plus three Statement files; HDL:280-420; I4R:1-55.
- TPS: IndefiniteRealisationChoice.lean:60-100; RowRRowsOfParts.lean (all); TupAllUsedAtPart.lean (all); OntoAtChosenStatement:13-15; OntoAtChosen:13-19; OntoPath.lean (all); ExportSt.lean:30-50; OntoXOfPrints.lean:28-50; OntoXOfTwistSharesExp.lean:15-30; HypothesesNonemptyOfUnramifiedExponents.lean:30-64; LinkROfIsLinked.lean:50-90; BernsteinUnitaryProductIrreducible.lean:22-80; MainTyzTer.lean:22; CFinal.lean:19-23; TieTwRecOf.lean:20-60; HermWCellLastMulMulVecEqOfInWb(Statement).lean (all); TopShapeAlt.lean:18-100; ShapeOf.lean (all); ColumnChoiceWithTies.lean:61; Hyps.lean:22-34; NonemptyHypsOfAllRows.lean:40-70.
- BaseRankDimension.lean:80-100; PartitionSelectionEvaluation.lean (all); DesWin.lean:11-31.
- CPI:120-169; ReFaceZeroPartConventionsChosenAgain(Statement).lean (all); SZP:90-130; PAU:1-80; FurtherRowsUpdatedScalars.lean:12-26; ReFacePrim.lean:13-19; WeakCharacterisationWithError.lean:55-75; LinksStage.lean:205; StableIffCarrierEq.lean:55-58.
- LTD WeightSetResidueCharacteristic.lean:20-70; LTD RationalDataSizedFamily.lean:12-40; LTD RealDataWeightVectorFamilyCore.lean:12-50; ConstructionStartingChoicesOfFineAdelicData.lean:195-244; CopyLIntegral.lean:50-52, 73-81, 100; NonzeroPlacesOverPrimes.lean:47-59; NonzeroPlacesOverPrimesLifts.lean:102-105; WeakCharInertPartRealAdelicDataTransport.lean:201-205; ExistsMovedRowLiftDataToFittingStages.lean:84.

Greps run:
- `theorem (localIdx|disc_product|heights_arith|deepCore|recursive_page_lattice_bound|theorem_zero_of_named_inputs|heights_definite|qAt_run|disc_at|lenBase_all|lenPoleL_all)`;
- `levelsQDesc|firstLength_le_prime_bound|len_Zm_le|ker_rhoN|rhoN_mem`; `def (Kp|Op|Rp|Vw|sec|secPow|WK|rhoK|OsK|Ila|AA|AAp|InBasis)`;
- `length_base_t0|lenBase_of_taylorHasse|TaylorHasse`; `def LamConst|def HtLAM`; `def PPv|PP0v|dimY|Zb`;
- `ev_prem|def EvWC|summandNormBound|row_rRows_stage0_alt`; `eventually_norm_bound_of_more_points`; `def SurjectiveOntoX`; `SurjectiveOntoX` (all files: 10, none in the LinkN/VWin chain);
- `SurjectiveOntoX|BoundsMu|\.ON\b|HasIndexBound|SlopeIneq|DivClausesR|LinkDIV` over CFinal, LinkNFam, ImportsFurtherTail(+Statement), AdmissibleParameterEventually, ExistsSetupLarge, DivinNOfHypV, DesWin, DTC WindowBoundOfLiteratureLevel/HVCore/LinkedUnlE/VwinOfRow, MainTyzTer. Only hit: DesWin:18, the LinkDIVt *consumer*;
- `structure UnitaryGroupThirdPlaceHypotheses`; `mainTheorem`;
- `reFace_zero_part_conventions_chosen_again`; `def zeroLam|zeroLam_of_ne|thmB_zeroLam|thmA_zeroLam|galD_zeroLam|prim_updS|def updS|def upd6|def reFace|reFace_prim`;
- `intersectionNumber_baseChange :=` (11 sites); `primRows3_of_parts`; `WeightCaseCondition`; `holds_of_ties_alt`; `holds_of_copy|holds_back|holds_tr|cp_holds|holds_transfer`; `structure RowsT`; PrimRows3 producers;
- `indefiniteRealisationChoiceOfSelection`; `AllRealisationsPrimitive`; `linkedAt_hPA_prmR`; `TopShapeAlt`; `selectionBundleOfRawSelection|structure HypsAlt|hPA :`.

Not opened:
- bodies of `taylorHasse_of`, `filtration_length_bound`, `localStepLevelsQ`, `lattice_main`, `disc_hadamard`, `sphere_height_lower_bound`, `transference_successive_minima`, `levels_real`, `total_le_of_bounds`, `four_term_sum_bound_of_parameters`, `qat_of_kill_detect`, `detectQ_of_known`, `known_holds`, `primRows3_tr`, `scal_zeroLam` (beyond its signature), `XE_updS_zeroLam`, `budget_numeric`;
- the FUN producer;
- which of the four Holds-transport sites the live t.r uses.
