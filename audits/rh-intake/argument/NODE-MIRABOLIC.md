# NODE-MIRABOLIC: the twisted-place link Θ → θ_j(μ(w))T_j(μ(w)) (LeafTW1, LeafTW2), with `QAt` and `ShareRd`

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.

Abbreviations:
- `ONL` = `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean`
- `TW1` = `Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeafTW1OfAllConjugatesGood.lean`
- `TW2` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/GoodLiftOntoOfBase.lean`
- `MRS` = `Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemRangeSrcForm.lean`
- `TST` = `Development/AbelianVarietyTheory/Definitions/Foundations/ThetaSeriesTies.lean`
- `IHF` = `Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean`
- `GSA` = `Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean`
- `AIB` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean`
- `AOS` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `RCT` = `Development/AbelianVarietyTheory/Definitions/Divisors/RealisedChainTorusEq.lean`
- `TRB` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/TupleReadBaseTupleEqFamily.lean`
- `TPB` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwistedPlacesBoundChainTwoRunChain.lean`
- `SO` = `Formalism/DivisorInequality/StatementObj.lean`; `WPS` = `Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/WeightedPrimeSumBound.lean`
- `SRB` = `Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ShareRdOfInBasis.lean`

## 0. Verdicts

**No ESCALATE.** Every load-bearing statement in the chain has a supplier on the live route. The glued local data form one global lattice in one fixed vector space.

The brief expected the chain to end in the congruence-module / Selmer machinery. **It does not.** The supplier of LeafTW1 is the `IdxAt` conjunct of `GoodTw`. That conjunct is proved by a Hecke-operator determinant argument (`propABCD_of_rel`), not by `CongBound_at`, `KillAt`, `LinkN` or `VWin`. The only things it shares with KillAt are the choice of twist and the auxiliary primes. LeafTW2 is the easy direction: an explicit theta series built from integral data is the theta lift of an integral source vector. The "integral surjectivity" the brief looked for is not a separate theorem. It is the global budget (A) of NODE-INDEXBUDGET, transported to the twisted lattice at a cost of ε ≤ 1/l² per place.

| Q | Answer | Status |
|---|---|---|
| 1 | LeafTW2: X₃ ⊆ Im locally at v. LeafTW1: lix(Ms∩Zg, X₃) ≤ lix(Ms∩Zg, eJ) + ram·ε0, with Σ_j(ε0(w)+ε0(w̄)) ≤ 2/p². Both are asked at w and w̄ for w ∈ Tw, and the tuple is μ(w). QAt bounds a quotient-length piece of the budget (A). ShareRd is a dimension count inside (A). Neither of the last two is in the TW chain (§1). | definitions read |
| 2 | LeafTW2 ← `leafTW2_of_isRec` ← `lattices_of_tie` ← `HidaSetting.thetaTuple_le` (proved, read). LeafTW1 ← `hasTwistBound_at` ← `exists_leafTW1_of_twGoodAt` ← `Reads.lix_le` ← GoodTw.`IdxAt` ← `admissibleIndexBoundAllPowers_of_conditions` ← `PropABCD` ← `propABCD_of_rel` (ThURel, HeckeLaws, AllGood, adm8, T3). §2b gives the mathematics. | TW2 proved and read. TW1 glue proved and read. AIB read. `propABCD_of_rel` top read. ThURel supplier statement only |
| 3 | One global object: a lattice R ⊆ K^D with R_y = ι(μ(y))·abelian₂(μ(y)) at every y, and {μ ≠ μ0} finite (SO:42-48). M_j, the target space and the metric XE are independent of the tuple. Twisting changes only the source-side data θ_j(t), T_j(t), ι(t). LeafTW1 compares two lattices (twisted-tuple theta series and base theta series) **in the same target space** Zg_j ⊆ K^{nZ_j}. No `SameExport` is needed for this identification. | SO read; TieCoord/TjId read |
| 4 | ShareRd: C(T−1, dimY)·del ≤ rk M_ka. **Proved** (`shareRd_of_inBasis`, SRB:58-106): it counts C(T−1, dimY)·del linearly independent monomials w^α·s0^{T−\|α\|}·th′_i in S_ka. So it cannot fail numerically. It is a Hilbert-function lower bound, tight to leading order *(inferred)*. | proved and read |

## 1. Statements

**Objects of the chain** (ONL:43-139 OnObj fields; ONL:158-170 defs, read):
- P = `Mir R`. This is ∏_{v∈Pg} (the mirabolic subgroup of GL_r(residue field at v)) (`LiftWeightComplexPointEqTwist.lean:263`, grep line). It acts by ρ_j on the coordinate space K^{nZ_j} of layer-j forms. U is the unipotent subgroup and ψ is a generic character (`MirabolicIsMackey`, `Formalism/MirabolicMackeyTheory/StatementL.lean:157-162`).
- Zg_j = eig(ρ_j, U, ψ) ∩ V₀_j (ONL:158). This is the (U,ψ)-eigenpart of the type part V₀ = range e_j. It is a finite Gelfand–Graev / Kirillov-type projection at the level primes.
- Ms_j = the integral forms. Th, ThK = test lattices built from products of short theta series. Th0 = `thetaEig`, the U-traces of orbit-family theta series of unimodular lattices (TST:138ff; `IsOrbitFamily`, TST:30-35).
- ThJ = comap of `thetaBase` (TST:89-92): theta series whose kernel is attached (IsKernel, TST:77-87) to the base character `delAt(plc v)`. eJ = e(ThJ) (ONL:160).
- X₃ = e(comap `thetaTuple`(μ(v))) (TST:94-96; `X₃_eq`, TST:187). This is the span of the theta series θ_{φ}(h, w) with the Weil datum (ω_P, v_P) of the **twisted tuple** μ(v), at points h and integral coefficient vectors w (`seriesSet`, TST:72-75; `InCoefLat`).
- Im = e(θ′(Mt)) (ONL:163). Here Mt = `lvlNab`, the integral (U,ψ)-level lattice of source forms for tuple μ(v) (`Mt_eq`, TST:190). θ′ is the class-sum theta lift, θ′(x) = ph·thF(srcForm x) (`IsClassSum`, TST:109-114).
- ImageLattice = θ′(pr(eX(Mt))) (ONL:166). `TjId` (ONL:230) says φ(θ_j(t)T_j(t)) = ImageLattice. LeafIdentity (ONL:280) gives ImageLattice = Im.

**LeafTW2** (ONL:284-286): at v ∈ {w, w̄}, w ∈ Tw, for all j: X₃ and Im are lattices in Zg, and (X₃)_v ⊆ (Im)_v.
- In words: the twisted-tuple explicit theta series lie, v-integrally, in the theta image of the integral source lattice of μ(w).

**LeafTW1** (ONL:288-291): at the same places,
  lix_v(Ms∩Zg, X₃) ≤ lix_v(Ms∩Zg, eJ) + ram_v·ε0(v, j),
together with Σ_j (ε0(w, j) + ε0(w̄, j)) ≤ 2/p_w². In words: the twisted theta lattice has v-adic index in the integral type part at most ε larger than the index of the base theta lattice.

**Where they enter** (`local_bound`, ONL:409-452, read). At v ∈ Tw, with t = μ(w), the Lean chains:

  idx_v(M_j, θ_j(t)T_j(t)) = lix(Ms∩Zg, ImageLattice) [TieCoord, TjId] = lix(·, Im) [LeafIdentity]
  ≤ lix(·, X₃) [TW2] ≤ lix(·, eJ) + ram·ε0 [TW1]
  ≤ lix(·, e·Th0) [Th0 ≤ ThJ, LeafRankJ ONL:276]
  ≤ … |U|·(ThK∩eig) ≤ Th0 [LeafData ONL:272], Th ≤ σ·ThK [LeafLemmaS ONL:257], lix(Ms, Th1) ≤ E·dim + r [budget, ONL:262].

The result is (E − v(σ) + v|U|)·dW + (r + nZ·v|U|)/|P:U| + ram·ε0. The division by |P:U| comes from `local_conditions_weighted_at_place` with `LeafMackey` (ONL:239). That lemma uses the Mackey property of (U, ψ) in the mirabolic group (`IsMackey`, StatementL.lean:34-36), proved as `mirabolic_is_mackey` (grep: `MirabolicMackeyProofs/Mirabolic.lean:224`).

**QAt** (WPS:41-56, read). Let MggK be the forms killed by every "small" Fourier–Jacobi coefficient map sg_{cu,χ}, where χ ranges over exponents with trF(hform χ ξ ξ) ≤ c1 (`Killed`, `MggK`, `WeightFamilies.lean:322-326`). Let Qm = M_ka/MggIn and rhoP = rk Qm (`WeightFamilies.lean:328-335`). QAt says: there is a finitely supported be ≥ 0 with Σ be·log N/deg ≤ PPv·|ka| such that, for any rhoP integral forms th_i that span modulo MggK and have meanLogSup ≤ PPv·|ka|, len_λ(Qm/⟨th_i⟩) ≤ nn(λ) + rhoP·be(λ), with Σ nn·log N/deg ≤ rhoP·PPv·|ka|. It is the "quotC" piece of r(λ) in (A) (INDEXBUDGET). It is a Siegel-lemma-type bound on Fourier coefficients and is not in the TW chain. Supplier: `recursive_page_lattice_bound` (`…/ThetaShiftProofs/RecursivePageLatticeBoundStatement.lean:22`, wrapper of `RunJoin.qAt_run`, body not opened). It is used at `inputsNet_recPlus` (`…/HeightProofs/ExistsIndexBoundHypothesesWithNetAllValuedPoints.lean:81`, read).

**ShareRd** (WPS:92): C(T−1, dimY)·del ≤ d, where d = rk(M_ka) and del = the number of weight-wF forms th′_i. Also dimY = f·(pq + C(p,2) + C(q,2)) for signature (p, q) of layer j (`WeightFamilies.lean:54-56`), and a0 = T − dimY (`GlobalFamilyData.lean:16`).

## 2. Argument

### 2a. LeafTW2 (proved, read)

The live supplier is `leafTW2_of_isRec` (TW2:65-82). It is called in `onto_path_alt` (`TPS/OntoPath.lean:66`). That theorem is the body of `onto_x_of_all_estimates`, which is reached from `ontoX_of_hypotheses_alt_alt` (`TPS/OntoXOfPrints.lean:28-46`) via `ontoX_of_twist_shares_exp_alt` (`TPS/OntoXOfTwistSharesExp.lean:21-26`). That is the SurjectiveOntoX producer NODE-JOIN placed on the live route.

`leafTW2_of_isRec` applies `lattices_of_tie` (MRS:409-470) at every v with ClassSumRational at μ(v) (from `TwistedRational`). The key step is `HidaSetting.thetaTuple_le` (MRS:297-321):

  thetaTuple(μ) ⊆ θ(lvlNab).

Proof as mathematics:
1. A generator of thetaTuple is a U-traced theta series θ_{v_P}(g, w) at g ∈ G_f, with w in the coefficient lattice.
2. `exists_latSys` / `exists_trace` write the kernel at (g, w) as χ_j^{−1}·(class sum of an integral source form f in the level lattice). `exists_src_trU` writes the U-trace of f as srcForm(y) with y ∈ lvlNab.
3. So the generator equals c·θ′(y), with c a root of unity (finite-order level character, `exists_int_smul`). Hence it equals θ′(a·y) with a·y still integral.

This is the standard fact that a theta series with integral Schwartz datum at a point is the lift of an integral delta-type source vector. It is the **easy direction**. The Lean proves the global inclusion X₃ ≤ Im, which is stronger than the local one LeafTW2 asks for.

`lattices_of_tie` also proves span_K(X₃) ⊇ Zg via `GoodLiftOnto` (`goodLiftOnto_of_base`, TW2:46-63). That is **rational** surjectivity of the theta lift onto the type part: Zg ⊆ span of θ(srcForm). It does not give integral surjectivity.

### 2b. LeafTW1 (glue proved and read; core statement plus top of proof)

**Live trace.**
1. `onto_path_alt` takes `tTw : HasTwistBound O` from `TwistStatement'` (`TPS/ExportSt.lean:41`). It is supplied by `twistSt_of_alt` (`TPS/TwistStOf.lean:20-38`). That calls `hasTwistBound_at` (TRB:47-63) with:
   - `ExportTie` at each v ∈ twPl, from `ExportedStatement`, supplier `exportSt_of_reciprocity_and_casselman_wallach` (statement only);
   - LeafSup, RankAtPlaces;
   - `TwGoodAt` from the family hypothesis (`hc…T0`).
2. `exists_leafTW1_of_twGoodAt` (TW1:439-465). At a twisted v it takes `IdxAt` from `hG` (GoodTw at the chosen index c.twI, with pack Q, k′, ψ′) and ε from `IsErrorFamily` (Σ ≤ twEps = 1/l²). It then applies `TiedAt.lix_le` (TW1:393-409) → `Reads.lix_le` (TW1:246-290).
3. `Reads` (TW1:220-230) is a semilinear embedding rd: K^{nZ} → FmExt (forms over the twist coefficient DVR O′). It intertwines e with eExt and sends:
   - Θ = thetaBase to span{th(a) : a ∈ SgJ};
   - Θψ = thetaTuple(μ(v)) to span ⋃_a thPsi(a).

   This is the identification of the explicit target-space theta series with the abstract records `Y.th` and `Y.thPsi` of the twist datum. It is supplied by ExportTie (TW1:365-374, def read; supplier not opened).
4. `IdxAt` (IHF:201-211): for every lattice M of V0 ⊗ O′,

   sIdx_l(M, eThPsi) ≤ sIdx_l(M, eTh ⊗ O′) + ε.

   This is the content of LeafTW1.

**How IdxAt is proved** (AIB:92-224, read; GSA:119-138, read; AOS:293ff, top read).
1. `PropABCD` (GSA:119-138). For each (j, b) there is an open normal H ⊆ G_E and integers v, nmax. For any auxiliary set Q of 2R split primes compatible with H, there is f ∈ O[X_q] with `OrdHyp` (GSA:16-27). OrdHyp says: modulo (X_inr, (1+X_inl)^{l^M} − 1), f = Dd·g with v(g(0)) ≤ v, and Dd is residually a unit times a monomial of degree ≤ nmax. Then for every character χ of Δ_Q = ∏(ℤ/l^M) with values u_q:

   sIdx(B, Tψ) ≤ sIdx(B, Th) + nval(f(u − 1)) − v/e,

   for any lattice Tψ containing the χ-specialised twisted theta series.
2. `propABCD_of_rel` (AOS:293) proves PropABCD from:
   - `ThURel` (GSA:105-117). The twisted universal theta series at level Q, specialised at χ, equals the Euler-factor operator PqF_P(χ(Frob_P)) = 1 + Σ_n (−1)^n N(P)^{n(n−1)/2} y^n T_{n,P} applied to the series at level Q∖{P, P̄}. At Q = ∅ it is the untwisted th.
   - So f = det over the lattice B of ∏_{P∈Q} PqF_P. This is a determinant in the Hecke algebra T generated by the hkF(k, P), P split ∉ S0 (`HeckeLaws`: commuting).
   - `exists_subgroup_isUnit` (`ExistsSubgroupIsUnit.lean:75-81`, statement read): if Frob_P is conjugate into z·H, with z a tame-inertia element at the twist prime, then 1 + Σ(−1)^n N^{…} hEig(s, n, P) is a **unit** for every good signature s. In words, det(1 − ρ̄_s(Frob_P)·η) is a residual unit.
   - `T3` (IHF:114-123, a conjunct of ABHyp IHF:125-147): every residual Hecke eigenvector in B mod 𝔪 has eigenvalues congruent to those of some s ∈ Sig. So residually f is a unit times a monomial, which gives OrdHyp.
3. `admissibleIndexBoundAllPowers_of_conditions` (AIB:92-224):
   - It takes the auxiliary primes P from `GaloisSideTwistedSelmerAuxiliaryPrimes` (`hX`). These are the same Chebotarev primes that kill the residual Selmer group (KILLAT §2), additionally constrained to the open subgroup ⋂HE ∩ ⋂HB.
   - It chooses one level k and exponents e_q (`exists_level`), so that a single ψ′ makes all the normalised valuations ≤ ε: partAT (Selmer), partC (theta values), partD (tame) and partB (index) together.
4. The RFam F used is `fam Y i z S` with A = |G|·e_G (`TwistModuleAllCharacterPowersOfAdmissible.lean:16-50`, read). ABHyp is from `abHyp_fam`, using `GoodLatticePoints` (= T3 on Mall ∩ V0). That in turn comes from `admT3_of_hecke_semisimple` (sig_all + HkSS; `TwistTheoremAllPowersOfSelmerSupLattice.lean:20-40`, read).
   - `sig_all` (`DataN.lean:878-883`, read) is a characteristic-zero classification: every Hecke eigenvector in the type part has the eigensystem of some s ∈ Sig.
   - `HkSS` (`OffRange.lean:35-36`, read) is semisimplicity.
   - *(inferred)* T3 is then Deligne–Serre lifting.

**Reconstruction.** Answers to the brief's questions:
- **Role of the Hecke algebra.** It is T = ⟨hkF(k, P)⟩ acting on the (U,ψ)-eigen good part V0 = e_G·Fm0 of layer j (IHF:32-37).
- **Role of the type component.** It is Zgood, the image of the finite level-group idempotent e_G.
- **The twist.** The ψ-twisted theta lattice is the untwisted theta lattice moved by the Hecke operator ∏_{q∈Q} P_q(ψ(Frob_q)). Its index cost is v(det), and the det is residually a unit because every residual eigensystem (T3) sees Frob_q ≈ z with no eigenvalue 1.
- **What is not used.** No congruence module, no Selmer group, no Ш and no class number enters IdxAt. Congruences between lifts and non-lifts never have to be excluded here, for two reasons:
  - The target lattice eJ is already a lattice of theta series. Its index in Ms∩Zg is what the global budget (A) pays for.
  - The comparison twisted vs untwisted is internal to the Hecke module.
- **Multiplicity one / freeness.**
  - The Mackey property of the mirabolic Gelfand–Graev pair (a finite-group multiplicity-one statement, proved in-tree) is used to divide the budget remainder by |P:U| (ONL:409-452).
  - The residual-eigensystem classification T3 is used in PropABCD.
  - No Hecke-algebra freeness or global multiplicity one is used on this chain. *(The congruence-module chain of CONGMOD/LINKN is a separate consumer: the dual index jw at Tw, SO:69.)*
- **The "mirabolic chain".** It is not Fourier–Jacobi or Whittaker coefficients of automorphic forms. It is the finite-level (U,ψ)-eigenprojection for P = ∏ mirabolic(GL_r(F_g)) at the level primes. Its links are the inclusions in §1 `local_bound`.
  - LeafLemmaS/LeafData: the test lattice, traced to (U,ψ), lies in the span of unimodular-lattice theta series (`trace_mem_thetaEig`, `LeafDataOfOnTieOfIntegral.lean:170-187`, read).
  - LeafRankJ: those lie in the base theta lattice.
  - TW1: base vs twisted theta lattice index ≤ ε.
  - TW2: twisted theta ⊆ twisted theta image.
  - TieCoord/TjId/LeafIdentity: identify that image with θ_j(μ)T_j(μ).

### 2c. Twisted places only; the global object (Q3)

- `BoundsMu` (SO:17-79, read) quantifies over one R ⊆ K^D, a lattice, with R_y = matLat(ι(μ(y)), abelian₂(μ(y))) at every finite y (SO:48). It requires {y : μ(y) ≠ μ0} finite and μ(ȳ) = μ(y) (SO:22-23).
  - M_j, XW_j, XE and K^D are fixed.
  - θ(j, t), Tl(j, t) and ι(t) are maps and lattices in that same K^D.
  - So the glued object is one global lattice R with one archimedean metric XE. The archimedean consistency is the det-ratio identities: for μ0 at every infinite place, and for every t at v0 (SO:31-34).
- The local index at y compares the **fixed** global M_j with the **twisted** image θ_j(μ(y))T_j(μ(y)) localised at y. The twist changes only source-side data.
- Off Tw the BoundsMu hypotheses demand index and dual index exactly 0 (SO:50-55). That holds by the definition Tw = W1 (NODE-TWSET).
- In the OnObj, TieCoord (ONL:247-251) asks (S.M j).map φ = Ms∩Zg once, globally, and TjId only at w, w̄ for t = μ(w).
- `SameExport` (NODE-ORDER) is not what identifies the spaces. It only keeps the twist record (ρ_s, Bloch–Kato data) the same between the two passes.

### 2d. ShareRd (Q4)

`shareRd_of_inBasis` (SRB:58-106, read). This is the live indefinite route: `cuspFormBasisShares_indefinite_liftIndex` → `exists_inBasis_shares_inContain` (`ExistsInBasisSharesInContain.lean:52`) → here. The definite route goes through `CuspFormBasisSharesDefiniteLiftIndex.lean:206`.

The proof:
1. From `InBasis` at one λ and `AnFacts.indep`, the leading monomials w^α·s0^{T−|α|}·th′_i, with |α| < a0 = T − dimY and i < del, are linearly independent.
2. They lie in S_ka, since ka = wF + T·wL.
3. Their number is C(T−1, dimY)·del (`card_exponents_sum_lt_sub`: #{α ∈ ℕ^d : Σα < T−d} = C(T−1, d), `CardExponentsAndChooseRatioBoundsPair.lean:7-8`).
4. So C(T−1, dimY)·del ≤ dim S_ka = rk M_ka.

**Numerics.** The inequality is a theorem, so no choice of (rank, k, m, t, T, wL, wF) can violate it once InBasis/AnFacts hold. *(Inferred)* It is tight to leading order: dim S_{wF+T·wL} ≈ deg·T^{dimY}/dimY! and del = deg is the generic rank of the sections over the Noether polynomial ring. So the budget factor binomial·del ≤ rk loses nothing. With T ≥ x^{Bx}·… (WA:417, per INDEXBUDGET) and dimY = f·C(n, 2), both sides are astronomically large. Only the ratio matters, and it is ≤ 1 by proof.

## 3. Children

| # | Name | file:line | Statement | Role | Weight / status |
|---|---|---|---|---|---|
| 1 | `leafTW2_of_isRec` → `lattices_of_tie` → `thetaTuple_le` | TW2:65; MRS:409, 297 | twisted explicit theta series ⊆ θ(integral source lattice); span ⊇ Zg | LeafTW2 | standard (theta of integral datum is integral); proved and read |
| 2 | `goodLiftOnto_of_base` | TW2:46 | rational surjectivity of the theta lift onto the type part | lattices in Zg | proved and read (top) |
| 3 | `hasTwistBound_at` → `exists_leafTW1_of_twGoodAt` → `Reads.lix_le` | TRB:47; TW1:439, 246 | IdxAt ⇒ LeafTW1 | glue | proved and read |
| 4 | `ExportTie` supplier `exportSt_of_reciprocity_and_casselman_wallach` | `TPS/ExportStOfReadingStatement.lean:11` | explicit theta series ↔ record th, thPsi | identification | **core, statement only** |
| 5 | GoodTw.`IdxAt` ← `admissibleIndexBoundAllPowers_of_conditions` | IHF:201, 219; AIB:92 | twisted theta lattice index ≤ untwisted + ε | content of TW1 | proved and read |
| 6 | `propABCD_of_rel`; `ThURel`; `exists_subgroup_isUnit`; T3 | AOS:293; GSA:105, 119; `ExistsSubgroupIsUnit.lean:75`; IHF:114 | twisted = Euler-factor operator on untwisted; det residually a unit | the determinant argument | core; top read; ThURel supplier `universalTwistedSeriesDistribution_of_compatibility` **statement only** |
| 7 | `sig_all`, `HkSS`, `admT3_of_hecke_semisimple` | `DataN.lean:878`; `OffRange.lean:35` | all type-part eigensystems are known; Deligne–Serre ⇒ T3 | residual classification | standard in kind; supplier `sig_all_of_sideB` (`GoodPartEigensystemIsTripleEigensystem.lean:141`) top only |
| 8 | `mirabolic_is_mackey`, `local_conditions_weighted_at_place` | `MirabolicMackeyProofs/Mirabolic.lean:224`; `…/LocalConditionsWeightedConditional.lean:83` | Gelfand–Graev of the finite mirabolic is multiplicity-free; r/\|P:U\| | type-part share | standard; statement only |
| 9 | `recursive_page_lattice_bound` (QAt) | `…/RecursivePageLatticeBoundStatement.lean:22` | Fourier-coefficient quotient length bound | piece of (A) | statement only |
| 10 | `shareRd_of_inBasis` | SRB:58 | binomial·del ≤ rk | piece of (A) | proved and read |

## 4. Oddities

1. **The brief's premise is off.** (B) is not where the Selmer/congruence machinery enters. The twisted-place index chain uses a *Hecke-determinant* bound with residual-unit Euler factors. KillAt and IdxAt are sibling conjuncts of GoodTw, satisfied by the same ψ and the same auxiliary primes. The congruence-module chain (CONGMOD) feeds only the dual-index term jw ≤ J·D + η (SO:69, 71-72) and E2.
2. **Integral surjectivity is never proved as such.** What is proved is index(twisted theta image) ≤ index(base theta lattice) + ε ≤ budget. A congruence between a lift and a non-lift in the type part would make the base theta lattice have large index. It is then paid from the global r-budget of (A), not excluded.
3. **T3 / sig_all are strong hypotheses.** They say every residual eigensystem in the type-part lattice reduces from a known signature s. That is a classification of **all** Hecke eigensystems in V0 at every twisted l (unbounded, per NODE-LARGETW). I read only the top of its supplier.
4. **ThURel** (twisted theta = Euler-factor operator applied to untwisted, at every split Q) is the automorphic input of LeafTW1. It is a distribution relation of Euler-system type. I read its statement, not its supplier.
5. LeafTW2's real content (`thetaTuple_le`) is unconditional given HidaSetting, and global. It is fine.
6. ExportTie, which ties the explicit theta series of tuple μ(v) to thPsi for the chosen ψ_w, is where the twisted tuple and the twist character are identified. Its supplier is unread. If it failed, LeafTW1 would compare unrelated lattices.

## 5. Coverage

Read:
- PROTOCOL; NODE-INDEXBUDGET, TWSET, LARGETW, CONGMOD, LINKN, KILLAT, LIVEPATH (all).
- ONL:1-300, 380-452; RCT:1-140; TPB (all); TW1:200-469; TW2 (all); MRS:200-470; TST:30-240.
- IHF:20-80, 84-160, 185-300; GSA:14-30, 80-140; AIB (all); AOS:285-340; `ExistsSubgroupIsUnit.lean:75-87`; `BlochKatoPhases.lean:90-118`; `DataN.lean:875-883`; `OffRange.lean:30-36`; `GoodPartEigensystemIsTripleEigensystem.lean:130-160`; `ExistsGoodPlacesEveryConjugate.lean:150-190`; `ExportAllOfSixInputs.lean`, `TwistModuleAllCharacterPowersOfAdmissible.lean`, `TwistTheoremAllPowersOfSelmerSupLattice.lean:20-40`.
- `TPS/OntoPath.lean`, `OntoXOfPrints.lean`, `OntoXOfTwistSharesExp.lean`, `ExportSt.lean`, `TwistStOf.lean` (all); TRB (all); `SurjectivityFromAllEstimates.lean:1-40`.
- `StatementL.lean:1-80`; `LeafDataOfOnTieOfIntegral.lean:138-190`; SO:1-80; WPS:30-120; `WeightFamilies.lean:50-56, 315-345`; SRB (all); `ExistsIndexBoundHypothesesWithNetAllValuedPoints.lean:60-90`; `RecursivePageLatticeBoundStatement.lean`.

Greps run:
- `LeafTW1|LeafTW2|leafTW1|leafTW2`; `twistedPlacesBoundChain_twoRunChain|on_base_atPlaces|leafTW2_of_isRec|exists_leafTW1_of_twGoodAt`; `onto_path_alt|SurjectiveOntoX`;
- `def Mir|mirIncl|IsMackey|def eig`; `lattices_of_tie|GoodLiftOnto|ClassSumRational|OnTie|thetaTuple|thetaBase`; `HidaSetting`;
- `IdxAt|PartBAt|GoodTw`; `PropABCD|OrdHyp|ABHyp|RFam|specU`; `goodE`; `exists_subgroup_isUnit`; `sig_all|HkSS|admT3`; `ThURel`; `exportAll_of_six_inputs`; `exportSt_of_reciprocity…`;
- `ShareRd`; `shareRd_of_inBasis|sharesAt_all`; `dimY|a0`; `card_exponents_sum_lt_sub`; `recursive_page_lattice_bound`; `MggK|Qm|rhoP`.

Not opened:
- bodies of `local_conditions_weighted_at_place`, `mirabolic_is_mackey`, `exists_latSys`/`exists_trace`;
- `propABCD_of_rel` beyond its first 50 lines; `universalTwistedSeriesDistribution_of_compatibility`; `admT3_of_hecke_semisimple`; `abHyp_fam`; `export_at`;
- the ExportTie supplier; `qAt_run`; `inBasis_iff_pointValues…`, `AnFacts`.
