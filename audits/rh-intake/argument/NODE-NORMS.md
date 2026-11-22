# NODE-NORMS: which hermitian metric sits on each lattice at the base archimedean place, and whether the three per-lift inputs of DIV share them

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own algebra, inference or computation. [NODE] means taken from that node and not re-read. Nothing from the tree was compiled or executed. The only code run was the auditors' own script `numtest/normcheck_cs.py` (Python standard library plus `numtest/sigma_lib.py`), whose output is `numtest/out_normcheck_cs.txt`.

Abbreviations:
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`; `PO` = `Formalism/LocalToGlobal/IndefiniteReal/PartsOrth.lean`; `ZPE` = `.../IndefiniteReal/ZeroPartEigenvalueConvention.lean`; `LD` = `.../IndefiniteReal/LinksDefs.lean`; `LC` = `.../IndefiniteReal/LinksChar.lean`; `LL` = `.../IndefiniteReal/LinksLemmas.lean`; `AL` = `.../IndefiniteReal/ArithLemmas.lean`; `BLP` = `.../IndefiniteReal/BaseLiftsPackageOfPrimitiveLinks.lean`; `PPS` = `.../IndefiniteReal/PackageFromPrimitiveStatements.lean`; `LNF` = `.../IndefiniteReal/LocalNewformFunction.lean`; `DV` = `.../IndefiniteReal/DatumVec.lean`; `SPF` = `.../IndefiniteReal/ScalarOnPartsFull.lean`; `OCC` = `.../IndefiniteReal/OrthogonalComplementCharacterisation.lean`
- `CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`; `NNC` = `.../Definitions/Divisors/NormNegCmConstantEqAtAllEmbeddings.lean`; `IPM` = `.../Definitions/Foundations/IsProbabilityMeasureMuPart.lean`; `EFS` = `.../Definitions/Foundations/ExistsFlatSecRankZero.lean`; `OMS` = `.../BlockTheory/DivisorBase/OneMeasureSizes.lean`; `MAO` = `.../Proofs/DivisorProofs/MeasAtOf.lean`; `IPF` = `.../Proofs/DivisorProofs/InnerProductFormula.lean`; `HLC` = `.../BlockTheory/TwistedDiscreteSeries/HalfLinearCocycle.lean`; `DEZ` = `.../Proofs/TwistedOperators/DerivEqZeroOfEven.lean`; `FVI` = `.../Proofs/TwistedOperators/FockVectorsInnerEqFockInnerProductMulNorm.lean`
- `TCG` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolG.lean`; `CMR` = `.../ThirdPlaceSeries/CoveringMeasureReductionBound.lean`
- `PWN` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/PaddedWittNormSquare.lean`; `NFL` = `.../Proofs/DivisorProofs/NormFockLSqLe.lean`; `CM` = `Formalism/LocalToGlobal/Divisibility/CoefMod.lean`; `DHB` = `Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean`; `D7F` = `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean`

## 0. Verdict

**No ESCALATE.** The audit found no pair of inputs stated for different metrics without a tie. It found no surviving per-unit-weight constant on the a-row. The numeric check confirms the Lean's constant.

1. **The coefficient of a_t comes from input (a) alone.**
   - The top weight a_t appears only in the column-side jet bound (`BlockBound`).
   - The hook product omits the a_t row [STEPE §2.2]. The covolume l3m involves only the caps w (ZON:64-65 [STEPE]).
   - So m·(ph(a_t) − a_t·logΩ) is fixed by one proved theorem in one metric: the column Fischer metric `pairK`.
   - A mismatch c^{wt} between (a) and (b) or (c) could only hit the k·w·logΩ and Σph(ν_w)-versus-hook terms. Such a mismatch would make L6 or D2 false, since each would be off by ≍ k·f·b·|log c|, far above their stated errors. It would not shift Main by c·ΣA. *(mine, from the shapes)*
2. **(b) and (c) are tied by shared record fields, and the ties are definitional.**
   - The Rallis scalar λ_j (L6, `thmA`), the det identity (`SpecDet`) and the covolume lcv(XW_j, M_j) (L3, `RecAt`) all read the same fields `IndefData.XW`, `.lam`, `DefSide.XT` (IS:304-316; CXC:57-59).
   - On the live constructor these fields come from one inner product: that of the layer Hilbert space `HW` (PO:165-166; ZPE:120-140).
   - That inner product is ∏dimK × the Schur-normalised L² over a fundamental domain for the Haar measure νW (LD:321-323; LC:192-193).
3. **The (2πx)^{−|wt|/2} factor is applied consistently.**
   - It is `lieFacZ` (IPM:664-665), with x = ‖φ₀(ξ₀)‖ (`xiR`).
   - It sits inside the dictionary f ↦ (adelic form) = lieFacZ·adel f (`adFun`, OMS:50-54), inside petW (IPM:734, 787-788) and inside the flat-section degree (`homN` in `ConstSec`, EFS:443-456, 751-754). It is the same definition in all three places.
   - The comparison of the Rallis-side norm with petW (`ExactRatio`, OMS:75-80) has lieFacZ on both sides. It cancels by construction and leaves only ratAt = νW(fdW)·∏dimK.
4. **The Gaussian and Fock normalisation of the hook formula is a proved theorem.**
   - The archimedean test vectors are P(a⁺)·(vacuum), with a⁺ = (creation operator)/fockScale and fockScale² = 8π·Im τ(ξ₀) (LNF:130-141).
   - `fockModel` (DEZ:133-162) proves ⟨P(a⁺)f, Q(a⁺)f⟩_{L²(covol-1)} = fockIp(P, Q)·‖f‖². Its core is a commutator lemma whose constant is 4π·(symplectic form) against fockScale² (FVI:69-109).
   - So the Fischer norm (⟨z^m, z^m⟩ = m!) in `DeltaNorm` (IPF:147-149) is the Weil-representation norm.
   - The column-side Gaussian (H = area⁻¹Σz w̄ [ENGINE]) is a different object and does not enter (b).
5. **The two logΩ's are not compared by a lemma.** Each is proved equal to the same real number:
   - (a) through mean log(area/π) [STEPE §4, MLC];
   - (c) through `chowla_selberg_period` inside `FlatDegree_holds`, then `logPeriod_eq_kroneckerCharacter_logPeriod_of_host` [COVOL].

   Only that number is shared, so no metric comparison is needed. The constants log π and log 2 cancel exactly (§2.5).
6. **Numeric check *(mine)*.** It covers only (a), the only input that carries a.
   - For d = 4 and d = 3, γ + log(2π/√d) − L′/L(1, χ_{−d}) equals log(area(L₁)/π) for the Δ = 1 lattice to 8 decimals.
   - 2·log|D^aσ(0)| − [ph(a) − a·logΩ_Lean + (a/6)·log|Δ|] = 7.4 at d = 4, a = 5997, and 5.4 at d = 3, a = 5995. That is O(log a). The control Ω → 2Ω misses by ≈ a·log 2 ≈ 4160.

## 1. Statement (the question, and the metric on each object at the base place v₀)

The question, from the brief: are inputs (a), (b) and (c) of DIV stated for one hermitian metric on each lattice, and do the per-unit-weight constants cancel exactly? The table below answers item 1 of the brief.

| object | archimedean norm in the Lean | formula | file:line |
|---|---|---|---|
| column forms at level j, including the source M_u (level 0) | class-weighted `famIpAt` of `pairK` | Σ_c ‖stab c‖⁻¹·pairK. Here pairK = (∏_τ det G_τ^{detShift}/extNorm)·fockL∘blockAct(Gᵀ), and fockL(z^m, z^m) = m! (Fischer form; no π, no weight power). It is normalised so that the extremal (highest-weight) vector has norm 1 | DHB:245-246; CM:21-31, 160-176; NFL:71-77 (`normSq_eq`) |
| source N_u ⊂ Mram_u | the same frame as (fm u).lat 0 | `nuIn_norm`: normAt_{N_u} = normAt_{(fm u).lat 0} ∘ nuIn; the Hilbert inner product of Mu is (fm u).ipC 0 (`eMu_isom`) | D7F:287-299 |
| layer lattices M_j (frame XW_j) | the HW inner product, read on the basis bW = nP^{−1/2}·FW.j(bL) | XW_v = frameOf(Gram(bW_v)) (PO:165-166). bW and eW = √nP·subtype (ZPE:120-140; LD:675-681). HW ≅ Wall with ⟨·,·⟩ = ipAt = ∏_ρ dimK(κ_ρ)·ipM(νW, fdW) (LC:192-193; LD:321-323). ipM is ∫_{fdW} ⟨Tv, T′v′⟩ dνW, normalised by ∏⟨v, v′⟩ (Schur, SPF:94-96). νW and fdW are fields of `RealDat` (LD:573-574) with `IsMeasFD` (LC:223-224) | as cited |
| the same M_j, as the covolume theorem sees it | petW | nrmR(f) = ‖FW.j f‖ (NNC:31-32). nrmR = √ratAt·petW (`ExactAt`, MAO:22-26), with ratAt = νW(fdW)·∏_τ dimK (OMS:18-19). petW = petAt = lieFacZ·‖ptN(modelWt G)(f)‖_{L²(muQ1)}, where muQ1 is a probability measure (IPM:734, 787-788). lieFacZ = exp(−(Σ_{τ,i}G_{τ,i}/2)·log(2πx)) (IPM:664-665), x = xiR D = ‖φ₀(ξ₀)‖ (`CuspidalL2Subspace.lean:35`) | as cited |
| type parts T_j (frame XT_j), top definite forms (frame XQ) | `Bridge.adInner` on HV and HX (definite adelic) | LC:184-187 (HV). Not unfolded further | — |
| target RR ⊂ EE (frame XE) | HE ≅ EEat with ipM(ν0, fd0), **without** the dimK factor | LC:189-190. XE_{v₀} = frameOf(nP⁻¹·Gram(Θe_i)), XE_{v≠v₀} = `rowXE` (PO:142-147) | as cited |
| Weil test vectors (layer lifts) | the Schrödinger model, L²(μ, 𝓧) with IsCovolOne | ptAt = pureTensorO = P(a⁺)·f (`ReadingsExistRow.lean:28-30`; DV:130-134). a⁺ = fockScale⁻¹·crea, fockScale = 2√(2π‖τ(ξ₀)‖) (LNF:130-141). `FockCoefficient` and `InnerProductFormula` use l2 μ 𝓧 and petW = l2(νW, fdW) (IPF:76, 120-160) | as cited |

## 2. Argument

### 2.1 Input (a), `BlockBound` (brief item 2)
- **Statement.** `BlockBound` (PWN:36-49) bounds `OpNormSqLe lam lam′ (jetOp …)` by tmax (PWN:32-34). Its hypotheses are:
  - Gaussian growth ‖G(z)‖ ≤ S·exp(Σ r_τ²|z_τ|²/2);
  - ‖cD_τ·r_τ‖² = 1/Ω_τ.
- **The two normed spaces** are VV_λ → VV_λ′ with `normSq` = Re fockL(v, v)/∏_τ eN(λ_τ) (NFL:71-77). That is the pairK norm at gramTw = 1 (CM:160-176).
- **Match with the column metric.** The column chain uses pairK through famIpAt (DHB:245-246; HEIGHT's reading of `CKB`/`JetCConstMul.block`, not re-read). The source N_u has the level-0 frame (D7F:297).
- So (a) is stated for the column metric of §1. The tie to the source and target norms is definitional, through `pairK`, modulo the definition of `OpNormSqLe`, which I did not open.
- **One metric for every level.** Every column level uses the same normalisation, with the extremal vector of norm 1. A per-weight normalisation that changed from level to level would therefore have to sit inside `normSq` itself, which is uniform in λ.

### 2.2 Input (b), the Rallis identities `thmA`/`thmB` (brief item 3)
- **The adjoint.**
  - `PThmA` (BLP:68-69): `Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) …`. The adjoint is taken between the Hilbert spaces (HV i t).H and (HW i sg0).H (LD:609).
  - `ThmA` (PO:260-265) states the same scalar on coordinates: ⟨θ′x, θ′y⟩_W = nP·λ·maj_{XT}(x, y).
  - On the W side, `EWnorm` (PO:247) and eW = √nP·subtype give exactly the HW norm. So **the adjoint is with respect to HW (and HV), the same inner product that defines XW_j in §1.**
- **The Gaussian and Fock normalisation.**
  - The hook main term enters as fock(δ, δ) in `FockCoefficient` (IPF:134-145), and `DeltaNorm` (IPF:147-149) evaluates it as the Fischer norm `Formalism.E.fock` (`FockGram/StatementFock.lean:9-10`). That norm has m!, with no π.
  - Its identification with the Weil-representation L² norm is `FockModel` (HLC:300-321), part of `PlaceModels` (HLC:384-385). It is **proved** as `fockModel` (DEZ:133-162), through `ipO_pureTensorO` (FVI:111).
  - The key computation is `scal_lemma_2` (FVI:69-109): (−fockScale_k⁻¹)(fockScale_l⁻¹)(−4πi·(ω-pairing)) = δ_{kl}, using fockScale² = 8π·Im τ(ξ₀) (`.../FockTheta/RealPlaceImaginaryGeneratorReEqZero.lean:28-32`).
  - So the creation operators are exactly unit-normalised for the Heisenberg character of ψ. **The Gaussian for which the hook formula holds is the vacuum of that Heisenberg representation, and the normalisation is proved, not assumed.**
- **The column-side theta.** ENGINE's H = area⁻¹·Σ z w̄ belongs to the column-side theta kernels (the jets K_j). It is not the Weil vector of the layer lifts. *(mine)* It enters only (a), through r² = π/area.

### 2.3 Input (c), the covolume (brief item 4)
- **One frame.** L3 (IS:315-316) is lcv(S.XW j, S.M j)/D ≤ l3. RecAt (CXC:57-59) bounds lcv((p.S false).XW i, …) by −slope(nrmR, latGood). nrmR is the HW norm (NNC:31-32), and XW is frameOf(Gram bW) in HW. So this is **the same Petersson-type inner product as in (b)**, up to the common nP and the 1/√nP in bW.
- **The comparison with petW.**
  - `MeasAt` (CXC:81-86) is produced by `covering_measure_reduction_alt` (CMR:18-27) as `measAt_of (exactAt_of_oneMeasure …)` (MAO:28-46), with |log ratAt| ≤ K·unitE.
  - `ExactRatio` (OMS:75-80) states ipAt(F, F) = ratio·probSq(f) whenever F v = adFun f (`Corr`, OMS:70-73).
  - adFun = lieFacZ·adel(f) (OMS:50-54) and probSq = (lieFacZ·petE_prob)² (OMS:45-48). **lieFacZ occurs on both sides.**
  - *(mine)* So ExactRatio amounts to "ν(𝓕)-normalised L² = vol·dimK × probability L²". The (2πx)^{−|G|/2} is the convention that fixes which adelic form an integral algebraic section f represents.
  - OneMeasure comes from `normalized_covolume_eq_one` ← PublishedHodgeBundleTheorems (`HodgeBundleWeights/NormalizedCovolumeEqOne.lean:34-35`). Its body (`covolume_measure_eq_one`) was not opened.
- **Where (2πx) is used again.** `FlatDegree` (EFS:751-754) is FlatExistsAt U x (−flatDegVal), with flatDegVal = (p−q)/2·logOm + q(log d − lrd E). Each flat section's degree is lineDeg of cInf, with cInf = homN U x (…) (EFS:443-456; `def deg` at EFS:514). Here homN = lieFacZ·ptN (IPM:680-681), the same factor and the same x as petW. **So the logΩ of (c) is computed in the metric of petW, by shared definition.**
- **What FlatDegree uses.** The geometry statement that `FlatDegree_holds` proves uses Hodge-Gram norms (`IsConstMul.lean:80-82`; `FlatDegreeHolds.lean:72-118`). Its link to homN runs through the transport chain [COVOL], whose bodies I did not open.

### 2.4 How (b) and (c) close against each other *(mine, from the read statements)*
- SpecDet (DETSIG; IS:304-311) gives det ι = κ^D·∏_j det θ_j in the frames XQ, XE, XT_j, XW_j. BoundsMu then uses lcv(XW_j, M_j), with the θ_j-image traded for M_j by finite indices (`Iw`, IS:275-276).
- So any rescaling of the HW metric moves λ_j (and hence L6) and lcv(M_j, XW_j) together.
- κ (EE normalisation) enters +meanLog κ in BoundsMu and −log κ in the height [DETSIG]. So the missing dimK in HE (LC:189-190) cancels.
- Only the absolute truth of L6 (for HW and HV as defined) and of D2 (for HW via petW) remains. Each is a theorem from premises, so a normalisation error could only be a false premise. On the archimedean Fock side the relevant premise is proved (§2.2). On the covolume side the factor that would carry the error (lieFacZ) is shared by definition (§2.3).

### 2.5 logΩ and the per-unit-weight constants (brief item 5)
Per lift j and place ρ, the coefficients of logΩ are as follows (they assemble as in DIVKEY step 1):

| input | coefficient of logΩ | other per-unit-weight constants |
|---|---|---|
| (a) BlockBound, (s4) | −Σ_iν_{jρi} = −(a_ρ[ρ∈TT] + k·w + δ) (s8) | none. tmax carries e·(2\|ν\|+2)^{2ab}, which is polynomial (PWN:32-34) |
| (b) L6, (s5) | 0 | none. The non-hook factors (dimK, vol, formal degree, mass, L^S, d^S) are ≤ 8f·nV²·Lp, which is poly(x) [L6]. No c^{\|wt\|} appears: fock(δ, δ) is exactly the hook (§2.2) |
| (c) D2, (s2) | +(p_j − q_j)·w | q_j(log d − log rd_E) per unit weight (flatDegVal). Its coefficient is q_j ≤ m, in the "m" family [COVOL, VOLUME]. \|log ratAt\| ≤ unitE |

Sum: −a_t·logΩ at tops, plus (p_j − q_j − k)·w·logΩ − δ·logΩ, both booked in the per-lift error [DIVKEY].
- The constant log(π/v) inside logΩ cancels exactly against Count5's log(v/π) [DIVKEY §2.2].
- No constant c·(weight) with coefficient ≍ a or ≍ k survives in any input. The cancellation is exact, not absorbed.
- The (2πx) of lieFacZ has no free-standing coefficient: it sits inside petW, homN and FlatDegree together (§2.3).

### 2.6 Numerical check of the constant *(mine; `numtest/normcheck_cs.py`, output `numtest/out_normcheck_cs.txt`)*
**Setup.** Curves A: g₂ = 4, g₃ = 0 (CM by ℤ[i], d = 4) and B: g₂ = 0, g₃ = 4 (ℤ[ω], d = 3). Here s₂ = 0, so σ = σ*, and D^aσ(0) is an exact integer (sigma_lib). The area comes from Δ = (2π/ω₁)^{12}η^{24}. L′/L(1, χ_{−d}) was summed in full periods with a tail term. For d = 4 it is checked against γ + 2log 2 + 3log π − 4logΓ(1/4) and agrees to 8 decimals.

| | d = 4 | d = 3 |
|---|---|---|
| Lean logΩ = γ + log(2π/√d) − L′/L(1, χ) | 1.47633597 | 1.49750497 |
| log(area(L₁)/π), Δ = 1 lattice | 1.47633597 | 1.49750497 |
| R(a) = 2log\|D^aσ(0)\| − (log a! − a·log(area/π)), a from 301 to ≈ 6000 | between −3.5 and +2.2 | between −4.5 and +2.1 |
| 2log\|D^a\| − [ph(a) − a·logΩ_Lean + (a/6)log\|Δ\|] at a ≈ 6000 | 7.4 | 5.4 |
| control: same with logΩ + log 2 | 4164 | 4161 |

**Reading.**
- The size is 2log|D^aσ(0)| = ph(a) − a·logΩ + O(log a), with exactly the Lean's Ω. The leftover ≈ ½log(2πa) is log a! − ph(a). The (a/6)·log|Δ| term rescales Δ = 64 or −432 to the Lean's Δ = 1 lattice, and by the product formula it lives at p = 2, 3.
- A per-unit-weight error of log 2 would show as ≈ 4160 at a = 6000. None is present.
- **Scope.** This tests (a) only, in rank one with one lift, which is the input that carries a. By the product formula, log|D^a| = Σ_p v_p log p holds trivially for the integer. How much of it the inert primes supply is the separate gain question of NUMTEST, which this does not revisit.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `IndefData` fields, `RowLatticeBoundForBasis`, `L3`, `L6` | IS:241-326 | XW, lam, XT shared by thmA, SpecDet, L3, L6 | the definitional tie of (b)–(c) | glue (read) |
| `CxData.XW`, `ThmA`, `EWnorm`; `toCx3` | PO:165-166, 247, 260-265; ZPE:120-140 | XW = frameOf Gram(bW) in HW; θ′ scalar in HW/XT | live realisation | glue (read) |
| `models_HW`, `ipAt` | LC:192-193; LD:321-323 | HW = ∏dimK·Schur-L²(νW, fdW) | the metric on M_j | definition (read) |
| `ExactAt`/`measAt_of`/`ExactRatio` ← `covolume_measure_eq_one` | MAO:22-46; OMS:70-80; `NormalizedCovolumeEqOne.lean:34` | nrmR = √ratAt·petW | the (c) side tie | core; producer body not opened |
| `petW`, `petAt`, `lieFacZ`, `homN` | IPM:664-681, 734, 787-788 | (2πx)^{−\|G\|/2}·L²(probability) | the covolume metric | definition (read) |
| `FlatDegree` (EFS) ← transport ← `FlatDegree_holds` | EFS:443-456, 751-754; `FlatDegreeHolds.lean:72-118` | flat degree in the homN metric = (p−q)/2·logΩ + q(…) | logΩ of (c) | core; transport bodies not opened [COVOL] |
| `fockModel`, `ipO_pureTensorO`, `scal_lemma_2`, `fockScale_sq` | DEZ:133-162; FVI:69-111; `RealPlaceImaginaryGeneratorReEqZero.lean:28-32` | Fischer norm = Weil L² for a⁺ = crea/(2√(2π\|ξ₀\|)) | the Gaussian normalisation of (b) | standard (Bargmann–Fock); proved (read to the commutator) |
| `FockCoefficient`, `DeltaNorm`, `InnerProductFormula` | IPF:76, 100-149 | the Weil coefficient = fock(δ, δ)·…; fock(δ, δ) = ∏ hooks | the hook term | premise statements read; suppliers [L6] |
| `BlockBound`, `normSq_eq`, `pairK` | PWN:28-49; NFL:71-77; CM:21-31, 160-176 | jet bound in the extremal-normalised Fischer metric | (a) | standard; proved [HEIGHT] |
| `base_lift_test` → `ratThOfLiftTest` (RATth) | PPS:86-90 | theta-lift matrices in algebraic bases are rational | carries the algebraic compatibility of fockScale with lieFacZ (both built on ξ₀) | definition to unfold; not opened |

## 4. Oddities
1. **The EE metric lacks the dimK factor that HW has** (LC:189-190 against 192-193). This is harmless, because κ absorbs it and cancels between BoundsMu and the height (§2.4). Still, the two "Petersson" normalisations differ by convention.
2. **The scale ξ₀ is used per place in one input and globally in the other.** fockScale uses Im τ(ξ₀) for each place τ (LNF:135-136). lieFacZ uses the single x = ‖φ₀(ξ₀)‖ for all τ (`CuspidalL2Subspace.lean:35`). These agree only if |τ(ξ₀)| does not depend on τ, e.g. if ξ₀ ∈ ℚ·√−d. The question matters only for rationality of θ_j (RATth) and the E1 index, not for λ or lcv separately. Not checked.
3. **No lemma compares the column Fischer metric with homN, or the two logΩ's.** Each logΩ is proved equal to the classical constant on its own (§0.5). That suffices for DIV, but it means the k·w cancellation rests on two independent proofs, and on the unopened FlatDegree transport chain.
4. **`OpNormSqLe` was not opened.** That it refers to `normSq` is taken from HEIGHT and NFL's name.
5. None else seen.

## 5. Coverage
Read in this pass:
- PROTOCOL; MAIN-ARGUMENT §0 and §5; NODE-STEPE and NODE-DIVKEY in full; NODE-HEIGHT, L6, COVOL, DETSIG and ARCH in full; NODE-VOLUME:1-60 plus grep; NODE-HS, GATIE and LEDGER by grep for metric, Petersson and normalisation lines; NODE-NUMTEST:1-60.
- IS:225-335; PO:60-185, 225-320; ZPE:80-170; LD:155-185, 516-690; LC:165-262; LL:440-520; AL:1-90.
- BLP:1-75; PPS:75-100; LNF:95-175; DV:60-160; SPF:90-96; OCC:276-282, 360-380.
- CXC:1-100; NNC:20-60, 270-292; IPM:640-810; EFS:700-760 plus grep 376-530; OMS:1-140; MAO:1-50.
- IPF:1-185; HLC:360-420 plus grep; `HeckeCharacterParameters.lean`:130-160; DEZ:100-175; FVI:69-111 plus grep.
- `FockVectorMatrixCoefficientFormulaStatement.lean`:1-16; `FockVectorsInnerEqFockInnerProductMulNormStatement.lean`:10-11; `RealPlaceImaginaryGeneratorReEqZero.lean`:28-32.
- `FockGram/StatementFock.lean`:1-30; `DisjointSplitLevelPlaces.lean`:85-110; `ReadingsExistRow.lean`:15-40.
- TCG:1-61; CMR:1-37; `NormalizedCovolumeEqOne.lean`:34-35; `FlatDegree.lean` (GeometryStatements, all); `FlatDegreeHolds.lean`:1-118; `IsConstMul.lean`:60-95; `CuspidalL2Subspace.lean`:25-40.
- PWN:28-50; NFL:65-80; CM:18-35, 155-180; DHB:238-252; D7F:286-300.

Not opened:
- the bodies of `covolume_measure_eq_one`, `ratThOfLiftTest`/`base_lift_test` and `OpNormSqLe`;
- the FlatDegreeSt transport chain (`degree_of_flatOnModel`, `kronecker_character_frame_bound`);
- `hermitian_metric_log_norm_formula`, `chowla_selberg_period`'s supplier, `heisO`/`symplO` (the Heisenberg character constant beyond `scal_lemma_2`), and `Bridge.adInner`;
- the Rallis unfolding suppliers (measure normalisations IsCovolOne, IsMinf, IsMeasDef) [L6].

Greps run:
- `def nrmR|def latGood|def nrmK`; `def petW|def petAt|def lieFacZ|covering_meas_of_prints`;
- `def ratAt|def ExactAt|measAt_of|exactAt_of_oneMeasure|normalized_covolume_eq_one`;
- `def fock\b|def ptAt|def pureTensorO|def aPlusAll|def fockScale`; `fockVector_matrixCoefficient_formula|PlaceModels|fockModel`;
- `HMod.Is|IsModels|models_HW`; `ratTh :=|RATth`; `def FlatDegree|def flatDegVal|def HasNorms|def xiR`.
