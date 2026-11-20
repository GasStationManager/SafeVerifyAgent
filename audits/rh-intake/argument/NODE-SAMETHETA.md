# NODE-SAMETHETA: one theta-jet entry, followed through both sides

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `LAT` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/LatAtLattice.lean`
- `TCC` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/TrueColumnChoicesHeckeCharReferenceEqOne.lean`
- `XIA` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/XiAtPenultimateEqXiCpl1.lean`
- `VAC` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1.lean`
- `TDC` = `Formalism/LocalToGlobal/KernelLattices/ThDistC.lean`
- `LAT2` = `Formalism/LocalToGlobal/KernelLattices/LateralTheory.lean`
- `KER` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/KernelEntriesCompatibleTrueColumns.lean`
- `EKT` = `Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsKerTie.lean`
- `RF` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/Reframe.lean`
- `NCM` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/NatCastMemOfPlace.lean`
- `FDC` = `Formalism/LocalToGlobal/PairingIndexBounds/OrthogonalChartLevels/FdOfCharts.lean`
- `KTH` = `Formalism/LocalToGlobal/PairingIndexBounds/OrthogonalChartLevels/KerTh.lean`
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `TLM` = `Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean`
- `TPLT` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TopPlaceLogTheta.lean`
- `MLC` = `Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanLogPeriodConjugatesEqChowlaSelberg.lean`
- `MLP` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogPeriodChowlaSelberg.lean`
- `CKB` = `Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ChainKernelBoundAtEmbeddingAnyLevelPrime.lean`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`

## 0. Verdict (short)

**Same number, same lattice, same period normalisation: yes.** I checked this at the level of definitions and theorem
statements. I did not check the proofs of the site identities.

1. **Loose end (1) is closed by a proved equation (`kerRd_Th`).** The theta used in `KernelDifferenceAtLevel` is
   `(t.rd u μ).Th`. On the live path it equals the chain's own theta `I.th` (`KER:153-169`, used at `EKT:43-45`).
   The local kernel `FrecG` is *defined* from the Taylor series of that same function. The relation is
   `Dec.SerAt` (`RF:138-143`), proved as `serAt_all`; its Lean statement is quoted in §2(b).
   `kerTh` and the global theta are the same constructor `thC`. The lattice δ·O_K (cc = ⊤), the factor area⁻¹, the
   coefficient ideal and the vacuum `eNat` all agree (`KTH:25-30` vs `XIA:256-259`, `TCC:155-164`).
2. **Loose end (2) is resolved: there is no net power of p on the kernel.**
   - `FrecG` multiplies by p^{expG} (`FDC:55`). `kerF` multiplies by eS/eT = p^{−expG} (`FGS:510-517`). Both use the
     same `len X` (`PendingLemmas/WittFractionAlgebraCp.lean:60`), so the two cancel exactly.
   - The chain entry therefore equals cK·DelF(raw series): `srOf` = (eS/eT)·ThF (`InertKernelTheory/TieSerPin.lean:11-13`).
   - `stmt_proved`'s bound never charges expG, and needs no charge. The jet bound g it feeds into adm7 is uniform in U.
     adm7 is a theorem quantified over **every** series f (`pending_tuple_admissible`,
     `…/RowActionCoefficients/LatticeShapeMiddleHolds.lean:26`). So whatever eS/eT does is already inside a proved
     statement.
   - The one place a negative expG must be paid is the **hypothesis** that clause 2 holds for p^{expG}·Θ. It is paid by
     `ScalGLt`: ‖p^{expG}·scalG‖ ≤ 1 (`InertKernelTheory/DefsRepLt.lean:193-197`). That is a `Joint.At.Scal` field,
     discharged by `scal_at_site` → `thetaSeries_scalar_bounded_of_pos_pair` (body unread).
3. **(3): the same function, variable and periods.**
   - Archimedean Ω_τ^ρ = area(Λ^ρ)/(π|ρ(c_D)|²) (`TPLT:49-50` with `TLM:157-158`). Its mean over conjugates is a
     Chowla–Selberg theorem whose hypotheses are **Λ = δ·σ(I), Δ(Λ) = 1** (`MLC:141-149`). That is the same lattice
     `lamOf D cc δ` (δ¹² = Δ(lamOf cc 1), `VAC:20`) that the p-adic side uses through `Base D cc δ` and `wModel`.
   - The function is the same holomorphic Θ on both sides: a reduced theta built from σ\* translates.
     - Archimedean: its growth e^{π|z|²/2A} is used with r² = π/A.
     - p-adic: the quotient by ∏σ\* in z = u⁻¹·log_W T is used.
   - c_D enters both sides identically: in the archimedean jet `jetC` and in the p-adic `polDY`/`polDel`.

## 1. Statement: the entry, as the Lean defines it (a)

**The step-map entry** (`LAT:73-78`): `jet i c c' := jetMap (jetC I.J.cD (I.th u a i …)) 0`, with
jetC c_D G m = (∏_k c_D(k.1)^{m_k})·∂^m G(0) (`TDC:60-61`; derivAt0 is the iterated Fréchet derivative, `TDC:56-58`).
So a single entry of the jet is

  E_m = c_D^{|m|}·∂^m Θ_{c,c′}(0),  with c_D^{|m|} := ∏_τ c_D(τ)^{|m_τ|}.

**Θ = `thAt` = `thOf … (xiAt …)`** (`XIA:254-264`):
- the constructor is `thC (embC σ₀) δ d sc AA Sall N N' levC (σ₀∘Ξ) (A.e …)`;
- the `Amb` record is built by `AmbIn.amb` (`TCC:155-164`):
  - δ = J.δ, with **Ok.delta: δ¹² = discr(lamOf ⊤ 1)** (`TCC:146-148`, `VAC:20`). So Λ := lamOf ⊤ δ = δ·O_K has Δ(Λ) = 1.
  - sc = area(Λ)⁻¹;
  - AA = perAA ⊤ = span{c·t : c ∈ O_K, t ∈ AA0} (`VAC:120-121`);
  - e = J.V.eNat χ, i.e. eNat = chiFac·thMoved (`VAC:140-141`). thMoved is two coset averages `Iop` of
    thZero = tensPow(thMM), carrying the 1/√index factors and the automorphy factor
    exp(−πHf(z,x) − πHf(x,x)/2), where Hf(z,w) = Σ z·w̄/area(Λ) (`VAC:40-52`).
- thMM = `thM L ω₀ (√d/2) lamMM gC κ` (`VAC:131`). By `IsThM` (`LAT2:23-29`) it lies in the theta space of
  H = area(L)⁻¹·I on ΛM, and tens4 θ = κ·kernel4(…).
- kernel4 is a product of th0 = opU(ω₀/2)(σ\*)(z)/opU(ω₀/2)(σ\*)(0)
  (`TorsionIntegrality/EisensteinTranslationProducts/SemiChar.lean:23,34`).
  - σ\* = wSigma·exp(−s₂z²/2) is holomorphic.
  - Its 2-torsion translate is normalised to 1 at 0.

**Constants in E_m.**
- c_D^{|m|}, where c_D(τ) generates ellT_τ = (emb_τ AA0)·O_M (`IsDgen`, `VAC:80-82`). This is an algebraic number, not a
  period.
- No π, no factorial and no Ω appear in the entry itself.
- ∂^m is a full derivative (Taylor coefficient × m!).
- The Gaussian exp(−π|z|²/A) is **not** part of Θ. It appears only as the growth bound (archimedean) and inside the
  automorphy factor of Iop.
- The finite-adelic data are Ξ = σ₀∘xiAt (lattice indicators) and chiFac (χ-values).
- The theta in the KerEntTied record is `(t.rd u μ).Th`. On the live path `t` is built with `cc := ⊤`, `δ := I.J.δ`,
  `B := I.J.toRec`, `cD := I.J.cD` (`KER:200-217`), and `kerRd_Th` proves
  `(I.kerRd l Z u a).Th seam (ambOf … I.J.toRec … I.J.cD) i c c' = I.th u a i …` (`KER:153-169`). So **(t.rd u μ).Th is
  the chain's Θ**. The step `stdRd_keep` (`EKT:43-45`) swaps in this rd and re-proves `O_Th` from it.
- cc = ⊤ on every KerEntTied of the live D (`IwasawaDecomposition/ChiDValuesAndCcTop.lean:114-116`, `ccK_top`).

## 2. Argument

### (b) The p-adic side

`KernelDifferenceAtLevel` (`InertKernelTheory/SecondKernelEntrywiseLastLevel.lean:46-53`):

  Rd(entRec x) = cK · DelF_j(cmp x, Sr),  with ‖cK‖ = 1,

and `tieDel_all_steps` instantiates Sr = `srOf S.Y` (`SP/KernelSiteFrameValuesAllStepsLtM.lean:69-82`).

The live kernel is ThA = FrecG(…, t.B, t.χ, ssRec, (t.rd).lev, J.xi0, muT, ltC) (`SP/KernelSiteContractionIdentityOperatorHalf.lean:24-28`).
`Dec.SerAt` (`RF:138-143`) states, as a proved theorem (`thetaSeries_site_eq_changedFrame_classSeries`):

  FrecG = linSub(ltC·subBG_{fd2}) ( pPow · ι(sC) · ι∘tay(thCl) ),

where:
- thCl = `(t.rd u μ).Th … j (cls La) (cls La')` (`RF:43-48`);
- tay = Taylor coefficients ∂^α/α! (`RF:21`, `TLM:115-118`);
- **pPow = p^{Σ_v vm_v(j+1)·(len_{j+1} − len_j)} = p^{expG}** (`NCM:50-51`);
- sC = scal0·chiFac⁻¹·sP (`RF:105-107`), and `Dec.ScalAt` gives sC = ρ·ρ′·uS·uT (`RF:149-154`);
- ι : ℂ → ℂ_p agrees with lam on Q̄ (`hι`). The Taylor coefficients are algebraic (`TransAlg`, `KernelLattices/FirstKernelLawReading.lean:386-388`).

The definitions then give:
- ThF = linSub(bc)(ThZA ThA) (`FGS:466-467`);
- eS/eT = ∏_v p^{vm_v(j+1)(len_j − len_{j+1})} (`FGS:510-514`);
- kerF = (eS/eT)·DelF(G, f) (`FGS:516-518`);
- srOf = (eS/eT)·ThF (`TieSerPin.lean:11-13`).

The pairing is DelF(G, f) = Σ_n n!·coeff_n f·coeff_n(polDel G). By `TieOpS` (`RF:50-56`):

  coeff(polDel(Gm x)) = sO·trDY(polDY(c_D, Q)),

and polDY carries C(c_D) per variable (`InertKernelTheory/KernelDifferenceOfFrame.lean:61-64`). One displayed formula:

  ι(cK⁻¹·entry) = Σ_α ι(c_D^{|α|}·∂^αΘ(0)) · ι(ρρ′·uS·uT) · [ltC^{|α|} × (frame minors of subBG, bc)] · sO · (Q-coefficients),

with **net power p^{expG}·p^{−expG} = p^0**.
- ltC = (u·ep)⁻¹ is a unit (KERNELLAW, `RepDict.lean:478-487`).
- cK is a unit.

**Loose end (2), line by line.**
- `FDC:55`: `((p : ℂ_[p]) ^ (∑ v, X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2))) • serP …`
- `FGS:510-517`: `eS … ^ (X.vm v (j + 1) * Y.len v j La.2)`, `eT … ^ (X.vm v (j + 1) * Y.len v (j + 1) La'.2)`,
  `kerF … := (Y.eS j La * (Y.eT j La')⁻¹) • Y.DelF j G f`.
- `Y.len = len X` (`WittFractionAlgebraCp.lean:60`). So ker = DelF(raw), exactly.

Where the bound comes from:
- Clauses adm2/adm2b/adm3/adm11 are about ThA = p^{expG}·raw (`FGS:546-563, 627`).
- adm7 (`FGS:613-623`) reads: if every PI-jet of f is ≥ g, then p^{ΣN′}·kerF(linSub f)(G) ∈ g·HtupW(L′).
- Feeding f = ThZA ThA gives kerF(linSub(bc) f) = ker. So the chain is bounded by the jet bound of p^{expG}·raw,
  through a theorem that holds for all f.
- `LowTermBound`'s right-hand side (`FGS:708`) contains gB/gA (Legendre minus LT cost), Pr and dG, and no expG term. It
  needs none, because there is no residual p-power.
- The cost of a negative expG falls on the hypothesis side, `ScalGLt` (`DefsRepLt.lean:193-197`):
  `‖(p : ℂ_[p]) ^ expG X j L0 La' * lamC lam (scalG fd χ muT j L0 La')‖ ≤ 1`.
  *I infer* this is plausible: scalG contains χ-values of detId ideals whose p-parts have length len, which should
  supply p^{−expG}·unit. Unverified.
- **No uncharged division found.**

### (c) The archimedean side

`kernel_le_sharp` (`CKB:17-35`) bounds the conjugate kernel of `stepC … (ambOf s B χ cD)`. That is the same Amb as the
chain (`AmbIn.amb_eq_ambOf`). The bound is exp(kernelBound_sq(…, logOmAt B cD M ρ, logThAt B M ρ …)), via
`block hB …` (`CKB:76-83`) with BlockBound hypothesis |c_D r|² = 1/Ω. Here:
- logOmAt(ρ, τ) = −logMet(Λ, ρ, c_D(τ)) = −log(π|ρ c_D(τ)|²/area(Λ^ρ)) (`TPLT:49-50`, `TLM:157-158`);
- Λ^ρ = lamConj (g₂, g₃ conjugated, `TLM:128-130`), so **Δ(Λ^ρ) = ρ(1) = 1**.

One displayed formula, per conjugate ρ and step (NODE-HEIGHT §1(b)):

  |ρ(c_D^{|m|}·∂^mΘ(0))|² ≤ S_ρ²·∏_τ (π|ρ c_D(τ)|²/area(Λ^ρ))^{|m_τ|}·e·(2|m_τ|+2)^{2ab}·exp(Σ ph(m)),  with S_ρ² = exp(logThAt ρ).

This has the same c_D^{|m|} as the p-adic side and r² = π/area. It is consistent with Θ ∈ Th(H = area⁻¹·I), so
|Θ(z)| ≤ S·e^{π|z|²/2A} (`LAT2:23-26`).

**The normalisations agree.**
- `mean_log_area` (`MLC:141-149`) takes `hL₀ : z ∈ L₀ ↔ ∃ x ∈ I, z = δ·σ x` and `h1 : g₂³ − 27g₃² = 1`. It concludes
  mean_s log(area(L_s)/π) = γ + log(2π/√d) − L′/L(1, χ).
- `meanPeriodAt` (`MLP:58-85`) applies it to `lamOf D cc δ` with `IsDiscriminantTwelfthRootOfIdealLattice D cc δ`,
  the same δ-predicate as `KerEntTied.δ_ok` and `AmbIn.Ok.delta`. The p-adic `GL3Theta.At D cc δ g` and
  `wModel lam Λ` (Δ = 1, `TLM:176-182`) use the same `Base D cc δ` (`B.tor` = `tor0 D cc δ`).
- The mean of log|ρ c_D|² is not zero. `meanPeriodAt` absorbs it into logOmVal through the log rdE and two_log_brN terms
  (`MLP:80-85`). So logΩ in the Lean includes the norm of AA0. *I infer* this matches c_D being a p-unit at
  unramified inert p. Not verified.

### (d) The product formula as the Lean has it

**The Lean never forms Σ_v log|E_m|_v = 0 for a single entry.**
- The comparison is made on lattices:
  - divisibility at served inert w is a lattice statement, chainK_m(Iprod) ⊆ ϖ^{gain}·Int (LOCALDIV);
  - the archimedean side is an operator-norm height (HEIGHT).
- The two meet in the slope inequality on N_u against RR^∨ (SUMMARY §1.4).

Places other than served inert ones:
- `gainS` = 0 at excluded or split places (GLOBALCHAIN §1(d)). Integrality there is whatever B_u(M_u) ⊆ RR^∨ asserts
  at baseline. I did not trace that.
- The p-adic integrality used at served p (adm3, jets ≥ 0) needs:
  - p ≥ 5 (`Std.five_le`);
  - p ∤ d (CM2);
  - the 2-torsion translate normaliser 1/σ\*(ω₀/2), a unit at p ≥ 5 when Δ = 1 (I infer);
  - s₂ non-integrality, which is absorbed into be (KERNELLAW §6.1);
  - Iop's 1/√index, which needs index prime to p (StdStep).
- The stabiliser denominators cost dG_j (charged).

I found no place where E_m is assumed integral without a supplier. I also did not find a single theorem stating
"v_ℓ(E_m) ≥ 0 at every ℓ".

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `serAt_all` (`thetaSeries_site_eq_changedFrame_classSeries`) | `SP/ThetaSeriesSiteEqChangedFrameClassSeriesStatement.lean:7`; def `RF:138` | local kernel FrecG = frame-substituted p^{expG}·ι(sC)·ι(Taylor(global Θ)) | **core** (the identification; body unread) |
| 2 | `thetaSeries_scalar_bounded_of_pos_pair` (ScalGLt) | `SP/KernelSiteSeriesScalarPowIntegral.lean:15` | ‖p^{expG}·scalG‖ ≤ 1 | **core**: this is where a negative expG is paid |
| 3 | `pending_tuple_admissible` (adm7) | `…/LatticeShapeMiddleHolds.lean:26` | jet bound ⇒ lattice bound for (eS/eT)·DelF, for all f | core, proved; absorbs the eS/eT normalisation |
| 4 | `kerRd_Th`, `kerEntTied_true`, `stdRd_keep` | `KER:153, 179`; `EKT:16` | (t.rd).Th = chain theta; cc = ⊤; δ = J.δ | glue, proved (read) |
| 5 | `mean_log_area` / `meanPeriodAt` | `MLC:141`; `MLP:58` | Chowla–Selberg mean for Δ = 1 lattices δ·I | standard, proved (statement read) |
| 6 | `FamilyTie`/`normalisedFamily_*`, `block` | `CKB:47-49, 76` | Gaussian growth of the conjugate Θ^ρ for Λ^ρ | core analytic, unread |
| 7 | `Dec.ScalAt` | `RF:149` | sC = ρρ′·uS·uT | glue; supplier unread |

## 4. Oddities

1. **The p-adic kernel's jet bounds apply to p^{expG}·Θ, not Θ.** This is harmless as accounted for above. If
   expG < 0, clause 2 is a strictly stronger claim than integrality of Θ/∏σ\*, and its truth rests on ScalGLt (child 2).
2. **ι : ℂ →+* ℂ_p** is an abstract field embedding, pinned only on Q̄. It is harmless, because every Taylor
   coefficient used is algebraic (TransAlg).
3. **Archimedean kernel vs chain entry.**
   - CKB bounds `kerOf stepC`, built from `jetK` = desc(chiF⁻¹·jetC(thInd)) (`TDC:117-118`).
   - The chain's entry includes chiFac inside eNat.
   - These agree up to χ-values. *I infer* those have absolute value 1 at every conjugate. Not checked.
4. **c_D (the generator of emb(AA0)·O_M)** sits on both sides. Its p-adic valuation at served w was not checked.
   If p | N(AA0), the p-adic side would gain v(c_D)·|m|. That gain would be paid by the archimedean −log|c_D|² inside
   logΩ, and the Lean's logΩ = logOmVal includes the rdE/brN term for it. So I see no asymmetry, but it is unverified.
5. Nothing false-looking found.

## 5. Coverage

Read:
- context files;
- `LAT:1-260`; `TCC:100-200`; `XIA:225-300`; `VAC:1-214`; `TDC:1-140, 270`; `LAT2:1-180`;
- `KER:1-220`; `EKT` (all); `ChiDValuesAndCcTop.lean:100-124` (grep); `KerChTie.lean:1-140`;
  `FirstKernelLawReading.lean:300-460`;
- `SecondKernelEntrywiseLastLevel.lean:1-90`; `KernelDifferenceOfFrame.lean:1-110`; `TieSerPin.lean`;
- `SP/KernelSiteFrameValuesAllStepsLtM.lean`; `SP/KernelSiteContractionIdentityOperatorHalf(Statement).lean`;
  `SP/ThetaSeriesSiteEqChangedFrameClassSeriesStatement.lean`; `SP/KernelSiteSeriesScalarPowIntegral(Statement).lean`;
- `RF:15-175`; `NCM:35-60`; `FDC:1-90`; `KTH`; `ScalG.lean:1-80`; `DefsRepLt.lean:185-200`;
- `FGS:440-640`; `DataG.lean:40-100`; `InvarianceIffAdditiveMapsExist.lean`; `InvarianceRepresentativesTrivial.lean:425-445`;
  `WittFractionAlgebraCp.lean:60` (grep); `LatticeShapeMiddleHolds.lean`;
- `TLM:100-215`; `TPLT:1-80`; `MLC:30-70, 135-160`; `MLP:50-90`; `CKB:1-95`; `SemiChar.lean:23,34` (grep);
  `DataForms.lean:60-175`.

Not opened:
- bodies of `serAt_all`, `thetaSeries_scalar_bounded_of_pos_pair`, `delPolAt_site` leaves
  (`contraction_identity_frames_with_operator_scalar`, `kernelScalar_of_sourceTarget_parts_product`);
- `normalisedFamily_*`, `block`;
- `GL3Theta.applyAt0`/`polD`, beyond their use in `entQ`;
- integrality at non-inert places (RR^∨ baseline).
