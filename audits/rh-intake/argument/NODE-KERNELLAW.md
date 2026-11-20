# NODE-KERNELLAW: from the CM theta function to the abstract kernel law

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `TLM` = `Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean` (namespace `TaylorLogMetric`)
- `GL3` = `Formalism/SharpRestriction/GlobalSchurBounds/GL3Theta.lean`
- `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- `CMS` = `Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean`

## 0. Verdict (short)

- **The bridge for clauses 2/2b/3 (`first_kernel_law_global_small`) is proved in the tree, from mathematics I recognise**
  (σ-function of a CM curve; Mazur–Tate/cube-theorem integrality; Robert/Kato-type distribution relation; Deuring good
  reduction; Honda/Lubin–Tate isomorphism of the supersingular formal group; Dwork). I did not read every leaf.
- **The `ltC` flag is resolved.** c = ltC = (u·ep)⁻¹ has ‖c‖ = 1, proved (`RepDict.lean:478-487`): the lattice is
  normalised so that Δ(Λ) = 1, hence Δ(good model) = u⁻¹² and ‖Δ‖ = 1 forces ‖u‖ = 1; ep is a unit of W by
  definition of `LTIso`. The same `ltC S.g S.hLT` is used in the kernel-difference identity
  (`SP/KernelSiteFrameValuesAllStepsLtM.lean:65-74`). Since c is a unit, rescaling by c changes no valuation, so even a
  mismatch of c could not create a gain.
- **`KernelDifferenceAtLevel` (target 3)** is proved (`del_of_pos` → `tieDel_all_steps`) by a chain of frame/polynomial
  identities. I read its top level only. It is a change-of-coordinates identity, with a unit cK. Nothing analytic is
  involved. The open question is only whether the global theta used in the chain (`(t.rd u μ).Th`) is the same function
  as `kerTh` in the local kernel; I did not close that by reading.
- **`GlobalArtinReciprocity` has a closed proof term**: `CompanionTheory.FamInh.globalArtin`
  (`CompanionTheory/AutomorphicTheory/PlaceSeparation/IsOpenQuotientMapArt0.lean:233`), built from an in-tree Artin map
  `art0` (`GroundTheory.GlobalFields…`, unread). It is re-exported as `GlobalTheory.globalArtinReciprocity_holds`
  (`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlobalArtinReciprocityHolds.lean:5`). CM3 and CM4 are
  also proved (`CMGoodModels/CmAll.lean:10-11`). Because these are `Prop`s with closed proofs, the hypothesis is
  discharged, whichever term the live path passes.

## 1. The classical picture, and the dictionary to the Lean

### 1.1 Classical facts (in my words)

- Let K = ℚ(√−d), with d prime, d ≡ 3 mod 4, and let 𝔞 = cc be an ideal prime to 2dp. Choose δ with δ¹² = Δ(𝔞).
  Then Λ = δ·𝔞 has **Δ(Λ) = 1**. This δ plays the role of the period Ω.
- With Δ = 1 we have j = 1728·g₂³ and 27g₃² = g₂³ − 1. So g₂ and g₃ are algebraic and p-integral for p ≥ 5, and
  y² = x³ − (g₂/4)x − g₃/4 has discriminant exactly 1.
- For p inert in K the reduction is supersingular. Its formal group is a Lubin–Tate formal O_{K_p}-module (O_{K_p} = ℤ_{p²})
  of ℤ_p-height 2, with uniformiser p·(root of unity). Over Ŵ = W(F̄_p) it is isomorphic, by a power series θ(T) = εT + …
  with ε ∈ Ŵ^×, to the Honda group with log ℓ(X) = Σ_j X^{p^{2j}}/p^j. This is Honda/Lubin–Tate theory plus Deuring.
- **The theta function is σ\*(z) = σ(z)·exp(−s₂z²/2)**, where s₂ = s₂(Λ) is the value at Λ of the non-holomorphic E₂\*,
  normalised so that η(ω) − s₂ω = πω̄/A(Λ).
  - It is the unique odd entire function with σ\*′(0) = 1 and σ\*(z+ω)·exp(−πzω̄/A − π|ω|²/2A) = ±σ\*(z).
  - For a CM lattice, s₂ is algebraic (Ramanujan–Masser–Shimura).
- **Supersingular case.**
  - There is no Frobenius (unit-root) splitting of H¹_dR, so there is no canonical Mazur–Tate p-adic σ.
  - What replaces it is the **CM splitting**: the eigen-decomposition of H¹_dR under O_{K_p}. At inert p, the Frobenius σ
    acts on O_{K_p} as complex conjugation, so this splitting is the hermitian one.
  - σ\* is the complex realisation of that splitting (Shimura/Katz). In p-adic terms it is characterised by the
    distribution relation σ\*(αz)/σ\*(z)^{αᾱ} = (an elliptic function with divisor on E[α]). That function is p-integral
    in the formal parameter for α prime to p, because prime-to-p torsion is integral and stays off the formal group.

### 1.2 How the Lean realises this (the Lean says)

| classical | Lean |
|---|---|
| Λ = δ𝔞, Δ(Λ) = 1 | `lamOf D cc δ` (TLM:53), `IsDiscriminantTwelfthRootOfIdealLattice`: δ¹² = discr(lamOf cc 1) (TLM:59) |
| Weierstrass model | `wModel` = ⟨0,0,0,−g₂/4,−g₃/4⟩ mapped by `lam : Q̄ → ℂ_p` (TLM:183); `JetsModel.wModel_Δ` gives Δ = 1 (used at `RepDict.lean:480`) |
| good model over Ŵ | `G1` = (lam, Λ, change of variables C = (u,r,s,t), wq, ex) (GL3:62); `IsModelU` (integral, ‖Δ‖ = 1, GL3:46); `ModelOverW` (coefficients in Ŵ, GL3:57) |
| formal log of the model | `g.l = flog g.W g.wq` (GL3:75; TLM:207) |
| Honda/LT isomorphism | `LTIso g` (`…/PendingLemmas/CoeffOneLNe.lean:60`): ∃ ep ∈ W^×, θ ∈ W[[T]], θ(0) = 0, θ′(0) ∈ W^×, ℓ(θ(T)) = ep·g.l(T). A non-strict isomorphism over W with unit leading coefficient |
| σ\* | `sgStar Λ` (TLM:238): the ε-choice of the function with exactly the functional equation above; `sgSer` = its Taylor series mapped to ℂ_p (TLM:242). `Sigma.sgSer_eq` identifies it with the explicit σ-series with s₂ = `F.s2 L` (`RepDict.lean:334-336`) |
| z in the formal parameter | `ePhi1` = σ\*(u⁻¹·log_W T)/(u⁻¹T) (TLM:245); `g.ph = −log ePhi1` (GL3:80) |
| Gaussian / bilinear | `g.be(a,b) = ph(a+_E b) − ph(a) − ph(b)` (GL3:101); `beLT = beOf g ep` (CoeffOneLNe:123) |
| "≃" | f ≃ g ⇔ exp((f−g)∘ℓ) has W-integral coefficients (FGS:139; GL3:27) |

### 1.3 What the kernel law says, in these terms

**Clause 2** (`ExtensionLocalCondition`, FGS:162). In LT-log coordinates, the restricted kernel is
Th = exp(−Ph)·U. Here:
- U(ℓ(X)) is integral;
- Ph is even (Ph(−X) ≃ Ph);
- Ph ≃ Σ_e be(x_e, y_e), with one term per hyperbolic pair of variables;
- be is hermitian-biadditive mod ≃: `BeProp` (FGS:147), be(αX, Y) ≃ be(X, σ(α)Y) for α ∈ W(F_{p²}).

So the kernel law is "theta = (hermitian Gaussian in log coordinates) × integral".

**Where hh and π/p come from** (LOCALDIV, with my reading of `RestBeta`/`RestGc`,
`MV/DworkExponentialRestrictions.lean:15-36`):
- Every hermitian be is ≃ a standard Gser(c, σc), with c ∈ W(F_{p²}).
- After the change Z ↦ ϖZ (ϖ^{p²−1} = p) its exponential factors as exp(−(π/p)·hh(Z))·V, with π = ϖ^{p+1} (π^{p−1} = p),
  V integral, and hh = Σ_s u_s S_s(Z)^p·S_{s+1}(Z).
- S_s = Σ_l (−1)^l Z_{s−2l}^{p^{2l}} are Frobenius-twisted LT logs (FGS:200-211).
- *I infer:* the leading monomial of hh is Z_s^p·Z_{s+1}. Undoing the rescaling, (π/p)·Z^pZ′ = z^p z′/p. So the
  Gaussian's obstruction to integrality is the term x^p y/p. This term pairs the Hodge line with its Frobenius image, the
  second O_{K_p}-eigenline, which is the hermitian/CM splitting. Its denominator is exactly one p per factor. That is
  the "#factors" loss in LOCALDIV.
- Plausibility as a theorem about σ at supersingular primes: consistent with what I know.
  - The supersingular p-adic σ converges only on a disc of radius about p^{−1/(p−1)} (Bernardi-type results).
  - The ±-logarithms Σ(−1)^j X^{p^{2j}}/p^j are Kobayashi's.
  - I do not know this exact factorisation as a named published theorem.

**E₂\* at the CM point.**
- The Lean takes s₂ = εu²·lam(s₂(Λ)). It proves s₂ algebraic (`Sigma.secondEisensteinAlgebraic`, derived from `invAlg`
  in `SP/CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra.lean:27`) and s₂ ∈ ℚ̂_p^{ur}
  (`s2_in_unramified_closure`, `SP/PadicNormTwoHundredSixteenEqOneOfFiveLe.lean:505`, using CM4).
- **It never asserts ‖s₂‖ ≤ 1.** `CurveAt` (`IKT/DefsRep.lean:17`) requires integrality of g₂, g₃ and θ, ‖ε‖ = 1, the norm
  relation, and be ≃ cob(F, phFF). It does not require integrality of s₂.
- So whatever denominator s₂ has at p is absorbed into the class of be, and `RestBeta` normalises that class to
  Gser(c, σc) with c ∈ W.
- The real constraint on s₂ is the **norm relation** `NormRel` (`…/GaussSumParity/StatementC.lean:27`):
  ph([α]T) ≃ α·σ(α)·ph(T) for every α ∈ ℤ_{p²}^×.
  - It is proved in `rdictMain` (`RepDict.lean:420-438`). It is first proved for α = m + nω_K prime to p, via `nrDense`
    with CM4 (prime-to-p torsion of a good model is integral and unramified), and then extended by density of O_K in
    ℤ_{p²} and closedness of ≃.
  - This is the classical integrality of σ\*(αz)/σ\*(z)^{Nα}. With σ = Frobenius = conjugation on O_K, α·σ(α) = Nα. A
    wrong s₂ would break it, because α² ≠ αᾱ for non-real α.

## 2. Statements of the three targets

### T1. `first_kernel_law_global_small : TranslatesOfInertKernelAtPlace`

Location: `IKT/InertCoprimeLemmas/FirstKernelSmallOfFrameTwist.lean:124`, under `[Fact CM2]`.

Conclusion: clauses adm2, adm2b, adm3 for the pending datum whose kernel is
`FrecG E pos fd B χ g.lam SS cl Ξ₀ muT (ltC g hLT)` (`…/OrthogonalChartLevels/FdOfCharts.lean:42`). Unfolded
(`FirstKernelSmallOfFrameTwist.lean:39-56`), the kernel at (j, La, La′) is
  ThA = linSub(subBG)( sclY(ltC)( p^{expG}·pSer_lam( scalG·kerTh B χ SS cl (kerN_j La)(kerN_{j+1} La′) Ξ ) ) ).

The pieces:
- kerTh is the global theta of the hermitian lattice pair. Its building block is `B.eNat χ N N′ L L′`
  = χ-factor · Iop(Iop(thZero)) (`KernelLattices/LateralTheory.lean:170-178`), i.e. the standard theta
  thZero = tensPow(thMM) transported to (L, L′) by finite coset averages with a 1/√index factor.
- thMM is the one-copy theta on ℂ^{Tau}/(Λ⊗𝔄) for the CM type Tau of the host E, normalised by κ and the 4-fold
  isometry gC (`LateralTheory.lean:128-155`).
- pSer is the Taylor series at **z = 0**, coefficient-wise mapped by lam (TLM:211). Translates by prime-to-p torsion t
  enter through `IsComb` (TLM:279) and `TorsPrime`.
- sclY(c) rescales every variable by c; linSub(subBG) is the frame change of variables.
- expG = Σ_v vm·(len_{j+1} − len_j) (`IKT/ScalG.lean:19`). scalG is a ratio of χ and μ̃ values (`ScalG.lean:22`).

**The coordinate.** The Taylor variable is z in ℂ^{Tau×N′×N}. It is pulled back along z_i = (u⁻¹)·log_W(T_i) in an
orthonormal O_K-basis b of the hermitian Hom-lattice (`atLog`, TLM:255). Then T ↦ LT parameter by θ.

**The CM point.** The moduli point is the CM curve E_Λ itself. The expansion is at the origin of (E_Λ ⊗ 𝔄)^{N′N} and at
its prime-to-p torsion translates. It is not at a point of the upper half-plane.

### T2. `admissible_fourth_instance` / ExpansionEquality

The chain map equals Σ_{La} (cK/|Stab La|)·ker_j(La)(F), with cK a unit (FGS:566).
- It is assembled from `TiesAt` (`IKT/SecondKernelEntrywiseLastLevel.lean:55`), whose last part is T3.
- `TieSerAt` (:39) says ThF = (eS/eT)⁻¹·Sr. Since kerF = (eS/eT)·DelF(ThF), this gives ker = DelF(Sr): the p^{expG}
  inside ThA is taken back exactly.

### T3. `KernelDifferenceAtLevel` (:46)

  Rd(entRec(global class, x)) = cK·DelF_j(cmp_j x, Sr_j(La)(c′, L′)), with cK, cK⁻¹ ∈ O.

In words: the ℂ_p-image (via ι = lam on Q̄, `hι`) of the global step-map entry, which is a P(∂)-jet of the global theta
at 0 against the frame polynomial of column minors, equals a unit times the local derivative pairing DelF of the local
kernel series.
- Proved by `StepDel.del_of_pos` (`SP/KernelSiteFrameValuesPositiveSteps.lean:10`) → `DelA.tieDel_all_steps`
  (`SP/KernelSiteFrameValuesAllStepsLtM.lean:24-94`).
- That proof uses:
  - `stepDeterminantConstant_unit_independent`, which gives cK and ‖cK‖ = 1;
  - `operatorOnFrame_and_classSummand_polynomial`, which expresses the global entry as
    (∏ de^{sDiv})⁻¹·frPoly(ρρ′·framePol(Q, Th));
  - `transportedFramePolynomial_complex_values_at_point`;
  - `equiv_frame_b … (ltC S.g S.hLT)`, the **same c**;
  - `kernelSite_contractionIdentity_operatorHalf`.

### How CM2 and CM3 enter

- **CM2** (CMS:45): every CM-by-O_K lattice has, at every l ≥ 5 with l ∤ d, a rescaling λ with λ⁴g₂, λ⁶g₃ ∈ ℚ̂_l^{ur},
  integral, and unit discriminant.
  - It is proved from GlobalArtinReciprocity + Chebotarev (`CmGoodModelOfGlobalArtinReciprocity.lean:10`) and passed as
    `Fact` in `servH_row_of_artin` (`SP/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean:15-24`).
  - It supplies `ModelOverW`, the existence of g with `At`, and feeds `kernels_integral_inert`
    (`IKT/KernelsIntegralInert.lean:9`).
  - It is consistent with Weber: γ₂ = j^{1/3} and γ₃ = √(j−1728)/√−d generate unramified extensions at l ∤ 3d.
- **CM3** (CMS:49): the u-series composed with (ε·ℓ) has integral ℚ̂^{ur} coefficients at inert l. That is the
  Honda/LT isomorphism with an integral unit ε. Proved (`ReciprocityTheory/…/FgClose.lean:25`, via `curve_law`).
  - On this path the corresponding facts are `LTIso` (a hypothesis of T1, supplied upstream by
    `exists_genusOne_formal_iso_of_unramified_good_reduction`, unread) and `thetaS` integral (`hTT`,
    `RepDict.lean:394-399`).
- **CM4** (`CMGoodModels/CM4.lean:7`): prime-to-l torsion points have integral unramified x, y on a good model. Proved
  (`…/UnramifiedIntegrals/TorStatus.lean:15-38`) by "torsion of order prime to l is not in the formal group". Used for
  the norm relation and for s₂ ∈ ℚ̂^{ur}.

## 3. Argument (two levels)

### T1, level 1 (`FirstKernelSmallOfFrameTwist.lean:21-82`)

1. Rewrite the kernel as linSub(S)(sclY(ltC)(F)), where F = p^{expG}·pSer(scalG·G) (`hFam`).
2. Get BeProp for beLT (`beProp_ofA`).
3. Get `CombAtLt`: F is a p-integral combination of prime-to-p torsion translates of the standard theta for admitted
   lattices (`combAtLt_of_dataRec` + `combAtLt_scalar` with `hSc`).
4. Get `FrameHypLt`: in each frame φ, the kernel is a hyperbolic σ-semilinear substitution of thOrth (the theta in an
   orthonormal O_K-basis b) (`frameHypLt_of_lat`).
5. Apply `K1_representatives_LT_of_dictionary` (`…/K1RepresentativesLTOfDictionary.lean:253`) with `curve_dictionary`
   and `kernels_integral_inert`.
6. adm2 and adm3 follow from adm2b by `admissible_second_of_variant` / `admissible_third_of_second_eleventh` (:131-134).

### T1, level 2

**(i) `K1_representatives…` (:253-286).**
- From `CurveDict` obtain g₂, g₃, ε, s₂ with `CurveAt` and `DictInt`.
- `DictInt` says: if, in Weierstrass-formal coordinates T_i, G·∏_i ePhi1(T_i)⁻¹ is integral (`ePh`, TLM:251), then
  exp(Σ_i ph(X_i))·(thOrth(c·b)G)∘ℓ is integral, with c = u⁻¹ep⁻¹. That is the transfer from the Weierstrass formal
  parameter to the LT parameter.
- `IntInert` supplies the hypothesis for the real theta.
- `k1gen_of_orth` (`RepAsm.lean:17`) converts exp(Σ_i ph(X_i))·Θ integral, after the hyperbolic change hypLin, into
  Ph ≃ Σ_e be(x_e, y_e). It uses the cube relations (be is the polarisation of ph mod ≃) and `CurveAt`'s
  be ≃ cob(F, phFF).

**(ii) `rdictMain` (`RepDict.lean:301-553`), the one-variable law.**
- g₂(W) = u⁻⁴·g₂(Λ) and g₃(W) = u⁻⁶·g₃(Λ).
- σ\* rescaled is the σ-series of W with s₂ = u⁻²s₂(Λ) (`hR`).
- ph = phW(W, s₂) (`formal_phase_agree`).
- s₂ ∈ ℚ̂^{ur}.
- θ integral.
- NormRel by density.
- BeRat (be has K₀-coefficients) from `beta_coefficients`.
- be ≃ cob(F₀, phFF) (`coboundary_exact`, `coboundary_equivalence`, `phase_compatibility`).
- **‖u‖ = 1 from Δ(W) = u¹²·Δ(wModel) = u¹² and ‖Δ(W)‖ = 1** (:478-487).
- `dict_core` performs the change of parameter T = ν·v(T′) and gives exp(phC)·… integral, with V = exp(phC − ψ)
  integral (:489-553).

**(iii) `kernels_integral_inert` (`IKT/IntegralInertOfWeakApprox.lean:9-13`), the multi-variable law.** The
integrality of θ_{L,L′}/∏σ\* in formal coordinates is reduced in stages:
1. One copy, N = N′ = 1, on ℂ^{Tau} (`OneCopyLoc`, `IKT/DefsMM.lean:40`). This is obtained from the 4-fold isometry
   `IsomONB` (`IKT/OneCopyTh1S.lean:51`): ⊕⁴ of the one-copy hermitian lattice is, with prime-to-p index, the standard
   product lattice, whose theta is ∏σ\*. The relation is tens4(thMM) = e·kernel4(g₁), with ‖e‖ ≤ 1.
2. From one copy to 2×2 (`FourProd`, DefsMM:62).
3. From 2×2 to even N×N′ by tensor (`TensFact`).
4. To an admitted (L, L′), which is equal to the standard lattice away from p, via `StdStep`: a combination of
   prime-to-p torsion translates of thZero with integral algebraic coefficients.
5. Change between local orthonormal bases (`LocInv`, unit_substitution_local).

*I infer:* this is the standard fact that, for a principally polarised CM abelian variety isogenous to E^g by a
prime-to-p isogeny, the reduced theta functions are combinations of translates of products of σ\*. The 4-copy device
(Lagrange) produces an explicit isometry over K.

### T3, level 1

Fix the class and the frame decomposition d₀. Write the global entry φ_κ as a polynomial P (frame polynomial of the
theta datum, of weight ν_{j+1}). Then transport P along the frames, which brings in `ltC`. The contraction identity
turns "P evaluated on the global jet" into "DelF of the local series". The two realisations agree because ι is
injective (`MvPolynomial.map_injective`, :90). I did not open level 2.

## 4. The higher-rank step (d)

- The local kernel lives on variables (Frobenius position s ∈ ℤ/n′, row a, column b) (`Zidx`, FGS:186).
- The Gaussian is Ph ≃ Σ_{e = (r,a,b)} be(x_e, y_e): one hermitian pair per (Frobenius half-orbit, matrix entry). The
  even and odd positions s are the two hyperbolic halves (`coordZ`, FGS:188-196).
- So hh = Σ_s u_s Σ_{a,b} S_{s,a,b}^p·S_{s+1,a,b}: one hh-factor per entry per position, as LOCALDIV assumed.
- The derivatives are applyD(PI) with PI a product of column minors of the Y·X matrix (FGS:405-420). The cap
  ("a minor in a fixed column direction can be differentiated at most capN times") comes from the minors, not from the
  theta. This matches LOCALDIV §3.2 C.
- The passage from the one-variable law to r variables is exactly `phSum` = Σ_i ph(X_i) over an orthonormal basis
  (`OrthInt`, `IKT/DefsRep.lean:26`), followed by the hyperbolic regrouping. I found no extra factor.

## 5. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `kernels_integral_inert` (`IntInert`) | `IKT/KernelsIntegralInert.lean:9`; def `IKT/StatementInt.lean:18` | θ_{L,L′}(Σ b_i z_i)/∏σ\*(z_i) is integral in good-model formal parameters at inert p ≥ 5 | **core**; reduction proved via OneCopy/FourProd/TensFact/StdStep, leaves unread |
| 2 | `rdictMain` (`CurveDict`) | `IKT/InertCoprimeLemmas/RepDict.lean:301` | the one-variable dictionary: σ\* in LT coordinates, NormRel, be ≃ cob(ph), ‖u·ep‖ = 1 | **core**, proved; leaves `coboundary_exact`, `beta_coefficients`, `phase_compatibility`, `nrDense`, `dict_core` unread |
| 3 | `tieDel_all_steps` / `kernelSite_contractionIdentity_operatorHalf` | `SP/KernelSiteFrameValuesAllStepsLtM.lean:24`; `…OperatorHalfStatement.lean:6` (→ `DelB.delPolAt_site`) | KernelDifferenceAtLevel | **core** (identity; is it the same theta?) |
| 4 | `k1gen_of_orth` | `IKT/InertCoprimeLemmas/RepAsm.lean:17` | orthonormal Gaussian Σph ⇒ hyperbolic Σbe | core-ish, proved |
| 5 | `s2_in_unramified_closure`, `secondEisensteinAlgebraic` | `SP/PadicNormTwoHundredSixteenEqOneOfFiveLe.lean:505`; `SP/CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra.lean:27` | E₂\*(Λ) algebraic and in ℚ̂_p^{ur} | standard (Masser), proved |
| 6 | CM2 / CM3 / CM4 | CMS:45,49; CM4.lean:7; `CmAll.lean` | Deuring good reduction over ℚ̂^{ur}; Honda/LT isomorphism; integrality of prime-to-p torsion | standard, proved |
| 7 | `globalArtin` | `IsOpenQuotientMapArt0.lean:233` | global Artin reciprocity | standard (CFT), proved in tree (GroundTheory unread) |
| 8 | `ScalGLt` (hSc), `AdmGLt`, `XiAwayLt` | hypotheses of T1 | integrality of p^{expG}·scalG; admissibility of kerN | **definition to unfold** |

## 6. Oddities

1. **s₂ is never required to be p-integral.** This is correct as far as I can see: its non-integrality, if any, is
   absorbed into the class of be. It does mean the "Gaussian" is not a mild correction; it is exactly the 1/p-Gaussian
   that LOCALDIV's γ_p bound pays for.
2. **p^{expG} in ThA.** Clause 2 is asserted for p^{expG}·(theta), not for the theta itself, and ker then divides by
   eS/eT = p^{−expG} (TieSerAt). The two uses are consistent by the Lean's definitions. Whether `stmt_proved`'s bound
   charges this −expG is LOCALDIV §4.4 item; I did not resolve it. If expG > 0 is not charged, it would be a free gain
   of Σ vm·Δlen per step. **Expert check.**
3. `sgStar` and `beOf` are `Classical.epsilon`/`choose` definitions. Both are pinned on the live path: `sgSer_eq`
   identifies sgStar with the σ-series, and `hBR` proves BeRat, so beOf is not the junk 0.
4. Iop carries 1/√[index]. If an admitted L differs from the standard lattice at p, this could be non-integral. That
   would make clause 2 *harder*, not easier; StdStep avoids it with prime-to-p translates.
5. The theta of T3's global side (`(t.rd u μ).Th` in `framePol`) and `kerTh` in FrecG are different names. I did not
   read the proof that they agree.

## 7. Judgement

**Is the bridge proved, from mathematics I recognise?**
- T1 and the c-normalisation: **yes**.
  - "rdictMain: ‖εu‖ = 1 … `rw [hΔW, norm_pow]`" (`RepDict.lean:483-487`) and `hFr … sclY (u⁻¹ * eLT⁻¹)` (`K1…:268`).
    These are the decisive lines for the scaling flag.
  - The one-variable law is the classical "σ\* = exp(−s₂z²/2)·σ, and σ\*(αz)/σ\*(z)^{Nα} integral" in Honda coordinates.
- T3: **could-not-determine** beyond its top level. It is a proved algebraic identity with a unit constant, but I did not
  verify that both sides use the same theta.
- Nothing false-looking found.
- Ranked children to open next:
  1. T3's `delPolAt_site` (same theta?);
  2. `IntInert` leaves (`FourProd`, `StdStep`);
  3. `ScalGLt`, and expG accounting in `stmt_proved`;
  4. `coboundary_exact` / `RestBeta` (the claim that the class of a hermitian be is Gser(c, σc) with c integral).

## 8. Coverage

Read:
- context files;
- `FirstKernelSmallOfFrameTwist.lean` (all);
- `CoeffOneLNe.lean` (all); `LtCNeZero.lean`; GL3:1-140; TLM:1-340;
- `K1RepresentativesLTOfDictionary.lean:1-60, 240-288`; `DefsRep.lean`; `DefsRepDict.lean`; `RepDict.lean:1-30, 290-565`;
- `RepAsm.lean:1-98`; `DefsRepLt.lean:15-45`;
- `StatementInt.lean`; `KernelsIntegralInert.lean`; `IntegralInertOfApproxBasis.lean`; `IntegralInertOfWeakApprox.lean`;
  `IntegralInertOfWeakApproxTheta.lean` (grep); `DefsMM.lean:1-80`; `DefsInt.lean:100-175`; `OneCopyTh1S.lean:1-80`;
  `OneCopyTh1SOfIsom.lean`;
- `GaussSumParity/StatementE.lean:1-60`, `StatementC.lean:1-60`;
- `CMS:30-70`; `CM4.lean`; `CmAll.lean`; `TorStatus.lean`; `FgClose.lean:1-40`; `CmGoodModelOfGlobalArtinReciprocity.lean`;
- `ExistsUniqueHcharOfFiniteOrder.lean:55-80`; `IsOpenQuotientMapArt0.lean:1-20, 180-238`;
  `GlobalProofs/Imports.lean`; `GlobalArtinReciprocity.lean` (WeilBound);
- `BundleBothParts…(Statement).lean`;
- `KernelSiteFrameValuesPositiveSteps.lean`; `KernelSiteFrameValuesAllStepsLtM.lean`; `…OperatorHalfStatement.lean`;
  `SecondKernelEntrywiseLastLevel.lean:1-80`;
- `LateralTheory.lean:100-215`; `ScalG.lean` (grep); FGS:120-215; `DworkExponentialRestrictions.lean:1-40`.

Not opened: `nrDense`, `dict_core`, `coboundary_*`, `phase_compatibility`, `beta_coefficients`, `s2_in_unramified_closure`
body, `FourProd`/`StdStep`/`TensFact` proofs, `delPolAt_site`, `art0`/GroundTheory CFT, `ScalGLt`/`AdmGLt` definitions,
the upstream supplier of `LTIso`.
