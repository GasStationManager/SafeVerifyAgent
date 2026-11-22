# NODE-ADM2: the kernel law `adm2` and the position structure `posOK`

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`; `ICL/` = `IKT/InertCoprimeLemmas/`
- `FKS` = `ICL/FirstKernelSmallOfFrameTwist.lean`; `K1LT` = `ICL/K1RepresentativesLTOfDictionary.lean`
- `TTP/` = `Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/`
- `ELC` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocIdOfCompletions.lean`
- `PCB` = `Formalism/LocalToGlobal/GroupLattices/LevelGatherings/PosCompatOfBase.lean`

"Read" means I read it in this round. "Stmt" means I read only the statement. Inferences are marked *I infer*.
Computations marked **(mine)** were done by me, by hand, in this round.

## 0. Verdict (short)

- **A (`adm2`): proved in the tree. It is consistent with the supersingular behaviour and with every numerical test. No ESCALATE.**
  - What is asserted integral is **not σ\***. It is the kernel multiplied by exp(+Ph), as a series in the height-2
    Lubin–Tate parameters X of the hyperbolic coordinates. Ph is only pinned down up to "≃", i.e. up to a factor
    whose exponential is W-integral in X. Ph ≃ Σ_e be(x_e, y_e), with be the polarisation of log σ\*.
  - The supersingular non-integrality lives entirely in be. RestBeta says be ≃ Gser(c, σc), whose 1/p part is
    c(xy^p − x^p y)/p.
  - In one variable this predicts that the coefficient of W^a (W = z/ϖ) in σ\* has v ≥ −⌊a/(p+1)⌋ **(mine)**. NUMTEST
    measured exactly −a/(p+1). The self-Gaussian is real, of unit size, and saturated.
- **B (`posOK`): supplier located and read. It is a theorem about the actual host E and its CM type, not a free
  assumption** (`exists_locId`, ELC:444; `posCompat_of_base`, PCB:29).
  - A position (v, s) is the CM-type element τ_{v,s} = orbRep_v·(1, h)^s ∈ Psi = Gal(E/K).
  - Its p-adic embedding is the s-th Witt-Frobenius twist of a base embedding, conjugated at odd s.
- **Caveat on the claim.** `first_kernel_law_global_small` is **conditional**: `TranslatesOfInertKernelAtPlace` is an
  implication with about 15 hypotheses (§1). On the live path they reach `Joint.At.K1` and `Joint.At.Pos`. `Pos` is
  proved for all sites. I did not open the suppliers of the other K1 fields (AdmGLt, MInv, FrameLatMapLt, ScalGLt;
  GAUSSCLASS read ScalGLt).

## 1. Statement A: `adm2` exactly

**Supplier.** `first_kernel_law_global_small : TranslatesOfInertKernelAtPlace` (FKS:124-133, read). It is a
three-line wrapper:
- `first_kernel_small_of_frame_twist` (FKS:85-120) truncates Ξ₀ outside the levels used;
- `first_kernel_small_of_frame` (FKS:21-83) does the work;
- clauses adm2b, adm2 and adm3 follow by `adm_two_pendant_iff_representative`, `admissible_second_of_variant` and
  `admissible_third_of_second_eleventh` (stmt).

**`TranslatesOfInertKernelAtPlace`** (IKT/TranslatesOfInertKernelAtPlace.lean:20-40, read) says: for every D, p ≥ 5,
system X, LT-isomorphism `hLT`, positions `pos`, and lattice data, the clauses adm2, adm2b and adm3 hold for the kernel
`FrecG … (ltC g hLT)`. The hypotheses are:
- At (Δ(Λ) = 1 curve data), InertK, ModelOverW, IsCurveIdeal, IsDiscriminantTwelfthRoot, IsChi;
- AdmGLt, ClAway, XiAwayLt, ScalGLt;
- **LamPosG** (the position structure), MInv, FrameLatMapLt;
- `[Fact CM2]`.

**Clause content** (`ExtensionLocalCondition`, FGS:162-170, read). The variables are Eidx ⊕ Eidx, with
Eidx = Fin(n′/2) × Fin r0 × Fin r1. These are pairs (x_e, y_e) of **LT-log coordinates**, one pair per
(half-orbit index r, matrix entry a, b). The clause asserts that there exist Ph (over K0 = Frac W(F̄_p)) and U with:
1. Th = exp(−Ph)·U;
2. **U(ℓ(X)) has coefficients in R1**: `IntR R1 (inParamK U)`, with ℓ(X) = Σ_j X^{p^{2j}}/p^j (`logF`, FGS:126).
   This is the integrality claim. It is integrality in the LT parameter X, with no growth allowance: plain bounded
   coefficients.
3. Ph(−X) ≃ Ph;
4. BeProp(be): be is biadditive mod ≃, and be(αx, y) ≃ be(x, σ(α)y) for α ∈ W(F_{p²}) (FGS:147-160);
5. **Ph ≃ Σ_e be(x_e, y_e)**: a hyperbolic cross form, with **no diagonal terms**.

Here f ≃ g means that constcoeff(f − g) = 0 and exp((f − g)∘ℓ) ∈ 1 + X·W[[X]] (FGS:139-142).

**Which kernel.** Th is the Taylor series at z = 0 of the global CM theta θ_{c,c′} = `kerTh` (ENGINE §1.1). The
following operations are applied to it (FKS:39-56):
- multiply by p^{expG}·scalG (‖·‖ = 1, GAUSSCLASS §2d);
- map Q̄ → ℂ_p by lam;
- rescale every variable by c = u⁻¹ep⁻¹ (a unit, KERNELLAW);
- apply the frame change subBG.
The kernel's z is the CM-type coordinate z_{τ,i,j} with τ = pos(v, s) (NUMTEST3 §A). The pair structure comes from the
hyperbolic change of `FrameHypLt` (§2 step 4).

**Which place.** p is a prime of class GIdx: p ≥ 5, inertClass, HNeZero, not a level prime, and p ∤ T
(`Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:68-69`, read). Here:
- inertClass means Frob_p = (c0, h) with c0 = (−1, −1) (`frob_val`, `.../SpanPowerMembership/GatTies.lean:137-153`, read);
- HNeZero means ord h is even (`.../DataHost.lean:198-200`, read).

## 2. Argument A, to the bottom, as mathematics

| step | content | where | status |
|---|---|---|---|
| 1 | kernel = linSub(S)(sclY(c)(p^{expG}·pSer(scalG·θ))) | FKS:56-67 | read |
| 2 | BeProp for beLT (cube theorem + NormRel) | `beProp_ofA` | stmt (GAUSSCLASS read the top level) |
| 3 | `CombAtLt`: F is a p-integral combination of prime-to-p torsion translates of the standard theta | `combAtLt_of_dataRec`, `combAtLt_scalar` (FKS:68-78) | stmt |
| 4 | `FrameHypLt`: in each frame, kernel = Θ_orth∘hypLin(f, f′), where (f, f′) is an isotropic, dual, σ²-fixed, integral pair; built from **LamPosG** + FrobTw + n′ even | `frameHypLt_of_lat` (FKS:85-88) | stmt; GAUSSCLASS read the top level; ENGINE read `iso_fK`/`dual_fK` |
| 5 | `IntInert`: for admitted (L, L′), each integral torsion combination F and orthonormal local basis b: atLog(F)·ePh is integral, i.e. θ_{L,L′}(Σ_i b_iz_i)/∏_iσ\*(z_i) is integral in Weierstrass formal parameters | IKT/StatementInt.lean:9-27 (read); supplier `kernels_integral_inert` | stmt; reduction via OneCopy/FourProd/TensFact/StdStep (KERNELLAW, GAUSSCLASS, LEAVES) |
| 6 | `DictInt`: transfer from the Weierstrass parameter to the LT parameter via LTIso (unit ep, ‖u‖ = 1) | K1LT:253-286 (read) | read at this level |
| 7 | per-letter law (§2.1) | TTP/ | **read this round** down to its named leaves |
| 8 | Σ_i ph(X_i) over an orthonormal basis ≃ Σ_e be(x_e, y_e) after hypLin; self-terms cancel by isotropy | `k1gen_of_orth`, `hyperbolicSum` | read by GAUSSCLASS and ENGINE (HPS) |
| 9 | (downstream) be ≃ Gser(c, σc); RestGc; Dwork ⇒ InClass | DER, TwoSums | read by ENGINE and GAUSSCLASS |

### 2.1 The one-letter law (read this round)

`joint` (`TTP/NonsingularJetNorms/Joints.lean:48-89`) gives exp(−ph)·V = thetaOne, with V integral. Here:
- thetaOne(X) is the Taylor series of U_s th0 at z = εℓ(X) (`UniformGaussModels/IsHypPair.lean:13-17`);
- s is a torsion point with N·s ∈ Λ and p ∤ N;
- th0 is σ\* translated to the 2-torsion point ω₀/2 and normalised to 1 at 0;
- ph = phFF = −log σ(εℓ) + (s₂/2)(εℓ)² − log(ℓ/X) (`GaussSumParity/StatementE.lean:24-28`).

So exp(−ph(X)) = σ\*(εℓ(X))·X/ℓ(X): it is σ\* itself, in LT coordinates. V comes from `VIntegral` (`TTP/StatementV.lean:10-18`),
proved at `TTP/NonsingularJetNorms/VIntegral.lean:46-71`:
1. Pass to the Weierstrass formal parameter T of the unit-discriminant model, using thetaS (the integral LT↔Weierstrass
   isomorphism, hypothesis hθ).
2. `phCompare`: phFF ≃ phL∘thetaS. Here phL = phO(s₂, ℘, logSer) = −log σ\*(z(T)) + log T (`TTP/StatementA.lean:25-27`;
   `FrobeniusFibreCurves/CurveHyp.lean:75-76`).
3. `th0Analytic` (`ThetaZeroAnalytic`, `TTP/StatementA.lean:81-87`): exp(phL)·U_t th0 is integral and of Gauss norm 1.

The proof of step 3 is `Th0Analytic_of` ← `AnalyticTrans_of` (`TTP/NonsingularJetNorms/Taylor0ConstMul.lean:180-215`).
It rests on the following:
- `AnalyticSys`: the family G_t = exp(phL)·(U_tσ\*)(z(T)) = T·σ\*(z+t)e^{…}/σ\*(z) is a **translation system**
  (`IsTransSys`, `TTP/IsTransSys.lean:60-66`, read). That is, G_t = εT for t ∈ Λ; G_t(0) ≠ 0 otherwise; and
  T²·G_{P+Q}G_{P−Q} = G_Q(0)²·(x(Q)T² − T²x(P ⊕ T))·G_P². This is the **σ-addition formula**
  σ(z+u)σ(z−u)/(σ(z)²σ(u)²) = ℘(u) − ℘(z), written in the formal parameter.
- `PtOfInt`/`TorsionIntegral`: prime-to-p torsion points have integral x and y on the good model, i.e. they stay off
  the formal group.
- `TransUnit`: the induction/telescoping plus root extraction with p ∤ N. Statement only; body not read.

*I infer* the mathematics: σ\*(z+t)e^{−πzt̄/A}/σ\*(z) is, up to a constant, an N-th root of a rational function with
divisor N(−t) − N(O). Multiplied by T it is a unit power series on a good model, because t reduces away from O. This
is the classical integrality of Kronecker/Robert theta quotients at prime-to-p torsion. **It does not use
supersingularity.**

### 2.2 Where supersingularity enters, and why `adm2` is not "σ\* is integral"

- In one variable `adm2` is tautological: U = exp(ph)·(letter) = letter/σ\*-shape, and ph *is* −log σ\*.
- The content is that the **class** of Ph is Σ_e be(x_e, y_e), with be ≃ Gser(c, σc) (RestBeta). Gser =
  c·Aser − σc·Aser′, with Aser = Σ_{i≤j} X^{p^{2i}}Y^{p^{2j+1}}/p^{i+j+1} (`UTS/OddLogRelation.lean:20-29`, via
  GAUSSCLASS). This is the Dieudonné statement: H¹_dR of the height-2 Honda group is spanned by ℓ and
  g0 = Σ X^{p^{2j+1}}/p^{j+1} (`LemmaOne`, stmt).
- So **yes: the Gaussian exp(−(π/p)·hh) is the supersingular non-integrality of log σ\* made explicit.** Its leading
  term is c·x·y^p/p, i.e. (π/p)·Z·Z′^p after z = ϖZ with π = ϖ^{p+1}.

**One-variable prediction versus NUMTEST (mine).**
- By NormRel with α = 2: be(x, x) = ph(2x) − 2ph(x) ≃ 2ph(x). So ph ≃ be(x, x)/2 ≃ (c − σc)x^{p+1}/(2p) + … = c·x^{p+1}/p + ….
- In W = z/ϖ: exp(−c(π/p)W^{p+1}) = Σ_k (π^k/k!)(−cW^{p+1}/p)^k with v(π^k/k!) ≥ 0 (Dwork). So the coefficient of W^a has
  v ≥ −⌊a/(p+1)⌋.
- Translate the data into W **(mine)**. NUMTEST measured v_p(D^aσ(0)) ≈ Σ_k⌊a/p^{2k}⌋ ≈ a/(p²−1) (NODE-NUMTEST §1). The
  Taylor coefficient then has v ≈ a/(p²−1) − a/(p−1) = −γ_p·a. Multiplying by ϖ^a adds a/(p²−1), giving −a/(p+1).
- **Exactly the predicted bound, attained.** This also shows c is a unit: c ≢ 0 mod p. That agrees with the known
  picture of a supersingular σ converging only on v(z) > p/(p²−1).

**Consistency with each test.**

| test | what adm2-type reasoning predicts (mine) | observed | consistent? |
|---|---|---|---|
| NUMTEST (σ, one variable) | self-Gaussian survives: v(D^aσ) ≥ v(a!) − a/(p²−1) − a/(p+1) = a/(p²−1) | a/(p²−1), excess ≤ 7 | yes, saturated |
| ℘ addendum | ℘ = x(X) is integral in X: no Gaussian, v ≥ v(n!) − n/(p²−1) ≈ γ_p·n | γ_p to three decimals | yes |
| NUMTEST2 σ(z+w)/σ(z)σ(w) | exp(+be(z, w)), both variables in the same place; each zw^p/p or z^pw/p factor costs one p, so the loss is ≤ min(a/p, b)-type | slope γ_p, cap at e = 1 | yes (ENGINE: the Lean's bound is weaker here) |
| NUMTEST3 (n′ = 2 kernel) | isotropy kills the self-terms; only the cross term remains | v ≈ γ_p(a+w) − w, worst −0.98 | yes |
| NUMTEST4 (n′ = 4, minors) | caps per partner position | worst −1.54 | yes |

No test contradicts the asserted class. The supersingular radius is p/(p²−1) in z. Equivalently, there is no
integrality in z/ϖ for σ\* alone. That is exactly what `adm2` does **not** claim.

## 3. Statement and supplier B: `posOK`

**Statements (read).**
- `LocPack.posOK` = `PosCompat` (`GroupLattices/CloudFilling/FillInstRecEqWj.lean:54-58`; PCB:23-27). For each orbit v,
  s < n′ and x ∈ E: iK(ι(σ^s(iw_v x))) = λ(emb(posG(v, s)·cc^s)(x)).
- Consumed as `pos_emb` (`ChartComparison/StepIn.lean:165-166`):
  e(τ_{pos(v,s)}(s even ? x : x̄)) = ι_v(σ_v^s(iw_v x)).
- `LamPos`/`LamPosG` is the same, with lam in place of e (`SatakeParameters/LamPosOfPosEmb.lean:39-54`;
  `LamPosGOfLamPos.lean:15-18`).

**What a position is.**
- Tau ≃ Psi = Gal(E/K) ⊂ GG = Gal(E/ℚ), with the CM type lifted from K (NUMTEST3 §A; HOSTS).
- zPsi = (1, h) = Frob_p·cc (`zPsi_eq`, `LevelGatherings/SecPsiMulPow.lean:148-151`).
- posG(v, s) = orbRep_v·zPsi^s (`SecPsiMulPow.lean:64-66`). `gatRec_pos` = posG∘eTau⁻¹ (`LevelGatherings.lean:49-50`).
- So the positions are the CM-type embeddings, grouped into ⟨zPsi⟩-orbits. **Orbits correspond to places of F above p**
  (`place_injective`/`place_surjective`, ELC:256-320, read).
- n′ = ord(zPsi) = ord h (`orderOf_zPsi`). The matrix index (a, b) ∈ N′ × N is a separate factor.

**Why Frobenius rotates by one.**
- Since posG(v, s)·cc^s = orbRep_v·Frob^s in the abelian group GG (PCB:44-49), position s+1 is position s composed
  with Frob·cc (`gatRec_step`).
- `posCompat_of_base` (PCB:29-50, read) needs two inputs:
  1. hbase: iw_v = λ∘emb(orbRep_v) at s = 0;
  2. hfrob: σ∘iw_v = iw_v∘σ_{(c0,h)}. That is `fr_apply` (ELC:189-195, read): the Witt Frobenius on
     Q_{p^n} = W(F_{p^n})[1/p], pulled back along a good embedding, is the arithmetic Frobenius. For abelian E that is
     (c0, h) at every prime above p (`frob_eq`, `GatRecStepFrob.lean:14-24`, ← `frob_val` ← `H.der.frob`, the
     host's Artin/Frobenius field).
- Induction on s gives σ^s∘iw_v = iw_v∘Frob^s.

**Why n′ is even, and what "served" means.**
- `frobOrder_spec` (`AutomorphicMembership/FrobOrderSpec.lean:17-37`, read) gets Even(ord h) and ord h ≥ 2 from
  HNeZero ⊂ GIdx.
- Then cc ∉ ⟨Frob⟩, so each place v of F above p splits in E: the conjugate places of E are distinct
  (`plc_ne_conj`, ELC:233-239, read). That makes the hermitian space split at v, and "+1" swaps parity on ℤ/n′.
- [E_w : ℚ_p] = ord(Frob) = ord h (`degree_eq`, ELC:205-217), so the residue field is F_{p^{n′}} (HidaSetting).
- "Served" for this supplier means GIdx: inertClass and ord h even.

**Supplier on the live path.**
- Consumption: `pos_at_site : AllSites (… S.Pos)` (`SatakeParameters/SitePlaceInducesPositionEmbeddings.lean:11-13`,
  read) takes `(J.Gd.cmp.tie u w hg).pos_emb`, a field of `CmpTied` (`ComparisonMaps/TiedRec.lean:56-67`).
  `Joint.At.Pos`/`Joint.At.K1` are the site fields that feed the K1 hypotheses
  (`GaloisGeometry/JointCmpEmbeddingY.lean:158-164`, read).
- Production:
  - `pos_emb` is produced by `pos_C` (`TiedFamilies/TieIwLevTieOf.lean:56-96`, read), which rewrites posOK into
    pos_emb.
  - The posOK it uses comes from `posOK_placeId` (`IwasawaDecomposition/ExistsConcrete.lean:82-90`, read), i.e. from
    `exists_locId` (ELC:444-460) → `exists_locId_of_emb` (:411-436) → `exists_locId_host` (:352-409) +
    `posCompat_of_base`.
  - This is used by `exists_isLocalFamily` (`IsRecGOfIsLocalFamily.lean:39-47`), called at `ExistsGIs.lean:139-150`.
- *I infer, not traced by equality:* the `J.Gd.cmp` of the live site is the `cmpInC` that this recursive family
  builds. All five `pos_C` call sites take `hPos` from this construction.

**Tops, partners, caps.**
- Tops are host data: t ∈ H.TT ⊂ A with τ1(t) ∈ topPlaces ⊂ Psi (`tau_top_places_iff`,
  `CloudFilling/TauTopPlacesIff.lean:40`, stmt). A top's position is the s with pos(v, s) = τ1(t).
- The partner at level e is s + e mod n′ (posAdd).
- The cap is the number of minors at s + e: ν_{j+1,s+e,1}, or ν₂ at a top (ENGINE §1.4, FGS:36-38).
- I did not open how TT is chosen (FactTopsThick, PAIRING).

## 4. Status (task C)

| item | status | unopened |
|---|---|---|
| A: `adm2` for the live kernel | **proved and read** at levels 1–2 and at the one-letter law to named leaves. Conditional on hypotheses passed down to `Joint.At.K1` | bodies of `TransUnit`, `TransGauss`, `OpUTh0Root`, `phi_comparison`, `nrDense`, `betaIsG` steps, `LemmaOne`; `kappa_integral_of_calculation`/fourth-power trick and `pairs_standard_at_p` (LEAVES read the latter two); `frameHypLt_of_lat` body; suppliers of AdmGLt, MInv and FrameLatMapLt at the site |
| B: `posOK` | **proved and read** (`exists_locId_host`, `posCompat_of_base`, `pos_C`, `lamPos_of_posEmb`, `pos_at_site`) | the identification of `J.Gd.cmp` with the recursive `cmpInC` (inferred); `H.der.frob` (a field of the HostDer Prop; whether the actual host satisfies it is HOSTS' question); `exists_good`, `exists_completion_equiv` bodies |

## 5. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `first_kernel_small_of_frame` | FKS:21 | kernel law from CombAtLt + FrameHypLt + dictionary | core, read |
| 2 | `K1_representatives_LT_of_dictionary` | K1LT:253 | orthonormal integrality + hyperbolic frame ⇒ clause | core, read |
| 3 | `IntInert` / `kernels_integral_inert` | IKT/StatementInt.lean:18 | θ_{L,L′}/∏σ\* integral in formal parameters | core, stmt (reduction read by others) |
| 4 | `v_integral_nonsingular_jet_norms` | TTP/NonsingularJetNorms/VIntegral.lean:46 | per-letter: exp(ph)·(U_s th0)(εℓ) integral | core, read |
| 5 | `th0Analytic`, `AnalyticTrans_of`, `IsTransSys` | TTP/…/AnalyticTransOfAdd.lean:35; Taylor0ConstMul.lean:180; IsTransSys.lean:60 | Kronecker-quotient integrality via the σ-addition formula | standard (Robert/Coates–Wiles type), read to leaves |
| 6 | `betaIsG` (RestBeta) | UTS/FinalS.lean:61 | be ≃ Gser(c, σc) | standard (Dieudonné/Honda), stmt |
| 7 | `exists_locId_host` | ELC:352 | local identification with iw_v = λ∘orbRep_v and σ∘iw = iw∘Frob | core, read |
| 8 | `posCompat_of_base` | PCB:29 | position s = Frob^s twist | glue, read |
| 9 | `pos_C`, `lamPos_of_posEmb`, `pos_at_site` | TieIwLevTieOf.lean:56; LamPosOfPosEmb.lean:39; SitePlaceInducesPositionEmbeddings.lean:11 | posOK ⇒ pos_emb ⇒ LamPos at every site | glue, read |
| 10 | `frob_val` / `H.der.frob` | GatTies.lean:137; ConjEMemHostFIff.lean:104 | Frob_p = (c0, art(p)) for inertClass p | standard (CFT for abelian E), host field |

## 6. Oddities

1. **"Integral" is in the LT parameter X of the hyperbolic coordinates, and Ph is defined only mod ≃.** The clause
   alone is weak. Its force comes from Ph ≃ Σ be together with RestBeta's explicit Gser. A reader who expects
   "σ\* = Gaussian × integral in z" will misread it (GAUSSCLASS oddity 4 agrees).
2. The one-letter integrality (2.1) is independent of supersingularity. Supersingularity enters only through the class
   of be (Dieudonné) and the height-2 log.
3. `TranslatesOfInertKernelAtPlace` packages about 15 hypotheses. "adm2 is proved" means proved **given** the site
   data K1. Pos is discharged for all sites. The other K1 fields are a residual statement-level input.
4. GIdx serves inertClass primes only. Signal primes, which carry the Riesz term, are served by the orbit route
   (MAIN-ARGUMENT §4.6). That route's position structure is not covered by this node.
5. Nothing found that contradicts known supersingular behaviour or the numerics.

## 7. Coverage

Read:
- FKS (all); IKT/TranslatesOfInertKernelAtPlace.lean (all); ICL/AdmissibleEntriesOfKernelLaw.lean (all);
- IKT/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:1-120; SatakeParameters/InertThetaAdmissibilityOfComplexMultiplication.lean;
- FGS:120-240; K1LT:253-288; IKT/StatementInt.lean:1-40;
- TTP/NonsingularJetNorms/Joints.lean (all); TTP/StatementV.lean; TTP/NonsingularJetNorms/VIntegral.lean;
  TTP/StatementA.lean; TTP/AnalyticTransOfAdd.lean; TTP/IsTransSys.lean:1-80; Taylor0ConstMul.lean:180-215;
  UniformGaussModels/IsHypPair.lean:1-40; GaussSumParity/StatementE.lean:20-40; CurveHyp.lean:60-80;
- SatakeParameters/LamPosOfPosEmb.lean; SitePlaceInducesPositionEmbeddings.lean; LamPosGOfLamPos.lean:1-20;
- FillInstRecEqWj.lean:1-110; PCB (all); ComparisonMaps/TiedRec.lean:1-80; ChartComparison/StepIn.lean:140-200;
  LocMore.lean; LocTiesOf.lean:1-60; TieIwLevTieOf.lean (all);
- ELC:92-135, 178-462; ExistsConcrete.lean:60-100; IsRecGOfIsLocalFamily.lean:20-60; FrobOrderSpec.lean (all);
  GatRecStepFrob.lean:1-50; IsResidueClassZero.lean:85-110; GatTies.lean:110-175; DataHost.lean:20-40, 190-235;
  ConjEMemHostFIff.lean:87-215; RhoDetPrimeEqMuTildeMulChiPow.lean:55-80; LevelGatherings.lean:40-60;
  SecPsiMulPow.lean:140-155; JointCmpEmbeddingY.lean:140-175; ExistsGenusOneFormalIsoOfUnramifiedGoodReduction.lean:23-24.

Greps run:
- `first_kernel_law_global_small|TranslatesOfInertKernelAtPlace`; `def AdmAtEnt2|…`; `ThetaSeriesDataHypothesesBelowMaximalLevel`;
- `lamPos_of_posEmb|posOK`; `pos_emb`; `structure CmpTied`; `def PosCompat`; `pos_C\b`; `exists_isLocalFamily`;
- `def GIdx|frobOrder_spec|…`; `def HNeZero|inertClass`; `theorem frob_eq`; `frob_val|def hOf`; `der :`; `DerOfRaw`;
- `joint_integrality`; `def VIntegral`; `th0Analytic|phL|inU|phCompare`; `IsTransSys|OneUnit|GaussOne|phO`;
- `exists_genusOne_formal_iso…`; `kappa_integral_of_calculation|fourth_power` (body not followed).

Not opened: as listed in §4.
