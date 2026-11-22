# NODE-KLAW: the kernel law and `lemmaS` at signal primes, read to the bottom

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`; `NFS` = `SP/NormalisedFamilyStandardBasesIntegrality.lean`; `AKS` = `SP/AdmissibleKernelSeriesInertPrimeNonConjugateFrob.lean`
- `GG/` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/`
- `OP` = `Formalism/SharpRestriction/Divisibility/OrbitPlaces.lean`; `PZF` = `Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean`
- `GJ/` = `Formalism/GaussJetBounds/`; `GJP/` = `GJ/GaussJetProofs/`; `GSP/` = `Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/`
- `FO` = `Formalism/FrobeniusOrbits/Statement.lean`; `IKT/` = `Formalism/LocalToGlobal/InertKernelTheory/`

**read** = proof body read this round. **stmt** = statement only. **(mine)** marks my own computation, which is not in the Lean.

## 0. Verdict

**No ESCALATE.**
1. **The signal-prime kernel law is the same theorem as the Hecke route's, specialised.** Its arithmetic input is `HostLog`: exp(Σ_i ph(X_i))·Θ_orth(ℓ(X)) is integral in the LT parameter. That is `IntInert` (= `kernels_integral_inert`, the orthonormal integrality of θ_{L,L′}/∏σ\*), and the only hypothesis it needs is "p inert in K" (`jacobiSym(−d, p) = −1`). A hyperbolic frame (f, f′) and the class computation `HypShape_of`/`b0` (GAUSSCLASS links 3–6) are then applied. No signal-specific analytic input exists. What is signal-specific is the Frobenius identity σ∘ρ_z = ρ_{z+1}∘conj (proved, §2.2), which makes the frame hyperbolic.
2. **B3 is structural, not an extracted property of the kernel.** The Lean *defines* be = Σ_r be₀(x_r, y_r). Here x_r is a linear form in the even-position variables only and y_r one in the odd-position variables only. be₀ = cob(ph) has no pure-x or pure-y monomials (`DivAB`), and averaging over the torus kills bidegree (1,1). The real content is that the kernel *equals* U·exp(−Σ be). That rests on isotropy: the hermitian pairing couples position z only with z+1. I checked this against the local picture by hand (§2.3) and it holds.
3. **Slopes (mine).** The kernel's CM type is Φ = Psi = ker χ_{−d} ⊂ Gal(E/ℚ), i.e. the type lifted from K (FO:43-47; `tauPl`, `DataForced.lean:11-15`). At every place w above any p inert in K, χ_{−d}(Frob) = −1. So |Φ ∩ (embeddings at w)| = f_w/2, and the slope is **1/2 at every place**, for signal primes and inertClass primes alike. The abelian variety is isogenous to a power of the supersingular CM curve, so the height-2 Lubin–Tate coordinate is legitimate.
4. **`lemmaS` is proved and read** down to `BinomExtract` (body read). The proof is Lucas' theorem on the coboundaries of be. It is consistent with NUMTEST5: the leading cross term saturates clause 1, and the backward bipowers that NUMTEST5 needed are in lemmaS's bad set.

## 1. Statement

### 1.1 The kernel law (OP:186-190, read)

`ThetaExpansionAllPlaces D p R ep sg be Th`: there is U with all coefficients of norm ≤ 1 such that

  Th(ep·logPl(X)) = U(X) · [exp(Σ_{r∈R} sg_r Σ_{a,b} be_r(X_{orbMap r ·, a, b}))](logPl(X)).

Here:
- logPl(X_{s,a,b}) = Σ_e X_{s−2e,a,b}^{p^{2e}}/p^e (OP:133-135, with backPl at OP:124). This is the height-2 Honda logarithm, with σ² written as a shift by 2 positions.
- On the live path sg = −1 (NFS:19, AKS:52).

`BeOK` (OP:181-184) requires B1–B4 (PZF:37-72, read):
- B1: the coefficients lie in Wfrac (unramified);
- B2: invariance under the torus u ↦ u^{±p^s}, with the sign + at even s and − at odd s;
- B3: every monomial has even-degree ≠ 0, odd-degree ≠ 0, and bidegree ≠ (1,1);
- B4: exp of cobX(be) and of cobY(be), the additivity defects in the even and in the odd variables, is W-integral with constant term 1 in jetLog coordinates.

**Supplier.**
- `normalisedFamily_standardBases_integrality` (NFS:19-30, read). Its hypotheses are HostAt, OrbOK, and (IsResidueClassZero ∧ h ≠ 0) ∨ IsSg. It produces ep with ‖ep‖ = 1, and be = beOf(σ, cob F(phFF), om, oms, ζ) with `BeStd`.
- Applied in `exists_beFam_evenConditionsInert_of_kerEnt` (AKS:24-66, read) to `stdSer` of the adapted global entries. B1–B4 come from `standard_series_b_conditions_large_prime` = `bHyps_of_beStd` (read, §2.4).

### 1.2 `lemmaS` (GJ/Statement.lean:98-105, read)

Data:
- K is ultrametric of characteristic 0, l is an odd prime, d ≥ 2 is even, and ‖l‖ < 1;
- K₀ is unramified, and ζ is a primitive (l^d−1)-th root of unity;
- be satisfies BHyp (GJ/Statement.lean:85-93): unramified coefficients, torus invariance, `NoLowBidegree` (= B3), and B4 in letter-log form.

With ρ = 1/(l²−1) and |n| the total degree, every coefficient satisfies:
1. v(coeff_n be) ≥ 1/(l−1) − 1 − ρ|n| for **all** n;
2. v(coeff_n be) ≥ 1/(l−1) − ρ|n| unless n is a **bipower** X_s^{l^α}X_{s′}^{l^β}, with s even, s′ odd, (α, β) ≠ (0, 0) and s + α ≡ s′ + β mod d (`IsBiPower`, :78-81).

## 2. Argument

### 2.1 Reduction of the kernel law (task A1)

`NFS` composes four pieces.

(a) **HostAt** (GG/ExistsConstantCoeffOne.lean:37-44, read) provides:
- curve data (g₂, g₃, s₂, ε, σ, F) (`CurveData` :18-21: integrality, the formal-group law F with log ℓ, and NormRel for ph);
- for every admitted (L, L′), an orthonormal local basis b (`LocBasis`, `Orthonormal`);
- `HostLog` (:23-26): exp(Σ_i ph(X_i))·Θ_orth(ℓ(X)) is integral, where Θ_orth = thOrth(b, G) (:31-35) is the theta combination G in the orthonormal coordinates.

HostAt is supplied by `hostAt_inert` (SP/JacobiOfClass.lean:63-81, read) from `IntInert`, `CurveDict` and `GenusOneModelExistsLattice`. The only arithmetic fact used about p is `jacobi_of_class` (:41-61): (−d/p) = −1 for inertClass **or** signal p.
- `IntInert` (IKT/StatementInt.lean:9-24, stmt) is exactly the Hecke route's orthonormal integrality.
- On the live path the three inputs come from CM2 (`servH_row_of_artin`, SP/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean:15-25, read). They are `kernels_integral_inert` (SP/IntInertOfComplexMultiplicationCondition.lean:11-15; IKT/KernelsIntegralInert.lean:9) and `torsionTaylorAlgebraic_latticeExists_of_cm` (SP/TorsionTaylorAlgebraicLatticeExistsOfCm.lean:15-21).
- The live caller is `servH_row_linkR_alt`, under the closed premise GlobalArtinReciprocity [ROWSU, KERNELLAW].

(b) **`BeData.exists_of_curveData`** (stmt) supplies the dual bases om, oms of W(F_{p^{nP}}) over W(F_{p²}) (TrDual, GSP/TrDual.lean:63-67) and ζ.

(c) **`hyp_of_stdBases`** (SP/StandardBasesHyperbolicPairOrthonormal.lean:27-52, read) turns the adapted entry into Θ_orth composed with a hyperbolic substitution: stdSer(c·X) = Θ_orth(hypZ(f, f′)(X)). Here:
- hypZ_i = Σ_e f_{e,i}·Σ_{s even}σ^s(oms)X_s + f′_{e,i}·Σ_{s odd}σ^s(om)X_s (GG/BeData.lean:36-51);
- f = fOf(gK) collects even positions and f′ = fOf′(gK) odd positions (SP/ExistsRingHomRhoK.lean:42-50);
- HypPair (f, f′) means: integral and σ²-fixed (stmt), isotropic (`fOf_isotropic`, read), and dual (stmt).

(d) **`orbitIdentity_all_of_integralClass_hostLog`** (SP/OrbitIdentityAllOfIntegralClassHostLog.lean:113-236, read) proceeds as follows:
- It feeds HostLog and HypPair to `HypShape_of CalcC_proof` (:119-120). This is GAUSSCLASS link 3, the same code as the Hecke route. The result is Θ_orth∘inHyp = exp(−Φ)·U₀ with Φ ≃ Σ_e be₀(x_e, y_e), be₀ = cob F(ph).
- It applies `b0` (:157-158, stmt) to pass to position coordinates as exp(−beMean)·U.
- It inverts the log by `generalized_log_inverse` and factors over orbits (`expFactor_allOrbits_eq_prod_orbits`, stmt). The rest is reindexing.

**Answer to A(1).** The law reduces to orthonormal integrality (IntInert), the hyperbolic frame and the isotropy cancellation, exactly as ADM2 found for the Hecke route. The one difference is that `VIntegral` enters through IntInert's reduction, not as a separate one-letter step. It is the same theorem, specialised. The signal case is admitted by the disjunctions at NFS:19 and `ne_of_inert` (SP/PrimeOfLiesOver.lean:18-23). No signal-only analytic argument exists.

### 2.2 Frobenius swaps parity (task A2, the Lean says; all read)

- Gal(E/ℚ) = G0 × A with G0 = {±1}² and A = (ℤ/2^{e+2})^×/±1, a cyclic 2-group. c = ((−1,−1),1). χ_{−d} = chD is the second sign, χ_{−q} = chQ the first. Φ = Psi = ker chD (FO:24-47).
- Frob_p classes (`FactClassFrob`, `Formalism/LocalRingCardinality/DataHost.lean:221-227`): signal ⇔ Frob.1 = (1, −1); inertClass ⇔ Frob.1 = (−1, −1).
- Position z = (b, t) ∈ Bool × A is plGG(z) = ((b ? −1 : 1, 1), ι t) ∈ Φ. posPl(z, e) = (b xor [IsSg ∧ e odd], t + e·h) (`DataForced.lean:19-20`).
- `plGG_posPl_one` (SP/PrimeOfLiesOver.lean:46-70): plGG(z+1) = plGG(z)·Frob·c. Hence `rhoH_posPl_one` (:92-97): ρ_{z+1}(x) = ρ_z(Frob(c x)).
- `exists_kur_frob_tauEmb_posPl` (SP/ExistsKurFrobTauEmbPosPl.lean:76-117) shows two things. Every λ∘τ_z(y) lies in K^ur. The Witt Frobenius σ satisfies σ(ρ_z(y)) = ρ_{z+1}(conj y). The second uses `IsArithFrobAt` and uniqueness of Frobenius (`H.der.frob`, a host field).
- Restated as `sigma_rhoK` (SP/ExistsRingHomRhoK.lean:73-79): **σ∘ρ_z = ρ_{z+1}∘conj**. It moves to the coordinate functionals as σ(g_z) = h_{z+1} (`frob_moves_coords`, SP/FrobeniusLiftMovesLetterCoordinates.lean:23-74). That step uses the StdBases condition conj(P_{z+1})ᵀP_z = 1 (GG/StdBases.lean:12-17): adapted bases at adjacent positions are conjugate-dual.
- The second ingredient is `hK_gK_dual` (stmt): Σ_i h_w g_z = δ_{w,z}, from orthonormality of b. Together they give the **hermitian pairing Σ_i σ(g_z)g_{z′} = δ_{z+1, z′}**.
- `posPl_succ_ne_of_parity` (SP/HyperbolicCoordinatesIsotropic.lean:13-33): on an orbit of even length, z_s + 1 ≠ z_{s′} when s ≡ s′ mod 2. Hence the even block f and the odd block f′ are each isotropic (:35-63, :64-81). This is the "hyperbolic plane split".

### 2.3 The local picture at a signal prime, by hand (mine)

Take Frob = ((1, −1), h), let f = ord Frob = lcm(2, ord h) = nP, and let D = ⟨Frob⟩.
1. **c ∉ D.** Frob^k = ((1, (−1)^k), h^k) never has first sign −1. So every place v of F = E^c above p splits as w ≠ w̄. E ⊗ ℚ_p = ∏_{4n/f places} E_w with E_w ≅ ℚ_{p^f} ⊃ K_p = ℚ_{p²}. E ⊗_F F_v = E_w × E_{w̄}.
2. **Embeddings.** Fix ρ₀ = ρ_{τ₀} inducing w. The embeddings inducing w are ρ₀∘Frob^k = σ^k∘ρ₀. Those inducing w̄ are σ^k∘ρ₀∘c. Then χ_{−d}(τ₀Frob^k) = (−1)^k and χ_{−d}(τ₀cFrob^k) = (−1)^{k+1}. So Φ_w = {k even} and Φ_{w̄} = {k odd}, each of size f/2.
3. **Positions.** Position s is ρ_s = σ^s∘ρ₀∘c^s (from §2.2). So **even s enumerate Φ_w and odd s enumerate Φ_{w̄}**, alternating. All of them restrict to the same embedding of K, since Φ is lifted from K.
4. **The hermitian form** tr(x·c(y)) pairs E_w with E_{w̄}, so V_w and V_{w̄} are complementary Lagrangians. In coordinates it pairs position s with s+1 only (§2.2), never s with s.
5. **B3, by hand.** For an orthonormal coordinate X_i = [f_i]x +_F [f′_i]y:
   - Σ_i ph(X_i) ≃ (Σ_i N f_i)ph(x) + (Σ_i N f′_i)ph(y) + be(x, (Σ σ(f)f′)y) + (x–x and y–y cross terms).
   - Isotropy kills the self and same-side terms, and duality leaves Σ_e be₀(x_e, y_e) with x_e supported on even positions and y_e on odd ones.
   - be₀ = cob(ph) vanishes on (x, 0) and (0, y), which is DivAB. So every monomial has positive even and positive odd degree.
   - A bilinear monomial X_sX_{s′} (s even, s′ odd) has torus weight p^s − p^{s′} ≢ 0 mod p^{nP} − 1, so it averages to 0.

   **B3 holds.**
6. **Comparison with inertClass.** Take Frob = ((−1, −1), h) with ord h even. Then Frob·c = ((1,1),h), and c ∉ D exactly when h ≠ 1, which in a 2-group means ord h is even (`HNeZero`). The picture is identical: Bool is constant on the orbit and the parity lives in s. If ord h were odd, c ∈ D, w = w̄, and the type at w is not split. Such primes are not served.

**Slopes (task A3, mine).** By Shimura–Taniyama, the slope at w is |Φ ∩ (embeddings at w)|/f_w = 1/2 whenever χ_{−d}(Frob) = −1. This holds for every p inert in K, at every place, whether or not c ∈ D. The kernel's CM type is literally Psi (`tauPl`), and Psi is lifted from K. So A is isogenous to C^{2n} with C the CM curve (period lattice δ·O_K, `CurveData`), and A[p^∞] ≅ C[p^∞]^{2n} is isoclinic of slope 1/2. "Integral in the Lubin–Tate parameters" means integral in the parameter X of the height-2 Honda group of C over ℤ_{p²}, applied coordinatewise (FGS `logF`; OP:133). **Consistent at every served place; no ordinary factor exists.**

### 2.4 Where B1–B4 come from (read)

- `bHyps_of_beStd` (SP/StandardSeriesBConditionsLargePrime.lean:145-182) applies `biextension_hypotheses_of_level_one` (GSP/BiextensionHypothesesOfLevelOne.lean:29). That theorem is composed of five named theorems.
- B3 comes from `third_mean_condition` (GSP/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean:423-449, read). It uses `divAB_addC` for the two positivity clauses and a geometric sum of the torus character ≠ 1 at bidegree (1,1).
- be = beMean is the torus average of beTil = Σ_r be₀∘addC(linE(oms_r), linO(om_r)) (GSP/TrDual.lean:26-44).
- B4 is the biextension (cube-theorem) integrality, transported by `b4_of_coeff_subst_letterLog` (:93-136).
- F2 (NormRel) is not used for B1–B4 (:148). It is used in `b0` inside orbitIdentity.

### 2.5 `lemmaS`: proof and explanation (task B, read)

`lemmaS` = `lemmaS_of` (GJ/OneLetterRadius.lean:17-19; GJP/ConstantCoeffEvenDerivativeEqZero.lean:166-178). The proof has five steps.

1. **The coboundaries are Dwork-integral.** B4 states that E_i = exp(de_i be)∘letterLog is integral with constant term 1 (i = 1, 2). Here de1 be = be(x+x′, y) − be(x, y) − be(x′, y) is the additivity defect in the even variables (GJ/Statement.lean:54-72), and de2 is the defect in the odd variables.
2. **Undo the log** (`asmS_diff`, :97-164). g = letterLog^{−1} has weight ρ (`LemmaSt`: integral in X means weight ρ in z). Hence exp(de_i) − 1 has weight ρ (`SubstWt`).
3. **Quantise** (`Quant`, GJ/GenLogInverse.lean:104-110, stmt). Torus invariance gives Σ n_x·(±l^{s_x}) ≡ 0 mod l^d − 1 on every non-zero monomial. With integer valuations (K₀ unramified), this lifts weight ρ to weight 1/(l−1).
4. **Take the log** (`LogStep`, stmt). log(1+u) keeps weight 1/(l−1), because v(m) ≤ (m−1)/(l−1). So de_i be has weight 1/(l−1).
5. **Binomial extraction** (`binomial_coefficient_extraction`, GJP/SwappedParitySeriesBinomialForm.lean:760-877, read).
   - The coefficient of de1 be at a split of the s-exponent n_s into (j, n_s − j) is coeff_n(be)·C(n_s, j) (`evenDerivative_binomial_coeff`, :327-354).
   - If the even part of n is not a single variable to an l-power, some C(n_s, j) with 0 < j < n_s is a unit (Lucas, `bnx_choose_nonpow` :445-462). Then be has weight 1/(l−1) there. The odd side is handled the same way.
   - Otherwise n = X_s^{l^α}X_{s′}^{l^β}, and C(l^α, l^{α−1}) has valuation exactly 1 (`bnx_choose_pow`, :464-). Then be has weight 1/(l−1) − 1 there.
   - Torus invariance forces s + α ≡ s′ + β (`bnx_torus_cong`, :600-650).

   B3 is used to guarantee that both an even and an odd variable occur (`bnx_exE`/`bnx_exO`). It also excludes (α, β) = (0, 0).

**Dieudonné shape (mine).** be ≃ Gser(c, σc) with terms c·X^{p^{2i}}Y^{p^{2j+1}}/p^{i+j+1} and its mirror [GAUSSCLASS].
- The bound needed is i + j + 1 ≤ 1 − 1/(p−1) + ρ(p^{2i} + p^{2j+1}).
- It holds because ρp^{2i} ≥ i + ρ and ρp^{2j+1} ≥ j + pρ, and ρ + pρ = 1/(p−1).
- Equality holds at (i, j) = (0, 0), the term c·xy^p/p, and at (1, 0), the term X^{p²}Y^p/p². Both are bipowers.
- In position coordinates xy^p couples s with s − 1 (backward) and x^p y couples s with s + 1 (forward). These are the two bad directions that `IsBiPower` allows.
- The Dwork step: off bipowers, weight ≥ 1/(p−1) survives exp, since v(m!) ≤ (m−1)/(p−1) (`ExpWtLe`). Each bad bipower costs exactly one p, which Lemma RA's radii pay for.

**Against NUMTEST5 (mine, from its numbers).**
- Slope at ν = 0: 0.2078 at p = 5 and 0.1457 at p = 7, against γ₅ = 0.2083 and γ₇ = 0.1458.
- Cost per minor below the kink: 0.8045 at n′ = 4, against 1 − γ₅ = 0.7917. Each forward factor costs exactly one p, i.e. clause 1 is saturated and c is a unit.
- Past the kink the slope is 0.040–0.047 ≈ ρ. This is the backward bipower top·partner^p.
- The forward-only LP fails at 32,682 points, while the LP with lemmaS's forward and backward bipowers fits within [−3.8, +7.3].
- The anisotropic and wrong-Gaussian controls fail by thousands of points. There, self-terms X_s^{p+1}/p are present, B3 fails, and lemmaS clause 2 would be false.

**The data match lemmaS's bad set exactly.**

## 3. Status list, kernel law → `thmAJetA` at a signal prime (task C)

| link | where | status |
|---|---|---|
| Frob class at signal p | `FactClassFrob` (DataHost.lean:221) via `factClassFrob` | stmt (theorem, RankBoundMonotoneInDimension.lean:568) |
| arithmetic Frobenius exists and is unique | `H.der.frob` (host field) | hypothesis field of the host [HOSTS] |
| σ∘ρ_z = ρ_{z+1}∘conj | SP/ExistsKurFrobTauEmbPosPl.lean:76; SP/PrimeOfLiesOver.lean:46-97 | **read** |
| adapted bases conjugate-dual at z, z+1 (StdBases) | AKS:60-62 ← `t.Adapted` (`AdaptedEnt.lean:94-97`) ← `StdTie.adapted` ← `linkR_stdTie_entry` | passed down; supplier located, body not read |
| frob_moves_coords; isotropy | SP/FrobeniusLiftMovesLetterCoordinates.lean:23; SP/HyperbolicCoordinatesIsotropic.lean:64 | **read** |
| duality, σ²-fixed, ‖h‖ ≤ 1, linear-forms identity, stdSer = Θ_orth∘hypZ | SP/*Statement.lean (five files) | stmt |
| HostAt ← IntInert, CurveDict, GenusOne | SP/JacobiOfClass.lean:63 (**read**); `kernels_integral_inert` | IntInert stmt (reduction read by GAUSSCLASS/LEAVES); inputs are theorems from CM2 |
| BeData exists | `BeData.exists_of_curveData` | stmt |
| orbit identity | SP/OrbitIdentityAllOfIntegralClassHostLog.lean:113-236 | **read**; `HypShape_of`, `b0`, `expFactor…` stmt |
| B1–B4 | `bHyps_of_beStd`, `third_mean_condition` | **read**; `biextension_hypotheses_of_conditions` leaves stmt |
| entries = stdSer, IsComb | AKS:59-65 (`comb_of_tied`, `atLin_adaptedCoef_eq_standardSeries`) | stmt |
| B1–B4 ⇒ BHyp | `tieB` (`JetPolynomialLogs/UniformBoundAllData.lean:26`) | stmt |
| lemmaS | §2.5 | **read**; `Quant`, `LogStep`, `ExpDeInv`, `GenLogWeight`, `SubstWt` bodies stmt |
| lat_S | `kerEntHyp_latS` (IW/TrueChainsKernelDatumSourceSideLattice.lean:36-67) | **read**; 3 leaves stmt |
| Hecke-only K1: AdmGLt, MInv, FrameLatMapLt | `kernelSite_seriesData_below_lastStep` (SP/KernelSiteSeriesDataBelowLastStep.lean:20-35) | **read**: AdmGLt ← S.Pair; MInv ← `isUnit_det_frameMatrix_ofCharts` (stmt); FrameLatMapLt ← `frameLatMapLt_of_ties` (read :56-70) ← S.Pair. S.Pair, J.Dict, S.Pos, S.Scal are hypotheses of that theorem. **Not on the orbit route** |

No link lacks a supplier. The residual hypotheses on this route are the host field `der.frob` and `StdTie.adapted` (whose supplier I did not open). Everything else is proved or rests on statements read by GAUSSCLASS, LEAVES and JETA.

## 4. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `kernels_integral_inert` (IntInert) | IKT/StatementInt.lean:18; KernelsIntegralInert.lean:9 | θ_{L,L′}/∏σ\* integral, any p inert in K | core, stmt |
| 2 | `HypShape_of` / `b0` | used at OrbitIdentity…:119, :157 | Σph ≃ Σbe₀(x, y) under the hyperbolic change; transport to positions | core, stmt here (GAUSSCLASS top level) |
| 3 | `exists_kur_frob_tauEmb_posPl` | SP/ExistsKurFrobTauEmbPosPl.lean:76 | σ∘ρ_z = ρ_{z+1}∘conj | core, read |
| 4 | `fOf_isotropic` | SP/HyperbolicCoordinatesIsotropic.lean:64 | even and odd blocks isotropic | core, read |
| 5 | `third_mean_condition` | GSP/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean:423 | B3 for beMean | glue (structural), read |
| 6 | `binomial_coefficient_extraction` | GJP/SwappedParitySeriesBinomialForm.lean:845 | coboundary weight ⇒ lemmaS | core, read (Lucas) |
| 7 | `Quant`, `LogStep` | GJ/GenLogInverse.lean:88-110 | torus quantisation; log keeps weight 1/(l−1) | standard (Dwork-type), stmt |
| 8 | `linkR_stdTie_entry` | `…/ThirdPlaceSeries/LinkRStdTie.lean:20` | supplies StdTie (adapted bases) | definition to unfold |

## 5. Oddities

1. **B3 is true by construction of be.** It certifies nothing about the kernel. The kernel's shape is asserted by the equation in ThetaExpansionAllPlaces, and that equation is where isotropy is used. A reader should not take B3 as evidence that the self-Gaussians cancel.
2. The signal branch and the inertClass branch run through the same code. The only difference is in `plGG_posPl_one` (whether the Bool coordinate flips). For signal primes, Bool records the χ_{−q} sign, which flips at every step.
3. The adapted-basis condition conj(P_{z+1})ᵀP_z = 1 is a hypothesis (StdTie.adapted). It is what turns the Frobenius identity into σ(g_z) = h_{z+1}. Its supplier is located but not read.
4. Nothing false-looking. The slope computation and the hand check of B3 agree with the Lean.

## 6. Coverage

Read:
- PROTOCOL; MAIN-ARGUMENT §0 and §3–4; NODE-ENGINE2, ADM2, JETA, ORBIT, NUMTEST5, GAUSSCLASS; KERNELLAW:15-30; ROWSU (greps).
- NFS (all); AKS (all); SP statement files for hyp_of_stdBases' leaves, B-conditions, BeData, orbitIdentity, NFS-alt.
- SP/StandardBasesHyperbolicPairOrthonormal.lean (all); ExistsRingHomRhoK.lean (all); FrobeniusLiftMovesLetterCoordinates.lean (all); ExistsKurFrobTauEmbPosPl.lean (all); PrimeOfLiesOver.lean (all); HyperbolicCoordinatesIsotropic.lean (all).
- OrbitIdentityAllOfIntegralClassHostLog.lean:1-30, 113-236; StandardSeriesBConditionsLargePrime.lean (all); JacobiOfClass.lean (all); AtOfTrueColumns.lean (all); KernelDatumConditionsAtStandardKernelComparison(Statement).lean; RowAtOfStdTie.lean; BundleBothParts…(both).lean; ReciprocityKernelService.lean; ServHRowLinkR.lean; IntInertOfComplexMultiplicationCondition.lean; TorsionTaylorAlgebraicLatticeExistsOfCm.lean; KernelSiteSeriesDataBelowLastStep.lean; OrthonormalLocalBasesCarryWittLattices.lean:56-70; IsUnitDetFrameMatrixOfCharts.lean:14.
- GG/StdBases.lean, BeData.lean, ExistsConstantCoeffOne.lean (all).
- OP:120-200; PZF:37-72; FO:1-60; DataForced.lean:1-40; DataHost.lean:160-240; IKT/StatementInt.lean:1-30; KernelsIntegralInert.lean; FrameInt.lean:40-70; DefsRepLt.lean:140-200; JointCmpEmbeddingY.lean:150-175.
- GSP/TrDual.lean:1-88; BiextensionHypothesesOfLevelOne.lean; SubstZeroOfConstantCoeff.lean:423-449; GJ/Statement.lean:15-130; OneLetterRadius.lean; GenLogInverse.lean:85-127; GJP/ConstantCoeffEvenDerivativeEqZero.lean (all); SwappedParitySeriesBinomialForm.lean:327-360, 440-480, 554-612, 760-877.
- IW/TrueChainsKernelDatumSourceSideLattice.lean:30-70; AdaptedEnt.lean:20-30, 94-97.

Greps run:
- `theorem (standardSeries_scaled…|orbitIdentity…|exists_of_inertPrime…|standard_series_b_conditions…|hyp_of_stdBases|hostAt_inert)`;
- `def HostAt`; `def (gK|hK|fOf)`; `frob_moves_coords|fOf_isotropic|hK_gK_dual`;
- `theorem (exists_frob_step|rhoH_posPl_one|ne_of_inert)`; `factClassFrob|def plGG|mem_Psi_iff|def Psi`; `def FactClassFrob`;
- `biextension_hypotheses_of_level_one|beMean`; `def (NoLowBidegree|MeanNoLowBidegreeTerms|DivAB|torus|lw)`;
- `LemmaS|lemmaS` in GJ; `def (BinomExtract|Quant|LogStep|ExpDeInv)`;
- callers of `exists_beFam…`, `hostAt_inert`, `at_of_true_columns`, `at_of_stdTie`, `rowAt_of_stdTie`, `servH_row`;
- `theorem … : (IntInert|AlgTAll|GenusOne…|CurveDict)`;
- `def (AdmGLt|MInv|FrameLatMapLt)`; `ThetaSeriesDataHypothesesBelowMaximalLevel`; `theorem .*(MInv|FrameLatMapLt|AdmGLt)`;
- `def TieB|theorem tieB`; `def .*Adapted|def AdPl`; `theorem linkR_stdTie_entry`.

Not opened:
- bodies of `Quant`, `LogStep`, `ExpDeInv`, `GenLogWeight`, `SubstWt`, `HypShape_of`, `b0`, `BeData.exists_of_curveData`, `hK_gK_dual`, `fOf_fOf'_dual`, the σ²/norm leaves, `comb_of_tied`, `tieB_of`;
- latS leaves; `linkR_stdTie_entry`; the supplier of S.Pair / J.Dict (Hecke route only); `H.der.frob` instantiation.
