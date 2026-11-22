# NODE-ENGINE2: the orbit route for one lift at one signal prime, as a paper proof

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `OP` = `Formalism/SharpRestriction/Divisibility/OrbitPlaces.lean`
- `PZF` = `Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean`
- `IB` = `Formalism/IncomingBounds/IncomingBound.lean`
- `GJ/` = `Formalism/GaussJetBounds/`; `GJP/` = `GJ/GaussJetProofs/`; `CLR` = `GJP/CapacityLeReachCapacity.lean`
- `DPW` = `Formalism/SharpRestriction/Divisibility/JetPolynomialLogs/DworkPowerSeriesWeights.lean`; `LBE` = `.../JetPolynomialLogs/LocalBoundElevenComparison.lean`
- `GIRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean` (namespace `G`, the one `OP` opens). NODE-SIGNAL's `IRZg` (`Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean`, namespace `Loc`) is a twin with the same formulas; I read both.
- `DF` = `Formalism/LocalRingCardinality/DataForced.lean`; `DE` = `Formalism/LocalRingCardinality/DataErr.lean`; `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- `OVB/` = `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitValuationBounds/`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`; `AKS` = `SP/AdmissibleKernelSeriesInertPrimeNonConjugateFrob.lean`; `NFS` = `SP/NormalisedFamilyStandardBasesIntegrality.lean`

Status words: **read** means I read the proof body in this round. **stmt** means I read only the statement. *Inference* marks my own reasoning, which is not in the Lean. [NODE] means the claim is taken from that node and not re-read.

## 0. Verdict (short)

**No ESCALATE.** At a signal place the proved per-lift exponent is g0S + F − ES. Here g0S is the same Σ_{reps} max(g0, 0) that `gainP` puts into Ga, and ES = vDG + EatI is the error field E that Ga's companion Ee charges. So the proved exponent equals the exponent sg that the ledger uses, symbol for symbol (§2.6). The kernel law has a supplier, `normalisedFamily_standardBases_integrality` (NFS:19-30, read). Two of its three inputs were read only as statements.

The route in one paragraph:
1. A signal p is inert in K = ℚ(√−d) and split in ℚ(√−q), and c ∉ ⟨Frob⟩.
2. The orbit of positions under z ↦ z·Frob·c has **even** length nP = 2·ord(2h) (GIRZ:86-88, DF:19-21, 53-68). Even positions are top or thin places at w. Odd positions are thick or thin places at w̄.
3. So the self-Gaussian cancellation of the Hecke route **is** available. It is the same isotropy mechanism, stated uniformly for "inertClass with h ≠ 0, or signal" (NFS:19). It is encoded in condition B3: every monomial of be has positive even-position degree and positive odd-position degree, and is not of bidegree (1,1) (PZF:47-49). What changes at signal places is not the Gaussian. Three things change:
   - there is no Hecke operator and no colength;
   - every odd partner of a top is a `true` place, so dTop = ∞ and there are no top–top exclusions;
   - the valuation is bounded by an LP-duality argument (`thmAJetA`) instead of the adjointness cap lemma.
4. The local exponent per top s is Σ_{e odd}((ν₀ − ν₁)(s)/p^e − ν₀(s+e))₊ − γ_p·Wc(s). The first sum is the ledger's Σ_{e odd}(a_t/p^e − w_{partner})₊, because:
   - the number of minors at a partner is ν₀(s+e) = wPl − kaJ + u₀ (CapLe.lean:11-26, read);
   - the family weight wPl at a thick place lies in [b, b+η+1] (GIRZ:148).

   So at p ≈ x it is b·(a_t/(bp) − 1)₊ + O(poly x).
5. The extra term −γ_p·Wc ≈ −γ_p·b per top (errF) has a source: Gaussian factors that point **backwards**, from a partner at s − |j| into the top. It is booked in E, not in Ga.

## 1. Statement

### 1.1 Setup at a signal prime (task 1)

**Splitting** [SIGNAL §1.1, LEDGER §0.4; definitions re-read at GIRZ:131-155]:
- Frob_p = ((+1, −1), h) ∈ {±1}² × A, and c = ((−1, −1), 1).
- p is inert in K and split in ℚ(√−q).
- No power of Frob equals c, so every place v of F = E^{⟨c⟩} above p splits as w ≠ w̄ in E.
- The residue degree is f = ord Frob = lcm(2, ord h) = nP.

**Positions** (DF:19-21, read):
- `posPl z e = (z.1 xor (IsSg ∧ e odd), z.2 + e·h)`. At a signal prime, from (false, t₀), position s is (s odd, t₀ + s·h).
- `posPl_period`/`posPl_inj` (DF:53-68, 137-168, read) show that the orbit has exactly nP = 2·ord(2h) elements, which is even.
- *Gloss from SIGNAL §1.2, not re-traced:* position s is the CM-type embedding τ₀·(Frob·c)^s. Even s lie over w and odd s over w̄. The w-coordinates and w̄-coordinates are the two Lagrangians of the split hermitian space.

**Tops and partners** (GIRZ:131-137, read):
- partner(t, e) = (IsSg ∧ e odd, t + e·h).
- Tops are (false, t) with t ∈ TT.
- A place is thick if it is (true, t′) with t′ ∈ dig(T2) + u₀.
- So at a signal prime every odd-e partner of a top is a `true` place: thick or thin, never a top.
- `orbit_place_term_le_sum` proves dTop = ⊤ for every top on a signal orbit (OVB/SummableTruncatedGeometric.lean:184-192, read).

**Kernel and coordinates.**
- The object is the adapted-basis entry `t.ent.Th u μ w i c c′` of the **global** theta kernel. It is rewritten as the standard series `stdSer` (AKS:63-65, read).
- Variables are X_{s,a,b}, with s a position on the orbit and (a, b) ∈ N_i × N_{i+1} a matrix entry.
- They are height-two log coordinates: `logPl` sends X to Σ_e X_{s−2e}^{p^{2e}}/p^e (OP:133-135, read). This is the Honda logarithm ℓ, with the Frobenius twist written as a shift of position by −2.

**Kernel law** (`ThetaExpansionAllPlaces`, OP:186-190, read):

  Th(ep·logPl(X)) = U(X) · [exp(Σ_{r∈R} sg_r Σ_{a,b} be_r(X_{orb r, ·, a, b}))](logPl(X)),   with U integral and ‖ep‖ = 1.

- This is the same kind of statement as `adm2`: kernel = exp(−Ph) × (integral in the LT parameter), with Ph = Σ_{orbits} Σ_{a,b} be(X_{orbit,a,b}) and sg = −1.
- be = beOf(σ, cob F(phFF), ω, ω\*, ζ) is the polarisation of ph = −log σ\* (NFS:23, read), written in the nP position variables of one orbit. The Hecke route writes it as hyperbolic pairs (x_e, y_e) instead.
- be must satisfy B1–B4 (`BeOK`, OP:181-184; PZF:37-72):
  - B1: coefficients are unramified;
  - B2: torus invariance;
  - B3: every monomial has positive even-position degree and positive odd-position degree, and bidegree ≠ (1,1). **This is the "self-Gaussians have cancelled" condition**;
  - B4: the Dwork form, i.e. exp of the coboundaries is W-integral in letter-log coordinates.

**Supplier of the kernel law** (read at these lines):
- `exists_beFam_evenConditionsInert_of_kerEnt` (AKS:24-66) applies, for a place w with (RCZ ∧ HEv) ∨ IsSg, the theorem `normalisedFamily_standardBases_integrality_alt` (AKS:41). It gets B1–B4 from `standard_series_b_conditions_large_prime` (AKS:52, stmt not opened).
- `normalisedFamily_standardBases_integrality` (NFS:19-30) composes three pieces:
  - `HostAt` (curve data; supplied by `hostAt_inert` at SP/AtOfTrueColumns.lean:35);
  - `standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst` = `hyp_of_stdBases`, which gives the kernel as Θ_orth ∘ hypZ(f, f′) with a hyperbolic pair (statement at SP/StandardBasesHyperbolicPairOrthonormalStatement.lean:12; its leaves were read by SIGNAL);
  - `orbitIdentity_all_of_integralClass_hostLog_alt` (statement at SP/OrbitIdentityAllOfIntegralClassHostLogStatement.lean:12; ORBIT and JETA read the body as an outline).
- The hypothesis is `(IsResidueClassZero ∧ hP ≠ 0) ∨ IsSg` (NFS:19). **Signal places are covered explicitly.**

**Lattice.**
- The local bound `KvalGe` (PZF:99-102) is stated for every column choice I, i.e. against every product of target column minors Gxz I, and for every class pair (L, L′) (`EntGe`, OP:60-62).
- `KForm` (OP:71-73) turns it into `KGe`, which holds for **every** x in the global lattice (T.fm u μ).lat i at w (OP:19-28). This goes through `kform_of_ker` and the equality `KerEnt.lat_S` [ORBIT §2(b), JETA §2.3; not re-read].

### 1.2 The statement: exponent per top and per lift (task 2)

**Local theorem** (`Loc.Cor` with C6 = 11, Cd = 1, the `Cor2` of LBE:13-22; `split_bound_eleven_one`, LBE:64-67, read). Fix one orbit with tops TT ⊂ ℤ/nP and Young diagrams ν_s at the positions (the level-(i+1) shape). Assume HidaSetting:
- p ≤ a;
- every size is ≤ a;
- N₀ ≥ 2·log_p a + 3.

Then every monomial coefficient of every jet applyAt0(Th, Gxz I) has v_p at least

  Σ_{s∈TT} baseTerm(s) + lpF((k−1)w) − 11·Σ_s w_s/p − γ_p·Σ_{s∈TT} Wc(s) − nP·N₀N₁·(log_p a + 1),

with these definitions:
- baseTerm(s) = Σ_{e odd, e ≠ dTop(s)} ((ν_{s,0} − ν_{s,1})/p^e − cap(s+e))₊ (PZF:173-178);
- cap(z) = ν_{z,1} at a top and ν_{z,0} elsewhere (PZF:157). Since every column minor at z uses row 0, ν_{z,0} is the number of minors at z;
- Wc(s) = sup{cap(s−i) : i odd, p^i ≤ size(s−i)} (PZF:163-164);
- lpF((k−1)w) is the Gaussian-free base LP of the non-top rows. That LP is defined in IB:18-28, and lpF is identified with Fnum at LBE:44.

**At a signal orbit** (dTop = ∞) the per-orbit statement used is `OrbitValuationBound` (OP:355-360, read):

  β_r = g0Pl(r) + FOrb(r) − errF(r),

- g0(t₀) = Σ_{s∈topsOn t₀} Σ_{e odd} (al_s/p^e − capU(s,e))₊ − dl (GIRZ:247-250). Excl is empty here.
- al = a_t − 2cG (GIRZ:230).
- capU = fillG(partner) + cG = fill(partner) − kaJ(j) + cG (GIRZ:232-233, 154-159).
- FOrb = lpF((k−1)·wPl on the orbit) (DF:99-100).
- errF = γ_p·topsOrb·(b+η+1+3Sc) + c6·Σ_s w_s/p + nP·N_{j−1}N_j·(log_p(4nP·Nm·a) + 1) + dl-terms (OP:239-244).

**Cap, w, thick, and the family weights: the explicit correspondence.**

| object | definition | file:line (read) |
|---|---|---|
| cap at partner z = (true, t′) | ν_{z,0} = number of column minors at z | PZF:157; OP:58 |
| row 0 of ν_z | wPl(j+1, z) − kaJ(j+1) + u₀(z) | `row_le`, CapLe.lean:11-26 (via `nuRowOK`, `nuRow_head`, stmt) |
| cap ≤ capU | ν_{z,0} ≤ fillG + cG; proved for every family member x ≥ x₀ | `cap_le` CapLe.lean:28-45; `Shape.capG` OP:272; `shape` CapLeWidth.lean:73-114 |
| fill = family weight | fill(z) = [z top]·b_z + off_j(z); fill = wj (`ParametersFill`); count's partner weight wPart = fill(partner) | GIRZ:154-155, 401-405 |
| thick | z = (true, t′), t′ ∈ dig(T2)+u₀; off ∈ [b, b+η+1] | GIRZ:136-137, 148 |
| thin / top offsets | off ∈ [w″, w″+η] at thin, [b′/x, b′/x+η] at tops | GIRZ:146-147 |
| a at a top | al ≤ ν₀ − ν₁ at (false, t) | `al_le` AlLeParams.lean:30 (stmt); `Shape.alG` OP:270 |
| caps are ≤ b | ν-cap ≤ b+η+1+3Sc everywhere | `cap_le_width` CapLeWidth.lean:47-71; `Shape.capW` OP:268 |

**Derivation of the Riesz weight** (*inference*, arithmetic on the definitions above). Take a signal p, a top t at an even position s, and level j.
- **e = 1, thick partner.** The partner of t at e = 1 is (true, t+h). If it is thick, capU = off − kaJ + cG with off ∈ [b, b+η+1]. With a_t ∈ [a, a(1 + 1/(k·x^{13}))] and a = x·b [LEDGER §2a], the e = 1 term is

    (al/p − capU)₊ = (a_t/p − b − θ)₊ = b·(y/p − 1)₊ − O(|θ|),   y = a_t/b ≈ x,   |θ| ≤ η + 1 + kaJ + cG + 2cG/p.

  This is the Riesz kernel (y/n − 1)₊ at n = p, at scale b. It is nonzero only for p < y ≈ x.
- **e ≥ 3, thick partner.** The term is b·(y/p^e − 1)₊, the Riesz term at n = p^e. In it χ_{−d}(p^e) = −1 and Λ(p^e) = log p.
- **Thin partner.** Then capU ≤ w″ + η − kaJ + cG, the term is ≈ a_t/p^e, and its Riesz length is ≥ X′ (ThinScales territory, [LEDGER §2c]).
- **The factor 2 log p.** It comes from Ga = Σ_w sz(w, ·) with sz = 2·lwP·e_w·y (DP2:205-206, [GATIE]). That factor is outside this node.

So "cap = w" on this route is literally ν₀(partner) = w_j(partner) − kaJ + u₀, and the shift kaJ ≈ k/2 is ≤ poly(x) ≪ b. The ledger term 2 log p·b·(a_t/(bp) − 1)₊ is the e = 1 summand of g0 at a thick partner. Note that g0 can **exceed** the ASK summand by up to kaJ per active level, because capU uses fillG = fill − kaJ. That direction is harmless: the lower clause needs only ASK − Ga ≤ LoP.

## 2. Argument (task 3), link by link

| # | link | where | status |
|---|---|---|---|
| L1 | kernel law (Gaussian class, B1–B4) for the actual entries at signal w | AKS:24-66; NFS:19-30 | **read** at these two levels; `hyp_of_stdBases`, `orbitIdentity…`, `standard_series_b_conditions…` stmt |
| L2 | full kernel → per-orbit kernel (`OrbitRestriction`), and orbit bounds add (`OrbitsAddLowerBound`) | OP:207-221; `entI_of` OP:1090-1127 | defs and `entI_of` **read**; `orbAddUp_main` [ORBIT] |
| L3 | orbit law ⇒ AdmB ⇒ BHyp; log inversion Θ(ep·X) = U(g(X))·exp(ε·bSum be) | `thmA_of` DPW:177-211; `KernelFromExponentialTwist` DPW:154-164 | `thmA_of` **read**; `tieB`, `kernel_from_twist_holds` stmt |
| L4 | generic frame: KvalGe ⇐ frameJet bound at a residually generic frame | `TieFrame` DPW:165-175; `thmAGauss_of` ThmAGaussOf.lean:13-56; `theorem_A_generic` Generic.lean:133-226 | **read**; `GaussPow`, `frameA_letter`, `theorem_A_frame` stmt or [JETA] |
| L5 | per-monomial LP-duality bound `thmAJetA` | GJ/StatementG.lean:33-64; GJP/TheoremAOneMonomialLogLoss.lean:15-239 | **read** |
| L6 | weighted-radius jet lemma (Legendre + Dwork + "one p per Gaussian factor") | `lemmaRA_of`, GJP/LemmaRA.lean:13-172 | **read**; `lemmaS`, `PureCross`, `ExpWtLe` stmt |
| L7 | top LP (primal/dual) and assembly | `rowRadiusAssembly`, `asmA_top_gen`, `asmA_top_choice`, `asmA_row` CLR:45-299 | **read** to :299 (the final assembly lines 300+ not read) |
| L8 | ThmA ⇒ Cor (gap row0−row1; base LP perturbation) | LBE:33-62 | **read**; `normCor7`, `base_term_le_top_term` stmt |
| L9 | Cor on orbLoc ⇒ g0Pl + FOrb − errF | `prvF_of_orbitLetterBounds` OVB/PrvFOfOrbitLetterBounds.lean:17-59; `orbit_place_term_le_sum` SummableTruncatedGeometric.lean:136-199 | **read**; `sum_Wc_le`, `loss_le`, `setting_sq` stmt |
| L10 | one lift: entries ⇒ KGe at g0S + F − ES (+sp·vDG at i = 0) | `liftI_of` OP:970-1015; `KForm` OP:71-73; `OrbitSumBound` OP:388-391 | **read**; `sumI` (OP:1278) and `kform_of_ker` [ORBIT] |
| L11 | m lifts | `chain_ge` OP:779-791, `KG.loc`/`KG.step` OP:753-777, `compose` OP:806-812, `noOp_of` OP:919-932 | **read** |

### 2.1 The orbit identity (L1–L3)

**What the entries are.** The adapted entry is the standard series of the global kernel, `stdSer` (AKS:63-65). `hyp_of_stdBases` writes it as Θ_orth ∘ hypZ(f, f′): an orthonormal product theta, composed with a linear map built from a hyperbolic pair (f, f′). There are nP/2 pairs per orbit, isotropic and dual.

**Where the self-terms go** (*inference*, as at GIdx [ENGINE §2(c)]). The orbit identity then gives ThetaExpansionAllPlaces with be the polarisation of ph, summed over orbits.
- The self-terms Σ_i N(f_i)·ph cancel by isotropy, exactly as `hyperbolic_plane_split` does on the Hecke route.
- In the Lean the result is recorded as B3 on be. B3 forbids monomials supported only on even positions or only on odd positions.

**Answer to "is the orbit odd here?"** No. nP is always even at signal places (DF:53-68). The Hecke route's cancellation is therefore available unchanged, and nothing replaces it. The differences lie downstream (§0 item 3).

**The step to BHyp.** `thmA_of` (DPW:177-211) carries out two steps:
1. turn B1–B4 into BHyp (`TieB`);
2. invert the log (`KernelFromExponentialTwist`).

The result is Θ_x = U(g(entries(W)))·exp(ε·bSum(frameM x, be)) in frame coordinates W, which is the kernel of `ThmAJetA` (GJ/StatementG.lean:59-61).

### 2.2 Generic-frame reduction (L4)

KvalGe bounds the monomial coefficients of the jet polynomial applyAt0(Th, Gxz I) in the source frame variables. `TieFrame` (DPW:165-175) reduces it to a bound on the coefficients of `frameJet`. `thmAGauss_of` (ThmAGaussOf.lean:13-56, read) then proceeds as follows:

1. **Residually generic point.** It takes a residually generic point Y of an extension field (`residuallyGenericExists`). Every primitive integral polynomial has norm 1 at Y. So the Gauss norm of a polynomial is bounded by its value at Y, and also at Y^{k} with positive exponents k (`GaussPow`, stmt). It evaluates at genFrame = Y^{l^m} on top rows and Y elsewhere (:47-56). The Frobenius power l^m on the top rows makes the backward directions Y_top^{l^{m+j}} (j < 0) polynomial.
2. **Labels and unit Gram determinant.** `theorem_A_generic` (Generic.lean:133-226, read) dedicates one row e(s,i) = i (+1 at a top) to each label (s₀, j) [`LabelsExist`, which is why N₀ ≥ 2·log_p a + 3]. It proves that the Gram matrix ⟨λ_i, Y_{s,e(i′)}⟩ with λ_i = Y_top^{l^{E}} has unit determinant (`hdet` :185-224, via `generic_minor_norm`, which specialises to a monomial determinant).
3. **Change of frame.** `theorem_A_frame` (stmt) then changes the frame by an integral T. Every unlabelled row becomes orthogonal mod p to every twisted top direction (the `hkill` hypothesis, StatementG.lean:54-58).
4. **Cauchy–Binet.** Products of minors of T·x are integral combinations of products of minors of x, so the bound transfers [JETA §2.2(iii)].

### 2.3 The LP-duality bound `thmAJetA` (L5–L7)

**Weights.** Give each frame coordinate i a radius ρ + r_i, with ρ = 1/(p²−1). Write wt(f) ≥ w when every coefficient of monomial n satisfies v ≥ w − Σ n_i(ρ + r_i).

**Lemma RA** (LemmaRA.lean:55-169, read). Suppose every pure bipower W_i^{p^α}W_j^{p^β} ≤ κ whose coefficient in bSum fails the good weight 1/(p−1) satisfies the dual inequality p^α r_i + p^β r_j ≥ 1. Then

  v(κ!·coeff_κ Θ_x) ≥ Σ_i κ_i(γ_p − r_i) − |coords|·(log_p a + 1).

The proof has four steps:
1. **bSum has weight ≥ 1/(p−1) with the new radii** (:95-113). Non-pure monomials are good by `lemmaS` clause 2 and `PureCross`. A bad pure monomial has weight ≥ 1/(p−1) − 1 − ρ·deg by `lemmaS` clause 1 (GJ/Statement.lean:98-105). The dual inequality absorbs the −1.

   **This is "each Gaussian factor costs one p":** lemmaS says the polarisation be is at most one power of p worse than the Dwork-good weight 1/(p−1), and only on bipowers X_s^{p^α}X_{s′}^{p^β} with s even, s′ odd and s + α = s′ + β (`IsBiPower`, GJ/Statement.lean:78-81). These are the terms c·x·y^p/p of Gser.
2. **exp(ε·bSum)** keeps weight ≥ 0 (`ExpWtLe`), since v(m!) ≤ (m−1)/(p−1).
3. **U∘g has weight ≥ 0 at radius ρ** (`GenLogWeight`, `SubstWt`). This is the height-two radius: integral in X means integral in z/ϖ.
4. **Legendre** (`factValA`, :13-53): v(κ_i!) ≥ κ_i/(p−1) − log_p a − 1. With 1/(p−1) − ρ = γ_p (:68-73), the result follows.

**Which pairs can be bad** (TheoremAOneMonomialLogLoss.lean:74-95, `jet_bipower`/`jet_collapse`). A bad pair joins coordinates at different positions with s + α = s′ + β and α + β odd. So a top at s₀ can pair only with rows at odd distance j = α − β.

**Radii** (`rowRad`, GJ/StatementA.lean:10-17; proof :24-59, 96-206):
- a top row gets ε(s₀);
- a row labelled (s₀, j > 0) gets max(σ, 1 − p^j ε);
- a row labelled (s₀, j < 0) gets max(σ, p^{−|j|});
- any other row gets σ, where σ is an optimal dual of the base LP for Dl (`lemmaFa`).

The dual checks:
- **Forward pair** (j = α − β > 0): p^α ε + p^β(1 − p^j ε) = p^β ≥ 1 (:169-174).
- **Backward pair** (j < 0): p^α ε + p^{α+|j|}·p^{−|j|} ≥ 1 (:158-164).
- **Top with an unlabelled row:** impossible. The frame is orthogonal mod p and `FramePure` adds an extra p (:175-187).
- **Two non-top rows:** handled by IsDualAll of σ.
- **Two tops at odd distance:** p^α ε + p^β ε′ ≥ 1 needs ε ≥ p^{−dTop} (:205-206). This **never occurs at signal places**.

**The top LP, stated** (CLR:45-187, read). For one top with budget A = ν₀(s₀) (the degree of the top row, which equals the number of minors) and caps c_j = cap(s₀+j), j odd:

- **Primal** (the number of forward Gaussian factors the jet can absorb): maximise Σ_j n_j subject to 0 ≤ n_j ≤ c_j and Σ_j p^j n_j ≤ A.
  - A factor W_top^{p^α}W_row^{p^β} with α − β = j uses p^α ≥ p^j top degrees.
  - The labelled row's total degree is ≤ c_j (StatementG.lean:51-53; one row per label, `hinj`).
- **Dual:** minimise over ε ≥ 0 the quantity A·ε + Σ_j c_j(1 − p^j ε)₊.
- **What the Lean proves** (`asmA_top_choice`, :81-118). Choose ε = p^{−T}, where T is the first odd level with A/p^T ≤ c_T, i.e. the first level at which the budget, not the cap, binds (ε = 0 if there is none and dTop = ∞). Then

    A·ε + Σ_j c_j(1 − p^j ε)₊ ≤ Σ_{j odd} min(c_j, A/p^j)   (`asmA_top_core`, :45-79).

  With A·γ_p = Σ_{j odd} A/p^j and max(A/p^j − c_j, 0) + min(A/p^j, c_j) = A/p^j, `asmA_top_gen` (:126-186) gives

    A·γ − A·ε − Σ_j c_j(1 − p^j ε)₊ ≥ Σ_{j odd} (A/p^j − c_j)₊ = topTerm (dTop = ∞).

- **Assembly** (`asmA_row`, :255-276). Each row loses at most κ_i·cost(label). Summed:
  - forward labelled rows give the dual's Σ c_j(1 − p^j ε)₊;
  - backward rows give Σ_{j<0} c_{s₀+j}·p^{−|j|} ≤ γ·Wcap (`capacity_le_reachCapacity`, :219-239);
  - non-top rows give Fnum(Dl) = ΣDl(γ − σ).

**Why the Lean charge Σ_e min(cap_e, A/p^e) is what the ledger needs** (*inference*).
- The true LP optimum shares the budget A across levels. It is ≤ Σ min, so the Lean charge is conservative. `jeta_lp.py` checked this on 4000 instances.
- The charge Σ_e min(c_e, A/p^e) is exactly γA minus the sum of independent per-level Riesz terms Σ_e(A/p^e − c_e)₊.
- ASK is Σ_n Λ(n)(1 − χ(n))(a/n − w)₊, which is independent per prime power n = p^e. So the Lean's weaker charge is the one that reproduces ASK term by term. The optimal LP value would give a larger gain, but not in Riesz form.

### 2.4 Legendre, ThmA ⇒ Cor, and the per-orbit numbers (L8–L9)

**ThmA ⇒ Cor** (LBE:56-62, read). Cor uses two facts:
- baseTerm ≤ topTerm, because the gap ν₀ − ν₁ ≤ ν₀ (stmt);
- `local_bound_eleven_comparison` (LBE:33-54): lpF((k−1)w) − 11·Σw/p ≤ FD, whenever Dl = (k−1)w + E with 0 ≤ E ≤ 4w (and −2w at tops). Shape.low and Shape.top supply these hypotheses (OP:253-258).

**`prvF_of_orbitLetterBounds`** (read) applies Cor to orbLoc with w = wOrb and a := a² (:22-24). It then compares:
- g0Pl ≤ Σ baseTerm (`orbit_place_term_le_sum`). Termwise, al ≤ gap (Shape.alG) and cap ≤ capU (Shape.capG). The proof also shows dTop = ⊤ and Excl = ∅ at signal places (SummableTruncatedGeometric.lean:148-199);
- γ·ΣWc ≤ γ·topsOrb·(b+η+1+3Sc) (`sum_Wc_le` with Shape.capW; :39-41);
- the Legendre digit-sum term C·nP·N_iN_{i+1}·(log_p a² + 1) is ≤ the N·N and dl parts of errF (`loss_le`, stmt);
- FOrb = lpF((k−1)w), by definition (:44).

### 2.5 The source and size of errF

errF (OP:239-244) has four parts. They reappear verbatim in `EatI` (DE:147-155), and Eval = vDG + EatI at signal places ≤ X″ (DE:159-169; `eE`, OP:997-999).

1. **γ_p·topsOrb·(b+η+1+3Sc).** This is the backward-partner loss of §2.3: Σ_{j<0 odd} c_{s₀+j}·p^{−|j|} ≤ γ_p·Wcap.
   - At a signal top the backward positions s₀ − |j| are `true` places. Some of them are thick, with cap ≈ b, and Wc takes the sup over all of them. Hence ≈ γ_p·b per top.
   - Mathematically these are Gaussian factors W_top·W_partner^{p^{|j|}}, which the partner row pays for. The ledger has no counterpart for them.
2. **c6·Σ_s w_s/p.** This is the base-LP perturbation from Cor (11Σw/p ≤ c6Σw/p, c6 = 12). Since Σ_s w_s ≈ (number of thick positions on the orbit)·b, it is again ≈ b/p per thick position.
3. **nP·N_{j−1}N_j·(log + 1).** The Legendre digit sums, one log per frame coordinate.
4. **dl.** Duplicates of g0's own dl.

**Size** (*inference*). Per lift and per signal p ≤ X″, part 1 summed over orbits is γ_p·|TT|·(b + …). With the weight 2·log p per prime [GATIE], the sum over signal p ≤ X″ is

  ≈ 2|TT|·b·Σ_{p sig ≤ X″} log p/p ≈ (1/2)|TT|·b·log X″,   log X″ ≈ x^{ε/3}.

The density of signal primes is 1/4. Over m lifts this gives ≈ |TT|·m·b·log X″, which agrees with GATIE §2c. It is booked in E, not in Ga, and is charged against adm11 (C·B₀ per lift, B₀ = f·m·b·x^ε) [GATIE, stmt]. It is larger than LoP = C|TT|mb by x^{ε/3}, but it is relative x^{−1+ε/3} to the main mass m·|TT|·a.

### 2.6 One lift, and the ESCALATE check (L10)

`liftI_of` (OP:970-1015, read) works as follows:
- For a signal w, it sets L.F = FInert = Σ_{reps} FOrb (DF:112-114; `sum_orbits` DF:170-189) and ES = vDG + EatI (:993-999).
- It feeds `EntriesAtInert` (entry bound Σ_r β_r) into KForm (B − vDG, or B − (1−sp)·vDG at i = 0).
- It applies `OrbitSumBound` (OP:388-391): Σ_{reps} g0⁺ + FInert − EatI ≤ Σ_r β_r.

The result is KGe at g0S + F − ES (+sp·vDG at i = 0) (`OneLiftInertBound`, OP:398-405). Here:
- g0S = Σ_{reps} max(g0, 0) (WJS:54-55);
- gainP at a signal prime is the same sum, since VV = ∅ (GIRZ:355-358);
- the ledger's sg = Σ_j(gain + F − E) [GATIE §0.3].

**So the proved exponent is not smaller than the one Ga uses. No ESCALATE.**

## 3. Numerical experiments that bear on this route (task 4)

| script | what it did | what it did not test |
|---|---|---|
| `numtest/jeta_lp.py` (out: `out_jeta_lp.txt`, 0/4000 violations) | Exact rational arithmetic on the **top LP only**. Checks: the assembly inequality Aγ − loss(ε\*) ≥ topTerm with the best breakpoint ε; that Σ min(cap, A/l^j) ≥ the greedy LP primal; and every top–partner dual constraint, j > 0 and j < 0. Range: l ∈ {3,5,7,11}, A ≤ 3l⁴, dTop ∈ {∞,1,3,5,7} | no kernel, no valuations of any series. Not tested: lemmaS, LemmaRA, the frame reduction, the γ·Wcap sum, the base LP Fnum |
| `numtest/signal_twotops.py` (NODE-SIGNAL §E; worst v − pred = −1.13 over 57 jets) | p-adic valuations of **actual jets** of the n′ = 4 CM product-theta kernel (kernel3/kernel4 libs, ℤ[ω], p = 5). Two tops at the even positions 0 and 2 (orders a ≤ 160 and n₂ ≤ 32); caps n₁, n₃ ∈ {0, 4, 8} at the odd positions. Prediction γ(a+n₂) − Σ min. This is the signal-place configuration | rank one: one matrix entry, no column minors, no frame, no HidaSetting (N₀ ≥ 2log a + 3 fails). Only p = 5. Caps ≤ 8 ≪ a/p, so the regime a/p ≈ cap ≈ b (the kink of the Riesz weight) was never probed. γ₅·cap ≤ 1.7, the size of the digit-sum slack, so the test cannot tell whether the γ·Wcap backward charge is real or an artefact. It does not test the Lean code, the global entries, adapted bases or lat_S |
| NUMTEST3 [SIGNAL §5] | a signal place with h = 0, n′ = 2, one entry, one top, one cap | as above; also only one top |
| NUMTEST4 | n′ = 4 with genuine minors (det^m blocks): caps per position, det^m costs m | its prime class is disputed (MAIN-ARGUMENT §4.7). It tests the local law shared by both routes, not this route's code |

*Inference.* The predictions of all four use only forward caps, without −γ·Wcap. The observed slack is −1.13 to −1.54, far below the γ·Wcap allowance at these sizes. So the data are consistent with the backward charge being conservative, but at these sizes they cannot show it.

## 4. Composition over m lifts (task 5)

`chain_ge` (OP:779-791, read) is an induction on n.
- **Hypothesis after n steps:** the image is y = a·z with z ∈ locW(lat n) and v(a) ≥ e·Σ_{j≤n} s_j.
- **Extension to the localisation.** `KG.loc` (OP:753-769) extends the one-step bound from the global lattice (M.lat i).L to its O_w-span by span induction (zero, add, scalar multiplication).
- **One step.** `KG.step` (OP:771-777) applies the bound to z and uses linearity of K_i: K(a·z) = a·a′·z′ with v(a′) ≥ e·s_{n+1}.

**What composes:** the linear maps K_i between the actual global lattices (T.fm u μ).lat i. Gains add because a scalar factors out of a linear map, and because the one-step bound is universal over the lattice. Nothing about z is used beyond lattice membership.
- `compose` (OP:806-812) handles twisted μ through `base_map_mem_local_lattice`.
- `noOp_of` (OP:919-932) only regroups Σ_j(g0S_j + F_j − ES_j) + sp·vDG as Σ_j g0S_j + lowS.

**Per level** (*inference* from the definitions):
- The partner cap at level j is ν₀ = w_j − kaJ(j) + u₀, which grows with j through w_j.
- al is the same at every level (Shape.alG, ∀ i).

So the total is Σ_j Σ_t Σ_{e odd}(al_t/p^e − capU_j)₊. This matches the ledger's Σ_j in ASK.

## 5. Honest list (task 6)

**Verified by reading (this round):**
- the position structure and nP even (DF);
- partner, thick and fill definitions (GIRZ);
- the kernel-law supplier at two levels (AKS, NFS);
- the full `thmAJetA` proof (TheoremAOneMonomialLogLoss) and LemmaRA;
- the top LP and dual (CLR:45-299);
- the generic-frame top level (ThmAGaussOf, Generic:120-228);
- thmA_of and ThmA ⇒ Cor (DPW, LBE);
- prvF and orbit_place_term_le_sum, including dTop = ⊤ at signal places;
- errF = EatI parts; Eval;
- liftI_of, KForm use, chain_ge/KG.loc/KG.step/compose/noOp_of;
- Shape proved for family members, and cap_le via row_le (CapLe, CapLeWidth).

**Statement only:**
- `lemmaS` (the "one p per bipower" weight law);
- `PureCross`, `ExpWtLe`, `GenLogWeight`, `frame_pure_weight`, `GaussPow`, `theorem_A_frame`/`frameA_letter`, `generic_minor_norm`;
- `tieB`, `kernel_from_twist_holds`, `tieFrame`;
- `hyp_of_stdBases`, `orbitIdentity_all_of_integralClass_hostLog_alt`, `standard_series_b_conditions_large_prime`;
- `base_term_le_top_term`, `normCor7`, `sum_Wc_le`, `loss_le`, `sumI`;
- `nuRow_head`, `fill_eq_wPl`, `al_le`;
- `kform_of_ker`/`KerEnt.lat_S` [ORBIT, JETA];
- the HostAt inputs (IntInert, CurveDict, GenusOneModelExistsLattice), which are hypotheses passed into `at_of_true_columns`;
- adm11 (E ≤ C·B₀) [GATIE].

**Inferred:**
- even positions lie at w and odd ones at w̄ (SIGNAL's gloss);
- self-terms cancel inside `orbitIdentity` as on the Hecke route;
- the Riesz-weight derivation of §1.2;
- the errF total of §2.5;
- that kaJ and cG are poly(x). I did not open `cG`'s definition; LEDGER and GATIE report the shifts as poly(x).

**The single statement an expert should check first:** the kernel law at a signal place, `normalisedFamily_standardBases_integrality` (NFS:19) in its IsSg branch, together with `lemmaS`. It asserts that:
- the adapted global theta entry is U·exp(−Σ_{orbits} be) with U integral in height-two LT parameters;
- be (the polarisation of −log σ\*) satisfies B3;
- be's coefficients are at most one power of p worse than the Dwork weight 1/(p−1), and only on the even–odd bipowers X_s^{p^α}X_{s′}^{p^β}.

Everything downstream is LP arithmetic and linear algebra, read to the bottom.

## 6. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `normalisedFamily_standardBases_integrality` | NFS:19 | ThetaExpansionAllPlaces with B1–B4 at RCZ∧h≠0 or IsSg | **core**; read at the top level, its three inputs stmt |
| 2 | `lemmaS` | GJ/Statement.lean:98 | be has weight ≥ 1/(p−1) − 1, and ≥ 1/(p−1) off even–odd bipowers | **core**, stmt (Dieudonné/Honda-type) |
| 3 | `ThmAJetA_of` / `lemmaRA_of` | GJP/TheoremAOneMonomialLogLoss.lean:15; GJP/LemmaRA.lean:55 | dual-radius jet bound | core, **read** |
| 4 | `rowRadiusAssembly`, `asmA_top_gen` | CLR:278, 126 | top LP duality, giving topTerm | core, **read** (tail of 278 not read) |
| 5 | `thmAGauss_of`, `theorem_A_generic` | ThmAGaussOf.lean:13; Generic.lean:133 | generic frame | standard (Gauss norm = generic value; Cauchy–Binet), **read** |
| 6 | `prvF_of_orbitLetterBounds`, `orbit_place_term_le_sum` | OVB/PrvFOfOrbitLetterBounds.lean:17; SummableTruncatedGeometric.lean:136 | Cor ⇒ g0Pl + FOrb − errF | glue, **read** |
| 7 | `shape`, `cap_le`, `row_le` | CapLeWidth.lean:73; CapLe.lean:28, 11 | Young rows = family weight − kaJ + u; caps ≤ capU | core identification, **read** (leaves `nuRow_head`, `fill_eq_wPl` stmt) |
| 8 | `liftI_of`, `chain_ge`, `noOp_of` | OP:970, 779, 919 | one lift; m lifts | glue, **read** |
| 9 | `kform_of_ker` / `KerEnt.lat_S` | OP:1621; DKI:100 | entry lattice = chain lattice | core [ORBIT, JETA] |

## 7. Oddities

1. **The backward charge γ_p·Wc ≈ γ_p·b per top per signal prime per lift** is a real term of the proof, not of the mathematics of the ledger. It totals ≈ |TT|·m·b·log X″, which is above LoP and is carried by E/adm11. It is plausibly an artefact: the radius for j < 0 is the crude p^{−|j|} [JETA oddity 2].
2. **Gain can exceed the ASK summand.** capU = fill − kaJ + cG, while ASK uses fill. The actual number of minors is w − kaJ + u₀, so the true cap sits kaJ ≈ k/2 below the family weight. This is harmless in direction, but it means "cap = w" holds only up to a ρ-type shift kaJ.
3. **The Lean's charge Σ min(cap_e, A/p^e) is weaker than the LP optimum.** That weaker form is exactly the per-prime-power Riesz structure the bridge needs (§2.3).
4. **HidaSetting needs N₀ ≥ 2·log_p a + 3 at every level** (Shape.rankA, OP:264), with a := a² in the call. This is satisfiable, since k ≈ x^{4.5} ≫ x^ε.
5. Nothing false-looking.

## 8. Coverage

Read this round:
- PROTOCOL; MAIN-ARGUMENT §0, §4; NODE-ENGINE, ADM2, LEDGER, GATIE, SIGNAL, ORBIT, JETA, SERVED:1-120;
- OP:1-300, 326-365, 380-459, 745-812, 915-1015, 1088-1132;
- PZF:1-300; IB:1-150;
- GJ/StatementG.lean, Statement.lean, StatementA.lean (all);
- GJP/TheoremAOneMonomialLogLoss.lean, LemmaRA.lean, ThmAGaussOf.lean (all); Generic.lean:120-228; CLR:40-299 (and its declaration list);
- DPW:150-215; LBE (all);
- OVB/PrvFOfOrbitLetterBounds.lean (all); OVB/SummableTruncatedGeometric.lean:60-199;
- DF (all); DE:120-200; GIRZ:125-160, 228-255, 350-375, 398-413; `Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean`:60-259; WJS:15-80;
- SP/: AKS, NFS, NormalisedFamilyStandardBasesIntegralityStatement, AtOfTrueColumns, StandardBasesHyperbolicPairOrthonormalStatement, OrbitIdentityAllOfIntegralClassHostLogStatement, KernelDatumConditionsAtStandardKernelComparison, CapLeWidth, CapLe (all);
- numtest/jeta_lp.py, out_jeta_lp.txt, signal_twotops.py.

Greps run:
- `theorem prvF_of_orbitLetterBounds`; `def FOrb|def wPl|def kindA|def topsOrb`;
- `theorem orbit_place_term_le_sum|sum_Wc_le|loss_le|setting_sq|admissible_of_jet_bounds`;
- `^def (g0|capU|al|partner|fill|fillG|kaJ|askG|gainP)` in GIRZ;
- `at_of_true_columns`; `at_of_stdTie`; `OrbitPlaces\.Shape\b`;
- `def EntriesAtInert|def OrbitValuationBound|theorem sumI|def OrbitLetterBoundsAll`.

Not opened:
- bodies of `lemmaS`, `PureCross`, `ExpWtLe`, `frame_pure_weight`, `theorem_A_frame`, `frameA_letter`, `GaussPow`, `tieB`, `kernel_from_twist_holds`, `tieFrame`;
- `hyp_of_stdBases`, `orbitIdentity…` (body), `standard_series_b_conditions_large_prime`;
- `base_term_le_top_term`, `normCor7`, `sum_Wc_le`, `loss_le`, `sumI`;
- `nuRow_head`, `fill_eq_wPl`, the definition of `cG`;
- `kform_of_ker`, `lat_S` leaves; CLR beyond :299.
