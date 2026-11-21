# NODE-ORBIT: the second (Hecke-free, global-entry) route that delivers the gain at signal primes

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `OP` = `Formalism/SharpRestriction/Divisibility/OrbitPlaces.lean`
- `PZF` = `Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean`
- `DKI` = `Formalism/LocalRingCardinality/DataKerI.lean` (structure `KerEnt`)
- `KEH` = `Formalism/LocalToGlobal/KernelLattices/ColumnData/KerEntHyp.lean`
- `SOP` = `Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean`
- `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- `DPW` = `Formalism/SharpRestriction/Divisibility/JetPolynomialLogs/DworkPowerSeriesWeights.lean`
- `GJ/` = `Formalism/GaussJetBounds/`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- `IW/` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/`

## 0. Verdict (short)

1. **What is bounded.** `NoOperatorOrbitBound` (OP:423-429) bounds the **m-fold chain** applied to x. Here x is any
   vector of S₀(w) ∩ ramSub. The chain image is measured against the level-m global lattice (T.fm u μ).lat m,
   localised at w (`ColGe`, WJS:24-35). The bound is Σ_{j=1}^m g0S_j + lowS.
   - It is obtained from **single-lift** bounds `KGe` (OP:19-28). KGe says: for every x in the level-i global lattice,
     K_i x lies in ϖ^{⌈e·s⌉}·(level-(i+1) lattice localised at w).
   - The single-lift bounds come from bounds on the **entries** (jets of products of minors) of each K_i.
2. **The iteration is honest.** `chain_ge` (OP:779-791) is a plain induction.
   - `KG.loc` (OP:753-769) extends the one-step bound from the global lattice to its localisation by span induction.
   - `KG.step` (OP:771-777) then applies it to a·z, where z is an arbitrary element of the localised lattice.
   - No intermediate form is assumed to be a theta image. Each level uses the single Lean object (T.fm u μ).lat i.
   - The total is Σ_{j=1}^m s_j exactly, and `noOp_of` (OP:919-932) only regroups that sum.
3. **Entry lattice = chain lattice.** The tie is a field of the structure `KerEnt` (`lat_S`,
   `levelFree_lattice_condition`, DKI:100-110). It states that the localisation at w of (Tw.fm u μ).lat i is *equal*
   to the set of rational forms whose class components have integral pairings with the products of ∇-minors in the
   adapted basis.
   - On the live path the KerEnt is `kerEntC` of a `KerEntHyp` (`IsEntC`). Its `latS` is proved by
     `kerEntHyp_latS` (IW/TrueChainsKernelDatumSourceSideLattice.lean:36-67), and its `latT` by the target-side
     analogue.
   - This is the exact analogue of GLOBALCHAIN's `latS`/`intS`. The only index charged is the automorphism
     denominator v_p(DGam), in `kgeTw_of` (OP:1464-1585), once per lift i ≥ 1. Level 0 has trivial stabilisers
     (`Stab0`, sp = 1).
4. **The local theorem is the same mathematics in a separate library.**
   - `split_bound_eleven_one` proves ThmA ∧ Cor for every Gaussian-class orbit kernel. ThmA is proved in
     `GJ/` (`thmAGauss` → `theorem_A_generic` → `thmAOp` → `thmAJetA`).
   - That proof uses a generic frame, frameJet of products of minors, a per-monomial shape bound with capped
     partner rows, and Dwork.
   - The Hecke route uses `Formalism.ThetaLogCoordinates…G7.kernel_a_two_generic` instead. The two are distinct code
     with the same architecture.
   - At signal places dTop = ∞, so baseTerm is the full Σ_{e odd}(gap/p^e − cap(s+e))₊ with cap = row 0 (number of
     minors) at the w̄ partner. That is NODE-PAIRING's formula.
5. **Orbits add with no loss.** `orbAddUp_main` expands U into monomials, which factor over orbits, and uses the
   multiplicativity of KvalGe across disjoint orbit variables. dG plays no role here.
6. **Judgement.** As reconstructed, the route delivers Σ_j Σ_reps g0⁺ for the m-fold chain at signal primes. The
   charges are lowS (per-lift F − ES with ES ∋ vDG, errF) plus one vDG returned at level 0. I could not follow the
   bodies of `thmAJetA`, of `kerEntHyp_latS`'s two leaves, or of `orbitIdentity_all_of_integralClass_hostLog` beyond
   its outline.

## 1. Statement

### 1.1 `NoOperatorOrbitBound` (OP:423-429), = `WJS.OrbitsWithoutOperator` (OP:454-455, rfl)

For every word u and every place w the following holds.
- **Hypotheses on w**: resChar w ≠ T_u; (inertClass with h ≠ 0) ∨ **signal**; ¬Exc p; p ≤ X″; every used tuple μ
  with p ∉ Qp μ.
- **Conclusion**: for every x ∈ `LT.Sram D u w` = S₀(w) ∩ ramSub (`DataLatDefs.lean:90-91`),
  `ColGe T u μ w x (Σ_{j∈lifts} g0S_j + lowS)`.
- `ColGe` (WJS:24-35): there is y in the level-m lattice of T.fm u μ such that emb y = col(e0Tw x) and
  `VGe w (lat m).L y s`.
- `VGe` (WJS:19-22): y = a·z with z ∈ locW w Λ (the 𝓞-span localised at w) and v_w(a) ≥ e_w·s.
- So the chain image is divisible by ϖ^{e·s} inside the integral lattice at w.
- **Gain** (WJS:51-52): g0S_j = Σ_{t0∈reps} max(g0(j,t0), 0).
  - g0(j,t0) = Σ_{s∈topsOn t0} Σ_{e odd} (al_s/p^e − capU_{j}(s,e))₊ − dl, from NODE-SIGNAL §2(c).
  - At signal places Excl = ∅.
  - al_s = a_s − 2cG.
  - capU = fillG(j, (true, s+e·h)) + cG. This is the level-j weight at the thick or thin place w̄, plus cG.
- **lowS** (WJS:73-74) = Σ_j (F_j − ES_j) + sp·vDG.

### 1.2 The single-lift statement it is built from
- `KGe T u μ w i s` (OP:19-28): ∀ x ∈ (T.fm u μ).lat i (the global 𝓞-lattice), ∃ y, emb y = K_i(emb x) ∧
  VGe w (lat (i+1)).L y s.
- `OneLiftInertBound` (OP:398-405): KGe at level i with s = g0S_{i+1} + F_{i+1} − ES_{i+1} + [i=0]·sp·vDG.
- `KForm` (OP:71-73): EntGe(i, B) ⇒ KGe(i, B − (if i = 0 then 1 − sp else 1)·vDG).
- `EntGe` (OP:60-62): every entry Th(L, L′) of the level-i kernel satisfies `KvalGe`.
- `KvalGe` (PZF:118-121): for every column choice I, every monomial coefficient of applyAt0(Th, Gxz I) has norm
  ≤ p^{−B}.
  - Gxz I = ∏_s ∏_{columns c of ν_s} (p_c × p_c minor of the product X·Z, rows 0..p_c−1, columns I_{s,c}).
  - applyAt0 pairs the Z-monomials against Th with factorials, i.e. takes jets at 0.
  - The result is a polynomial in the source frame variables X(s, row, a).

## 2. Argument

### (a) The supplier, end to end (the Lean says)
1. `sum_over_primes_service` (SOP:174-224) takes from `pdv` (SOP:128-138) a `KerEnt E` together with
   UnUnit, KmapRat, KFi, Stab0, EvenConditionsInert and the other clauses.
   - It builds `KForm` by `kform_of_ker E … (Or.inr ⟨rfl, hS0⟩)`, i.e. sp = 1 (SOP:207-209).
   - It builds `admitted` (SOP:210-212).
   - It applies `lift_bounds_of_essential hA (orbit_entry_bounds_hold … h01 …)` (SOP:213-214).
2. `lift_bounds_of_kernelForm` (OP:1326-1338) proceeds in four steps.
   - **Entries**: `entI_of` turns per-orbit OrbGe bounds into EntriesAtInert. This uses OrbitsAddLowerBound and the
     Gaussian class EvenConditionsInert.
   - **One lift**: `liftI_of` uses KForm, then `sumI` (OP:1278).
   - **Chain**: `noOp_of` composes the lifts with `compose` (OP:806-812). `compose` is `chain_ge` on D.fm for μ0, or on
     T.fm after `base_map_mem_local_lattice` for twisted μ.
3. `pdv` is supplied by `at_of_true_columns` (SP/AtOfTrueColumns.lean:30-50) with E = t.ent.
   - `IsEntC t` (`GaloisGeometry/IsEntC.lean:36-37`) says t.ent = kerEntC P t.O B h for some h : KerEntHyp.
   - `kerEntHyp_true` (IW/KernelEntryHypOfTrueColumnChoices.lean:19-22) supplies h from four theorems: val, latS,
     latT and kform.

### (b) THE ITERATION and the lattices
- **`kform_of_ker`** (OP:1621-1656) states exactly: for a KerEnt E with SB, UnUnit, KmapRat, KFi and SupSpansPsiPart sp,
  KForm holds. That is, an entry bound B at level i gives KGeTw(i, B − v_p(n)), with n = 1 if i = 0 ∧ sp = 1 and
  n = DGam otherwise. The μ0 case follows from the twisted one (`kernelValuation_of_twisted`).
- **Proof (`kgeTw_of`)**:
  1. Take x ∈ lat i. Then `lat_S` (⇒) gives, for each class c, a rational vector v_c with emb x(c) = ev v_c and
     |⟨prS v_c, ∇_J⟩| ≤ 1 for all J.
  2. `KmapRat` gives v′_{c,c′} with ev v′ = Kmap_{c,c′}(ev v_c).
  3. The structure field `kform` gives prT(v′) = un·prS(v)(applyAt0(Th, Gxz I)).
  4. SB (KvalGe ⇒ the jet polynomial is Σ_J c_J ∇_J with |c_J| ≤ p^{−B}; supplied by `cutKW_holds`,
     "coefficient norm ⇔ span norm given a complement") and ultrametricity give |prT(v′)| ≤ p^{−B}.
  5. Choose a with v_w(a) = ⌈e·B⌉, and absorb the class weights 1/|Stab c| = p^{−k}·(unit) with k = v_p(n).
  6. `latT` (⇐) puts ψ = Σ_c (r_c/a)·v′ in the localised level-(i+1) lattice.
  7. Conclusion: K_i x = (a/p^k)·ψ.
- **Which lattices.** Both sides are `(Tw.fm u μ).lat i` localised at w (`locW`), i.e. the same objects that `ColGe`
  and `KGe` use. The bases in which the entries are taken are the adapted bases `B u μ w i c τ` (`BasOk`: `BasR` of
  the class lattice (O u μ).lat i c, KEH:24-34). The adapted entry kernel is `thAtW` (KEH:36-41): the global theta
  kernel transported by B_{i+1}·(·)·B_i^{−1}, times the unit `dgen`.
- **Where equality of lattices is proved.** `KerEntHyp.latS`/`latT` (KEH:166-176) are proved by `kerEntHyp_latS`. That
  proof uses three leaves, not opened:
  - `hermitianChart_complex_rational_integral_forms`: x ∈ locW lattice ⇔ for every class c and every local basis Bm,
    the component is integral;
  - `dualLattice_localBasis_iff_unimodularCompanion`;
  - `formsLattice_atClass_iff_twistedPolynomial`: integrality in Bm ⇔ integrality of the ∇-pairings in the adapted
    basis.
  So the index charged between the two descriptions is **zero**. They are proved equal, not compared up to an index.
- **The composite.** `chain_ge` gives Σ_{j∈Icc 1 m} s_j. The proof has three properties:
  - the hypothesis after n steps is "a·z with z ∈ locW(lat n) and v(a) ≥ e·Σ"; nothing else about z is used;
  - the next step's KG holds for every element of the global lattice, extended to the localisation by `KG.loc`;
  - Int_j is literally `(M.lat j).L` at every level.

### (c) The local theorem
- `split_bound_eleven_one` (`JetPolynomialLogs/LocalBoundElevenComparison.lean:64-68`) is
  `SplitConstantsUniformBound 11 1`: ∀ Loc with AdmB, ThmA 1 ∧ Cor2 11 1; and ∀ Loc1 with AdmB, ThmOne 1.
- **ThmA** (PZF:265-270): KvalGe at the level Σ_{s∈TT}(topTerm_s − γ_p·Wc_s) + FD − d·N₀N₁(log_p a + 1). The
  ingredients:
  - topTerm (PZF:241-247) = Σ_{e odd, e < dTop}(A_s/p^e − cap(s+e))₊ + Σ_{e odd, e > dTop} A_s/p^e, with
    A_s = row 0 at the top = number of minors.
  - cap(z) (PZF:233) is row 1 at a top and row 0 elsewhere.
  - FD (PZF:255) = lpF(Dl) is the Gaussian-free base flow, with Dl = size − A at tops and size elsewhere.
  - Wc(s) (PZF:239) = sup over odd i with p^i ≤ size(s−i) of cap(s−i).
  - HidaSetting: p ≤ a, size ≤ a, 2·log_p a + 2 ≤ N₀ − 1.
- **Cor** (PZF:272-281): the same bound with Σ baseTerm (gap row0 − row1 in place of A; PZF:249-253) and lpF((k−1)w).
  It costs C6Σw/p and is derived from ThmA via `base_term_le_top_term` and `local_bound_eleven_comparison`
  (LocalBoundElevenComparison.lean:36-61).
- **Proof of ThmA** (`thmA_of`, DPW:177-211) has three steps.
  1. `TieB`: B1–B4 ⇒ BHyp (an unramified field and a root of unity ζ of order p^d − 1).
  2. `KernelFromExponentialTwist`: Θ(ep·X) = U(g(X))·exp(ε·Σ be), with g the inverse of the entry logarithm. This is
     the Dwork/log-coordinate form.
  3. `TieFrame` (frameJet bound ⇒ KvalGe), then `thmAGauss`.
- `thmAGauss` = `thmAGauss_of` (GJ/GaussJetProofs/ThmAGaussOf.lean:13-56) works as follows.
  - Pass to a residually generic extension with a generic frame Y.
  - Apply `theorem_A_generic` (GJ/GaussJetProofs/Generic.lean:133-226). This chooses a Frobenius-twisted frame
    genFrame = Y^{l^m} on top rows and checks, by `generic_minor_norm`, that the partner-minor determinants are units.
  - `theorem_A_frame` → `thmAGen` (`ConstantCoeffAevalLinP.lean:409`) → `thmAOp` (ThmAOp.lean:312-) bound jetPair
    term by term.
    - Every monomial κ of ∏ minors has top-row degree ν₁ at tops, Dl in the other rows, and degree ≤ capL(s0+j) in the
      rows coupled to top s0 at odd distance j (`op_prod_shape`, `hcap`).
    - `thmAJetA` (statement `GJ/StatementG.lean:33-64`; body in `GJ/MonoShapeTop.lean`, **not read**) bounds
      κ!·coeff_κ of U(g)·exp(ε·bSum) by the ThmA exponent for every such κ.
- **Same mathematics or different?**
  - It has the same architecture as the Hecke route's `kernel_a_two_generic` (`ThetaLogCoordinates/…/EGaussK.lean:216`):
    Gaussian class, generic frame, products of minors, capped partner rows, the cap being the number of minors (NUMTEST4).
  - It is a separate code base (GaussJetBounds vs ThetaLogCoordinates/InvariantFactorPaths.G7), specialised to no
    Hecke operator.
  - The gain formula differs in form. Here: topTerm/baseTerm with dTop and a −γ_p·Wc loss. There: gainG/excessGain
    with dSet.
- **Cap bookkeeping at signal places.**
  - dTop = ∞, because odd partners are `true` places. So baseTerm(s) = Σ_{e odd}(gap_s/p^e − row0(s+e))₊.
  - Shape gives gap ≥ al and row0 = Ent.cap ≤ fillG(j, ·) + cG (OP:270-272).
  - Hence baseTerm ≥ Σ_{e odd}(al/p^e − capU)₊. This is NODE-PAIRING's ask_s = Σ_{e odd}(a/p^e − W_{s,e})₊ with
    a → a − 2cG and W → W + cG.
  - It matches NUMTEST4 (per-position caps, cost = number of minors) and signal_twotops (two tops at even positions
    add).

### (d) Orbit identity and orbit sum
- **`orbitIdentity_all_of_integralClass_hostLog_alt`** (SP/OrbitIdentityAllOfIntegralClassHostLogStatement.lean:12):
  CurveData + OrbOK + BeData + IsReps R + HypPair(f, f′) + HostLog Θ, and Th(ep·X) = Θ∘hypZ(f, f′), together imply
  **ThetaExpansionAllPlaces** with sg = −1 and be = beOf(cob F(phFF)). That is,
  subst(ep·logPl)Th = U·subst(logPl) exp(Σ_r −Σ_{a,b} be(X_{orb r,·,a,b})) with U integral (OP:186-190).
  - The "orbit identity" says the theta kernel in position coordinates is, up to an integral unit series, the
    exponential of the polarisation series be summed over orbits.
  - Proof (body 113-236, outline read): merge R × rows into one block of M = |R|·N rows, then apply `Th1.D.b0`. This is
    the GAUSSCLASS links 3–6 machinery (polarisation, trace duality, Dwork). The log is inverted by
    `generalized_log_inverse`.
- **`orbit_entry_bounds_hold`** (`Divisibility/ChainOperators/OrbitEntryBounds.lean:49-53`) gives `Core`. Its pieces:
  - `OrbitsAddLowerBound` ← `orbAddUp_main`
    (`PeriodIntegrals/UnitaryGroupMassFormula/OrbitJetDegreeBound/ConstantCoeffZeroOfBoundGeneral.lean:90-157`, read):
    1. Truncate U to the degree that the minors see.
    2. Write Th′ = Σ_m U_m·∏_{r∈R} Fk_r(resM r m). Each factor satisfies an orbit theta expansion with a monomial
       (integral) U.
    3. So each satisfies OrbGe(β_r). `kval_prod` multiplies over disjoint orbit variables, and ultrametricity gives
       Σ_r β_r.
    - **Loss: none.** dG is not involved. "Restricts from the full kernel" is `OrbitRestriction` (OrbRestr), which
      is used at the conjugate/one-letter places.
  - `OrbitValuationBound` ← `PI.OrbBoundF` ← Cor (via `prvF_of_orbitLetterBounds`, read by SIGNAL) gives
    β = g0Pl + FOrb − errF.
  - The rest of Core concerns the ramified, conjugate and split classes.
- **Orbits** are z-orbits on positions Pl = Bool × HH: z ↦ posPl z 1 = Frob·c (`isReps_repsPl`, OP:835-911). At
  signal places the reps are (false, t0) with t0 ∈ reps for step 2h.

### (e) Uniformity and non-vacuity
1. **Rank and orbit-length dependent errors**, with universal constants (Cd = 1, C6 = 11):
   - d·N₀N₁·(log_p a + 1) per orbit;
   - errF (OP:239-244): γ_p·topsOrb·(b + η + 1 + 3Sc) [the Wc loss], c6·Σw/p, nP·N_{j−1}N_j·(log_p(4·nP·Nm·a) + 1),
     and dl1·nP·Nm²·log, dl2·tops·log².
   These are absorbed through `OrbitSumBound` into EatI ⊂ ES ⊂ lowS. They are N²·log a ≪ a/p only because
   a ≈ e^{x^ε}.
2. **HidaSetting needs rank ≥ 2·log_p a + 3** (`Shape.rankA`: 2·log₅(a²) + 2 ≤ k − 1). This is satisfiable and, with
   a ≈ e^{x^ε}, forces k ≳ x^ε. It is not vacuous, but it is a structural requirement.
3. **Degenerate KerEnt constructors exist in the tree:**
   - `ExtraEnt.lean:26`, with `IsEmpty (cls (j+1))`;
   - `EntPlNonempty.lean:15`, with Subsingleton lattices.
   They are **not** on this path: `IsEntC` pins t.ent = kerEntC.
4. `at_of_true_columns` takes "∀ Ee : Ent, Shape Ee ∧ …". This is harmless: Shape reads only ν, and ν is pinned by
   `nu_row`.
5. a = 0 or empty orbit sets: g0⁺ ≥ 0 and the Σ over reps is empty only if there are no tops. This is not used to make
   anything vacuous.

## 3. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `thmAJetA` | GJ/StatementG.lean:33; body GJ/MonoShapeTop.lean | per-monomial bound κ!·coeff of U(g)·exp(ε·bSum) ≥ ThmA exponent under shape, cap and genericity | heart of the local theorem | core, **not read** |
| 2 | `kerEntHyp_latS` leaves: `hermitianChart_complex_rational_integral_forms`, `formsLattice_atClass_iff_twistedPolynomial`, `dualLattice_localBasis_iff_unimodularCompanion`; target `kernelDatum_lattice_target_side_trueChains` | IW/TrueChainsKernelDatumSourceSideLattice.lean:36 | adapted-basis ∇-integrality ⇔ membership in (T.fm).lat i at w | entry lattice = chain lattice | core, outline read |
| 3 | `orbitIdentity_all_of_integralClass_hostLog` (`Th1.D.b0`) | SP/OrbitIdentityAllOfIntegralClassHostLog.lean:113 | ThetaExpansionAllPlaces for the hyperbolic-substituted kernel | Gaussian class at signal places | core, outline read (shared with GAUSSCLASS) |
| 4 | `cutKW_holds` / `coeffNormLE_iff_spanNormLE_of_hasCompl` | Divisibility/ChainOperators/GenericFramesLetters.lean:8 | monomial-coefficient bound ⇔ ∇-span coefficient bound | SB in kform_of_ker | core (standard-monomial saturation over ℤ), not read |
| 5 | `kernelEntries_form_true_chains` (KerEntHyp.kform) | IW/KernelEntryHypOfTrueColumnChoices.lean:22 | target pairing = unit · source pairing of the jet of thAtW | the pairing identity | core, not read |
| 6 | `kmapRat_kerEntC'`, `stab0_rec7_of_levelData` | SP/AtOfTrueColumns.lean:42-45 | Kmap preserves rational forms; trivial level-0 stabilisers | glue for kgeTw_of | standard/glue |
| 7 | `orbAddUp_main` | ConstantCoeffZeroOfBoundGeneral.lean:90 | orbits add | read | glue |
| 8 | `chain_ge`, `kgeTw_of`, `compose`, `noOp_of` | OP:779, 1464, 806, 919 | iteration and transfer | read | glue (honest) |

Ranked: 1 > 2 > 3 > 4 > 5.

## 4. Oddities
1. **The γ_p·Wc loss.** ThmA subtracts γ_p·Wc_s per top. Wc is the largest cap at a position s−i with p^i ≤ its size;
   at signal places that is the thick weight ≈ b. errF charges it per top, per lift and per signal prime p ≤ X″,
   giving ≈ |TT|·m·b·Σ_p γ_p ≈ |TT|·m·b·log log X″ in total. It enters through EatI ⊂ ES on the slope side. I did not
   check that Eval/ES absorbs it within the budget unit U ∝ |TT|·m·b·δ. **Worth a ten-minute check in the LOSS/Eval
   node.**
2. topTerm drops the cap for e > dTop. This is irrelevant at signal places (dTop = ∞).
3. Two independent Lean libraries prove the same local law (GaussJetBounds for this route, ThetaLogCoordinates/G7 for
   the Hecke route). Numerical evidence (NUMTEST3/4, signal_twotops) bears on the law, not on either code base.
4. The lattice tie is carried as **fields** of `KerEnt` (`lat_S`, `levelFree_lattice_condition`, `kform`). Their
   content lives in KerEntHyp's suppliers (child 2, child 5), not in OrbitPlaces.

Nothing false-looking.

## 5. Coverage
Read:
- OP:1-500, 575-935, 1320-1666;
- DKI (all) and KEH (all);
- SOP:100-224 and `AtOfTrueColumns.lean` (all);
- `KernelEntryHypOfTrueColumnChoices.lean` (all), `TrueChainsKernelDatumSourceSideLattice{,Statement}.lean` (all) and
  `IsEntC.lean:36-42`;
- WJS:15-80 and DataLatDefs:80-100;
- PZF:1-413 and `LocalBoundElevenComparison.lean` (all);
- DPW:1-300;
- GJ: `ThmAGauss.lean`, `StatementP.lean`, `ThmAGaussOf.lean` (all), `Generic.lean` (all),
  `StatementM.lean:20-58`, `StatementJ.lean:25-60`, `StatementG.lean:33-64`, `ConstantCoeffAevalLinP.lean:405-470`
  and `ThmAOp.lean:312-372`;
- `OrbitEntryBounds.lean` (all), `OrbAddUp.lean` and `ConstantCoeffZeroOfBoundGeneral.lean:66-157`;
- `OrbitIdentityAllOfIntegralClassHostLog{Statement,}.lean`: statement, and 113-173 of the body;
- `EaGeCOfNorm.lean:150-230`, `FirstTheoremPlaceBound.lean`, `EGaussK.lean:199-240` and `GenericFramesLetters.lean`
  (all).

Not opened:
- `MonoShapeTop.lean` (`thmAJetA` body) and `FrameA.lean`;
- the three latS leaves, latT and kform suppliers;
- `PrvFOfOrbitLetterBounds` (read by SIGNAL), `OrbRestr`, `cutKW` and `Th1.D.b0`.
