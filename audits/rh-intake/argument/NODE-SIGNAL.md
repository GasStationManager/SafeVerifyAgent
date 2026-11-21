# NODE-SIGNAL: the gain at signal primes (and at the other non-kernel-served gained primes)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `CEH` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean`
- `DH` = `Formalism/LocalRingCardinality/DataHost.lean`; `DF` = `Formalism/LocalRingCardinality/DataForced.lean`
- `IRZg` = `Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean` (the `Loc` namespace: partner, g0, gainP, VV, tauP)
- `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- `OP` = `Formalism/SharpRestriction/Divisibility/OrbitPlaces.lean`
- `PZF` = `Formalism/SharpRestriction/Divisibility/ProductZerothFirstParts.lean`
- `SRB` = `Formalism/SharpRestriction/GrowthBounds/AdmissibleIntegers/StatementsOfRemainingBound.lean`
- `SOP` = `Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- `NSC` = `Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/NotSingularOfCentral.lean`

## 0. Verdict (short)

1. **What a signal prime is.** It is a prime with (−d/p) = −1 and (−q/p) = +1. So it is inert in K = ℚ(√−d), split in
   ℚ(√−q), and inert in ℚ(√dq). In the Lean's multiplicative coordinates on Gal(E/ℚ) = {±1}² × A, the first sign acts
   on √−q and the second on √−d. So Frob = ((+1,−1), h) and c = ((−1,−1), 1).
   - c is never a power of Frob, because the first sign of every power of Frob is +1. So w ≠ w̄ and the hermitian space is
     split at every signal prime.
   - **The local geometry is the same as at an even-order inertClass (GIdx) place.** The orbit generator is
     z = Frob·c = ((−1,+1), h). It lies in the CM type Psi = Gal(E/K). The positions are the z-orbit, and consecutive
     positions lie at w and w̄ alternately. So the two descriptions in the brief ("even/odd positions" and "two
     Lagrangians E_w ⊕ E_w̄") are the same picture.
   - The only difference is the labelling. At a signal place z flips √−q, so odd positions are `true`-labelled places.
     Those are thick or thin places, never tops.
2. **The supplier is a different route from the one audited so far.** `OrbitsWithoutOperator` = `NoOperatorOrbitBound`
   (OP:423-429) is proved inside `OrbitPlaces.Conclusion₂` (`noOp_of`, OP:919-932). That route does not use `GIdx`,
   `LatInst`, local chain models, `SiteAdm`, `FormalGroupSystem.admitted`, Hecke operators or colength. It works on the
   **global** theta kernel entries `KerEnt.Th u μ w i` at every place w. The steps are:
   - **Gaussian class** (`EvenConditionsInert`): from `hostAt_inert` + `hyp_of_stdBases` + `orbitIdentity_all…`. The
     hypothesis is stated uniformly for "inertClass ∨ signal".
   - **Hecke-free local theorem**: `PZF.Loc.Cor` / `ThmA`, supplied as `split_bound_eleven_one`, applied per z-orbit.
   - **Sum over orbits** (`OrbitsAddLowerBound`).
   - **Entry → column transfer**: `kform_of_ker`, then composition over the m lifts (`ValuationComposition`).
3. **The gain is exactly Σ_j Σ_{reps} g0⁺, and the count side charges nothing extra.**
   - At signal places VV = ∅. So τ = 0, io = 0, there is no colength, and TTP = TT.
   - Excl is empty (`not_excl_of_sg`, NSC:569), because odd partners are never tops.
   - So g0 is the ASK summand with a → a − 2cG and cap → fillG + cG, minus dl.
   - `gain_bound_at_of_star`'s signal branch (NSC:640-668) proves Σ_j Σ_TT(askG − lo) − m·fl ≤ Σ_j gainP.
4. **NUMTEST3 was a signal place.** Its instance has Frob_p = c·g with g the √−q flip, which is exactly ((+1,−1), 0).
   NUMTEST4's "correction" is wrong on this point: zPsi = ((1,1),h) is the GIdx generator, but `posPl` (DF:19-21) also
   covers signal. NUMTEST3 therefore confirmed the Hecke-free signal-place law in its smallest case: h = 0, n′ = 2, one
   entry, one top and one cap.
   - I ran a small new check (§E): an n′ = 4 orbit with **two tops at even positions**, which is the signal-specific
     configuration. It holds to within −1.13.
5. **Structural point the earlier nodes missed.** partner(t,e) = (IsSg ∧ e odd, t+e·h) (IRZg:77). So **only signal primes
   reach the thick places**. The x-scale part of ASK, which carries ψ and Gm (NODE-CHBALANCE §2a), therefore sits
   entirely on signal primes. Its divisibility is delivered by the OrbitPlaces route, not by the GIdx/Hecke route that
   NODE-TWU/PAIRING/LOCALDIV/COLENGTH audited.
6. **Judgement.** The gain at signal primes is proved by a **different mechanism**: the Hecke-free orbit theorem on global
   entries. It reuses the same Gaussian-class leaves (IntInert, CM good models). I saw nothing false. The core leaves
   still unread are:
   - `split_bound_eleven_one` (local Cor/ThmA);
   - `orbitIdentity_all_of_integralClass_hostLog_alt`;
   - `orbit_entry_bounds_hold`;
   - the KerEnt/Adapted construction at signal places.

## 1. Statement

### 1.1 Signal primes (the Lean says)
- `primeClass` (DH:34-39) returns `signal` iff (−d/p) ≠ 1, p is not small, p ≠ q, p ≠ d, and `psAt p = 1`.
- `psAt p` = (art p).1.1 (CEH:68-69). Under `PsQ`, `psAt p = (−q/p)` (`PsQ.psAt_eq`, HostFacts.lean:197).
- `gal_sqq` (DH:46) has σ√−q = (gal σ).1.1·√−q, and `gal_sqd` (CEH:30) has σ√−d = (gal σ).1.2·√−d.
- `HostDer.frob` (CEH:204-213) gives Frob = (psAt p, (−d/p), h) with φ.hH h = class of p mod 2^{e+2}.
- **Signal**: Frob = ((+1,−1),h). **inertClass**: Frob = ((−1,−1),h) = c0·h.
- `HostDer.eta` (CEH:224-231) has η_F(𝔭) = −1 ⇔ cc ∈ ⟨Frob⟩. For signal this never holds, so every prime of F above p
  splits in E.

Decomposition and residue degree:
- D_p = ⟨Frob⟩ and f = ord Frob = lcm(2, ord h).
- The Lean's orbit length is `nP` = 2·ord(2h) for signal and ord h for inertClass (IRZg:88). This equals lcm(2, ord h) in
  both parities of ord h. It is always even and ≥ 2 at signal places.
- The places of E above p number 4|A|/nP, in conjugate pairs {w, w̄}.

### 1.2 Positions and the CM type at a signal place (the Lean says, with my gloss)
- `Pl D = Bool × HH D` (OP:17) indexes Psi = Gal(E/K) via `plGG`/`tauPl` (DF:11-17). The Bool is the √−q-sign
  coordinate: `false` = top/thin, `true` = thick/thin. `card_Pl` = f (OP:1138).
- `posPl D p z e = (z.1 xor (IsSg ∧ e odd), z.2 + e·h)` (DF:19-21).
- `plGG_posPl_one` / `exists_frob_step` (`SP/PrimeOfLiesOver.lean:72-78`) give plGG(posPl z 1) = plGG(z)·Frob·cc,
  under "IsResidueClassZero ∨ IsSg". So the step is z ↦ z·(Frob·c).
- `rhoH_posPl_one` (:92-99): τ_{s+1}(x) = τ_s(Frob(c x)). `samePrime_step` (:101-) says the prime of τ_{s+1} is the
  c-conjugate of the prime of τ_s.
- *Gloss.* Position s is the CM-type embedding τ₀·z^s.
  - Even s give embeddings in τ₀·D_p, i.e. place w. Odd s give embeddings at w̄.
  - The w-Lagrangian of the split hermitian space is spanned by the even-position coordinates. The w̄-Lagrangian is
    spanned by the odd-position coordinates, which are the CM-type coordinates at w̄ and *not* conjugate variables at w.
  - This is identical at signal and at even-order inertClass places. The difference is only that at signal places the
    odd positions are `true`-labelled.
- Tops are `(false, t)`, t ∈ TT (`IsTopPl`, IRZg:79). At a signal orbit from (false,t0), position s has Bool = (s odd). So
  **all tops sit at even positions, and every odd e-partner of a top is a `true` place** (thick if t+e·h ∈ T2+u0,
  thin otherwise).
  - This is the CHBALANCE partner cconj + e·Frob + topPl t = ((0,1), t+eh) = thickPl.
  - `Excl` (IRZg:139) needs partner(s,e) = (false, s′), so it is empty (`not_excl_of_sg`, NSC:569).
  - `Loc.dTop` (PZF:157) is ∞ for every top on a signal orbit.

### 1.3 The Gaussian-class statement at a signal place
**`ThetaExpansionAllPlaces`** (OP:186-190) says
subst(ep·logPl) Θ = U · subst(logPl)(exp(Σ_{r∈R} sg_r Σ_{a,b} be_r(X_{orbMap r s, a, b}))), with U integral.
- The be_r are series in the nP position variables of one orbit, satisfying B1–B4.
- It is supplied with sg = −1 by `exists_beFam_evenConditionsInert_of_kerEnt` (`SP/AdmissibleKernelSeriesInertPrimeNonConjugateFrob.lean:24-66`).
  That calls `normalisedFamily_standardBases_integrality` (`SP/NormalisedFamilyStandardBasesIntegrality.lean:19-30`)
  with the hypothesis **((RCZ ∧ hP ≠ 0) ∨ IsSg)**.

That proof composes three pieces:
- `HostAt` (`.../GaloisGeometry/ExistsConstantCoeffOne.lean:37-46`). It is supplied by `hostAt_inert`
  (`SP/JacobiOfClass.lean:63-83`) from `GenusOneModelExistsLattice`, `CurveDict` and `IntInert`. The only arithmetic
  input it uses is `jacobi_of_class`: p is inert in K. This is GAUSSCLASS link 1.
- `hyp_of_stdBases` (`SP/StandardBasesHyperbolicPairOrthonormal.lean:27-52`). It is the analogue of GAUSSCLASS link 2
  (FrameHyp): the kernel in position variables is Θ_orth∘hypZ(f, f′), with a unimodular hyperbolic pair over the
  σ²-fixed ring and nP/2 pairs per orbit. Its leaves are `frob_moves_coords` (`SP/FrobeniusLiftMovesLetterCoordinates.lean:29-75`,
  read) and `exists_kur_frob_tauEmb_posPl` (`SP/ExistsKurFrobTauEmbPosPl.lean:76-111`, read). Both are uniform in
  "RCZ ∨ IsSg".
- `orbitIdentity_all_of_integralClass_hostLog_alt`, the analogue of links 3–6 (polarisation, RestBeta/RestGc, Dwork).
  I did not read it.

**Answer to the brief's question.** The Gaussian couples each position only with its neighbours, s ↔ s+1, and
neighbours lie at different places w and w̄. So every Gaussian term is a w–w̄ cross term: in the w-variables alone (odd
positions set to 0) the kernel is Gaussian-free. This is NUMTEST3's w = 0 law and GAUSSCLASS's "never s ↔ s". It is the
same as at GIdx places.

**Caps** (the Lean says). In the count, the cap for top s at odd e is capU = fillG(j, (true, s+e·h)) + cG (IRZg:132-135).
Here fill(true, ·) = oj(·), the level-j weight at the thick or thin place, with no b-term (IRZg:81-82). On the entry side
the cap is `Ent.cap` = row 0 of the Young diagram at that non-top position (OP:58), with `Shape.capG` E.cap ≤ fillG + cG
(OP:272).

### 1.4 `OrbitsWithoutOperator` (WJS:194-200) = `NoOperatorOrbitBound` (OP:423-429; `noOperatorOrbit_iff`, OP:454-455, rfl)
```lean
L.FDef → ErrDefs D L Xe lev K ce → ∀ u w, resChar w ≠ (D.mem u).A.T →
  ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ¬ Exc D p → (p : ℝ) ≤ X'' →
  ∀ μ, DV.Used D μ → p ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
    ColGe T u μ w x ((∑ j ∈ lifts, g0S X K p j) + lowS L Xe K ce sp u w)
```
- g0S = 0 if IsCs, and Σ_{t0∈reps} max(g0,0) otherwise (WJS:51-52).
- lowS = Σ_j (F_j − ES_j) + sp·vDG (WJS:73-74).
- In plain terms: at every signal place, and at every inertClass place with h ≠ 0, with p ≤ X″, every vector of the
  ramified lattice S₀(w) has its m-step chain image divisible by ϖ to the order Σ_j Σ_{orbits} g0⁺ + low.

## 2. Argument

### (b) The supplier on the live path (the Lean says)
1. `sum_over_primes_service` (SOP:174-224) builds `WJS.admitted`. Its fourth component `n` is
   `J.four_orbit_conditions_of_proof` (`AdmissibleParameterJoins/GandSab.lean:11-17`), a projection of
   `OrbitPlaces.Conclusion₂`. That comes from `lift_bounds_of_essential hA (orbit_entry_bounds_hold …)` (SOP:215-216).
2. `hA : OrbitPlaces.admitted` = KForm ∧ AdmK (OP:475-481). The components are:
   - `kform_of_ker` (OP:1621-1656);
   - `orbit_admissible_of_split_bound`, which gives OrbOK: p ≥ 5, nP even, nP ≥ 2;
   - `split_bound_eleven_one` = `OrbitLetterBoundsAll 11 1`, the local theorem;
   - the AdmK components from the `pdv` hypothesis. On the live path pdv is `at_of_true_columns`
     (`SP/AtOfTrueColumns.lean:32-50`): EvenConditionsInert from §1.3, OrbitBoundWithoutOperator from `orbit_bound_rec`,
     JetIntegralityBis, ShapeAtD and Shape.
3. `lift_bounds_of_kernelForm` (OP:1326-1338) then derives the result in four steps:
   - **EntriesAtInert** (`entI_of`, OP:1090-1127). For each orbit rep r ∈ repsPl:
     - kindA reps (inertClass, Bool false) get β = g0⁺ from `OrbitBoundWithoutOperator`;
     - kindBC reps, which at a signal place are *all* reps (kindA needs ¬IsSg, DataErr.lean:127), get
       β = g0Pl + FOrb − errF from `OrbitValuationBound`;
     - `OrbitsAddLowerBound` adds them over orbits, given ThetaExpansionAllPlaces.
   - **`OrbitValuationBound`** ← `prvF_of_orbitLetterBounds` (`PeriodIntegrals/UnitaryGroupMassFormula/OrbitValuationBounds/PrvFOfOrbitLetterBounds.lean:20-59`,
     read). It applies `PZF.Loc.Cor` (PZF:214-224) to `orbLoc` (OP:145-152). Cor is the Hecke-free bound
     KvalGe(Σ_{TT} baseTerm + lpF((k−1)w) − C6Σw/p − γ_pΣWc − C·d·N0N1(log_p a + 1)), with
     baseTerm(s) = Σ_{e odd, e≠dTop}((ν_{s,0} − ν_{s,1})/p^e − cap(s+e))₊ (PZF:173-178). It then compares
     g0Pl + FOrb − errF ≤ that (`orbit_place_term_le_sum`, `sum_Wc_le`, `loss_le`; not opened).
   - **OneLiftInertBound** (`liftI_of`, OP:970-1015): KForm turns the entry bound into KGe for the chain map K_i, and
     `OrbitSumBound` (`sumI`) matches Σ g0⁺ + FInert − EatI ≤ Σ betaI.
   - **NoOperatorOrbitBound** (`noOp_of`, OP:919-932): `ValuationComposition` (`compose`) composes the m lifts on S₀(w).
4. **The tie to the global chain** is `kform_of_ker`/`kgeTw_of` (OP:1464-1656). It uses `E.lat_S`: the local lattice
   at w is characterised by the entries. It also uses `KmapRat`, `UnUnit`, `KFi`, `Stab0` and SB. The divisor
   n = DGam (or 1 at i = 0) gives the −vDG.
   - The quantifier is "all w with LevelFree" (resChar ≠ T, ∉ {g0,g1}, ∉ Qp μ). There is no class restriction.
   - `AdaptedTh` (`KernelLattices/AdaptedEnt.lean:66-73`) is required at `AdPl` places = inertClass ∨ **signal** ∨ ramD
     (:23-25).
5. **So the analogue of "Qp μ0 = ∅, modelled at every GIdx place" is this.** On this route nothing is modelled locally.
   The objects at a signal place are the global kernel entries of the global chain D.chTw at w, in adapted bases, and
   the quantifier ranges are LevelFree w (OP:64-66). Signal places are covered because `AdPl` and the (RCZ ∨ IsSg)
   lemmas include them explicitly.

**How the gain enters.** `baseBranch` of Conclusion1 (`baseChange_preserves_unitary_of`, SRB:163-192) splits on
`InNP` (WJS:61-63):
- **GIdx ∧ cmp x ∈ NP**: `kernel_valuation_served` (the UAt/Hecke route).
- **VV = ∅ ∧ x ∈ Sram**: gainS = gainP = Σ_{reps} g0⁺ (since VV = ∅), and the bound is exactly `OrbitsWithoutOperator`
  (SRB:185-192). Signal places, which are never GIdx, use only this branch.

### (c) Per-prime comparison at a signal prime
- At a signal prime VV = ∅, because `Cand` needs IsResidueClassZero (IRZg:194-196, 201-202).
- So `tauP` = 0 and `ioP` = 0 (IRZg:210-220), and `TTP` = TT (IRZg:232-234).
- gainP = Σ_{t0∈reps} max(g0, 0) for p ≤ X″ (IRZg:224-228).
- g0(t0) = Σ_{s∈topsOn t0} Σ_{e odd} (al_s/p^e − capU_{s,e})₊ − dl (IRZg:158-161), since Excl = ∅.
- The count summand is askP(s) = Σ_{e odd}(a_s/p^e − fill(true, s+eh))₊ (IRZg:243-244).

Term by term:
- al = a − 2cG and capU = fill − kaJ + cG ≥ fill, so g0 ≤ askG.
- The other way, each active (s,e) loses at most 2cG/p^e + cG. There are ≤ log_p 2a active e per top, and dl is extra.
- The Lean proves the lower direction: `gain_bound_at_of_star`, signal branch (NSC:640-668, via `noop` NSC:436 and
  `not_excl_of_sg`), gives Σ_j Σ_{s∈TT}(askG − lo) − m·fl ≤ Σ_j gainP − 0.

So the per-prime net is ASK − |TT|·m·lo − m·fl, the same `lo` as at kernel-served primes. Nothing else is charged:
- there is no τ, colength or io;
- **dG** enters only through lowS (sp·vDG, and ES = vDG + EatI), exactly as at every other place;
- the slope side's F_j = FInert at signal places is matched by FOrb (`OrbitSumBound`).

**Remark on sizes.** At signal primes the thick caps are ≈ b, so they are reached only for p < a/b ≈ x. That is the
x-scale ψ-part of ASK. The thin caps w″ ≤ b′/x make the ask nonzero up to p ≈ X′·x, which is the a·log(X″/X′) mass.

### (d) The other two gained-but-not-kernel-served sets
- **Even-order inertClass primes in [X′(1+Crρ), X″].** These are GIdx places (NODE-SERVED §1.1) with VV = ∅, because
  Cand needs p < X′. Two branches are available:
  - x with cmp x ∈ NP goes through `kernel_valuation_served`/UAt with VVs = ∅, which is the audited GIdx route
    (NODE-TWU: stmt_proved ⇒ LowTermBound, reps∖VVs term).
  - x ∈ Sram goes through `OrbitsWithoutOperator`. Here the Bool-false (kindA) orbits are supplied by
    `OrbitBoundWithoutOperator` ← `orbit_bound_rec` (`SP/OrbitBoundStandardSeriesInertPlaces.lean:22-42`), whose
    children are `standardOrbitSeries_valuationBound_zero`, `kvalGe_orbitGainWithoutOperator` and
    `wordFreeNumber_le_orbitBound`. These are local Hecke-free statements on orbLoc with Excl. I did not open them.
    The Bool-true orbits carry no tops and get FOrb − errF from Cor.
  - Per-prime matching is the `hfull` branch of NSC:640-668, with `excl_small_of_ge` (NSC:561) bounding Excl for p ≥ X′.
- **Bad orbits at kernel-served primes** (t0 ∈ reps∖goodReps, VV ≠ ∅). These go through the GIdx/UAt route. The third
  sum in `UAt` (WJS:206-215) is Σ_{reps∖VVs} g0⁺, delivered by LowTermBound from the local chain models, i.e. the audited
  mechanism (NODE-TWU §5, NODE-PAIRING §1). `OrbitsWithoutOperator` is not used for these, since InNP's first disjunct
  applies.

## 3. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `split_bound_eleven_one` (= `ExportAllConjugates 11 1`: Loc.AdmB ⇒ ThmA ∧ Cor; Loc1 ⇒ ThmOne) | `Divisibility/JetPolynomialLogs/LocalBoundElevenComparison.lean:64`; PZF:208-224, 284 | Hecke-free orbit bound: KvalGe(Σ_TT baseTerm + base F − errors) for any Gaussian-class orbit kernel | **the local theorem at signal places** | core, body not read |
| 2 | `orbit_entry_bounds_hold` (Core: OrbitsAddLowerBound, OrbitRestriction, OrbitValuationBound, …) | used at SOP:216 | orbit bounds add over orbits and restrict from the full kernel | assembles places | core, not read |
| 3 | `orbitIdentity_all_of_integralClass_hostLog_alt` | used at `SP/NormalisedFamilyStandardBasesIntegrality.lean:29` | HostLog integrality + hyperbolic substitution ⇒ ThetaExpansionAllPlaces (links 3–6 analogue) | Gaussian class at signal places | core, not read |
| 4 | `hostAt_inert` ← GenusOneModelExistsLattice, CurveDict, IntInert | `SP/JacobiOfClass.lean:63` | one-variable integrality at every p ≥ 5 inert in K | Gaussian input; shared with GAUSSCLASS link 1 | core (shared) |
| 5 | `hyp_of_stdBases`, `frob_moves_coords`, `exists_kur_frob_tauEmb_posPl`, `plGG_posPl_one` | `SP/StandardBasesHyperbolicPairOrthonormal.lean:27`; `SP/FrobeniusLiftMovesLetterCoordinates.lean:29`; `SP/ExistsKurFrobTauEmbPosPl.lean:76`; `SP/PrimeOfLiesOver.lean:72-99` | position s+1 = Frob∘c of position s; adapted bases give a hyperbolic pair | FrameHyp at signal places | core, read (leaves `hyperbolicCoordinates_*` not read) |
| 6 | `kform_of_ker`, `kgeTw_of`, `KerEnt.lat_S` | OP:1464, 1621 | entry valuation ⇒ chain-map divisibility at w (−vDG) | global tie | core, partly read |
| 7 | `at_of_true_columns` (pdv supplier), `KerEntTied.Adapted` at AdPl ∋ signal | `SP/AtOfTrueColumns.lean:32`; `KernelLattices/AdaptedEnt.lean:23, 94` | the actual entries, sg = −1, adapted bases at signal places | supplies E | definition to unfold |
| 8 | `prvF_of_orbitLetterBounds` | `…/OrbitValuationBounds/PrvFOfOrbitLetterBounds.lean:20` | Cor on orbLoc ⇒ OrbGe(g0Pl + FOrb − errF) | per-orbit numbers | glue (children `admissible_of_jet_bounds`, `setting_sq`, `loss_le` not read) |
| 9 | `gain_bound_at_of_star` (signal branch), `noop`, `not_excl_of_sg` | NSC:619, 436, 569 | ASK − lo ≤ gain at signal primes | count matching | glue, read |
| 10 | `orbit_bound_rec` | `SP/OrbitBoundStandardSeriesInertPlaces.lean:22` | kindA orbits at inertClass VV = ∅ places get g0⁺ | (d) first set | core, children not read |

Ranked by risk: 1 > 3 > 2 > 7 > 6 > 10 > the rest.

## 4. Oddities

1. **NUMTEST4's "correction to NUMTEST3" is mistaken.** zPsi = ((1,1),h) is the generator only for the GIdx
   (inertClass) machinery (SPM). `posPl` (DF:19-21) gives z = ((−1,+1),h) at signal places, and that z does move √−q.
   NUMTEST3's instance (Frob = c·g, g the √−q flip, h = 0) is a signal place, so its numbers are signal-place evidence.
2. **The ψ-carrying x-scale count lives only on signal primes** (partner, IRZg:77). Yet all of the Hecke/colength/τ
   machinery audited so far (TWU, PAIRING, LOCALDIV, COLENGTH, GAUSSCLASS link 2 via FrameHyp at GIdx) is irrelevant to
   it. The live support of the signal gain is the OrbitPlaces route of §2(b). This is not a defect, but the audit's risk
   map should move: Children 1–3 and 7 now carry the Landau signal.
3. At GIdx places with VV = ∅ there are **two** routes (UAt with VVs = ∅, and OrbitsWithoutOperator); InNP is a
   disjunction. This is harmless.
4. `OrbitsWithoutOperator` is a divisibility of the chain on **all** of S₀(w), with no colength cost. This is the
   Hecke-free statement REVIEW-TWU found on the GIdx path too. It must hold for the genuine global chain. There is no
   vacuity, since `kform_of_ker` ties it to the actual entries.
5. `entStd` (Th = ep = be = sg = 0; NODE-TWU) is used only for `Shape` on the twisted path. It is not the Ent here. On
   the live pdv path, E = t.ent, sg = −1, and ep, be come from `hostAt_inert`.
6. At signal places Excl = ∅ and dTop = ∞: every top is "V-type" (even position). That makes the count comparison simpler
   than at inertClass places.

Nothing false-looking.

## 5. (e) NUMTEST3 and a correct signal-place test

**Decision: yes.** NUMTEST3's "served" configuration is E = ℚ(i, √−13) with Frob_p = c·g, where g fixes i and flips
√−13. That is Frob = ((+1,−1), 0): signal, h = 0, nP = 2. Position 0 = (false,0) is the top, at w. Position 1 = (true,0)
is the thick/thin partner, at w̄. Its "anisotropic" control (Frob = c) is inertClass with h = 0, which is dropped and
correctly has gain 0.

**What it confirms** for one matrix entry, rank 1, and d ∈ {1,3} outside HostHyp:
- the Gaussian-free w-restriction;
- v_p(J(a,w)) ≥ (a/p − w)₊ + Σ_{e≥3 odd} a/p^e − 0.98, i.e. the signal-place g0 with one top and one cap, together with
  slope γ_p ± 0.0003.

**What it does not confirm:**
- nP ≥ 4, i.e. several tops on one orbit and e ≥ 3 caps;
- minors/frames (NUMTEST4 T2 did minors at an n′ = 4 orbit, which is locally the same object);
- the Lean's d ≡ 7 (mod 16) curve;
- the adapted-basis normalisation and the KerEnt tie;
- the regime cap ≈ b ≫ a/p³.

**New small check.** Script: `/tmp/claude-0/-home-user-SafeVerifyAgent/6f6a4549-468b-59ec-896e-73bdf5d26a96/scratchpad/sig/twotops.py`,
which reuses `numtest/kernel4_lib.py`. It took 98 s.
- Setup: p = 5, ℤ[ω], n′ = 4. Tops are at positions 0 (order a ≤ 160) and 2 (order n₂ ≤ 32). Caps n₁, n₃ ∈ {0,4,8}
  sit at positions 1 and 3. For the top at 2, position 3 is the e = 1 partner and position 1 the e = 3 partner.
- Prediction: γ(a+n₂) − Σ_e min(a/p^e, cap_{e mod 4}) − Σ_e min(n₂/p^e, cap_{(2+e) mod 4}).
- Result: v − pred ∈ [−1.13, +2.28] over 57 jets, so the two tops' gains add. For example, at (a, n) = (160, (0,32,8)):
  v = 34 against a prediction of 32.3.

**A full signal-place test would add the following:**
- the Lean's own host (d ≡ 7 mod 16, √−q, F = ℚ(ζ_{2^{e+2}})⁺);
- caps at the `true` positions set to the thick size b with a ≈ x·b, at a prime p < x;
- several entries with column minors;
- checking v ≥ Σ_tops Σ_{e odd}(a/p^e − b)₊ − O(log).

The local object is identical to NUMTEST4's. Only the top/cap labelling and the cap sizes differ.

## 6. Coverage

Read:
- DH:1-120 and CEH:1-230, both whole;
- IRZg:60-252;
- WJS:1-230;
- OP:1-500, 900-1130, 1320-1376, 1456-1470, 1612-1667;
- `GandSab.lean` (all) and SRB:15-224;
- SOP:100-225 and `ServiceOfTiedSelection.lean` (all);
- in SP/: `AdmissibleKernelSeriesInertPrimeNonConjugateFrob.lean` (all),
  `NormalisedFamilyStandardBasesIntegrality{,Statement}.lean`, `StandardBasesHyperbolicPairOrthonormal{,Statement}.lean`,
  `FrobeniusLiftMovesLetterCoordinates{,Statement}.lean`, `ExistsKurFrobTauEmbPosPl.lean`, `PrimeOfLiesOver.lean:60-115`,
  `ExistsRingHomRhoK.lean` (declarations), `JacobiOfClass.lean:55-83`, `AtOfTrueColumns.lean` (all) and
  `OrbitBoundStandardSeriesInertPlaces{,Statement}.lean`;
- `ExistsConstantCoeffOne.lean:1-80` and `AdaptedEnt.lean:15-100`;
- `PrvFOfOrbitLetterBounds.lean` (all) and PZF:100-290;
- DF:1-60;
- C1G:95-135 and NSC (declarations, 640-700).

Not opened:
- bodies of `split_bound_eleven_one`, `orbit_entry_bounds_hold`, `orbitIdentity_all_…`, `hyperbolicCoordinates_*`,
  `kvalGe_orbitGainWithoutOperator` and `noop`;
- the KerEnt `lat_S` construction and the supplier of `t.Adapted`.
