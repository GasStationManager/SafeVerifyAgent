# NODE-GLOBALCHAIN: the global chain, and how it is identified with the local models

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `GG/` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- `AM/` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/`
- `CZW` = `Formalism/SharpRestriction/GrowthBounds/ChartComparison/ComparisonZeroWeightBase.lean`
- `CC` = `Formalism/SharpRestriction/GrowthBounds/ChartComparison.lean`
- `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- `DK` = `Formalism/LocalRingCardinality/DataKernels.lean`
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`

## 0. Verdict (short)

**The local theorem applies to the global chain. The comparison preserves valuations exactly. The reason is structural:
the local chain is *defined* as the p-adic completion of the global chain.**
- At an inert place w, `ModelsOK` uses the local chain `chainAt H hT := chainMu (stepsMu H …).up`
  (`Formalism/SharpRestriction/GrowthBounds/ChartedClasses/ClsChartedLabAt.lean:104`).
- `chainMu` defines Kz_j := extK(cmp_j, cmp_{j+1}, KLxMu_j) (CZW:102-105). This is the global step map
  `(D.chTw u μ).K j`, transported along injective, embW-semilinear comparison maps cmp_j : V_j → Fm_j.
- The comparison is **lattice-exact**:
  - `latS`: cmp_{j+1} x ∈ Int_{j+1} ⇔ x ∈ (global lattice)⊗O_w (CZW:184-185);
  - `intS`: Int_{j+1} = O_w-span of cmp(global lattice) (CZW:195-199);
  - level 0: span cmp(L_0) = M (`LatCmp.cmp_M`, `Formalism/LocalRingCardinality/DataLatDefs.lean:26-27`);
  - `embW_int`: v_w(x) ≥ 0 ⇔ embW x integral (DataLatDefs:16-17).
- So divisibility of chainK^m by ϖ^s locally is the same statement as divisibility of the global composite at w.
- No scalar c_w enters the comparison. The only scalar anywhere is cK in `ExpansionEquality` (FGS:566-571). It is
  required to be a unit (cK ∈ O, cK⁻¹ ∈ O), so it cannot absorb any gain.

**The content therefore sits entirely in `admitted` for this transported chain**, chiefly ExpansionEquality: "the completed
global theta-jet map equals a unit times Σ (1/|stab|)·(local formal-group theta kernel)". That is supplied by `AdmAtEnt2`
(from CM2) on the inputs `TiesAt` / `KernelDifferenceAtLevel`. Those inputs are proved in
`SP/JointSiteChainComparedCarriesAdmittedSystem.lean:29-75` from per-site lemmas whose bodies I did not open.

## 1. Statement (as mathematics)

### (a) The global chain on the live path

**Ranks** (`Formalism/LocalRingCardinality/Params.lean:6-46`). Even k, m and odd t satisfy:
- m + 3 ≤ k and 3m < t;
- m ≤ 2·ord ≤ k.

The spaces are N(j) = k + j(t+1), so the rank **grows** by t+1 at each step. Separately, sigW(j) = (k+j−1, m−j) are the
indefinite signatures used elsewhere, for the Shimura varieties of NODE-COVOL.

**Spaces.** The chain lives on lattices in `Sp E n` with the standard hermitian form `hStd`.
- *I infer* the form is totally positive definite, because `autO_finite` uses `hStd_pos` (`AM/PredMemGamRanks.lean:340-341`).
- So these are totally definite hermitian spaces of rank N(j) over the CM host field E, relative to its totally real F.
- The class sets `cls j` are finite sets of lattice classes: GStep representatives (`AM/LatAtLattice.lean:48-60`).

**Mult_j.** These are the functions `cls j → (Y j → ℂ)`, i.e. algebraic modular forms with values in a finite-dimensional
weight space (DK:14-47). The integral structure is `MemberForms` lattices `(fm u).lat j`.

**The step map** (DK:63-68):

K_j φ (c') = Σ_{c ∈ cls j} |stab c|⁻¹ · ρ_j(c)ρ′_j(c′) · divDe ∘ unf_j(c,c′) ∘ sharp (φ(c)).

- The composite is `col = chainOpM` (DK:70-71), from `Formalism/ThetaLiftIndependence/Statement.lean:47-57`.
- On the live constructor, `unf` is `jetMap(jetC cD (th u a i c c′)) 0` (`AM/LatAtLattice.lean:73-78`). This is the
  Taylor jet at 0 of a theta function `thAt` = `thOf … (xiAt …)` (`AM/XiAtPenultimateEqXiCpl1.lean:263-276`), with:
  - finite-adelic Schwartz datum xiAt, which is local lattice-condition indicators phiT;
  - archimedean function `A.e = J.V.eNat χ`, built from a "vacuum" `Th.VacIn` for the period lattice Λ(δ) of a CM elliptic
    curve, with δ a twelfth root of the discriminant (`AM/TrueColumnChoicesHeckeCharReferenceEqOne.lean:127-147`).
- ρ, ρ′ are the splitting characters `rhoAt` (`AM/LatAtLattice.lean:62-67`). `rhoDet_eq_inv_muTilde_chiD_pow` pins them
  to μ̃⁻¹·χ^{∓N/2} (`AM/LatAtLattice.lean:206-211`).

**Construction.** `chTw := I.chain l` in `TC.cols` (`AM/LatAtLattice.lean:180-212`), and the D7 is `I.rec7 l Z`
(`:225`). `ModelsAt` is proved at points `β.Is (positionOf HasPart)` (`SP/TuplesHaveLocalModelsAtConstructedPointOverTrueC.lean:10-19`).
I did not open the bodies of `existsLayeredData_of_goodScaleContexts` / `layeredAutomorphicData_exists_of_twoPasses`.

**Bessel period.** `PeriodMap`: Ptil(ψ, F) = period(lowerMap(evz ψ))(F), and PtilCol φ = Ptil(col φ) (DK:163-195).
These are abstract fields here. `BesselId` (`Formalism/SharpRestriction/GlobalTheoremInputs.lean:65-67`) ties Bu to `besS`
up to a nonzero scalar and a unitary change of basis.

**Length.** m = R.m ≥ x^{1/2−ε} (`RestSize`, NODE-FAMILY).

**Nonvanishing of the composite.** I found nothing on this path that asserts col ≠ 0 or that the intermediate Mult_j ≠ 0.
The divisibility node does not need it, since 0 is divisible by everything. Nonvanishing must come from the slope side:
- `InputSG` near-orthonormality of the Bessel Gram matrix (`Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean:30-35`);
- `NuFull` / `RRFull` (`RhoDetPrimeEqMuTildeMulChiPow.lean:356-361`).

This is SUMMARY open node 4. Neither a Rallis inner product nor a tower property appears here.

### (b) CmpLite, CmpV, SiteAdm, ModelsOK

- **CmpLite(u, μ, w, Ch)** (`GG/ModelsOK.lean:46-54`). There exist embW-semilinear maps cmp_j : V_j(twisted forms) → Fm_j such that:
  1. cmp_0 ∘ e0 = c.cmp;
  2. whenever emb y = K_j(emb x), cmp_{j+1} y = Kz_j(cmp_j x), i.e. they intertwine the global and local steps;
  3. every K_j is rational (KRat);
  4. a local bound v(cmp_m y) ≥ s implies a global bound VGe_w(y, s).
- **SiteAdm** (`GG/IsPlaceCofactorValuationLowerBound.lean:10-14`). There is a pending datum Y5 on Sys(gat, Fl, Lv, Ch) with
  `admitted`, dG_0 = 0 and dG_j ≤ v_p(DGam).
- **ModelsOK** (`GG/ModelsOK.lean:56-62`). There is a family LC(μ, u, w) of local levels and chains such that, for every
  used twist μ and every place w with GIdx and p ∉ Qp(μ), both CmpLite and SiteAdm hold. It also requires e0(μ0) = eMu0.
- **CmpV** (WJS:156-159). Local chain divisibility of c.cmp x gives the column bound ColGe(x, s). It is derived from
  CmpLite by `cmpV_of_cmpLite` (`SP/UnitaryWeightModels.lean:29`).
- **Realisation** (`SP/ThetaLocalModelsOfSplitUnramifiedJoints.lean:11-28`). LC is `chainAt H hT`, built from a `Joint`
  (`GG/JointCmpEmbeddingY.lean:35-77`). The CmpLite fields are the `kaAt` fields `cmp, cmp_zero, cmp_K, rat, val`
  (`SP/JointSiteChainComparedCarriesAdmittedSystem.lean:80`).
  - `cmp_K` is `chainMu_cmp_K` (CZW:115-120): it holds by definition.
  - `val` comes from the lattice iff `latS`.
- **Answer to (b).** The local chain is the global map on the completion, extended from a spanning set. The lattices
  correspond exactly. There is no "up to a constant", no sublattice and no mere inclusion of images.

### (c) "Kz = Σ theta-kernel integrals" for the constructed family

- The global K is *defined* as the weighted kernel sum (DK:63-68).
- ExpansionEquality (FGS:566-571) asks for MvPolynomial.map(Kz_j F) = Σ_{La ∈ Rep} (cK/|stab La|)·ker_j(La)(F) with cK a unit.
- It is obtained inside `admitted` from `AdmAtEnt2` (`GG/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:106-129`), given:
  - `CurveIn`;
  - K1 = `ThetaSeriesDataHypothesesBelowMaximalLevel`;
  - `XiIn`, `LawInLt`;
  - `TiesAt` (`Formalism/LocalToGlobal/InertKernelTheory/SecondKernelEntrywiseLastLevel.lean:55-60`).
- TiesAt has five parts: FormsSharp, TieStab (|stab| global = local), TieRead (cmp read through ι), TieSer, and
  `KernelDifferenceAtLevel`. The last says the global theta-jet entry, read p-adically, equals cK·DelF(local formal-group
  kernel), with ‖cK‖ = 1.
- These are discharged at `SP/JointSiteChainComparedCarriesAdmittedSystem.lean:31-75`, by `kernelSite_*` lemmas
  (`…FrameValuesStepZero`, `…PositiveSteps` → `StepDel.del_of_pos`).
- **The identity is therefore a theorem**, not a definition. It rests on KernelDifferenceAtLevel: *the p-adic image of the
  complex theta-jet coefficients equals the formal-group theta kernel up to a unit*. That is where CM theory enters. Its
  bodies are unopened.

### (d) Uniformity over places

- Quantification (`GG/ModelsOK.lean:60-62`, `RowTwU` `:41-44`, `CmpV` WJS:157-158): for every x ≥ x0, every word u,
  every place w with `GIdx host T p` and every used twist μ with p ∉ Qp μ.
- `GIdx` (`RhoDetPrimeEqMuTildeMulChiPow.lean:68-69`) requires: p prime, **p ≥ 5**, inert class, HNeZero, p not a level
  prime, and p ∤ T.
- **Twist places.** `Qp μ0 = ∅` and `p_w ∉ Qp(muAt w)` (`Formalism/LocalRingCardinality/DataDIV.lean:488-494`). So for the
  untwisted chain μ0, **one global chain** (mem u).C is modelled at every GIdx place. The exclusion "p ∈ Qp μ" bites only
  for other twists.
- **Excluded places carry zero gain.** `gainS` = 0 unless (ResidueClassZero ∨ Sg) ∧ ¬Exc ∧ ¬Cs, where
  Exc = p | condN·g0·g1 (WJS:37, 47-49). `gainP` = 0 for p > X″ or (ResidueClassZero ∧ h = 0)
  (`Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean:224-229`). `GainZero` and `NoGain` list the rest.
- The cost of zero-gain primes is the ASK − Ga ≤ LoP accounting (NODE-LOSS), not this node.
- `Joint` additionally needs p coprime to N(cc) of the curve ideal (`GG/JointCmpEmbeddingY.lean:70`). `CurveEx` needs
  p ≥ 5 and p ∤ N(cc) (`GG/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:131-135`). I did not see GIdx imply p ∤ N(cc).
  It must come from `jointsAt_all_std`, which I did not open.

### (e) GlobalArtinReciprocity and CM2

- `GlobalArtinReciprocity` (`Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70-72`)
  says: there exists an Artin map Ideles E → Gal^ab with `IsGlobalArtin`. It sits in the namespace `Published`, i.e. it
  is an assumed literature input.
- `CM2` (`Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean:45-47`) is derived from it plus Chebotarev
  (`Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CmGoodModelOfGlobalArtinReciprocity.lean:10-11`). It says:
  every lattice with CM by O_{ℚ(√−d)} (d ≡ 3 mod 4, squarefree) has a **good model** at every l ≥ 5, l ∤ d.
  Concretely, rescaled g2, g3 lie in ℚ_l^{ur}, are integral, and the discriminant is a unit.
- `CM3` (same file, :49-55) is the formal-group form: u-series ∘ (ε·Lubin–Tate log with steps l²) has integral
  ℚ_l^{ur} coefficients at inert l. This is the height-2 supersingular formal group, matching the "height-2 Lubin–Tate
  parameter" of NODE-TWU.
- In `servH_row_of_artin` (`SP/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean:16-24`), CM2 feeds:
  - `torsionTaylorAlgebraic_latticeExists_of_cm`;
  - `intInert…`;
  - `AdmAtEnt2`;
  - `exists_genusOne_formal_iso_of_unramified_good_reduction`.
- *I infer*: their role is to make the CM theta values algebraic and l-integral, and to identify the complex expansion
  at the CM point with the formal-group expansion.

## 2. Argument

1. `rowTwU_of_models` (`SP/UnitaryWeightModels.lean:15-31`) takes ModelsOK and Shape and returns CmpV (by
   `cmpV_of_cmpLite`) and SysTw (by `local_systems_lower_bounds_second_real_place`, from SiteAdm).
2. ModelsOK comes from `modelsAt_bpt` → `modelsAt_of_part` (`SP/TuplesHaveLocalModelsOfStandardColumnObjects.lean:11-15`).
   That theorem gets `jointsAt_all_std` and `Stab0` (trivial stabilisers at level 0), then applies `modelsOK_of_joints`.
3. `modelsOK_of_joints` picks a Joint for each (μ, u, w) and sets LC = chainAt H. `site_cmpLite_siteAdm` then gives:
   - CmpLite from `kaAt`, i.e. by construction;
   - SiteAdm from `admissible_at_each_site`, which assembles TiesAt and applies AdmAtEnt2.
4. `tuplesLocalModels_of_otherDivisionLatticesHeights` (`SP/TuplesHaveLocalModelsAtConstructedPointOverTrueC.lean:19`)
   transfers ModelsAt from D to `setDiv D (nPrime L) h`. This is correct, because ModelsOK does not mention `div`.

## 3. Children

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `kernelSite_frameValues_step_zero` / `…positive_steps` (`StepDel.del_of_pos`) | `SP/KernelSiteFrameValuesPositiveSteps.lean` | p-adic image of the global theta-jet entry = unit · local formal-group kernel DelF | **core** (the actual local–global identity) |
| 2 | `AdmAtEnt2` (`inert_theta_admissibility_of_complex_multiplication`) | `GG/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:106` | TiesAt + K1 + XiIn + Law ⇒ admitted (incl. ExpansionEquality) | core (LOCALDIV sibling) |
| 3 | `jointsAt_all_std`, `jointData_at_p_and_adelicDatum_nonempty`, `latticeTuple_joint_dictionary`, `kernelSite_*` (Pair, Move, Away, Scal, Law) | `SP/JointSiteChainComparedCarriesAdmittedSystem.lean:31-38, 82` | a Joint (comparison data, incl. lattice-exact cmpJ) exists at every GIdx place | core, **definition to unfold** |
| 4 | `StepIn.cmpJ_lat`, `surj_of_card`, `cmpJ_inj` | used at CC:131-147 | comparison maps are injective, lattice-exact, surjective onto rational integral forms | core-ish (makes the transfer exact) |
| 5 | `cmGoodModel_of_globalArtinReciprocity` | `…/CmGoodModelOfGlobalArtinReciprocity.lean:10` | CFT + Chebotarev ⇒ good reduction of CM curves | standard (Deuring / Serre–Tate) |
| 6 | `chainMu`, `chainMu_cmp_K`, `chainK_forcedMu` | CZW:102-157 | local chain := completed global chain, uniquely on the span | glue (definitional) |
| 7 | `existsLayeredData…`, `layeredAutomorphicData…`, `TC.cols`/`rec7` | `AM/LatAtLattice.lean:180-225`; `…/MemberTopFinalContextParameters.lean:14-22` | constructs the D7 with chTw = theta-jet chain | core, bodies unopened |

## 4. Oddities

1. **Denominator cost v_p(DGam) per step.** DGam is the lcm of |Aut| over *all* unimodular hermitian lattices of ranks
   N(1..m), rankX′, … over E (`AM/PredMemGamRanks.lean:326-338`).
   - The local system is charged dG_j = v_p(DGam) at every step j ≥ 1 (`dGT`,
     `GG/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:137`; SysTw needs lowS ≤ ΣFn − Σ_j dG_j, `GG/ModelsOK.lean:37-39`).
   - Aut(O_E^N) ⊇ S_N, so v_p(DGam) ≥ v_p(N(m)!) ≈ N(m)/(p−1), with N(m) > 3m² ≳ x^{1−2ε}.
   - Total charge ≈ m·N(m)/p. That is the same 1/p order as the gain γ_p·Σa per step times m. The comparison needs the
     sizes of the weights a.
   - The bookkeeping is a proved theorem (`local_systems_lower_bounds_second_real_place` → `SiteSys.sysTw_sites`). I did
     not check where this charge is absorbed (Fn, ES). **An expert should check magnitudes.**
2. Nothing on this path forces the iterated lift to be nonzero. See (a): that burden is on InputSG/LinkS.
3. `ArchimedeanSignatureMatching` (FGS:587) is the kernel-expansion identity, not an archimedean statement (known).
4. The scalar cK in ExpansionEquality is a unit, which is fine. `PlaceB`/`Del` require ‖cK‖ = 1 and cK ≠ 0
   (`SP/JointSiteChainComparedCarriesAdmittedSystem.lean:62-75`).
5. `Joint.cop` (p ∤ N(cc)) is not visibly implied by GIdx. If it fails at some GIdx place, `jointsAt_all_std` would be
   false there. It is proved, so presumably cc's primes are inside levelPrimes. Unchecked.
6. `ModelsOK`'s default branch (`else ⟨Gl.Lv, Gl.Ch⟩`) is used only off the quantified set. Harmless.

## 5. Coverage

Read:
- context: PROTOCOL (Explainer); SUMMARY; NODE-FAMILY; NODE-TWU (full); NODE-ROWSU / NODE-SLOPESN (skim via TWU).
- `GG/ModelsOK.lean`; `GG/IsPlaceCofactorValuationLowerBound.lean`; `GG/HasPartAnd.lean`; `GG/JointCmpEmbeddingY.lean:1-196`;
  `GG/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:1-160`.
- `SP/UnitaryWeightModels.lean`; `SP/TuplesHaveLocalModels*` (3 files); `SP/ThetaLocalModelsOfSplitUnramifiedJoints(Statement).lean`;
  `SP/JointSiteChainComparedCarriesAdmittedSystem.lean:1-90`; `SP/BundleBothParts…GlobalArtinReci(Statement).lean`;
  `SP/LocalSystemsLowerBoundsSecondRealPlaceStatement.lean`; `SP/KernelSiteFrameValuesPositiveStepsStatement.lean`.
- CC (all); CZW (all); `…/InertKernelTheory/SecondKernelEntrywiseLastLevel.lean:1-80`; FGS:560-592; WJS:15-155;
  DK:1-200; `Params.lean:1-80`; `DataLatDefs.lean:11-36`; `DataDIV.lean:418-503`; `RhoDetPrimeEqMuTildeMulChiPow.lean:55-75`.
- `AM/LatAtLattice.lean:1-260`; `AM/TrueColumnChoicesHeckeCharReferenceEqOne.lean:127-260`;
  `AM/XiAtPenultimateEqXiCpl1.lean:230-300`; `AM/PredMemGamRanks.lean:320-345, 930-975`;
  `Formalism/LocalToGlobal/KernelLattices/ThDistC.lean:1-140`; `ThetaLiftIndependence/Statement.lean:47-57`.
- `CMGoodModels/Statement.lean`; `ExistsUniqueHcharOfFiniteOrder.lean:55-90`; `CmGoodModelOfGlobalArtinReciprocity.lean`;
  `MemberTopFinalContextParameters.lean`; `IsResidueClassZero.lean:200-262`; `DataParams₂.lean:240-256`;
  `DataForced.lean:110-134`; `GlobalTheoremInputs.lean:55-78`; `ClsChartedLabAt.lean:104` (grep).

Not opened:
- `StepDel.del_of_pos` and the other kernelSite bodies; `jointsAt_all_std`; `StepIn.cmpJ_lat` / `surj_of_card`;
  `admissible_entries_small_chain` / `first_kernel_law_global_small` (sibling LOCALDIV);
- `existsLayeredData…` / `layeredAutomorphicData…` bodies; `thC` / `xiInd` / `VacIn.eNat`;
- `cmLattice_good_model_unramified`; `SiteSys.sysTw_sites`; `kerAtMu` (val proof).
