# NODE-COUNTS: the two remaining counting statements (window mean of badShare; local defect masses)

Paths: `GB/` = `Formalism/SharpRestriction/GrowthBounds/`, `MF/` = `GB/MonomialFactorials/`,
`CSR` = `GB/CountingStatementReduction.lean`, `FM/` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`,
`FR` = `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ComplementReferenceCompactSubgroup.lean`,
`MM/` = `Formalism/MahlerMeasure/`. All relative to `.../scratchpad/art/lean/src`.

## 0. Verdict

**Part 1.** The window-mean statement is proved on the live path, uniformly in p and in the rank. It is **not** a
concentration-of-measure statement. It is a mean-value theorem for p-adic valuations of a polynomial determinant
along an arithmetic progression. That is, a Markov bound on elementary divisors plus root counting.

- The briefed worry, that badShare is small only because t0I sits just above the Pieri bulk, does not apply.
  The threshold sharpness is handled earlier, by the model: the block caps in `Kept` and `admB3`.
- `RemainingCountingStatement` deals only with kept blocks. Its question is this: is the true Fock pairing on a
  block lattice unimodular to depth D, outside a small set of tie weights?
- The answer is a bad share of ≈ 2S/Yl + 2κ/E per tie. Here S is the tie's polynomial degree in the weight,
  Yl ≈ a/(2kYP) is the window length, E = Y·κ_S, and the share is ≤ (30+C_M)/Y.
- Correction to ADMB2's wording: the "t" in C(t+1)N₁/Y is `SegData.t`, the number of far ties (≤ s ≤ N₁). It
  is not the threshold t0I. So the mean is ≤ C·N₁²/Y with Y = x^{13}, which is tiny.
- The cost of this is moved into the depth D = depthD ≈ C·Y²N₁²(r+1)²·log_p a. D is charged in τ = Σ m(t+D+1)
  (ADMB2 §2). It is huge in x, but polylog in a ∝ e^{x^ε}, so it is negligible against t ≳ b.

**Part 2.**
- The local defect counts are proved and have the right direction. Mass is Σ_{St-orbits} vol(K₀)/vol(stab).
  - Given the saturation, the mass of self-dual lattices is ≍ [Mh : M]^{−(k−1)}, two-sided with factor 4.
  - The total defect-β share is ≤ 4H^{4(r+1)}β^{−(k−1)}.
  - The per-datum mass with gluing image j is ≤ H^{…}·j^{k−1}.
  - Larger defect therefore means smaller mass. The mechanism: the complement lattice in W₀ (rank k−1) is closer
    to unimodular, so there are fewer such lattices.
- **Correction to PAIRB:** the second-type saving q^{−(k−2r−4)} per amplitude **is a character-sum cancellation**.
  It is the bound `amp ≤ 7q^{1−(k−2r−3)}·mass`, proved with a symmetric invariant averaging kernel. Only the
  first type is pure counting.
- `EnergyAbs` is the expected Schur-orthogonality/Bessel inequality and is used in the safe (≤) direction.
- `IdZero` is proved, by conjugation/lift vanishing of the identity cells for u ≠ u'.
- `PointSumInput` is supplied by "Theorem B (rotated)", which is proved in `CompanionTheory/…/BesselWaveGrids`.

Nothing false-looking was found. The constants close.

## 1. Part 1: statements

**`Conclusion1`** (GB/FlipOneThree.lean:305-308). Under `HI`, meanKapT ≤ C·(S.t+1)·N₁/Y. Here meanKapT is the mean
over the box winA^s × winA of kapT = badShare(blockForm, segLat, depthD).
- winA = [a, a + a/(kY) + xa] (CSR:2981-2987).
- S.t = s − σ (GB/ObjSeg.lean:136) is the number of tops with p^d ≥ a/b′.
- depthD = C·Y²N₁²(r+1)²·lgA + 2κ₀ (GB/FlipOneThree.lean:20-21).

**`RemainingCountingStatement`** (CSR:2427-2440). Assume HI and C(t+1)N₁ < Y. Then there is κ(aTop, aPlus) ≥ 0 such
that:
- for every kept block b there is a sublattice L₂(b) with GoodSub(blockForm b, blockLat b, L₂ b, depthD), i.e. the
  pairing on L₂ is perfect up to p^{depthD};
- (1−κ)·rank(segLat) ≤ rank(segSub L₂);
- meanBox κ ≤ C(t+1)N₁/Y.

`counting_statement_of_block_form` (CSR:2445) turns this into `Conclusion1` via badShare ≤ 1 − goodShare. The
small-Y case is trivial, because badShare ≤ 1 (CSR:2416).

**Reduction chain on the live path.** Every link was read. All are theorems unless named.

1. `block_form_of_segment_form` (CSR:2706): per-block defects g(b) suffice.
2. `segment_form_of_scaled_form` + `double_count` (CSR:2766, 3092-3118). The mean of shares is ≤ 2εK, from:
   - (i) per digit class dl, Σ_window bad ≤ ε·Σ_window model-dim (`DigitClassDimensionComparison`);
   - (ii) the true rank is ≥ ½ the model dim (`rank_ge`, from adm11);
   - (iii) flatness `RestFlat`: model dims vary by ≤ e³ across the window (`restFlat_exp`, CSR:3550, proved
     from s·r/(kY) ≤ 1 and p ≥ k²Y²).
3. `segment_weighted_counting_bound_of_all_remaining_bounds` (MF/SegmentWeightedCountingBoundOfAllRemainingBounds.lean:135).
   - ε = (30+C_M)t·e³/Y + 5/Y.
   - The input is `RestAll` = BlockBoundUniformiser ∧ RestPlus ∧ RestTM ∧ RestDir ∧ RestFree ∧ RestRatio ∧ RestDepth
     (MF/BlockBoundUniformiser.lean:98-157).
   - The combinatorial step is `assemble` (MF/Imports.lean:7).
4. Live root: `theorem_A_closed_form_holds` (GB/FockGramWindow.lean:24). It is
   `closed_of_minimal_vector D PI.exists_minimalNormVector diagonal_rank_bound restWinE_proved`, which takes no
   open hypothesis.
   - It passes through nine `closed_of_*`/`RestOpen9…4` weakenings (MF/*.lean).
   - `openE_of_open4` (MF/ThresholdsMonoNormalized.lean:50) supplies RestTM by `restTM_closed`, and
     BlockBoundUniformiser by `block_bound_of_dual_families`.
   - It is consumed as `p13A` (`LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean:64`).

**The content: `RestTM`** (MF/BlockBoundUniformiser.lean:134). For each digit class dl and level x:

> Σ_{aTop ∈ window} bad_Y(aTop, depth ⌊D1r⌋) ≤ (30+C_M)/Y · Σ_i Σ_{aTop} dim Y(aTop with coordinate uTop i moved to the
> window top).

It is proved by `restTM_of_rests` from `alternative_mean_value_theorem` = `ModelLatticeRank` (InstM version,
GB/FlipOneThree.lean:416; proof CSR:19 → `theoremMV7` → `theoremMXB_of_point`). The inputs are as follows.
- `XMof` (MF/DimYOvr.lean:130) sets the progression step dd = 1 in the tie weight n_i = (aTop_i − digits)/P − level.
  It sets E = Y·κ_S with κ_S = 3(s+2)r²·lgA, and Yl = the window length in units of P.
- **`WindowMeanAP` / `WindowFullAP`** (MM/QuotientUpperBoundsOfPowerBounds.lean:22-56). Let M(t) be an n×n matrix
  of integral combinations of binom(t,k), k ≤ δ₀, with det = lead·∏(t−ζ). Let t run over a progression of length
  Y₀ ≤ p^h with step prime to p. Then:

  mean_j #{Smith entries with v ≥ E} ≤ n·(δ₀/Y₀ + (La₀ + δ₀h/Y₀)/E), where v(lead) + #roots/(p−1) ≤ n·La₀.

  Proof idea:
  - Σ v(Smith) = v(det);
  - Σ_j min(v(t_j − ζ), h) ≤ Y₀/(p−1) + h for each root;
  - each root is p^{−h}-close to at most one t_j;
  - Markov at level E.
- `GamDeg`/`GamLead` (MM/HasOrder.lean:21-41) say that the tie Gram entries are polynomials in n of degree
  ≤ S = T.S (the total degree of the letters up to the tie, `MM/GoodCount.lean:91`). They also identify the
  leading coefficient as an initial-part Fock pairing. Its valuation is controlled by
  `GramDeterminantGradedHypothesis` (κ₄ ∝ r²·log).
- `PointMX` (bad ≤ Σ_i Σ_w #(bad Smith entries of tie i)·dim) is the triangular "partner" argument across the t ties.
- `restTMEps_of` (MF/EpsilonBoundMConstant.lean:115) checks S/Yl ≤ 7/Y, using these facts:
  - S·P ≤ 5/2·b′ + (2s+1)·2a/p (`S_bound`);
  - Yl·P ≥ a/(2kY);
  - kY²b′ ≤ a/2;
  - p ≥ k²Y².

**Uniformity.**
- In p: it needs p ≥ k²Y² = p₀. Smaller p are handled by the trivial kapIIf branch (ADMB2 §1).
- In rank: both sides of the Markov bound scale with n₀ (the rank of the tie lattice), so the share does not
  depend on it. The rank enters only through E ∝ r²·log, i.e. the depth, which is charged to τ.
- The constants are fixed (30+C_M, e³, 2) and do not depend on p, m or a.

**1b: the model vs the true lattice.**
- Inside the counting, BlockBoundUniformiser realises blockLat ⊆ Σ levels Ljj (`RestBCdim`), with a level
  passage loss `levelPassageLoss` = 10(s+1)(r+1)·lgA + κ₀ added to the depth. Both are proved.
- `extendedClosedForm` (GB/StandardPolynomials.lean:23) is `admitted D → Closed(…)`, proved from the three
  interfaces `restCols`, `restPre`, `restTCore` (theorems) and from key3Ord/loc4Res. What they state:
  - `ColsAt` (GB/StandardPolynomials/ColsDef.lean:42): each model test polynomial factors into column polynomials
    K_a. Each K_a has, after the embedding ioD into the global HH space, an exact w-divisibility order o_a, and
    Σ o_a = Σ_i P_i·deg_{2i} + deg_top. This is exactly blockOrd.
  - `PreAt`: a product system exists.
  - `TCoreAt`: perturbed products stay in the SSe filtration.
- What is assumed is only `admitted D` (20 clauses). The one used here, adm16 = `WittIdent`, is proved
  (`wittIdentity_holds`, GB/WittIdentPI.lean:11). The other clauses are supplied in `local_model_results`.
- I did not open the bodies of restCols/restPre/restTCore.

## 2. Part 1c: computation

`colen/winmean.py` and `colen/winmean_tight.py` test the WindowMeanAP inequality exactly (Smith form over Z_(p),
leading coefficient by finite differences):
- Hankel binomial matrices [C(t,i+j)] and random binomial combinations, with n = 3, 5, p = 5, 7, Y₀ = 200,
  E = 2, 4, 8: **0 violations out of 24**. The observed bad share is 0–8%; the bound is 7–42%.
- A tightness check with n = 1 and M = (t−3)^k, E = k: observed 1/p (0.200, 0.143) against bounds 0.26 and 0.17.
  So the lemma is sharp up to 1/(p−1) + O(h/Y₀).

Normalisation match: in the Lean, the share per tie is 2S/Yl + 2κ/E with E/κ = Y. The toy is the case
"Y" = E/La₀ ≈ 10–40, where the bound is ≈ La₀/E. Consistent.

## 3. Part 2: statements

Setting (FR:14-240): a local hermitian space V of rank k+2r+1, frames f, f′ (r+1 vectors each), ME = their E-span
(rank 2r+2), and W₀ = ME^⊥ (rank k−1).
- A *term* is a lattice Λ = n·stdLat(d.1) = n′·stdLat(d.2) over a datum d.
- mu(Λ) = invVol(K₀, St ∩ Stab Λ), and **mass(d, P) = Σ_{St-orbits, P} mu**.
- ν(d) = invVol(complement ref., H₀ ∩ Stab d). sumData φ = Σ_{H₀-orbits} ν·φ, and nn = total mass.
- **be(d,Λ) = [sat Λ : M]**, where sat = Λ ∩ ME and M = the O-span of fr and (fr′ − fr)/θ. This is the defect.
- cardI = [Ihat : M] is the gluing image.

| lemma | file:line | statement | proof |
|---|---|---|---|
| `selfDualHermitianLattice_mass_of_trace` | FM/SelfDualHermitianLatticeMassOfTraceStatement.lean | for k ≥ 2r+6 there is κ > 0 with κ/2·[Mh:M]^{−(k−1)} ≤ massSig(Mh) ≤ 2κ·[Mh:M]^{−(k−1)}, where massSig(Mh) is the mass of self-dual lattices with saturation Mh | leaf, body unread; consistent with local densities (the W₀-part has glue smaller by β) |
| `hermitianFrames_defectOrder_share_le` | FM/HermitianFramesDefectOrderShareLe.lean:29 | per frame class: Σ_d nT(be=β) ≤ 4q^{2a(2r+2)}β^{−(k−1)}·Σ_d nT(be=0) | read: the previous row plus #{integral Mh ⊇ M} ≤ q^{2a(2r+2)} (`encard_overlattices_le`) |
| `sumData_mass_be_eq_le` | FM/MassDefectOrderLe.lean:14 | Σ_d ν·mass(d, be=β) ≤ 4H^{4(r+1)}β^{−(k−1)}·nn | read: glue (frame-class decomposition) |
| `hermitianDoubleCoset_mass_le_and_finite` | FM/HermitianDoubleCosetMassLeAndFinite.lean:31,100 | mass(d, cardI = j) ≤ H^{9(r+1)²+12(r+1)}·j^{k−1}; finitely many orbits | read: glue over `hermitianTermCount_frameClass_le` (≤ H^{12(r+1)}j^{k−1} per class, the index-j sublattice count) × `hermitianFrameClasses_total_weight_le` (≤ H^{3(r+1)²}) |
| `family_bound` | FM/HermitianDoubleCosetSecondTypeFamilyAmpSqLe.lean:59 | ampSq(InFF β J β_J) ≤ 98·A₀·A₁·q^{−2(k−2r−4)}·nn | read: Cauchy–Schwarz `basic_inequality` with per-datum mass ≤ 2A₀β^{k−1} (`small_image`: cardI ≤ β, geometric sum) and total mass ≤ A₁β^{−(k−1)}; **β^{k−1} cancels**, so the saving is e² from the next row |
| `amplitude_le_mass_secondType_family` | FM/AmplitudeLeMassSecondTypeFamily.lean:31 | \|amp_d\| ≤ 7q^{1−(k−2r−3)}·mass_d on second-type terms | read: `exists_symm_invariant_kernel_hermitian_frames` + `norm_orbit_sum_le_of_symm_kernel`. The ψ-phase is averaged by a symmetric St-invariant kernel along "moves", which is **cancellation** |

Direction check: yes, larger defect means smaller mass. massSig(Mh) decreases like [Mh:M]^{−(k−1)}, while the
number of terms per datum with image j grows like j^{k−1}. In `family_bound` the two exponents cancel exactly,
which is why the gain must come from the amplitude.

**`EnergyAbs`** (`Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/EnergyAbs.lean:58`;
proof `…/TraceIntegralEstimates/EnergyAbsMain.lean:19`).
- Hypotheses:
  - σ is unitary with Schur relation ∫⟨b,σa⟩·conj⟨b′,σa′⟩ = ⟨a′,a⟩⟨b,b′⟩/d;
  - S, S′ are unimodular Følner closed subgroups;
  - W, W′ are S-equivariant vector-valued functions reproduced by convolution with d·conj⟨w,σ(·)w⟩ (they lie in
    the w-isotypic coefficient space), with ∫_{S\G}|W|² = 1.
- Conclusion: the disintegration over S\G/S′ of HS²(∫_G rk1(W(x), W′(h⁻¹x))dx) is ≤ 1/d.
- Proof: Følner truncations Ω_n, an exact energy identity for the truncation (`lintegral_hsA_Xop`, from Schur),
  pointwise lower semicontinuity (`point_lower`) and Fatou (`lintegral_liminf_le`).
- So it is the formal-degree isometry of the coefficient map, with Fatou giving only ≤. That is the safe
  direction, and it is used as an upper bound (IntOO ≤ 1/deg in `NormBound`).

**`IdZero`.** Supplier: `idZero_tO` (`…/FlagStabilizerTensors/RootLatticeThresholds/NuQPinExistsHolds.lean:57`) ←
`idCellOffC_holds_of_vol` (`…/GaugeLatticeShifts/IdCellOffCHoldsOfVol.lean:660`).
- `IdCellOff` (`…/ClosedLocalOrbits/TermOpStmt.lean:79`) says: u ≠ u′ → HasSum over identity terms = 0.
- It is proved from `idOffConj_all` and `idOffLift_all`: a conjugation and lift shifts the identity cells by a
  nontrivial phase.
- It is used in `splitAll_holds`. It is proved, and the hypothesis u ≠ u′ is genuinely used.

**`PointSumInput`** (`Formalism/HermitianCurvature/StatementPN.lean:240`). For every finite set S of points:

> Σ_{γ∈S} blockMinorWeight·n(γ)·(NG·ND)^{A(r+1)²}·J²(γ) ≤ TB, with TB = e^{CB(2r+2)⁵ f log b}·Ire.

- Live supplier: `point_sum_of_theoremB` (`…/FlagStabilizerTensors/ThmBUse.lean:83`, rotated variant `ThmBUseR`).
- That rests on `JointNormBoundRotatedUniform` = `theoremBRotated` (ThmBUseR.lean:29-39): a weighted sum over
  B-points of normWt^{A(r+1)²} ≤ e^{Cb(2r+2)⁵ f log b}·jSq.
- This is supplied by `weighted_bound_rotated_uniform` (`CompanionTheory/AutomorphicTheory/BesselWaveGrids/ThmBFinal.lean:7`)
  ← `hypsG_of_zuck zuckerman_gap`, and used in `analytic_pinnedTheoremB_uniform`
  (`CompanionTheory/AutomorphicTheory/UniformLocalFormulas/Closed.lean:20`).
- It is proved, and it is deep: this is the "ThmB" item of SUMMARY's ranking.

## 4. Children (ranked)

| # | name | file:line | role | weight |
|---|---|---|---|---|
| 1 | `theoremMXB_of_point` inputs: `gamma_degree_bound`, `gamma_integral_holds`, `bad_criterion_holds`, `partner_condition_holds`, `tieOpsX_main` | MM/MahlerMeasureProofs/GamDeg.lean:1153; …/PartnerMeanProofs/*.lean | the degree and leading-coefficient control of tie Grams, and the triangular passage across ties | core (bodies unread) |
| 2 | `valuation_window_lower_bound`, `windowMeanAP` | MM/StatementD.lean:32; MM/MahlerMeasureProofs/WindowMeanAP.lean:72 | the Smith/root-counting mean value lemma | standard in shape (tested, §2) |
| 3 | `exists_symm_invariant_kernel_hermitian_frames` | FM/ExistsSymmInvariantKernelHermitianFrames* | second-type cancellation q^{−(k−2r−4)} | **core**, unread |
| 4 | `selfDualHermitianLattice_mass_of_trace`, `hermitianTermCount_frameClass_le` | FM/ | two-sided β^{−(k−1)} mass and the j^{k−1} sublattice count | core-standard (local densities), bodies unread |
| 5 | `restCols`/`restPre`/`restTCore`, key3Ord, loc4Res | GB/StandardPolynomials/*.lean | the true lattice realises the model's block orders | core, bodies unread |
| 6 | `theoremBRotated` supplier | CompanionTheory/…/BesselWaveGrids | PointSumInput | core, unread (already ranked as "ThmB") |
| 7 | `restFlat_exp`, `restTMEps_of`, `assemble`, `double_count` | CSR:3550; MF/EpsilonBoundMConstant.lean:115; MF/Imports.lean:7; CSR:2766 | numerics and averaging | glue (read) |

## 5. Oddities

1. **Not concentration of measure.** The brief's model (a Pieri bulk just below t0I) belongs to admB3 and `Kept`,
   not to this node. Here the bad set is tie weights p-adically near roots of a Gram determinant. Its density
   ≈ (degree/window) + (log/E) is ≈ 1/Y.
2. **"t" in C(t+1)N₁/Y** is the number of far ties, not the threshold (correction to NODE-ADMB2).
3. **The depth is enormous**, D ≈ Y²N₁²k²·log a ≈ x^{27+O(ε)}·log a. It is affordable only because a ∝ e^{x^ε}. It is
   charged to τ, consistent with ADMB2's totalDegreeBudget.
4. **PAIRB's "no cancellation in ψ"** is wrong for the second type: `amplitude_le_mass_secondType_family` is an
   orbit-averaging cancellation. In `family_bound` the mass factors β^{±(k−1)} cancel exactly, so all the saving
   comes from it.
5. `IdCellOffC` carries u ≠ u′ inside `IdCellOff`, not as an outer hypothesis. It is harmless.
6. The leading-coefficient valuation of `binMatK` may be negative (1/k! factors; observed −4 in the toy). The
   lemma allows this.
7. Nothing false-looking was seen.

## 6. Coverage

Read:
- CSR:1-140, 2380-2800, 2840-3200, 3340-3612, 3838-3880;
- GB/FlipOneThree.lean:10-30, 299-450;
- GB/FockGramWindow.lean;
- MF/{ClosedOfMinimalVector, ClosedOfSplittingMatrix, ClosedOfOrthogonalSplitting, ClosedOfOrthogonalBasis,
  IntegralityFromMetricOfOrthBasisLat, ClosedOfOrthogonalLattice, SymmetryWindowOnAdmissible,
  SymmetryWindowLevelDimOnAdmissible, ClosedOfCoefficientFunction, SymmetryFinitenessWindowLevelDimOnAdmissible,
  IntegralityFromMetricOfOrthogonalityWindow, RestrictedBounds×3, PositiveOfDimensionChange,
  DirectionsOfPositivePart, ThresholdsMonoNormalized, ClosedOfOpenConditions,
  SegmentWeightedCountingBoundOfAllRemainingBounds, BlockBoundUniformiser, Imports, EpsilonBoundMConstant,
  RestTMExists}.lean;
- MF/ExponentMatrixFirstDepthEq.lean:1-40; MF/RestTMHypOf.lean:1-40; MF/DimYOvr.lean:100-175;
- …/PartnerMeanProofs/GramHypothesisOfLogBound.lean:1-200; …/PartnerMeanCoordinates/TheoremMXB.lean:1-150;
- MM/HasOrder.lean:15-41; MM/QuotientUpperBoundsOfPowerBounds.lean:20-60; MM/StatementD.lean:32-43;
  MM/GoodCount.lean:74-100;
- GB/StandardPolynomials.lean; GB/CoarseMultiplicity.lean:1-40; StandardPolynomials/{ColsDef, PreDef}.lean;
  TCoreDef.lean:60-107; GB/ColumnSystems.lean:200-285; GB/ObjBridge.lean:10-40;
- AdmissibleFamilyNoKernel.lean:1-90;
- FR:1-240; FM/{MassDefectOrderLe, MassDefectOrderLeStatement, HermitianDoubleCosetMassLeAndFinite(+Statement),
  HermitianFramesDefectOrderShareLe, HermitianDoubleCosetSecondTypeFamilyAmpSqLe,
  AmplitudeLeMassSecondTypeFamily}.lean; statements of four further FM leaves;
- EnergyAbs.lean:1-80; EnergyAbsMain.lean;
- NuQPinExistsHolds.lean:1-120; TermOpStmt.lean:60-100; FourParts.lean:140-175; IdCellOffCHoldsOfVol.lean:650-663;
- StatementPN.lean:225-250; ThmBUse.lean:60-160; ThmBUseR.lean:20-40; BDataOf.lean:495-520; NGLeaves.lean:40-70;
  CompanionTheory/…/Closed.lean; ThmBFinal.lean.

Not opened:
- the bodies of the GamDeg/GamIntC/BadCrit/partner proofs, `valuation_window_lower_bound`, and
  restCols/restPre/restTCore;
- the self-dual mass and term-count leaves, `exists_symm_invariant_kernel…`, `small_image`;
- the EnergyAbs sub-lemmas, the Theorem-B proof, and the `admitted D` suppliers other than WittIdent.
