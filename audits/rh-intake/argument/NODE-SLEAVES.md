# NODE-SLEAVES: the four content-carrying leaves of Theorem S (RowMain, LoopRowS, RowNG, the Dall count)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FM/` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `GA` = `Formalism/SharpRestriction/CuspSpanNormBounds/GlobAut.lean`
- `BCE` = `Formalism/SharpRestriction/CuspSpanNormBounds/BridgeCountE.lean`
- `SHF` = `Formalism/SharpRestriction/CuspSpanNormBounds/StandingHypothesesHoldFamily.lean`
- `PB` = `Formalism/HermitianCurvature/StatementPB.lean`
- `PN` = `Formalism/HermitianCurvature/StatementPN.lean`
- `TOP` = `Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/TermOp.lean`
- `HSet` = `Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/HidaSetting.lean`
- `SKI` = `Development/AbelianVarietyTheory/Statements/CuspFrameWeights/SameKindIsometric.lean`

## 0. Summary (answers to the brief's questions)

- **The automorphic space is the space of genuine L² automorphic forms on a non-compact unitary group.** It is
  not a space of functions on a finite class set, and it is not defined as the image of a theta lift.
  - Lean: `Dcount = finrank (eHom σs μf fund R Re)` (`GA:198-201`). Here `eHom` is the image under the level/character
    idempotent operator `Re` of `HomS` = Hom_{G∞}(π∞, L²(G(F)\G(𝔸))) (`GA:181-196`). `L2` is
    `Lp ℂ 2 (muA restricted to fund)` (`GA:117-118`), and `fund` is a fundamental domain for G(F) in
    G(𝔸) = ∏_v U_J(ε_v) × G(𝔸_f) (`GA:89-109`).
  - `Dstar d = d · vol(fund) · Re(e(1))` (`GA:205-206`): formal degree × covolume × e(1).
  - The tie to the project's Dall is `AutTie` (`Formalism/SharpRestriction/CuspSpanNormBounds/DstarEq.lean:10-22`):
    `D_eq : B.D = D.what₂.Dall` and `Dstar_eq : D.what₂.Dstar = B.I.Dstar (∏ fdeg) μf fund e`. The signature
    is `epsS D.R` (k+r, r+1) and the HC parameter is `lamS`.
  - So "Dall ≈ D*" is a **limit-multiplicity statement for discrete series of U(k+r, r+1)^f in L²**, with
    relative error e^{−n f log n/16}. The parent's reading was right. The "almost every class has trivial
    automorphisms" reading does not apply to Dall.
- **The definite class sets do occur, but on the column side.** The Gram kernel is indexed by pairs of lattices Λ ∈
  what₂, Λ' ∈ rows' (finite sets of lattices; `TOP` `GTerm`). The mass Σ 1/|Aut| appears in `MassBasic` and
  `SiegelMassRatio` (`Formalism/HermitianLattices/StatementMass.lean:56-80`). It is the source of the
  e^{−c k f log k} savings in LoopRowS (see §2).
- **The exponential precision of the count comes from the weight and the rank, not from the level.** The
  hypotheses of the count are: HC-parameter gap h ≥ C·n¹⁹·f⁵·log(b·rd), |λ| ≤ b², q² ≤ n, level g ≤ b^A,
  and g₀ > 4n a prime. The proof (`FM/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean:37-49`) is a
  pre-trace formula with the lowest-K-type matrix coefficient (the pseudo-coefficient). It splits the
  geometric side into:
  - the identity term (= D*);
  - near/unipotent terms;
  - far terms, which decay like e^{−h ε²/16};
  - a deep (thin) part of measure ≤ e^{−(1/3) n f log n}·vol, from the volume recursion (`VolumeStep`).
- **The archimedean side is genuinely real-analytic.** OO_t = ∫_{Ω_t} rk1(W_u(x), W_{u'}(γ⁻¹x)) dμ∞ (`TOP:28-30,
  149-152`). Here W_u : G∞ → V_π is a continuous Bessel/Whittaker vector reproduced by convolution with the
  discrete-series matrix coefficient (`IsWu`, `HSet:151-156`). The count also uses real decay estimates for
  discrete-series matrix coefficients (`DecGap`, `EigenfunctionFiniteCoefficients.lean:58-63`). No Fock-model
  algebraisation is visible.
- **RowNG is not "representation numbers = Siegel–Weil average".** It bounds the corank-one non-generic pairs. The
  saving 2^{−(k−2r−5)} is **local**:
  - `LocalNG.NGAt` (`PN:102-105`) requires, at each place p in the non-generic set Om, a local amplitude bound
    ≤ H^{C(r+1)²}·q_p^{−(k−2r−5)}·nn_p with q_p ≥ 2. This is a codimension or local-density gain in the rank k.
  - It is paid against a global height sum `PointSumInput` ≤ e^{C m⁵ f log b}.
  - Siegel–Weil enters only through mass/volume normalisations (`swxs_of_siegelWeil`, giving `MassData`), to
    match with dd = d_u d_{u'}/D*.
  - No spectral gap or Ramanujan input appears on this path.
- **RowMain and the mass-data leaves are assembly lemmas.** `rowFormAllP_of` and `massDataInputsAll_of` combine about
  20 named sub-leaves into an exact identity: the scalar-orbit row norm is c0·c0'·KV = n0c·Σρ rowNorm
  (`RowFormC`, `CokernelGLCounts/MassDataForm.lean:29-35`). The `NormBound` inequality then reads
  Gam1·AA·(c0c0')⁻¹·IntN ≤ d d'/D* (`PN` `NormBound`). I did not reach the bottom of these.

## 1. Statements

### Leaf 4: the dimension count
`row_counts_of_labels_alt` (`TPS/RowCountsOfLabels.lean:13-14`) → `row_counts_of_ties_alt` (`TPS/RowCountsOfTies.lean:12-21`).
The latter gets `c30` and the count from `count_constants_of_siegelWeil hSW` (`FM/CountConstantsOfSiegelWeil.lean:11-24`):
the constants are ⟨Cres=0, n0, A, Cb=0, C=C₀, c=1/16, cb=1/16⟩. The row hypothesis `hrow` (AutTie etc.) is only
threaded through (`hrow.imp`). The count itself is proved for **every** family.

The content is `PointsLemma` (`PlaceDegreeData.lean:364-378`), unfolded from `CountingTheorem`
(`.../SiegelWeilLocal/LatticeCountingTheorem.lean:10-16`):

> For every unitary group G = U(J) of rank n ≥ n₀ over a CM field E/F, of signature (p,q) at every real place with q² ≤ n,
> every discrete series π_v of HC parameter λ_v with gaps ≥ h and |λ_v| ≤ b², every admissible idempotent e of level
> g ≤ b^A with e supported on elements unipotent mod a prime g₀ > 4n (g₀ unramified in E), and every fundamental
> domain:
> if h ≥ C n¹⁹ f⁵ log(b·rd), log f ≤ √n and log log b ≤ n f log n/16, then
> |dim e·Hom_{G∞}(π∞, L²(G(F)\G(𝔸))) − d_π·vol·e(1)| ≤ e^{−n f log n/16} · d_π·vol·e(1).

Downstream, `countOwn_of_rows` (`SHF:661-690`) and `row_count_of_tied_bundles` (`SHF:531-566`) apply this to the
`RowsAut` X that is tied to D. The hypotheses come from `count_parameters_of_hyp` (`SHF:424`), from the standing
`Hyp`. This gives `adm7`: |Dall − D*| ≤ e^{−c n f log n}·D* (`FrobeniusProjectedBounds.lean:105-106`), with n = D.R.r
the full rank.

### Leaf 3: `rowNGP_of_siegelWeil` (`FM/RowPositivityOfSiegelWeil.lean:10-16`)
`RowNGP` (`RowsPos.lean:37-41`): for every D, X, Y and pair of words u, u' under `Hyp0`, `Stand`, `ConcTie` and AbsConv,
`(Y.tO u u').RowNG (epsNG D L C4) (ddC …)`. Unfolded through `PB:126`:

> Gam1·Σ_{(t,t') same row, s0 = 1, both non-generic} Re⟨vec t, vec t'⟩ ≤ 2^{−(k−2r−5)}·e^{C4 m⁵ f log b}·d_u d_{u'}/D*
> (`epsNG`, `RowsConc.lean:49-50`).

Proof: `corankOneNonGenericRowBound_closed` (SWXS, StepChoiceConstantsC, StepPinExists, FormNGC, StepThmBPinnedP) →
`RowNGJoint` (`PN:310-325`). This is an abstract theorem. Its inputs are a class decomposition (Cauchy–Schwarz
within classes), local amplitude bounds `NGAt` with the q^{−(k−2r−5)} gain (`PN:102-105`), a height bound, and a
weighted point sum ≤ e^{CB m⁵ f log b}·Ire. Siegel–Weil is used only through `MassData`/`NormBound` to convert to
dd.

### Leaf 2: `loopRows_of_large_gap_discreteSeries` (`FM/LoopRowsOfLargeGapDiscreteSeriesStatement.lean:16`)
Statement `LoopRowS` (`ThmSOwn.lean:1015-1023`):

> Gam1·Σ_{same row, corank s0 ≥ 2} |⟨vec t, vec t'⟩| ≤ e^{−(1/3) k f log k}·dd, and the same bound holds for the
> generic s0 = 1 non-scalar pairs (`epsL`, `RowsConc.lean:45`).

Proof (`FM/LoopRowsOfLargeGapDiscreteSeries.lean:121-209`): this is glue around
`loopRowBounds_along_family_largeGaps` (`…Statement.lean`). That lemma takes
`SiegelMassRatio` (mass(L_M)/mass(L_{M−1}) = ((M−1)!(v/π)^M)^f·d^{−1/2}·L(M, η^M), `StatementMass.lean:40-80`),
GapIn.Hyp and ThmBpDS, and gives `RowsND ∧ RowsDeg ∧ RowsOne`. It also uses
`stabiliserCovolume_relevantTerm_le_heightPow`.
- *I infer* the mechanism: a pair of corank s involves stabilisers of rank k−s definite sublattices. Their mass
  relative to rank k is ∏ massRatio⁻¹ ≈ ((k−1)!)^{−s f}, which is e^{−s k f log k}. This is the Siegel mass
  formula for definite hermitian lattices, so recognisable.

### Leaf 1: RowMain (`rowFormAllP_of`, `TheoremSClosedP.lean:229-256`; `massDataInputsAll_of`, `TheoremSRecursion.lean:168-185`)
- Both are assembly lemmas. `rowFormAllP_of` combines `absConvC_outright`, `FoldOKC_outright`, `ooIntAll_of`,
  phase agreement, norm representatives, VIndepAtAllP, NormalizingConstantPositiveAll and FormulaC into
  `RowFormC`. `RowFormC` is the exact identity for the scalar-orbit row sum.
- `massDataInputsAll_of` assembles MassData positivity, volumes, product convergence, typed facts and InInfinity.
- RowMain (`PB:128`: scalar-pair sum ≤ (1+δ)e1·dd) then follows from `NormBound`.
- Content: the scalar orbits give the main term = product of local densities × masses, normalised by Siegel–Weil.
  This is a recognisable unfolding / main-term computation. The inequality, not just the asymptotic, is
  `NormBound`, which I did not open.

## 2. Argument for the count (leaf 4), two levels down
`countingTheorem_of_volumeStep` (`FM/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean:37-49`):
1. **DecGap** (from a compression formula for the lowest K-type, `EigenfunctionFiniteCoefficients.lean:47-63`): for gap
   h ≥ 120 n q^{3/2}, the lowest-K-type matrix coefficients satisfy |⟨v,σ(g)u⟩| ≤ decHS(h, q, d(g)) and decE.
   This is real-analytic decay in the weight.
2. **PtBound** (`CuspFrame.lean:15-25`): the kernel φ_e satisfies |φ_e(y)| ≤ d·e(1)·∏_v decHS(…). It is supported in
   K_f, and φ_e(1) = d·e(1).
3. **VolumeStep** (from the Siegel–Weil formula, `SKI:32-46`): the volume ratio U(n)/U(n−1) = massRatioRightSide (the
   Prasad/GHY recursion). It yields:
   - `AbsoluteVolume`, gaugeVol ≤ X^{n² f} (`SKI:125-130`);
   - `FlagMeasureBound`, the measure of the set of points of isotropic type j relative to total volume
     ≤ kapBd·∫dens (`SKI:95-104`). `ConstantBound` gives kapBd ≤ e^{−½(Σj) n f log n};
   - `NonzeroFlagBound`, the thin part (stepLt < ½) has relative measure ≤ e^{−(1/3) n f log n} (`SKI:113-118`).
4. These give the near, far, rare and deep bounds. `discreteSeries_counting_of_finite_and_bounds` combines them:
   Dcount = tr(R_φ) = ∫_fund Σ_γ φ_e(x⁻¹γx).
   - The identity term is D*.
   - The far terms are ≤ … e^{−hε²/16}.
   - The near terms are unipotent (g₀ kills torsion).
   - The deep region is ≤ e^{−n f log n/3}.
   - `FiniteDimensional` and `CuspFrame` provide the finite-rank, cusp-supported image, so the trace is ∫K(x,x).
- This is the classical architecture of limit multiplicity (Savin, de George–Wallach, Shin–Templier), done in
  the weight aspect. The **precision e^{−n f log n/16}, uniform in the rank n, is a strengthening not in the
  literature.** Its shape is plausible: the thin-part measure decays superexponentially in the rank (a Siegel mean-value
  phenomenon), and the weight gap h ≥ n¹⁹ makes the other terms tiny.

## 3. Children

| name | file:line | statement | weight |
|---|---|---|---|
| `GlobalTheory.T.discreteSeries_counting_of_finite_and_bounds` | `FM/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean:49` (use) | trace-formula assembly | core (unopened) |
| `lowestKType_decayGap_of_compressionFormulaGap` (DecGap) | same:40 (use) | discrete-series matrix coefficient decay under gap h | core (unopened) |
| `nonzeroFlagProbabilityBound_of_volumeRatioInduction` (NonzeroFlagBound) | same:47; def `SKI:113` | thin part ≤ e^{−n f log n/3}·vol | core (unopened) |
| `isotropicFlagProbabilityBound_of_volumeRatio`, `flag_explicit_constant_le_exp_neg_half` | same:43,45 | measure of type-j cusp sets | core (unopened) |
| `farBound_of_ptBound`, `nearModerate`, `deepRegion_kernelDiagonal_bound` | same:45-48 | far/near/deep kernel sums | core (unopened) |
| `volumeStep_of_siegelWeil` | `FM/VolumeStepOfSiegelWeil.lean:34` | volume recursion U(n)/U(n−1) from SW | standard (Prasad / GHY mass formula) |
| `loopRowBounds_along_family_largeGaps` | `FM/LoopRowBoundsAlongFamilyLargeGapsStatement.lean` | RowsND/Deg/One from SiegelMassRatio | core (unopened body) |
| `siegelMassRatio` | `…/SiegelMassRatioOfLI.lean:59` | mass ratio of definite unimodular-type hermitian lattices | standard (Siegel / Gan–Hanke–Yu) |
| `RowNGJoint` + `NGChain` (`NGAt`, `PointSumInput`) | `PN:221-325` | non-generic pairs: local q^{−(k−2r−5)} × global height sum | core (local gain unopened) |
| `NormBound` | `PN` (def near top) | Gam1·AA·(c0c0')⁻¹IntN ≤ dd' / D* | core (unopened) |
| `rowFormC_of_leaves3`, `massDataInputs_Y` | `TheoremSClosedP.lean:251`, `TheoremSRecursion.lean:178` | scalar-orbit identity | core (unopened) |

## 4. Oddities
1. **Weight matters for the count but not for the kernel.** The count needs gap h ≥ C n¹⁹ f⁵ log(b rd) while
   |λ| ≤ b² (`PointsLemma`, and `unitaryAutomorphicCounting_unbundled` hypotheses). So the design must use very
   regular discrete series. NODE-THEOREMS's "the weight plays no part" holds only for the Gram-kernel bounds. That
   the D7 data meet this gap is `p9`/`p12` of `CountTheoremHypotheses` (`SHF:424-…`), not re-checked here.
2. **The count is stated universally.** `CountAllPointsClass` quantifies over every `AutInst` and ignores its
   predicate `P` (`count_constants_of_siegelWeil` proves it for every P). It is applied to Dall only via
   `AutTie` (D_eq, Dstar_eq). If no tied `RowsAut` existed, adm7 would never fire. Its existence (`hR`/
   `RowLabelCondition`) is supplied upstream.
3. **"Dall" counts all of L², not only the cusp spectrum.** For very regular discrete series these coincide
   (Wallach), and `CuspFrame` asserts a cuspidal frame. No issue seen.
4. **The constants record has `Cres = Cb = 0`.** Harmless.
5. Statements read literally: none seen false. The count theorem as stated, uniform in n with relative error
   e^{−n f log n/16}, is the strongest claim among the leaves. It is a precise, checkable mathematical
   statement about a non-compact group and should go to an expert.

## 5. Judgement
- **Leaf 4 (count):** a genuine limit-multiplicity theorem for U(p,q)^f with q² ≤ n, in the weight × rank aspect.
  Recognisable method; **strengthening** in precision, beyond published results. Proved in-tree from DecGap,
  volume recursion and flag/thin-part measure bounds, which were not opened.
- **Leaf 2 (LoopRowS):** recognisable. Siegel mass ratios for definite lattices give an e^{−k f log k} cost per extra
  corank.
- **Leaf 3 (RowNG):** a local-density gain q^{−(k−2r−5)} at non-generic places against a polynomial-in-b global
  sum. Recognisable shape. The local lemma is unopened.
- **Leaf 1 (RowMain):** assembly of an exact scalar-orbit identity plus `NormBound`. Content is in unopened sub-leaves.
- Ranked for expansion:
  1. the count's DecGap and NonzeroFlagBound;
  2. NGAt (the local q^{−k} gain);
  3. NormBound;
  4. loopRowBounds body.

## 6. Coverage
Read: `TPS/RowCountsOfLabels.lean`, `TPS/RowCountsOfTies.lean`, `TPS/CountsIrreducibilityConstants.lean:80-120`,
`TPS/RowGood.lean:1-50`, `TPS/LinkROfIsLinked.lean:60-90`; `BCE:1-110`; `FM/CountConstantsOfSiegelWeil.lean`,
`FM/CountTypedOfVolumeStep.lean`, `FM/VolumeStepOfSiegelWeil.lean`, `FM/UnitaryAutomorphicCounting*` (statements),
`FM/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean`; `LatticeCountingTheorem.lean`; `GA:32-260`;
`PlaceDegreeData.lean:364-390`; `DstarEq.lean:10-22`; `SHF:424-445, 531-612, 655-690, 1656-1664`;
`EigenfunctionFiniteCoefficients.lean:40-64`; `CuspFrame.lean:10-45`; `SKI:25-140`;
`FM/RowPositivityOfSiegelWeil*.lean`; `RowsPos.lean:30-60`; `RowsConc.lean:45-56`; `PB:1-140`; `PN:1-110, 150-330`;
`NGAnalytic.lean:1-160`; `FM/CorankOneNonGenericRowBoundClosedStatement.lean`; `TOP:20-160, 230-380`;
`PoincareInHH.lean:240-270`; `HSet:132-200`; `TheoremSClosedP.lean:200-256`; `TheoremSRecursion.lean:150-185`;
`MassDataForm.lean:29-37`; `FM/LoopRowsOfLargeGapDiscreteSeries*.lean`; `FM/LoopRowBoundsAlongFamilyLargeGapsStatement.lean`;
`StatementMass.lean:30-90`.
Not opened: the bodies of `discreteSeries_counting_of_finite_and_bounds`, DecGap's proof, the flag/thin-part bounds,
`rows_along_family`, `NGRowClose.close`, `NormBound`, `rowFormC_of_leaves3`, and `CountTheoremHypotheses` in full.
