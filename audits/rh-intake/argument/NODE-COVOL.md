# NODE-COVOL: `CovolumeBoundOfX` and its root supplier `topCovolSlim2_use_alt_alt`

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`
- `CGB` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/CovolumeFromGramAndBounds.lean`
- `IPM` = `Development/AbelianVarietyTheory/Definitions/Foundations/IsProbabilityMeasureMuPart.lean`
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`, `ZON` = `Formalism/LocalToGlobal/Divisibility/ZscOfNum.lean`
- `NNC` = `Development/AbelianVarietyTheory/Definitions/Divisors/NormNegCmConstantEqAtAllEmbeddings.lean`

## 0. Verdict (short)

- **Route (c).** The root's `topCovolSlim2_use_alt_alt` does **not** avoid the LowAt route. It is a wrapper. It calls
  `topCovolG_alt_alt` (`TPS/TopCovolG.lean:39`), which ends with `covolX_of_truncation_badSet_lambda_lowBound` (=
  `Assembly.covolX_of_lift_bounds_and_coreLe`, `TPS/CovolXOfSteps.lean:16`). So the two routes the parent saw are one route.
  The "Published" premises are what build the eight `LiftsCondition` inputs, `LowAt` among them.
- **The real content is `LowAt`.** It is a lower bound on the slope of the lattice of integral cusp forms, with
  normalised Petersson metric, on layer i of a tower of unitary Shimura varieties:
  μ(cusp lattice) ≥ −Σ_ρ (p−q)·w_ρ·logΩ − C·B0·log log x.
  It is proved by **descending induction over layers**. The top layer has signature (p, 0), so it is a definite, 0-dimensional
  Shimura set. Each step goes down through "deep covers" Y, using an explicit arithmetic Hilbert–Samuel lower bound (`HSAt`)
  and a flat-line degree formula (`FlatDegree`).
- **logΩ is computed, not only defined, in this subtree.** The geometric input `FlatDegAt` asserts that flat sections on each
  component have arithmetic degree (p−q)/2·logΩ + q(log d − log rd E). It is derived from `FlatDegree_holds`, which uses
  `chowla_selberg_period`: a CM elliptic curve over 𝒪_M with Faltings-type period −meanLog = γ + log(2π/√d) − L'/L(1,χ_d).
  This is Chowla–Selberg. It is proved in the tree, at least down to `exists_cmEllipticCurve_withPeriod` (not opened).
  Separately, `logPeriod_eq_kroneckerCharacter_logPeriod_of_host` identifies `CM.logOm E χ` with the record constant `logOm`.
- **Precision.** The bound is uniform over a family `FamP` (one constant C0 per family, eventually in x), with error
  C·B0·log log x per layer. This is far smaller than the main term (≍ k·Σw·|logΩ|). It is inherited from the explicit errors
  in `HSAt`/`HeightAt` (A·log A + R ≤ C·unitE) and `FlatAt`. Whether a real arithmetic Hilbert–Samuel theorem gives such an
  error uniformly, on varieties that change with x, is exactly what these Prop-level conditions assume or derive. I did not
  reach their proofs (see Children).

## 1. Statement

### `CovolumeBoundOfX` (`TPS/LiftLambdaBound.lean:60-61`)
```lean
def CovolumeBoundOfX : Prop := Closed FamHyp fun Fm CH =>
  ∃ C0 : ℝ, 0 ≤ C0 ∧ EventuallyAtAllPoints Fm fun _ _ _ p => ∀ C, C0 ≤ C → (p.S false).L3 (p.N C CH)
```
- **Quantifiers.**
  - `EventuallyAtAllPoints` (`:18-19`): ∃x0, ∀x ≥ x0, ∀ index ι, ∀ point p with `RowsTAlt p` (= PointConditions' ∧ RecTied).
  - `Closed FamHyp`: the clause holds for every family satisfying the FamHyp list. Not unfolded; see NODE-THETA.
- **`L3`** (`IS:315-316`): ∀ j, lcv(XW_j, M_j)/D ≤ N.l3 j.
  - `IndefScale.num` (`IS:228`) gives N.l3 j = l3m j + C·l3u.
- **`lcv`** (`Formalism/SizeWindowBrackets/SBrDiv.lean:339`): (2/[K:ℚ])·log ht(M), the normalised log-covolume of the
  𝒪_K-lattice M ⊂ K^d. The metric is the hermitian Gram matrices XW_j at the infinite places. K = `D.what₂.LL`, a totally
  complex field.
- **Live constants.** `lcv_le`'s conclusion (`CGB:43`) has the form mainT + C·unitE. Here
  - mainT = `p.Z.l3m i`,
  - unitE = `p.Z.l3u` (`CXC:22-24`).

  For the numeric scale (`ZON:64-66`):
  - **l3m j = Σ_ρ (k + j − 1 − (m − j))·w_{jρ}·logΩ**, and (k+j−1) − (m−j) = p_j − q_j, the signature difference
    (`AnchorBoundStatement.lean:105-117`);
  - **l3u = B0·log log x**.

So, as mathematics: for all large x and every admissible datum,

  (1/D)·log covol(M_j) ≤ (p_j − q_j)·Σ_ρ w_{jρ}·logΩ + C·B0·log log x,  where logΩ = γ + log(π/v) − L'/L(1,χ_d).

This is an **upper bound on log-covolume**, i.e. a lower bound on arithmetic degree (there are many small vectors). It is
one-sided. The error is additive, C·B0·log log x per layer, with C independent of x, of the datum and of the layer.

### What M_j is (via `RecAt`, `CXC:57-59`, and `muCore`, `CXC:51`)
`RecAt` says lcv(M_j)/D ≤ −slope(nrmR, latGood). `CoreAt`/`LowAt` then pass to

  `muCore = slope_sq (nrmK p.fw i) (latTypeK p.fw p.F.lv2 i)`.

Unfolding:
- **`latTypeK`** (`NNC:286-288`): `latW (T.U (i+1)) (wtZ (wtA κ_i) n)` intersected with the span of the cusp forms of
  "type K" (`typeK`, `NNC:271`). So it is the 𝒪_F-lattice of **integral cusp forms of vector weight (wtA κ_i, n)** on the
  layer-(i+1) moduli space `T.Q.Xo (i+1)` over the coefficient field F = `T.Q.c.F`, cut down to a type subspace.
  - `cuspW` (`IPM:425-427`): algebraic sections of weight G (`secZ`) whose restriction to every good complex uniformisation
    is holomorphic.
  - `latW` = `supLat` (`IPM:570-586`): sections with v(f) ≥ 0 for every valuation in `valSet Xo c (algCls …)`. I infer these
    are integrality conditions along the special fibres or divisors of a model.
- **`nrmK`** = `normW` = `petW` (`IPM:787, 802`). This is petAt = lieFacZ(x, G)·‖f‖_{L²(AutQ V, μ)}, with:
  - lieFacZ = (2πx)^{−|G|/2} (`IPM:664-665`);
  - x = `xiR D` = ‖φ₀(ξ₀)‖ (`Formalism/LocalToGlobal/ProjectiveLattices/CuspidalL2Subspace.lean:35`);
  - μ the **probability** measure `muQ1` on the adelic quotient.

  So the metric is a Petersson L² norm with volume normalised to 1 and a (2πx)^{−weight/2} factor.
- **Group, level, weight.**
  - Layer i+1 has signature (p, q) = (k + i, m − i − 1) (`AnchorBoundStatement.lean:98-110`, via `WtRead.sigW`), with
    p + q = r. It is a unitary group over the CM field E of the host.
  - Weight: wtA(κ_i) with parameter n; κ_i comes from the HC data. Level `l` is inside `T.Q`; I did not unfold it.
  - **Top layer, i+1 = m: q = 0** (`CoveringLowDefectBound.lean:41-42`). That is a definite unitary group, so a 0-dimensional
    Shimura set.

## 2. Argument

### Level 1: `topCovolSlim2_use_alt_alt` (`TPS/TopCovolSlim2Use.lean:16-22`)
It packages its 15 premises into four structures and calls `topCovolG_alt_alt`:
- `HypothesesX`: ToroidalForFanKS, SemiAbelianLieSeminegative, a proved Green-regularity lemma, PointSeparationPair, and the
  Fubini–Study/Chow height formula from `hP`;
- `HypothesesH`: SiegelToroidalIntegral, toroidal charts, ArDegree;
- `VolumeEstimateHypotheses`: a proved Chow-form comparison, and `small_sections_injective`;
- `HSCore.Quoted`: from `hP.q6, q8, q13, q7, q10` plus proved lemmas;
- `DeepStR`: from `HtPt.Ah.deep_slim_use h₁ h₂ hPL hU hBig hFar hZar hRR`. This is where resolution, principalisation,
  Poincaré–Lelong, `hsUse_outright` (arithmetic Hilbert–Samuel), `moriwakiBig_outright`, Fargues, Zarhin and NefRR are used.

### Level 2: `topCovolG_alt_alt` (`TPS/TopCovolG.lean:39-61`)
It builds the eight `LiftsCondition`s and applies `covolX_of_lift_bounds_and_coreLe` (`TPS/CovolXOfSteps.lean:16-40`). That
calls `lcv_le` (`CGB:39-89`) pointwise. `lcv_le` is a chain of four inequalities:

1. **RecAt.** lcv(M_j)/D ≤ −μ(latGood).
2. **Cut/Bad/Lam/Size** (`CutNum.slope_good_ge`). μ(latGood) ≥ μ(latType) − 12e^{−x^{ε/7}}·(x^A + x^B + C')·unitE. This uses:
   - eGood is an orthogonal idempotent with |G_p|·eGood(latType) ⊂ latType (CutAt);
   - rank(latBad) ≤ 3e^{−x^{ε/7}}·rank (BadAt);
   - μ_max ≤ x^A·b (LamAt).

   The loss is ≤ unitE for large x (`exists_loss_le`).
3. **CoreAt.** μ(latType) ≥ muCore − C1·unitE. This compares the realised lattice with the cusp-form lattice, using MeasAt (the
   norm is c·petW with |log c| ≤ C·unitE) and RatAt.
4. **LowAt.** muCore ≥ −mainT − C2·unitE.

Result: lcv/D ≤ mainT + (C1 + C2 + 1)·unitE. Steps 1–3 are lattice bookkeeping with exponentially small losses. **All the
arithmetic is in LowAt.**

### LowAt (`liftLowBound_of_cover_estimates` = `LowCover.low_of_cover_hypotheses`, `TPS/LowOfCoverHypotheses.lean:16`, proof not read)
Its premises are Size, LowDef, DeepEx, DeepGood, Ring, Maps, Rk, Gmin, Flat and ULow. From the definitions (`CXC:104-159`) the
shape is a descending induction on the layer:
- **Base, top layer q = 0 (`LowDef`, `CoveringLowDefectBound.lean:17-49`).** From Gram, Anchor and
  `two_mul_defBound_sub_le_muCore_of_gramAt hP`: muCore ≥ (a "definite bound") ≥ the anchored main term minus crude errors
  (`two_definiteBound_ge_anchoredMainTerm_sub_crude_errors`). On a 0-dimensional definite Shimura set the cusp forms are
  functions on finitely many CM points, so the slope is a CM-period computation. I infer this; I did not open the lemma.
- **Step, layer i < m−1.** Choose a good deep cover Y (DeepEx, DeepGood). Then:
  - RingAt: μ(latDeep Y) − 2b ≤ muCore.
  - MapsAt and RkAt: n maps φ_h from weight Gs(−c0) to Gk, jointly injective, of norm ≤ e^b, with controlled ranks. These give
    μ(Gk on Y) ≳ μ(Gs(−c0) on Y).
  - FlatAt: μ(Gs(−c0)) ≥ μ(wtOf uM 0) − mainT − C·unitE. Twisting by flat sections of degree flatDegVal is how
    −Σ(p−q)w·logΩ enters.
  - UAt: μ(wtOf uM 0) ≥ −C·unitE. This comes from the arithmetic Hilbert–Samuel package (SumAt, HSAt, HeightAt, DegAt, ShareAt;
    `uniform_lower_bound_of_sums'`, `height_lower_bound_general_alt`, `hilbertSamuel_of_component_estimates_alt`
    `TPS/HilbertSamuelLowerBoundOfComponents.lean:24`).
  - `AnchorAt` (`CXC:98-102`) is **proved outright** (`anchor_holds_alt`, `TPS/AnchorHolds.lean:20`; `anchorAt_of`,
    `AnchorBoundStatement.lean:77`). It is arithmetic: mainT equals Σ_τ(p−q)·e_i·logΩ **by `show`, i.e. definitionally**
    (`:112-117`), and the anchor weights are bounded by 4b.

### Where logΩ is computed
- `FlatDegAt p i Y := FlatDegree Y.U (xiR D) (ofRecord …).logOm` (`CXC:133`).
- `FlatDegree logOm` (`ExistsFlatSecRankZero.lean:754`): on every component Z and for every τ there is a flat section, and
  every flat section s has arithmetic degree = (p−q)/2·logOm + q·(log d − log rd E) (`flatDegVal`, `:751`).
- Supplied by `flatDegAt_of_st` (`DivisorProofs/FlatDegreeStatement.lean:15-24`) from:
  - `FlatDegreeSt` (`HtValOnSubset.lean:131`), which has `CM.logOm E χ` with CM.logOm = γ + log(2π/rd E) − L'/L(1,χ)
    (`CMLattices/ExistsIsThetaDegOfIsLocalModel.lean:23-25`);
  - `logPeriod_eq_kroneckerCharacter_logPeriod_of_host`: (CM.logOm E χ).re = record logOm = L.logOm.
- `FlatDegreeSt` is obtained by `flat_tensor_swap_isIso` (`HodgeBundleWeights/FlatTensorSwapIsIso.lean:7-8`). That proof
  **ignores its three premises** (PublishedHodgeBundleTheorems, CanonicalExtensionRankOne, PrismaticDieudonneHodge) and uses
  the chain
  `flatDegreeSt_of_resK resK` → `flatDegreeSt_of_resK_gaga` → `exists_constSec` → `kronecker_character_frame_bound` →
  `degree_of_flatOnModel` → `TopLL.degree_frames FlatDegree_holds`.
- `FlatDegree_holds` = `Fl.flatDegree` (`GeometryProofs/FlatDegreeHolds.lean:60-118`) uses:
  - `chowla_selberg_period` (`GeometryProofs/ChowlaSelbergPeriodStatement.lean:9`): for ρ² = −d there is a CM elliptic curve
    with period x = γ + log(2π/√d) − L'/L(1,χ);
  - `frame_function_cm_value/height` and `hermitian_metric_log_norm_formula`.

  `chowla_selberg_period` = `exists_curve0_hasPeriod` (`ChowlaSelbergPeriod.lean:18-43`), which rests on
  `exists_cmEllipticCurve_withPeriod`, `abelianSchemeLaws_all`, `thetaUnifAV_closed` and `card_torsion_points_unconditional`.
  None of these was opened.

**So yes: a Chowla–Selberg-type computation exists in the tree and is on the live path.** It enters through FlatDegAt → FlatAt
→ LowAt. It concerns CM elliptic curves (a degree-1 Faltings-height or period formula for ℚ(√−d)), transported to flat line
bundles on unitary Shimura varieties. It is not a Kühn / Bruinier–Burgos–Kühn arithmetic volume of the Hodge bundle. The
"volume" side is handled by the HS package instead.

## 3. Answers to (a)–(d)

**(a)** See §1.
- It is an **upper bound on normalised log-covolume** (lower bound on slope).
- It is **uniform**: one C0 per FamHyp family, valid for all x ≥ x0 and all points of the family. The error is additive,
  C·B0·log log x per layer.
- Relative to the main term, which has size ≍ (p−q)·Σw·|logΩ| ≥ k·|logΩ|, the error is O(B0·log log x/(k·|logΩ|)). The DIV
  budget absorbs m·C·B0·log log x inside C·m·(B0+Nc)·x^{Cε} (`DivisionHeightBoundStatement.lean:848-859`).
- That precision is not derived from an asymptotic Hilbert–Samuel theorem in the weight. It is **built into `HSAt`** as an
  explicit, effective inequality: binT·deg·(lenT·ht − 3(dim+1)|ht| − A·log(2+|ht|) − R) ≤ degC, with A·log A + R ≤ C·unitE
  (`CXC:153-156`). It is supplied by `hilbertSamuel_of_component_estimates_alt` from `exists_degree_parameters_bound_alt_alt`,
  `twisted_bundle_degree_lower_bound`, PublishedHodgeBundleTheorems, etc.
- An effective HS lower bound with error O(log log x), uniform over Shimura varieties whose degree and conductor grow
  polynomially in x, goes **well beyond** any published arithmetic Hilbert–Samuel or Moriwaki-bigness theorem. Those are
  leading-order in the weight for a fixed variety. Whether the tree's `ArithHilbertSamuel`/`HSUse` premises are stated
  effectively and uniformly enough to yield it is the key thing to check one level down. I did not read them.

**(b)** See §2.
- logΩ is **computed** via `chowla_selberg_period` (CM elliptic curve period). This computation is what is used, through
  `FlatDegree`.
- The match between the record constant (π/v form) and CM.logOm (2π/rd E form) is a separate proved identity.

**(c)** The root uses `topCovolSlim2_use_alt_alt`, and that is the LowAt/AnchorAt route: `topCovolG_alt_alt` ends in
`covolX_of_truncation_badSet_lambda_lowBound`.
- AnchorAt is proved arithmetically.
- LowAt is derived from covers + HS + FlatDegree.

**(d)**
- `mainT` equals Σ(p−q)·w·logΩ **by `show` (definitional)** (`AnchorBoundStatement.lean:112-117`). AnchorAt is therefore
  bookkeeping, not content.
- `L3main` is `le_refl` (parent, `ZON:92`).
- `flat_tensor_swap_isIso` discards its premises (`FlatTensorSwapIsIso.lean:7-8`), so the Published hypotheses named there are
  vacuous inputs.
- `PublishedHodgeBundleTheorems.q2/p18/q12` are proved lemmas that ignore `_h` (`HodgeBundleWeights/ToKnownTheoremsOf.lean`).
- The top layer is a **0-dimensional (definite, q = 0) Shimura set**. This is legitimate in itself, but the whole bound is
  anchored there.
- `slope_sq` is defined as **0 when no Gram frame exists** (`IPM:32-35`). GramAt supplies HasGram for nrmR, but not explicitly
  for nrmK, so muCore could in principle be the junk value 0. I did not check whether nrmK has a Gram frame on the live path.
- `SizeAt` (`CXC:75-79`) requires b ≤ unitE = B0·log log x, which ties the scale b to B0·log log x.
- No `True`-valued field was seen on the live path in the files read.
- No equality of a covolume with an asymptotic formula was seen. `FlatDegree` *is* an exact equality: deg(flat section)
  = (p−q)/2·logΩ + q(log d − log rd E). That is the right kind of statement for flat (torsion/unitary) line bundles, where
  Chowla–Selberg is exact.

## 4. Children (ranked)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `LowCover.low_of_cover_hypotheses` | `TPS/LowOfCoverHypotheses.lean:16` | Size+LowDef+covers(Ring,Maps,Rk,Gmin,Flat,ULow) ⇒ muCore ≥ −mainT − C·unitE (descending induction) | core (proof not read) |
| 2 | `hilbertSamuel_of_component_estimates_alt` (HSAt) and `height_lower_bound_general_alt`, `uniform_lower_bound_of_sums'` | `TPS/HilbertSamuelLowerBoundOfComponents.lean:24`; `TPS/HeightLowerBoundGeneral.lean:21`; `TPS/ULowOfStatement.lean:11` | effective arithmetic HS lower bound with error ≤ C·B0 log log x, uniform in the family | core: precision lives here |
| 3 | `covering_low_defect_alt` / `two_mul_defBound_sub_le_muCore_of_gramAt` | `TPS/CoveringLowDefectBound.lean:17` | top (definite, q=0) layer: muCore ≥ −mainT − C·unitE | core |
| 4 | `chowla_selberg_period` → `exists_cmEllipticCurve_withPeriod` | `GeometryProofs/ChowlaSelbergPeriodStatement.lean:9`; `ChowlaSelbergPeriod.lean:18` | CM elliptic curve with period γ + log(2π/√d) − L'/L(1,χ) | standard (Chowla–Selberg); proof to unfold |
| 5 | `Fl.flatDegree` / `FlatDegreeSt` / `flatDegAt_of_st` | `GeometryProofs/FlatDegreeHolds.lean:60`; `HtValOnSubset.lean:131`; `DivisorProofs/FlatDegreeStatement.lean:15` | flat sections have arithmetic degree (p−q)/2·logΩ + q(log d − log rd E) | core-ish (transport of 4) |
| 6 | `flat_of_prints_deepGood_flatDeg_anchor` (FlatAt) | `TPS/FlatBoundOfAnchor.lean:50` | μ(Gs(−c0)) ≥ μ(wtOf uM 0) − mainT − C·unitE | core (not read) |
| 7 | `deep_slim_use` (consumer of hsUse_outright, moriwakiBig_outright, resolution, …) | called at `TPS/TopCovolSlim2Use.lean:22` | produces `DeepStR` | core (not read) |
| 8 | `lcv_le`, `slope_good_ge` | `CGB:39`; `CutNum` | lattice bookkeeping, steps 1–3 | glue (read) |
| 9 | `anchorAt_of` | `AnchorBoundStatement.lean:77` | mainT ≡ Σ(p−q)e·logΩ (definitional); anchors ≤ 4b | glue |
| 10 | `logPeriod_eq_kroneckerCharacter_logPeriod_of_host` | `DivisorProofs/LogPeriodEqKroneckerCharacterLogPeriodOfHostStatement.lean:9` | CM.logOm(E,χ).re = record logOm | glue (proof not read) |
| 11 | MeasAt/CoreAt suppliers (`covering_meas_of_prints`, `coreLe_of_gram_meas_liftRational`) | `TPS/TopCovolG.lean:48,60` | realised norm = c·Petersson, |log c| ≤ C·unitE | core-ish (not read) |

## 5. Oddities

1. Route 2 is route 1: the "Published" list is consumed only to build the LiftsConditions.
2. `flat_tensor_swap_isIso` takes three hypotheses and uses none of them.
3. mainT is *definitionally* the target expression. All of the truth sits in LowAt.
4. Precision: the claimed error O(B0 log log x) per layer, uniform over a growing family of Shimura varieties, has to come from
   an effective uniform arithmetic Hilbert–Samuel. No published theorem gives that. Check how `ArithHilbertSamuel` / `HSUse` /
   `exists_degree_parameters_bound_alt_alt` are stated.
5. `slope_sq` returns 0 when there is no Gram frame (`IPM:32-35`). This is junk-value risk for muCore.
6. The norm includes the factor (2πx)^{−|weight|/2} with x = ‖φ₀(ξ₀)‖, and a probability-normalised measure. These
   normalisations are absorbed into logΩ bookkeeping. I did not check their consistency with `flatDegVal`.

## 6. Coverage

Read:
- `TPS/LiftLambdaBound.lean:1-65`; `TPS/EveryCharacterOfLiteratureOfVWin.lean:790-814`; `TPS/TopCovolSlim2Use.lean` (all);
  `TPS/TopCovolG.lean` (all); `TPS/CovolXOfSteps.lean:1-40`;
- `TPS/{AnchorHoldsStatement,SizeAltBisStatement,CovolXOfStepsStatement,LowOfCoverHypothesesStatement}.lean`;
  `TPS/AnchorHolds.lean`; `TPS/SizeAltBis.lean:1-30`;
- `TPS/CoveringLowDefectBound.lean:14-60`; `TPS/FlatDegreeStatement.lean:12-30`;
  `TPS/HilbertSamuelLowerBoundOfComponents.lean:20-60,120-140`;
- `CXC` (all); `CGB:15-140`; `AnchorBoundStatement.lean:77-117`;
- `IS:195-320`; `ZON:50-100`; `SBrDiv.lean:330-345`;
- `IPM:1-45,400-440,570-680,725-816`; `NNC:230-300`;
- `ExistsFlatSecRankZero.lean:720-800`; `HtValOnSubset.lean:90-140`; `DivisorProofs/FlatDegreeStatement.lean`;
  `LogPeriodEq…Statement.lean:1-12`; `ExistsIsThetaDegOfIsLocalModel.lean:15-40`;
- `HodgeBundleWeights/{ToKnownTheoremsOf,FlatTensorSwapIsIso,FlatDegreeHypotheses}.lean`;
- `FlatSlim.lean`; `PlugResK.lean`; `FlatDegreeStOfResKGaga.lean`; `ExistsConstSectionKroneckerChar.lean:40-80`;
- `KroneckerCharacterFrameBound{,Statement}.lean`; `GeometryStatements/FlatDegree.lean`;
  `FlatDegreeHolds{,Statement}.lean`; `ChowlaSelbergPeriod{,Statement}.lean`.

Not opened:
- `low_of_cover_hypotheses` proof;
- `two_mul_defBound_sub_le_muCore_of_gramAt`;
- `deep_slim_use`; `hsUse_outright`; `moriwakiBig_outright`;
- `exists_degree_parameters_bound_alt_alt`;
- `exists_cmEllipticCurve_withPeriod`;
- FamHyp; `RecAt`/`MeasAt`/`CoreAt` suppliers;
- `resK_of_weak`; `gagaSections`.
