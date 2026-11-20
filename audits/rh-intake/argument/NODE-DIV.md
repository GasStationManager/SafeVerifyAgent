# NODE-DIV: the degree bound `LinkDIV_at` (vii) = `WordFacts` clause 3

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
`RB` = `Formalism/LocalToGlobal/Divisibility/RecBridge.lean`, `C28` = `.../Divisibility/ConstantGeTwentyEight.lean`,
`INP` = `.../Divisibility/Inputs.lean`, `DHB` = `.../Divisibility/DivisionHeightBoundStatement.lean`,
`SLB` = `Formalism/QuotientMetricDivisors/ScalarLiftLowerBoundFull.lean`, `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`,
`ZON` = `.../Divisibility/ZscOfNum.lean`, `NUM` = `.../Divisibility/Numbers.lean`, `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`,
`TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`,
`CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`.

## 0. Verdict (short)

DIV is **neither a pure tautology nor a proved covolume theorem**. It is proved in Lean as
the sum of three inequalities plus real-number algebra. After unfolding:

  μ(RR^∨) + h(u) − Fo ≤ MAIN(u) + err

follows by linear arithmetic (`divIneqRecord`, a statement about reals only) from:

- **(A) a base slope bound for the glued lattice RR.** This is a proved theorem, `IndefSide.boundsMu` / `BoundsMu`.
  It gives μ(RR^∨) ≤ meanLog κ + Σ_j l3_j + 2·Fo + local index errors.
- **(B) a covolume bound.** `IndefData.L3`: for each j, lcv(M_j, XW_j)/D ≤ l3_j. On the live path l3_j is **defined**
  (`ZON:64-66`) as Σ_ρ pq_j·w_{jρ}·logΩ + C·B0·log log x. So (B) asserts that **a lattice M_j has log-covolume per
  dimension ≈ pq_j·Σ_ρ w_{jρ}·logΩ**. Here logΩ = γ + log(π/v) − L'/L(1,χ_d). This is a Chowla–Selberg/Colmez-shaped
  statement. On the live path it is **not proved**. It enters as a family-level hypothesis, `CovolumeBoundOfX`
  (`TPS/LiftLambdaBound.lean:60`). That hypothesis is in turn derived from further premises (`LowAt`, a lower bound on a
  slope of a lattice of cusp forms, or a list of "Published.*" Arakelov statements).
- **(C) a height bound for B_u.** htMap(B_u) ≤ hu − meanLog κ, where hu is an **explicit expression containing**
  −Σ_ρ(Σ_i ν_{jρi})·logΩ (`INP:189-197`). It is proved from operator-norm inputs (`HtNums`, `CBData`) that are supplied by
  the hypothesis `RowsU` (`Formalism/LocalToGlobal/PtKOfReal.lean:141`). In those inputs the per-embedding log-periods
  `logOmτ` are free reals; the only constraint on them is that their mean is logΩ (`INP:271`, field `i1`).

The logΩ·a_t term in MAIN comes out as a **net of two large logΩ terms**: +Σ_j pq_j Σ_ρ w·logΩ from (B), and
−Σ_ρ(a_t + k·w + δ)·logΩ from the definition of hu in (C). Since Σ_j pq_j = m·k exactly and |pq_j − k| ≤ m, the k·w·logΩ
parts cancel and −m·a_t·logΩ is left. So (B) and (C) must hold **with the same constant logΩ** to precision
o(|TT|·a·La), where they are individually of size ≈ m·k·b·|logΩ| ≫ |TT|·a·La. In the Lean this coincidence is
arranged by definition (the same `Nd.logOm` appears in l3m, in hB and in `HtNums.i1`). Whether it is true is pushed
into the hypotheses that supply (B) and (C).

## 1. Statement

### `LinkDIV_at` (vii) (`GTI:77-89`, clause 7) = `WordFacts` clause 3 (`RB:128-133`)
```lean
D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u +
    C * (D.host.TT.card : ℝ) * L.sc.a * L.La + C * (D.R.m : ℝ) * (L.B0 + L.Nc) * L.sc.x ^ (Cabs * L.sc.eps)
```
- **μ_dual** = `RR.muDual`. It is tied by `muDual_tie` (`RB:205`) to `P.cols.muCC` = μ(dualLat RR) with metric
  dualFrame XE (`IS:284-285`). μ is the normalised Arakelov slope from NODE-SLOPE §1(b).
- **RR** = `glueLat (fun w => matLat (ι(μ w)) (abelian₂(μ w)))` (`IS:281-282`). It is the O_LL-lattice glued from local lattices
  ι_t(abelian₂ t) at each finite place w, according to a "type" μ(w). The metric XE is a field of `IndefData` (`IS:232`).
  The covolume of RR is **not an input field**. It is computed by (A) from the M_j, the index data and κ.
- **h(u)** = `D.div.h u`. It is pinned twice:
  - `Fm.h_eq : div.h u = hExpl6 …` (`RB:543`);
  - `hTie : (R u).hu − meanLog κ = div.h u` (`RB:637`), proved by `hTie_of` (`RB:445-449`) from
    hu = SZbP + Σ_j kernelPlaceMeanBound − Σ_j L6lo.
- **The RecNums form of h** (`INP:185-197`):
  hu = hA + Σ_j (hB_j − hX_j), where
  - hA = −Σ_{t∈TT} a_t·log T + Ch(…)La;
  - hB_j = Σ_ρ(Σ_i ph(ν_{jρi}) − (Σ_i ν_{jρi})·logΩ) + Ch f Nn²(La + m³L);
  - hX_j = Σ_ρ logH_{jρ} − Ch f nV² Lp.

  ph(y) = y log y − y. ν are the HC-parameter entries, and logH are the log-hook/Γ terms (`NUM:259-267`).
- **Fo** = `L.Fo`, tied by `foTie : 2·FoOfR = L.Fo` (`RB:638`):
  - FoOfR = Σ_j Σ_{y∈Tw} lw(y)·ramw(y)·F0(y, j) (`C28:20-21`);
  - F0 = L.F via `FTie` (`SmallTies.lean:33-34`).

  In the numeric datum, Fo = Σ_j Σ_{p∈suppP} log p·FjP(j, p) (`NUM:209`). For inert unramified p ≤ X'' this is
  FInert = Σ_z (k−1)w_{jz}/(p²−1) (`NUM:170-173`).
- **MAIN(u)** = Σ_t [m(ph(a_t) − a_t logΩ) − a_t log T(u)] (`DP2:232-234`).
- **logΩ** = γ + log(π/v) − L'/L(1,χ_d): `DP2:224`, and the same formula in the numeric datum at `NUM:68`.

### `DivisionPackageFace` (`RB:601-631`) is a **data structure, not a theorem**
Its fields include:
- the indefinite package Pk;
- the identifications eNu, eRR, hNu, hRR, hBk;
- RecNums R u;
- **`inp : DivInputs0R …`**, the analytic inputs, including `L3main`, `HtNums`, `cb`, `nKcb`;
- **`hTie`, `foTie`, `rhs : (R u).rhs ≤ L.MAIN u + …`**.

`DivisionPackageFace.wordFacts` (`RB:635-645`) feeds these into `wordFacts_of_face` → `wordFacts_of_clauses`
(`RB:176-200`) → `wordFacts_of` (`RB:135-157`). The last step of `wordFacts_of` is `linarith` on
`c3 : muC − kap + hu − Fo2 ≤ rhs` plus the ties. The package is supplied, through `pkg_of_rows` (`RecBridgeSel.lean:131`) and
`pt_of_real`/`ptK_of_real` (`PtKOfReal.lean:94,113`), from the hypotheses `hInp : InpAt …` and `hP : CovolumeOntoIsometryConditions`.
`Wire4F.lean:44-84` builds those from `RowsAtSel … DefRowsF` (premises of `Wire4`).

### c3 itself: `DivClausesR` clause 3 (`C28:111-122`), proved in `divClausesR_of` (`C28:184-248`)
  muCC(cols) − meanLog κ + hu − 2·FoOfR ≤ rhs, where
  rhs = Σ_t (m(ph(a_t) − a_t logΩ) − a_t log T) + (50C0+10)|TT|·a·La + 60ce·m·x^ε(B0+Nc) (`INP:200-203`).

## 2. Argument (`C28:221-245`)

1. **(A) `IndefSide.boundsMu`** (`IndefUse.lean:271-292`, using the proved `BoundsMu`, `StatementObj.lean:17`;
   `BaseLevelBoundsWithCovolume.lean:7`):
   μ(RR_base^∨) ≤ meanLog κ + Σ_j l3_j + 2 Fo + LG + Σ_j(E1_j + E2_j) + E3.

   This is generic lattice geometry. Determinant ratios factor as κ^D·∏_j detRatio(XT_j, XW_j, θ_j), and local indices of M_j
   against the θ_j-images give the Fo/E terms. It consumes the hypothesis `S.l3` (i.e. (B)) and `S.on`.
2. **Passage** (`IS:331-345`, field `P.extra.passage`): μ(RR_cols^∨) ≤ μ(RR_base^∨) + 3de(…) + 28la. This adds a loss
   ≤ 1 + C0·m·lam0.
3. **`L3main`** (`INP:448`): Σ_j l3_j ≤ Σ_j Σ_ρ pq_j w_{jρ} logΩ + El3. On the live path this holds **by definition**: `ZON:64-66`
   defines l3m_j as exactly that sum, and `l3main_ofNum` (`ZON:85-92`) is `le_refl`.
4. **`RecNums.divIneq`** (`DHB:131-191`) → `divIneqRecord` (`SLB:52-94`). This is a statement **only about real numbers**.
   It combines the inputs with the RecNums fields:
   - `weight_height_sum_le`: Σ_i ph(ν) − logH ≤ ph(a_t)[ρ∈TT] + eE;
   - `weight_sum_eq`: Σ_i ν = a_t[ρ∈TT] + k·w + δ;
   - |pq_j − k| ≤ m and |logΩ| ≤ La.

   Since Σ_j pq_j = Σ_j (k + 2j − m − 1) = mk (`NumbersLink.lean:574`), the k·w·logΩ terms cancel up to
   m·Σ|w|·La-size errors. What is left is exactly rhs.
5. **Clause 2 (height)**: `height_chain_atR` (`C28:124-182`) + `HtNums.le_hu` (`DHB:107-117`) give htMap(B_u) ≤ hu − meanLog κ,
   from the norm inputs nP, nKcb. Here sz = `liftedMapLogSize` (`DivIneqExplicit6.lean:15-22`) contains
   Σ_τ(Σ ph(ν) − Σν·logOmτ(τ, s)), and `i1` sets mean_s logOmτ = logΩ.
6. `rhs_le_record` (`RB:260-288`): rhs ≤ MAIN + C·errors, using `NumRecTie.mainT` (`RB:250`). MAIN and mainT have the same formula (`NUM:271-273`).

## 3. Answers to (b), (c), (d)

**(b)** DIV is type (ii) in form: it bounds the slope of an actual glued hermitian lattice via a proved determinant
theorem (A). But the step "covolume of M_j ≈ pq_j·Σ w·logΩ", which is where an L-value/period enters, is **not proved**.
- It is `IndefData.L3` with l3 defined to be that expression (`ZON:64`).
- It is supplied by `RowsAt4.covol` (`IndefiniteRealisationChoice.lean:121`) ← `summandL3Bound` (`TPS/RowRRowsOfParts.lean:56`)
  ← `eventual_L3_of_covolume_alt`, whose first premise is `CovolumeBoundOfX` (`TPS/EventualL3OfCovolume.lean:15`).
- `CovolumeBoundOfX` is in turn obtained in two ways:
  - from eight `LiftsCondition` premises (`TPS/CovolXOfSteps.lean:16`), the decisive one being
    `LowAt : −mainT − C·unitE ≤ muCore`, a lower bound for the slope of a lattice of cusp forms with Petersson-type norm
    (`CXC:96`; `AnchorAt`, `CXC:98-100`, ties mainT to Σ_τ(p−q)·anchor·logΩ);
  - or from a list of named "Published" Prop premises (`TPS/TopCovolSlim2Use.lean:16`: Moriwaki, Zarhin, SiegelToroidalIntegral,
    ArDegree, PublishedHodgeBundleTheorems, …).

  I did not trace which route the root uses. Both routes end in Prop premises.
- RR's covolume is computed, not an input. M_j, XW_j and the norm data are fields of the realisation `RealDat3`.

**(c)** The truncated prime sum **never meets the global invariant inside DIV**.
- DIV's right side MAIN is a smooth function of a_t with one global constant logΩ. The only prime-indexed quantity in DIV is
  Fo (log p·w/(p²−1) over inert p ≤ X''). Fo comes from local indices in (A), and it cancels identically against the +Fo in the
  QSB lower bound (NODE-SLOPE oddity 1).
- The comparison "Σ_{inert p ≤ x} … ≈ PNT main term with γ, L'/L(1,χ)" is made only on the prime side: ASK − MAIN is the
  explicit-formula remainder, and Ga is defined from ASK (NODE-LOSS). On the degree side, logΩ is inserted by definition
  into hu, l3 and HtNums.i1. The values of γ, log(π/v) and L'/L(1,χ_d) are not derived from any lattice.
- So the chain is circular **by construction of the constants**, with the real content moved into the hypotheses (B) and (C).
  Those say that actual lattice covolumes and archimedean operator norms realise logΩ with coefficient pq_j·Σw, resp.
  −Σν, to accuracy O(|TT|·a·La) out of ≈ m·k·b·La.
- **Where the x^{1/2} comes from: by counting.** MAIN ≈ m·|TT|·a·log a, while the DIV error is C|TT|·a·La + C·m·(B0+Nc)x^{Cε}.
  The error is relatively O(1/m), and m ≥ x^{1/2−ε} (RestSize). No theorem supplies square-root cancellation here.
  It is assumed in (B)/(C) holding with error independent of m·k.

**(d) Free per-datum fields in this clause.**
- **F**: enters as Fo. Pinned by FTie to Nd.Fj (`NUM:197-204`), an explicit formula chosen by the package builder
  (`fixedScale_tied`, `EigenvalueSumLeClosedOf.lean:350`, not read).
- **gain, E, tau, io**: **absent** from clause (vii). E appears only in clause (viii) (EComp). gain, tau and io appear only in Ga/Ta/IO.
- **h**: a D7 field, pinned to hExpl6 by `Fm.h_eq`, a family field.
- **The free reals on which the truth of DIV actually depends** are not SizeData₂ fields. They are:
  - the realisation data M_j, XW_j, κ;
  - the `HtNums` fields (logOmτ, MainNotions, g0, logh, …; `INP:209-247`), chosen existentially inside `RowsU`;
  - `CBData`.

## 4. Children (ranked)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `CovolumeBoundOfX` (→ `IndefData.L3`) | `TPS/LiftLambdaBound.lean:60`; `IS:290-291` | lcv(M_j)/D ≤ Σ_ρ pq_j w_{jρ} logΩ + C·B0 log log x | core, hypothesis |
| 2 | `LowAt`/`AnchorAt`/`CoreAt` (route 1 of #1), or `topCovolSlim2_use_alt_alt` premises (route 2) | `CXC:92-100`; `TPS/TopCovolSlim2Use.lean:16` | slope of a cusp-form lattice ≥ −mainT; mainT ≈ Σ(p−q)·anchor·logΩ | core, hypotheses (definition to unfold) |
| 3 | `RowsU` (HtNums + CBData + nKcb) | `PtKOfReal.lean:141-160` | log‖K_j‖_v² ≤ sz (contains −Σν·logOmτ, mean logΩ) | core, hypothesis |
| 4 | `BoundsMu` / `slope_bounds` | `StatementObj.lean:17`; `BaseLevelBoundsWithCovolume.lean:7` | glued-lattice slope ≤ meanLog κ + Σ covolumes + local indices | standard-looking (proved, not read) |
| 5 | `Passage` field | `IS:331-345` | slope change base → cols ≤ 3de(…) + 28la | core-ish, a package field |
| 6 | `divIneqRecord` (`divisor_inequality_explicit`) | `SLB:52`; `GlobalBoundRefinements.lean:91` | real-number inequality | glue (proof not read) |
| 7 | `weight_height_sum_le` (RecNums field, from NumFacts) | `INP:106` | Σ ph(ν) − logH ≤ ph(a_t) + eE (Stirling/hook) | standard-looking |

## 5. Oddities

1. **Cancellation of large logΩ terms.** Two hypotheses each carry logΩ with a coefficient about k·w/(a_t) times bigger
   than what survives in MAIN. The surviving m·a_t·logΩ (which is what gives γ and L'/L(1,χ) in the PNT main term) is a
   difference. It is exact only because the same symbol `logOm` is used in both. If the true covolume and the true norm
   constants differed even slightly, the error would swamp the budget.
2. `L3main` is `le_refl` (`ZON:92`): l3 is *defined* as the target bound. The content is in `L3` (child 1).
3. `HtNums.logOmτ` is a free function constrained only by its mean (`i1`). No period is computed.
4. Fo cancels identically against QSB (see NODE-SLOPE). DIV's only prime-indexed term is therefore bookkeeping.
5. Σ_j pq_j = m·k exactly (`NumbersLink.lean:574`). This is what makes the cancellation work. pq_j is a chosen numeric parameter.
6. `DivisionPackageFace` carries `rhs` and `hTie` as fields. On the live path they come from proved ties
   (`rhs_le_record`, `hTie_of`).

## 6. Coverage

Read:
- `RB:1-260, 260-710`; `C28:1-260`; `INP:1-380`;
- `DHB:20-200`; `SLB:1-140`; `IS:150-400`; `ZON:50-100, 230-282`;
- `NumericScaleExponentEqExtended.lean:15-40`; `RecBridgeTied.lean:100-230`; `RecBridgeSel.lean:55-160`;
- `PtKOfReal.lean:1-175`; `InpAtOf.lean:1-60`; `ConstantGeTwentyEightAlt.lean:1-90`;
- `Wire4F.lean:1-110`; `FiniteTOf.lean:15-40`; `IndefiniteRealisationChoice.lean:110-200`;
- `BaseLiftsPackageOfPrimitiveLinks.lean:200-300`; `TPS/RowRRowsOfParts.lean`; `TPS/EventualL3OfCovolume.lean`;
- `TPS/LiftLambdaBound.lean:1-65`; `TPS/CovolXOfSteps.lean`; `CXC:20-135`;
- `NUM:60-70, 165-210, 255-280`; `GTI:40-95`; `SmallTies.lean:30-40`;
- `StatementObj.lean:17-60`; `IndefUse.lean:271-292`; `DivIneqExplicit6.lean:15-22`.

Not opened:
- proofs of `slope_bounds` and `divisor_inequality`;
- `lcv_le`;
- `TopCovolSlim2Use` premises;
- which `CovolumeBoundOfX` route the root uses;
- `NumFacts`, `fixedScale_tied`, `CBHyp`;
- `IndefPkgR` producer `primitivePackageFullHecke`.
