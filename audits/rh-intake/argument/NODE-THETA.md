# NODE-THETA: `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound`

Paths are relative to the source root. Abbreviations (as in NODE-ROOT):
`TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`,
`WTM` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean`,
`GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`,
`ROWS` = `Formalism/LocalRingCardinality/DataRows.lean`.

## 1. Statement

The Lean says (`TPS/SiegelEisensteinSecondTermHypotheses.lean:44`):

```lean
theorem nonempty_hyps_definite_side_of_closed_bound :
  UnitaryGroupThirdPlaceHypotheses → ThetaLocalInputs → ThetaIntegralsAgree → LocalMatching →
  CovolumeBoundOfX → ∀ (hL : RecTExists),
  (∀ cDep : ℝ, LinkedAt (parametersOfDependence hL cDep)
      (fun Q L => SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoThreeFamilyFonAlt Fm)) →
  Nonempty (HypsAlt S0.NL DefiniteSideCondition)
```

`S0.NL 𝒞 := Closed 𝒞 (fun Fm _ => LinkN Fm)` (`Development/AbelianVarietyTheory/Definitions/GlobalTwisting/GeometricWeakTiesOfStrong.lean:36`).
So the conclusion is exactly the `HypsAlt (fun 𝒞 => Closed 𝒞 LinkN) DefiniteSideCondition` that NODE-ROOT needs.

In words: given (i) a bundle of about 60 "published" automorphic and Galois facts (P), (ii) 16 local
representation-theory facts (F), (iii) a global theta-integral identity package and a local matching statement for pairs of
unitary dual pairs (hA, hM), (iv) a lattice covolume bound (hX), (v) existence of a local Langlands map (hL), and (vi) a
"bound at the places 2 and 3" for all families, there is a family class 𝒜 with a raw selection σ that carries all ~45 side
conditions of `HypsAlt` (listed in (a) below). The last field is that every large family in 𝒜 (after the `D3 3` refinement)
satisfies `LinkN`.

### (a) The fields of `HypsAlt` (`TPS/Hyps.lean:22-90`), grouped

Every field quantifies over families `Fm : FamP eps` in 𝒜 (or over `D3 3 𝒜`, `WithTw (WithSm (WithChN 𝒜))`), scales x
past `Fm.x1`, and indices `i : Fm.Ix x`, either "for all" or under `Closed` (eventually for large families). The datum
`Fm.D x i : D7` is a number-field "host" together with an abstract `Rows.Data` record (`ROWS:36-170`). That record holds
finite-dimensional inner-product spaces EE, Amb μ, a tower Mult μ 0..m with maps `io μ j : Mult μ (j+1) → Mult μ j`, the
composite `iota μ : Amb μ → EE` (`ROWS:184-186`), "theta" maps `thetaP μ j : Mt μ j → Mj j`, period pairings `Bu u`,
lattices `OLat` (finite generating sets), places, exponents `etaJ j w ∈ ℚ≥0` and Sha-lengths `shaLen l e`.
*Note*: these spaces are abstract. Nothing in `Rows.Data` ties them to automorphic forms. Any link has to come from the
HypsAlt fields or from the parts of D7 that I did not open.

1. **Structural/selection data (glue):** `𝒜`, `σ`, `cT`, `c30`, `cIc`, `hcI : 0 < cIc`, `hc30` (constant inequalities),
   `hServ` (selection serves 𝒜), `hduty`.
2. **Existence:** `hEx : MinkDiv → ExS 𝒜 cT` (`CharacterBoxes/ExS.lean:10`). For every la > 1 and requirement G with
   `HostExW la G.req`, "design choices" exist in the class `WithTw (𝒜 ∩ G.cls la)`. `MinkDiv` = ∀n, MinkMult n (minkM n)
   (`GlobalTwisting/AuxiliaryPrimeMemAvoidedPrimes.lean:22`). *I infer* MinkMult is a Minkowski-type divisibility of a group order.
   This is the only field that carries non-emptiness of the class (see NODE-ROOT oddity 8).
3. **Uniform "literature" Props quantified over all D7:** `hLit : LitThin` (`GlobalSchurBounds/MainSup.lean:88`; for all D7,
   short-interval prime admissibility statements adm6/adm7/adm11 with uniform constants), `hWu : WuDecayOfGap`
   (`…/WuDecayAll.lean:25`; for all D with GapHyp and every Hida setting X, WuDecay X and integrability of X.ph),
   `hRF : RowsFinDim`, `sTy/sNG/sM` (row positivity / RowNG / RowMainEq, the last two "of Siegel–Weil"),
   `hU : ∀ D, MassRatioUnderVolume D` (VolTie D → VolumeRatio₂ D), and
   `hG : ∀ D, GenusMassAt D 2` (`GL5/DiscreteSeriesOfFormalDegree.lean:112`): for every totally definite hermitian space W of rank 2
   over the host CM field, mass(W, L0) = massI D 2. *I infer* that this is the **Siegel mass formula for rank-2 definite hermitian
   lattices**, a standard result (Gan–Hanke–Yu / Prasad volume formula).
4. **Indefinite-realisation / row / twist side conditions, per (x, i):** `hRB` (indefinite realisation has bounded rows), `hTw`
   (`TieTwRec`, `Formalism/LocalToGlobal/Divisibility/LinkDefN.lean:36`: each twisted place y lies in the support and has
   μ_y ≠ μ0), `hPA` (PrimRows3, TypesSep3), `hLamP` (RowsHoldLam3), `hDivG` (DivRows3G), `hDcPtG`, `selJ`
   (IndefiniteRealisationJoin), `zL` (a projection `lPrj … .mulVec` is surjective for every k < m), `rRows`
   (`SelectionDefiniteRows DefiniteSideCondition`). Not unfolded.
5. **Arithmetic-geometry: lattices, volumes, class numbers, counting:** `hTu` (TuSize when cT ≤ CTu), `hn4` (class-number formula
   ClassNumberFormula₂ at each datum), `hTF` (a TFrame bound with exponents 1/4, 1/2, 3), `h30` (CountAllPointsClass with the
   c30 constants), `hInstR` (VolSigIndep and ClassItemsAt: genus/mass volumes), `irrC` (label count injective, AllJoin, CountAllRows
   at εC(cIc, r, f)), `aAtG` (used tuples bounded by a constant, family size bound at the type prime), `aC2`.
6. **Statements about the theta tower inside `Rows.Data`:** `jOn` (eventually `(V0 μ0).map (iota μ0) = ⊤`: the iterated
   down-map from the top layer Amb μ0 = Mult μ0 m to EE is onto on the image of the idempotent eOp), `hMt` (the lattice
   M̃ μ is stable under O_LL), and the period/point clauses `aPt0, aPtTw, aPer0, aPerTw, aP10` (Conclusion5Sharp/6,
   TwistedPointIntegral, PeriodClassSumWeyl, TwistedPeriodAdmissible, TwistedColumnBoundAtT), together with `tie`
   (RealPlaceSecondLayerConditions). None of these mentions a unitary group or a theta lift in its statement. They are
   properties of the abstract record.
7. **Theorem-S selections:** `sLp` (LoopRowS 3) and `sO` (TheoremSSelected Fm 3).
8. **`nRest : Closed (D3 3 𝒜) LinkN`** (unfolded in (c)).

No field of HypsAlt states Siegel–Weil, Rallis, seesaw or a theta lift between named unitary groups. The theta inputs are
consumed while the record is built, not stored in it.

### (b) `ThetaIntegralsAgree` and `LocalMatching` (`WTM:581-592`)

Setting (`WTM:140-395`): F is a number field and E/F is CM, Galois over ℚ and unramified over F (`Base.IsGood`, `:350`). ψ is a standard additive
character. V is a hermitian space of dimension a and signature (a−p, p), V′ is hermitian of dimension a′ and signature (q, a′−q), and W is
skew-hermitian of dimension a+a′ (`Geo.IsGood`, `:360`). The conditions are a′ < a, a+a′ even, κ: a+a′ < mα−mβ at every infinite place, and
2(p+q)+1 < min(a′, (a−a′)/2). That is, V and V′ are *nearly definite*: p, q are small, and p = q = 0 gives totally definite spaces.
X = (α, β, S₀, Q) are Hecke characters of E with prescribed restrictions to F^× (η^{a′}, η^{a}), infinity types, and ramification
exactly on T = S₀ ∪ Q, with ν = α/β (`Chars.IsGood`, `:374`). ω and ω′ are Weil representations of U(V)×U(W) and U(V′)×U(W),
split by (β, β/α) and (α, α/β) (`IsTriple`, `:388`). The theta integral is I(Φ)(h) = ∫_{[U(V)]} θ(g,h;Φ) dg (`:288`).

- **LocalMatching** (`:581`): for every such triple there exist "real maps" R and "finite maps" Rf with `IsMatched`
  (`:493`). Here Rf gives, at each finite v, a nontrivial irreducible common quotient Π_v of the U(W_v)-coinvariants of both local Weil
  representations. It is U(W_v)-equivariantly compatible, sends the spherical vectors to the same nonzero vector off T, and at the places in T is
  given by an explicit zeta-integral matching (`IsZetaAt`, bigP = smallP). R gives the same at infinity on polynomial
  Fock vectors (`IsRealMaps`, `:433`). *I infer*: this is the **local theta dichotomy / "complementary spaces" statement**. The
  big theta lifts of the characters from U(V_v) and U(V′_v) to U(W_v) share an irreducible quotient, which is the
  Kudla–Rallis / Lee–Zhu / Gan–Ichino (local second-term) picture for unitary groups, with character twists.
- **ThetaIntegralsAgree** (`:585-592`), three parts:
  1. `Decay` (`:498`): the U(V)-theta integral converges for all Schwartz Φ. The U(V′)-theta function on SoLoc vectors is
     rapidly decreasing in g and of moderate growth in h, and I′(Φ′) is of moderate growth.
  2. For matched (R, Rf): `OneConst` (`:503`). Some I′(Φ′) ≠ 0, and there is a *unique* c with I(Φ) = c·I′(Φ′) for all
     matched Φ ↔ Φ′ (`IsConst`, `:491`); this c ≠ 0. Also `Coinv` (`:507`): local coinvariants are described exactly by the
     kernels of Rf. *I infer*: this is a **global second-term-type identity**. The theta lift of the character from the
     larger space U(V) equals a nonzero constant times the lift from the complementary smaller space U(V′), for matched
     data. That is the shape of the regularised Siegel–Weil "second term identity" (Gan–Qiu–Takeda 2014, for trivial
     character; Kudla–Rallis for orthogonal/symplectic). Here it is in the convergent range, with Hecke twists α, β.
  3. `StepBeta` / `StepAlpha` (`:559-579`): *tower relations*. If one passes from (V′ of dim b+2, W) to (dim b) by splitting off an adapted hyperbolic
     plane H (`Plane.IsAdapted`, `:532`), the constants satisfy c·L^{S₀}(ν, (a−b−2)/2 + 1) = u·c₁, where u is the inverse of a nonzero C times
     an explicit ε-factor/ideal-value product `stepFac` (`:552`). StepAlpha does the same on the V side, with L^{S₀}(ν, (b+2−a′)/2). *I infer*:
     this is the Rallis tower / doubling-type recursion. The ratio of consecutive theta constants is a partial Hecke L-value.
  - **Known in this generality?** This is my judgement, not something the Lean says. The pieces are standard in spirit (Weil's convergence,
    Howe duality, Kudla–Rallis–Gan–Qiu–Takeda second term identity, the doubling method). A single theorem with all the clauses
    (character-twisted, unique nonzero constant, explicit tower factors with partial L-values at these points, for every CM E/F
    unramified) is not a statement I can match to one published result. Treat it as "standard?", needing an expert.
- **Where it is proved:** `PositivityTheory.ThKR.theoremK_head2`
  (`Development/WeilBound/ThetaLifts/Reductions/FiniteClosure/TheoremKOfMod.lean:26`) = `theoremK_head2_of_mod modSt2` (`:14-20`)
  = `Tr.closeSph …` (`Development/WeilBound/ThetaLifts/SphericalLattices/SphericalClosure/CloseSph.lean:28-200`). The only open
  hypotheses are `EisBL` and `SiegelWeilStd`, and the call site supplies both as closed theorems
  (`TPS/EveryCharacterOfLiteratureOfVWin.lean:561-566`: `PositivityTheory.RgEis.Hd.eisBL`,
  `PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd`). The `closeSph` skeleton assembles about 90 named leaves into
  `ThKG.Leaves` and calls `agree_of_leaves` (`:199`). The leaves include the tower relations `TowerA/TowerB`, constant-term computations
  `CTBigZero/CTSmallZero/…`, `NonZeroBot` "of doubling integral", `PolZero` (which uses SiegelWeilStd, EisBL and
  `HeckeLEntireAndNonzeroAtOne`), `Kills` (theta kills cusp forms), local multiplicity one (unramified/ramified/archimedean),
  and `EndA/EndB`.
  - `EisBL` (`Development/WeilBound/ThetaLifts/LatticeBasics/HypothesesE.lean:46`): the Siegel Eisenstein series on U(n,n) attached to a section
    converges for Re s > t, is holomorphic there, and continues meromorphically with finite-order poles, uniformly as a
    moderate-growth-valued function. *I infer*: **Langlands' meromorphic continuation of Eisenstein series**, a standard result.
  - `SiegelWeilStd` (`…/HypothesesS.lean:11`): for A of dimension m and Y of dimension n, with A *definite* (min r s = 0), the value at s₀ = (m−n)/2 of the
    Siegel Eisenstein series equals (1 if n < m, else 2) × the averaged theta integral. *I infer*: the **Siegel–Weil formula
    for anisotropic/definite unitary spaces** (Weil, Kudla–Rallis, Ichino 2004, Yamana), a standard result. The factor 2 covers the
    boundary case n ≥ m.

### (c) `Closed 𝒞 LinkN`, `DefiniteSideCondition`, `CovolumeBoundOfX`, `boundAtTwoThree_linked_of_recT`

- **LinkN Fm** (`GTI:41-49`): ∃ C, x0 such that for x ≥ x0, each i with ShaFinOdd, and each lift index j ∈ {1, …, m}
  (`lifts`, `Formalism/LocalRingCardinality/DataParams₂.lean:208`), if Σ_l vvTerm(l) converges then
  η_j := Σ_{w ∈ supp, μ_w ≠ μ0} lw(w)·e_w·etaJ(j,w) ≤ dZ0(j)·( C(f·m·b·L² + log²x·Nc) + Σ_l log l·Σ_{1≤e<t} len Sha_l(e) ).
  Here dZ0 j = dim_ℂ Zj(μ0, j) (`DataParams₂.lean:194`). `Closed 𝒞 LinkN`: for ε small there is K with LinkN for every
  K-large family in 𝒞.
- **DefiniteSideCondition** (`TPS/DefiniteSideCondition.lean:25-40`): for every bundle b, given Ok3/TypesSep3,
  CovolumeOntoIsometryConditions, PassIn3, numeric facts H, submodules NuC and three-sided division-compatibility data I,
  if `DivTied3 …` holds and I is b.P.I, then `RowsU` holds for every word u. It is an implication "three-sided divisibility
  ties ⇒ definite-side rows". Not further unfolded.
- **CovolumeBoundOfX** (`TPS/LiftLambdaBound.lean:60`): `Closed FamHyp`. There is C0 ≥ 0 such that eventually, at all points p
  with RowsTAlt, for all C ≥ C0, `(p.S false).L3 (p.N C CH)`. Here L3 (`Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean:315`) says
  that for every layer j, lcv(X_W j, M_j)/D ≤ l3 j. In words: the normalised log-covolume of the layer-j lattice M_j, in the given
  hermitian metric, is at most the budget l3 j. FamHyp (`Divisors/TupleReadBaseTupleEqFamily.lean:503`) is a list of family
  regularity conditions (PageFix, PageWin, DGam | minkM(2fN_m), CYL ≤ 9, TuSize, …). This is an **arithmetic-volume (Arakelov)
  upper bound per lift layer**, assumed as a hypothesis here. NODE-ROOT records that it comes from `topCovolSlim2_use_alt_alt`.
- **boundAtTwoThree_linked_of_recT P.nLink p** (`TPS/At23OfAll.lean:24-28`). From `Hypotheses₂` it proves
  `BoundAtTwoThreeFamilyFonAlt Fm` for *every* family (`at23_family_alt`, via `boundAtTwoThree_of_local_bounds_at_two_three`,
  `TPS/FamilyBoundAtTwoThreeOfLocalBounds.lean:37`, from SecondBoundCondition/ThirdBoundCondition constants). It then lifts this
  to any row by `closed_of_all`. `BoundAtTwoThree L ρ C` (`NonGaloisDescent/BoundAtTwoThreeFamily.lean:52`) says: at each twisted local
  index i whose residue prime is 2, or is 3 and not "small", every π ∈ Zgood i satisfies `Bd ρ i π (midF L C)`, where
  midF = C·f·m·b·log x + C·x^C·large₂². So it is a **local bound at the primes 2 and 3**. The `∀ cDep` hypothesis of the node
  is therefore discharged unconditionally from `P.nLink`.

### (d) Where the "iterated theta lift / divisibility / Bost slope / seesaw-Bessel" picture appears

- **Iterated lifts, m layers.** These appear in `Rows.Data` (`ROWS:93-100`, `:182-186`): a chain Mult μ m → … → Mult μ 0 ≅ EE with
  `iota = multZero ∘ io_0 ∘ … ∘ io_{m−1} ∘ multTop⁻¹` and its adjoint `thetaUp`. The integer m is `Ranks.m`
  (`Formalism/LocalRingCardinality/Params.lean:8-23`: m even, 2 ≤ m, m+3 ≤ k, 3m < t, m² ≤ k + m(t+1), m ≤ f). I found no "m ≈ √X" in
  the Lean read. The only square-root-type constraint is m² ≤ N_1 = k + m(t+1). HypsAlt uses the tower through `jOn` (iota
  onto), `hMt`, `zL` (∀ k < m) and the per-layer `L3`. The fact that these maps are theta lifts between unitary groups is not stated
  in `Rows.Data`; *I infer* it is meant to come from the WTM/theorem-K route.
- **"Each lift wins one unit of divisibility."** The nearest statement is `LinkN` and its consequence `DIVinN`
  (`GTI:59-63`, proved by `divinN_of_hypV`, `CharacterBoxes/DivinNOfHypV.lean:117`). For every layer j ≤ m,
  η_j ≤ D0·C·x^ε·(B0 + Nc), with B0 = f·m·b·x^ε. Here η_j is the weighted sum over twisted places of the exponents etaJ(j,w)
  (`etaJ_tie`: etaJ j w = Σ_{i∈locs j w} etaLoc i, `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:283`). So the Lean asserts an
  **upper bound on the total valuation (divisibility exponent) accumulated at layer j, linear in D0 and in the Sha budget**. It
  does not assert a lower bound of one unit per lift. I did not locate a "+1 per layer" statement; it may sit in `DivRows3G`/
  `DivTied3`/`RecTied`, which I did not open.
- **Bost slope inequality.** I found no identifier "Bost". The slope machinery is `Formalism.HN.muMax`/`htMap`. `LinkDIV_at`
  (`GTI:77-90`, a `topDesWin` link, consumer of HypsAlt) requires: sFrame + μ_max(RR) ≤ x^CH·b; for each word u with
  Bk u ≠ 0, h(Bk u) ≤ h u (height of the map); and μ_dual(RR) + h u − Fo ≤ MAIN u + errors. *I infer* that this is the
  slope-inequality step: μ_max(source) ≤ μ_max(target) + h(φ) for a nonzero map φ = Bk u. `IndefData.FUN`
  (`IndefSide.lean:335`) is μ_max(RR) ≤ hh − meanLog κ.
- **Seesaw / Bessel period independent of the characters.** The nearest is `BesselId D` (`GTI:65-67`), also inside LinkDIV_at.
  It says D.BuRational, and there is an isometry V of EE and, for each word u, an isometry U of Mu u and a ≠ 0, with
  Bu u φ F = a·besS u (Uφ)(VF). That is, the period pairing equals a nonzero multiple of a fixed "Bessel" pairing, up to
  isometries. Independence from the Hecke characters is not visible in the statement; *I infer* it is encoded by besS depending
  only on D.
- **How it bounds a prime sum (inferred from NODE-ROOT and the above).** The number of layers m and the per-layer valuation
  budget combine in ChainTied/`ch_core` into the gap bound that gives Gm(x) ≤ x^{1/2+O(ε)}. The divisibility exponents η_j
  at twisted places w (the places where μ_w ≠ μ0, i.e. where the character twist is non-trivial) are bounded above by
  covolume + Sha + slope terms, and that bound is what controls the weighted prime sum. I did not trace this step.

## 2. Argument (proof of the node, `TPS/SiegelEisensteinSecondTermHypotheses.lean:45-68`)

1. `functionalsSeparate_of_howeUnram_of_siegelWeil` (F, Howe unramified, Siegel–Weil convergent) ⇒ FunctionalsSeparate (`:47`).
2. `test_vector_assembly_holds` (Siegel sets, Howe duality, Green cuspidal, literature join + functional equation, **hA, hM**,
   hS) ⇒ RowTest ⇒ `RowRat` (`:49`).
3. `fourier_coefficient_fit_of_join_alt` (F, **hA, hM**, hS, onto/lamLow from P) ⇒ ConstantFunctionFits (`:51`).
4. `evaluation_grid_of_join` (Howe, **hM**, F, **hA**, twisted Weil convergence, twisted local factors match, twisted square
   theta integrals equal) ⇒ a constant CF1 beyond which the grid evaluation EvLgG(GridA c) holds (`:52`). `rowFun_at_gridA_alt` gives
   CF0 and a FunctionalCondition beyond CF0 (`:55`). Set c = max CF0 CF1.
5. `open0_of_unitary_group_hypotheses` ⇒ OpenParameterStatements at c (`:58`). The monotonicity lemma
   `open_and_linked_of_stronger_extension_alt` transports it to the extended parameters (`:59-62`), giving the
   FunctionalCondition row hFun (`:63`).
6. `linked_bundles_l3_of_open_alt` (…, **hX**, hL, …) ⇒ the row `CovolumeBoundThirdPlaceSeries` (`:65`).
7. `hypotheses_nonempty_of_unramified_exponents_alt P hRat hL c (GridA c) hEv (hN c) hFun hL3`
   (`TPS/HypothesesNonemptyOfUnramifiedExponents.lean:41-61`) builds the record. Large-unramified-exponent bundles exist (hP, hMem, hEx).
   `final_alt_alt` turns hN (BoundAtTwoThree) plus P.nLink, the local Tate-duality and Euler-characteristic facts and others into the
   `S0.NL` row; this is where `LinkN` comes from. `allRows_of_open0_alt` collects all row conditions, and `nonempty_hyps_of_allRows_alt`
   (`TPS/NonemptyHypsOfAllRows.lean:19-80`) calls `classSel` (`CharacterBoxes/ClassSel.lean:14`) to choose 𝒜, σ satisfying
   every row, then packages the fields. The literature fields come in as `litThin`, `wuDecayOfGap`, `rowsFinDim_link`,
   `rowsPos_typeP`, `rowNGP_of_siegelWeil`, `rowMainEqP_of_siegelWeil`, `volumeRatio`, `genusMassAt_two`.

So hA/hM enter only in steps 2-4 (RowRat, ConstantFunctionFits, EvLgG), and hX only in step 6.

## 3. Children

| # | Name | file:line | Statement (math) | Role | Weight |
|---|---|---|---|---|---|
| 1 | `GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt` → `nonempty_hyps_of_allRows_alt` → `UpperTheory.Top.classSel` | `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:41`; `TPS/NonemptyHypsOfAllRows.lean:19`; `CharacterBoxes/ClassSel.lean:14` | Row conditions ⇒ ∃ family class satisfying all HypsAlt fields | builds the record; existence of 𝒜 | core |
| 2 | `UpperTheory.GalC.final_alt_alt` | `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:47` (use) | BoundAtTwoThree + Galois/local-duality facts ⇒ row of `Closed · LinkN` | supplies nRest (LinkN) | core (definition to unfold) |
| 3 | `PositivityTheory.ThKR.theoremK_head2` / `Sph.Tr.closeSph` | `…/FiniteClosure/TheoremKOfMod.lean:26`; `…/SphericalClosure/CloseSph.lean:28` | ThetaIntegralsAgree ∧ LocalMatching (twisted second-term identity, tower relations, local matching) from EisBL + SiegelWeilStd + ~90 leaves | hA, hM | core; standard? |
| 4 | `GlobalTheory.T.test_vector_assembly_holds`, `fourier_coefficient_fit_of_join_alt`, `evaluation_grid_of_join` | `TPS/SiegelEisensteinSecondTermHypotheses.lean:49,51,52` (use) | theta identities ⇒ RowRat, constant-function fit, grid evaluation | consumers of hA/hM | core (definition to unfold) |
| 5 | `GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open_alt` | same file `:65` (use) | CovolumeBoundOfX ⇒ per-layer covolume row | consumer of hX | core |
| 6 | `CovolumeBoundOfX` (hypothesis; supplied upstream by `topCovolSlim2_use_alt_alt`) | `TPS/LiftLambdaBound.lean:60` | per-layer normalised log-covolume ≤ l3 j for large FamHyp families | the volume input | core |
| 7 | `UpperTheory.N.boundAtTwoThree_linked_of_recT` / `boundAtTwoThree_of_local_bounds_at_two_three` | `TPS/At23OfAll.lean:24`; `TPS/FamilyBoundAtTwoThreeOfLocalBounds.lean:37` | local bounds at the primes 2, 3 for every family | discharges the ∀cDep hypothesis | standard?/glue |
| 8 | `UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil` | same file `:48` (use) | Howe duality (unramified) + Siegel–Weil ⇒ functionals separate | glue | standard |
| 9 | `PositivityTheory.RgEis.Hd.eisBL`, `SiegelWeilFormula.Fin.siegelWeilStd` | `EveryCharacterOfLiteratureOfVWin.lean:561-564` | Langlands continuation; Siegel–Weil for definite spaces | inputs to 3 | standard (Langlands; Kudla–Rallis, Ichino) |
| 10 | `GlobalTheory.genusMassAt_two`, `VolRatioFromSiegelWeil.volumeRatio`, `ThinScaleLiterature.litThin`, `wuDecayOfGap` | `NonemptyHypsOfAllRows` call `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:57-60` | mass formula rank 2; volume ratio; uniform short-interval prime statements for all D7; Wu decay | HypsAlt literature fields | standard (mass formula) / unclear (LitThin) |
| 11 | `open0_of_unitary_group_hypotheses`, `open_and_linked_of_stronger_extension_alt`, `rowFun_at_gridA_alt` | same file `:55-63` | parameter-openness and monotonicity | glue | glue |

## 4. Oddities

1. **`Rows.Data` is abstract.** The "theta tower" is a chain of arbitrary finite-dimensional inner-product spaces with linear maps
   (`ROWS:93-186`). Its identification with theta lifts between unitary groups is not in the type. Whether it holds depends on
   how D7's `what₂` is constrained elsewhere (not opened).
2. **`LitThin`, `WuDecayOfGap`, `MassRatioUnderVolume`, `GenusMassAt D 2` quantify over all D7.** `LitThin` asserts uniform
   short-interval-prime admissibility (adm6/7/11) with fixed constants for *every* D7 (`MainSup.lean:88-90`). This is a strong uniform
   statement and should be checked (it is supplied as `ThinScaleLiterature.litThin`).
3. In `nonempty_hyps_of_allRows_alt` the large-base row is built with `largeBaseProperty_true : LargeBaseCondition KP Q (fun … => True)`
   (`GlobalTwisting/EventuallyAllScaleContextsAndOfBoth.lean:91`), and `classSel` imposes `IsSel … (fun _ _ _ _ _ => True)`. These are
   `True` slots. They look like they are meant to be harmless, but a reviewer should confirm.
4. The hypothesis `∀ cDep, LinkedAt … BoundAtTwoThreeFamilyFonAlt` is discharged for *all* families from `Hypotheses₂`
   alone (`At23OfAll.lean:20-28`). So it is not specific to the parameters.
5. `SiegelWeilStd` has a factor `(if n < m then 1 else 2)`, so the boundary case n ≥ m is included with factor 2. The precise
   range (definite A, any n) should be compared with Ichino/Yamana.
6. ThetaIntegralsAgree's `OneConst` asserts *uniqueness* of c (∃!) over all matched Φ ↔ Φ′. That is stronger than an identity
   for one test vector, and it relies on Match being nonempty and consistent.
7. "m ≈ √X", "Bost", and "+1 divisibility per lift" do not appear as such in the Lean I read. What appears is an *upper* bound
   on per-layer divisibility (LinkN/DIVinN), a slope/height inequality (LinkDIV_at), and `BesselId`.
8. Field `hcI : 0 < cIc` and `hc30` are trivial-looking inequalities, but they are genuine constraints on chosen constants. None
   seen supplied by `trivial` within HypsAlt itself apart from items 3-4.

## 5. Coverage

Read: PROTOCOL.md, NODE-ROOT.md; `TPS/SiegelEisensteinSecondTermHypotheses.lean:1-76`; `TPS/Hyps.lean:1-93`;
`TPS/HypothesesNonemptyOfUnramifiedExponents.lean:1-64`; `TPS/NonemptyHypsOfAllRows.lean:19-80`; `WTM:140-215,281-604`;
`…/FiniteClosure/TheoremKOfMod.lean` (all); `…/SphericalClosure/CloseSph.lean:1-200`; `LatticeBasics/HypothesesS.lean:1-25`;
`LatticeBasics/HypothesesE.lean:1-61`; `EveryCharacterOfLiteratureOfVWin.lean:555-568`; `TPS/BernsteinUnitaryProductIrreducible.lean:1-80`;
`LocalTypeDictionary/ThetaLocalInputs.lean:1-33`; `TPS/DefiniteSideCondition.lean:1-46`; `TPS/LiftLambdaBound.lean:1-66`;
`TPS/BoundAtTwoThreeFamilyFon.lean:15-37`; `TPS/At23OfAll.lean:15-30`; `TPS/FamilyBoundAtTwoThreeOfLocalBounds.lean:30-60`;
`NonGaloisDescent/BoundAtTwoThreeFamily.lean:30-75`; `GTI:1-100`; `CharacterBoxes/DivinNOfHypV.lean:1-140`; `CharacterBoxes/ExS.lean`;
`GeometricWeakTiesOfStrong.lean:25-40`; `ROWS:1-200`; `Params.lean:1-40`; `IndefSide.lean:290-340`;
`TupleReadBaseTupleEqFamily.lean:500-510`; `AuxiliaryPrimeMemAvoidedPrimes.lean:10-30`; `MainSup.lean:80-100`; `WuDecayAll.lean:20-40`;
`DiscreteSeriesOfFormalDegree.lean:105-125`; `LinkDefN.lean:30-48`; signature lines of `classSel`, `largeBaseProperty_true`.

Not opened: bodies of `test_vector_assembly_holds`, `fourier_coefficient_fit_of_join_alt`, `evaluation_grid_of_join`,
`linked_bundles_l3_of_open_alt`, `final_alt_alt`, `classSel`, `agree_of_leaves` and the ~90 closeSph leaves, `eisBL`/`siegelWeilStd`
proofs, `DivTied3`, `RowsU`, `DivRows3G`, `IsUWeilPair`, `MinkMult`, `adm6/7/11`, `Bd`, `besS`, the D7 structure, `RecTExists`.
No `rg` hit for "Bost". "seesaw", "Bessel" and "Iterated" have many hits that were not followed, except `BesselId`.
