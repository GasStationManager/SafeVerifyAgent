# NODE-THMB: "Theorem B (rotated)" and the second-type character-sum cancellation

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `WUR` = `Formalism/SharpRestriction/CuspSpanNormBounds/WeightedUniformRotatedOfExpansion.lean`
- `LMK` = `Formalism/SharpRestriction/CuspSpanNormBounds/LeadMinorK.lean`
- `RMB` = `Formalism/SharpRestriction/CuspSpanNormBounds/RootMeasBig.lean`
- `BSF` = `Formalism/FormalDegreeBessel/StatementBF.lean`
- `BSM` = `Formalism/SharpRestriction/CuspSpanNormBounds/BesselShellMomentBounds.lean`
- `TBB` = `Formalism/HermitianCurvature/StatementTBB.lean`
- `BWG/` = `CompanionTheory/AutomorphicTheory/BesselWaveGrids/`
- `FM/` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`
- `CRC` = `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ComplementReferenceCompactSubgroup.lean`

**Which "ThmB".** This node is `WeightedBoundRotatedUniform` / `theoremBRotated`: a bound on archimedean
Bessel orbital integrals at the singular double cosets. It is used only in
`CompanionTheory/AutomorphicTheory/UniformLocalFormulas/Closed.lean:20-27`, which feeds the non-generic rows of
`PairBound` (near-orthogonality). The `ThmB` in NODE-VOLUME is a different statement: `T.ThmB`, about tower
intersection numbers = vol × flag height polynomial + a linear form, from
`Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/TowerTheoremBStatement.lean:11`. The two share no
code. SUMMARY §10's line "`ThmB`/`weighted_bound_rotated_uniform` (shared by the lower slope bound and
near-orthogonality)" mixes them up. `weighted_bound_rotated_uniform` is not used on the slope route
(grep: its only consumer is Closed.lean).

---

## PART 1: `weighted_bound_rotated_uniform`

### 1. Statement

The Lean (`WUR:31-36, 156-157`):

```
def theoremBRotated (Aw Ch Cg Cb) := ∀ T T' b (X : BData D Ch Cg T T' b 0),
  (∀ v, AllGaps (X.L v).lam (Cg*(2r+2)^4)) →
  BSumR D X (fun γ => normWt D T T' γ ^ (Aw*(r+1)^2)) ≤ exp(Cb*(2r+2)^5 * #Tau * log b) * jSqG D X
def WeightedBoundRotatedUniform := ∀ Aw Ch, 0 ≤ Aw → ∃ Cb Cg₀, ∀ Cg ≥ Cg₀, ∀ D : D7, theoremBRotated D Aw Ch Cg Cb
```

Here r = `D.R.rS`. The real group at each place v ∈ Tau is U(Hpk). `Hpk` (`PeriodIntegrals/LongWeylElementSquare.lean:20`)
is r hyperbolic pairs plus a diagonal block diag(1,…,1,−1) of size k+1, so the group is **U(k+r, r+1)**. f = #Tau
is the number of archimedean places.

Unfolded, it says the following. Fix Aw, Ch ≥ 0. There are constants Cb, Cg₀, depending only on (Aw, Ch), with
this property. For every global datum D (any k, r, any CM field E), any T, T' ≥ 1, any b, and any family of local
data X = (L_v, f_v, μsec_v)_{v|∞}, in which at each archimedean v:
- L_v (`LocBessel`, `RelevantZeroGramTerms.lean:460`) consists of:
  - a discrete series σ_v of U(k+r, r+1) with Harish-Chandra parameter λ_v;
  - two Bessel data: negative vectors z, z' in the middle block with −h(z,z) = T, −h(z',z') = T'. The Bessel
    subgroups are R = U(W_z) ⋉ N, where U(W_z) ≅ U(k) is **compact** (`UWset`) and N is the unipotent radical
    of the flag of the r isotropic vectors (`Nset`);
  - finite-dimensional U(k)-types π, π' with highest weights u, u';
  - the generic character ψ_{N,z} (`StatementG.lean:55`);
- f_v is a K-finite matrix coefficient of σ_v (`IsKFinCoefH`);
- the hypotheses `LocOk`/`StdHyp` hold (`LMK:34-83`):
  - λ interlaces u and u';
  - |λ|, |u|, |u'| ≤ b, and T, T' ≤ b^{Ch(2r+2)};
  - all gaps of λ are ≥ Cg(2r+2)³, and the non-compact gaps are ≥ Cg(2r+2)^{9/2}(3(r+1)n² + n³), with n = k+2r+1;
  - a "shape" condition with bv ≥ Cg·n⁷;
  - a cut or separating-gap condition between u and u';
- and every gap of λ is ≥ Cg(2r+2)⁴,

the following inequality holds:

> Σ_{γ} wPt(γ)·ptWeightG(γ)·normWt(γ)^{Aw(r+1)²}·∏_{v|∞} orbSq_v(turn(γ_v)) ≤ e^{Cb(2r+2)⁵ f log b} · ∏_{v|∞} jNorm2_v.

The ingredients:

- **γ ranges over global singular points** (`IsBPt`, `LMK:150`). A `Point E (r+1)` (`Point.lean:11`) is a
  composition of r+1 into blocks (t_i, s_i) with t_i ∈ E^×. Its matrix `ptMat` is block diagonal, and each s×s
  block is anti-diagonal with constant entry t. All blocks of size 1 give the big cell (diagonal Ẑ); larger blocks
  are degenerate relative positions. The conditions are:
  - the point lies in a cell of an integral matrix;
  - G(γ) = |D_{r+1}|² − TT'|D_r|² is a nonzero algebraic integer. D_l is the l-th leading minor (`Gglob`).
- **orbSq** (`LMK:103`, `RMB:61`) is sup over representatives g with Ẑ(g) = ptMat γ (Ẑ(g)_{ab} = h(g f'_b, f_a),
  `StatementG`). Its value is
  ‖∫_{(R×R')/Stab} ψ(n)ψ'(n')⁻¹ π(w) f(w⁻¹n⁻¹ g n′w′) π′(w′)⁻¹‖²_HS.
  That is, the HS-norm² of the **archimedean relative (Bessel) orbital integral of the matrix coefficient f at the
  singular double coset R g R′**, with the quotient measure normalised on root coordinates (`IsRootMeas`).
- **jNorm2** (`LMK:86`, `BSF:146-152`) is ∫ ∏_a |c_a|^{2(M_a−2)} (|ζ|² − TT′)^{k−1} ‖J_f(bigCell(c, μsec ζ))‖²_HS
  over c ∈ (ℂ^×)^r and |ζ|² ≥ TT′. J_f is the same Bessel integral at big-cell points, so jNorm2 is the weighted
  L² mass of the relative character on the open double cosets. (*I infer* that this is the Plancherel density of
  R\G/R′ in the coordinates Ẑ = diag(c, ζ).)
- **The weights** are products over v of polynomials in |minors|_v (`wPt` `LMK:156`, `normWt` `LMK:164`, `ptWeight`).
  The heights NE(D_l), NF(G) are raised to the power Aw(r+1)².
- **"Rotated"** (`turnPt`, `FramesPt.lean:49`, with `ptMat_turnPt`) multiplies entry (a,b) by (−1)^r(−i)^{a+b}.
  It is a fixed diagonal change of normalisation, matching the global point to the local Ẑ convention (compare
  `ZhatO`'s (−1)^{r−b}, `RMB:70`). It is **not** K-conjugation and has no analytic content.

**Uniformity.**
- The constants Cb, Cg₀ are quantified before D, so they do not depend on k, r, E, f, b, T, λ, u.
- Rank enters the bound only through (2r+2)⁵ = m⁵ (m = number of lifts ≈ x^{1/2}).
- **k does not appear in the exponent.** k enters only through the hypotheses: gaps ≳ Cg·m^{9/2}·n³ and
  bv ≥ Cg·n⁷, so b ≳ n⁷ and log b ≳ 7 log k. The uniformity in k ≈ x^{4.5} is therefore *uniformity at the price
  of b*. Weights of size e^{x^ε} correspond to log b = x^ε, consistent with NODE-PAIRB's L.

### 2. Argument (three levels)

**Level 0: global to local** (`WUR:49-52, 107-152`; `BSM:815-1000`).
- `term_le` (`BSM:826`): if each archimedean factor satisfies the one-place bound (OnePlace, `BSM:815`)
  wLoc²(1+dLoc)^A·nLoc·WLoc^p·orbSq_v ≤ b^{CK m^e}·max(1, 1/|G|_v)^A·jNorm2_v,
  then the γ-term is ≤ wPt(γ)⁻¹·b^{CK m^e f}·∏jNorm2. The max(1,1/|G|_v) powers are cancelled by the
  (1+dLoc)^A and WLoc factors on the left (I did not trace the algebra).
- `theorem_B_second_bound_64` (`BSM:265`) gives Σ_γ wPt(γ)⁻¹ ≤ 64^{f(r+1)}: a lattice-point sum of
  ∏_v(1+|minor|_v²)^{−2} over integral points.
  - *I infer* why this is uniform in E: distinct algebraic integers cannot all be within 1 of each other at every
    place, by the product formula, so each unit box holds at most one point.
- `arith_B` (`BSM:921`) gives 64^{f(r+1)}·b^{CK m^e f} ≤ e^{(CK+6)m^e f log b}. Pure numerics.

**Level 1: the one-place bound** (`BWG/WeightedUniformRotatedOfExpansion.lean:16-30, 295-330`).
`WLoc1` asks, at one real place:

> ‖D_l(γ)‖^{2a}·ptWeight(γ)·orbSq(γ) ≤ b^{C m⁵}·max(1, 1/G(γ))^{40(r+1)²}·jNorm2, for every a ≤ Ca·m³.

It is derived from `WEnd.WBp` (`BWG/PowFourLeRpowNineHalves.lean:85`, the same inequality on the `KB.Pl` side)
and from `CoefCC1`. The frame passage is `frame_bound_of_bessel_torus` / `OneBesselTor`, with a constant
`le_refl 100`. `WBp` is proved by `wBp_of` (`:105`) from two cases:
- `EndDiffW`: u ≠ u′ with a cut;
- `EndEqW`: u = u′ with a separating gap.

Both reduce to `ThmBpAt` (`TBB:130`):

> Ew(f)(γ) ≤ b^{C₄m⁴}·G(γ)^{−(2p₀+n₀)}·jN2(f), for each singular point γ with G(γ) > 0.

**Level 2: why a singular orbital integral is bounded by the big-cell L² mass** (`TBB:93-170`;
`thmBpAt_of_leaves`, `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutBP.lean:136-160`). The mechanism has
four ingredients.

1. **Lemma S, an induction on blocks** (`LemmaS`, `TBB:93`; `StepOne`, `StepUp`, `TBB:172-200`).
   - Ew_{j+1}(h ++ [(s,t)]) ≤ (C₂Λ²)^s·Ew_j(h′). Iterating (`CorS`) bounds the point value at γ by
     (C₂Λ²)^{r+1}·Ew₀(∅), and Ew₀(∅) is ≤ κ₀·jN2 by a cut-off limit (`LimZeroAt`, `LemB`).
   - *StepOne* (block of size 1): `KernelFourierIntegralBound` says that the Fourier transform in the new
     coordinate c is ≤ min(1, (Λ/|s|)^K)·Ew_j. With K ≥ 3, Fourier inversion gives the pointwise bound
     (3/π)Λ²·Ew_j. This is a **band-limitation (Paley–Wiener-type) estimate**: the relative character is
     effectively band-limited at frequency Λ, so a point value is controlled by the mass. Λ ≤ b^{CΛ m}.
   - *StepUp* (block of size s ≥ 2, the degenerate cells) uses `BlockGrowthBound`:
     - Poisson summation over a lattice ℤω₁ + ℤω₂ in the block coordinate;
     - the dual-lattice terms are limits as t → 0 of the off-diagonal kernel between the (s−1)-blocks t and
       (t⁻¹+σ)⁻¹.

     So a size-s Jordan-type orbit is treated as a limit of size-(s−1) orbits (`GermAt`, `OnePointBasis…Volume.lean:935`).
   - "Wave grid" = `WaveGrid`/`LiftGrid` (`…FundamentalDomainVolume.lean:489, 683`): a finite set Y of exponents
     (letters), with a grid of K sample points per word, used for the Fourier-decay hypothesis.
     - Y is tied to the infinitesimal character through `EigStr`/`PStar lam` (`BWG/EigStrOfMem.lean:100-126`).
       *I infer* that the exponents of the germ expansion of J near the singular locus are fixed by Capelli
       (quantum-determinant) eigenvalues `capP`.
2. **NormAt / Amaps** (`TBB:144`; `CutBP.lean:117-128`): raising and lowering operators A± with
   ‖v‖² ≤ (3b)^{2n₀}(T/G)^{n₀}(‖A₊*v‖² + ‖A₋*v‖²), so that f is replaced by f∘A±. This is the source of the
   G^{−n₀} singularity (n₀ ≤ 30(r+1)²+6).
3. **RegularityBoundBigCell from `BigCellDerivativeExpansion`** (`CutBP.lean:130-138`):
   - det(Ẑ)^a·J_f = Σ co_i·J_{f_i} on the big cell, with Σ|co_i| ≤ b^{C₃m²a} and jN2(f_i) ≤ jN2(f);
   - the f_i are coefficients of the **Pieri/Zuckerman family** of discrete series σ_{λ+ν}, |ν| ≤ q₀
     (`In91`, `PowFourLeRpowNineHalves.lean:70`; supplied by `wave_inputs_of_hypotheses_global`,
     `BWG/WaveInputsOfHypothesesGlobal.lean:39-62`, via `family_through_discreteSeries`,
     `bigCellDerivativeExpansion_of_isDS_of_coefOf` and `momL_le`). Multiplication by the polynomial det^a is
     realised by tensoring with the standard representation and projecting (`ZuckT`, `TensRaw`).
4. **Representation-theoretic inputs**: `HypsG` (`PieriRules/ThetaBesselIsometries/IsDSOfIsDG.lean:79`), all
   supplied by named theorems in `hypsG_of_zuck` (`PieriRules/InfinitesimalCharacterDiscreteSeries.lean:51`):
   - decay of discrete-series matrix coefficients (`DecLow`, `DecInf`);
   - K-finite vectors are smooth;
   - **`RankOneG`**: the Bessel integral of matrix coefficients factors as L(w)⊗L(v)*;
   - smooth cyclic vectors;
   - infinitesimal character (Harish-Chandra);
   - existence of discrete series for large gap (`DSExistG`);
   - `ZuckG`: the tensor product with the standard representation decomposes into the shifted family (Pieri for
     discrete series at large gap);
   - `PoulsenG`: Schur's lemma for invariant forms;
   - the Harish-Chandra formal-degree formula (`HCFdegG`);
   - the uniqueness of the discrete series with a given HC parameter at large gap (`uniqueness_global`,
     `BWG/WeightedBoundRotatedUniformOfCubicThreshold.lean:10`).

**Bessel uniqueness: proved in the tree.**
- `RankOneG` = `be_rank_one` (`RankOneEstimates/RankOne.lean:32`). It rests on `thmM`
  (`ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/ThmMOfXi.lean:35`), which states: for a
  square-integrable σ with coefficient decay exponent ≥ aM there is a multiplicity-one map
  (`ThmM`, `…/StDiagExists.lean:151`).
- `thmM` is assembled from about 25 step lemmas (positivity and hermitian symmetry of the relative character J,
  Schur, dichotomy, rank-one minors) together with `multiplicity_one_hypotheses_hold` (`InHolds.lean:7`).
- It is **proved in the tree, for discrete series with gap ≥ 120n³, for the compact-U(W) Bessel pair**, and is not
  imported from `Published.*`. No `Published`/axiom/sorry was found in `MultiplicityOne/` or `BWG/` (grep).
- I did not open the 25 step bodies. The case is easier than Sun–Zhu: W is definite, so the Bessel subgroup is
  compact ⋉ unipotent and π is finite-dimensional.

### 3. Where it enters `PairBound` (question (c))

- It enters only the **non-generic corank-1 clause** `RowNG`, through `PointSumInput` (`StatementPN.lean:240`) in
  `t_RowNGJoint`.
- `pointSum_of_B3R` (`FlagStabilizerTensors/ThmBUseR.lean:54-80`) turns the bound into
  Σ_γ blockMinorWeight·n(γ)·(NG·ND)^{A(r+1)²}·J²(γ) ≤ TB = e^{C_B m⁵ f log b}·Ire. Each local Jacobian
  square J²(γ) is ≤ Cj·JSqR(γ) (`JointNormBoundRotated`, a tie lemma I did not open).
- **Precision required: crude.** The factor is absorbed into e^{Cn m⁵ f log b} and killed by
  2^{−(k−2r−5)}, because k ≥ 8Cn·m⁵ f log b (NODE-PAIRB §2(d)). So the exponent shape m⁵·f·log b matters, with
  constants independent of k. No constant-1 precision is needed, and the scalar main-term clause (1 + b⁻⁷) does
  not use it.
- *I infer* the role: the NG terms are lattices sitting over singular points γ. Their archimedean factors are
  singular orbital integrals, and Theorem B says that their total over all integral γ is no larger, up to
  e^{O(m⁵ f log b)}, than the big-cell mass that NormBound normalises.

### 4. Children (Part 1)

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `LemmaS` + `StepOne`/`StepUp` + `CorS`, `PtBoundOfCorS` (`lemma_s_of_parts`, `point_bound_of_corollary_s`) | `TBB:93-170` | point value at singular γ ≤ (C₂Λ²)^{r+1}·κ₀·jN2, by band-limitation, Poisson summation and degeneration of blocks | **core**, bodies unread |
| 2 | `KernelFourierIntegralBound`, `BlockGrowthBound`, `WaveGrid`/`LiftGrid`, `GermAt` suppliers (`EigStr`, `kDecay_of_gap`, `asymptotic_different_types`, `asymptotic_equal_types`) | `TBB:61-87`; `BWG/EigStrOfMem.lean:100-175` | Fourier decay of J beyond Λ ≤ b^{CΛm}; germ expansion at the singular locus with exponents from the infinitesimal character | **core**, unread; this is where uniformity in k must actually be earned |
| 3 | `BigCellDerivativeExpansion` ← `bigCellDerivativeExpansion_of_isDS_of_coefOf`, `momL_le`, `family_through_discreteSeries` | `CutBP.lean:130`; `BWG/WaveInputsOfHypothesesGlobal.lean:39` | det^a·J_f = Σ co_i J_{f_i}, Σ\|co\| ≤ b^{Cm²a}, via the Pieri family | core, unread |
| 4 | `Amaps`/`NormAt` | `CutBP.lean:117`; `TBB:144` | raising/lowering operators; source of G^{−n₀} | core, unread |
| 5 | `thmM`/`be_rank_one` (multiplicity one) | `MultiplicityOne/ThmMOfXi.lean:35`; `RankOne.lean:32` | Bessel integral of discrete-series coefficients is rank one | standard (GGP/Bessel multiplicity one, here for compact U(W) and discrete series); proved in the tree |
| 6 | `HypsG` components | `InfinitesimalCharacterDiscreteSeries.lean:51` | Harish-Chandra (existence, infinitesimal character, formal degree), Schur, Zuckerman/Pieri | standard |
| 7 | `term_le`, `theorem_B_second_bound_64`, `arith_B`, `onePlaceR_of_exp` | `BSM:826, 265, 921`; `WUR:107` | global sum = local bound × convergent lattice sum | glue (read) |
| 8 | `JointNormBoundRotated`, `PtTie`/`WtTie`/`NormTie` | `ThmBUseR.lean:43-52` | ties between PairBound's points and the Theorem-B points | glue, definition to unfold |

---

## PART 2: the second-type cancellation

### 5. Statement (question (d))

**`amp_le_mass`** (`FM/AmplitudeLeMassSecondTypeFamily.lean:31-36`). Let F be a non-archimedean local field with
residue field size q, E/F quadratic, V a hermitian E-space of rank k+2r+1, and k ≥ 4r+7. For a term datum d:

> |amp_d(InFF β J β_J)| ≤ 7·q^{1−(k−2r−3)}·mass_d(InFF β J β_J).

The definitions (`CRC:95-178`):
- amp_d(P) = Σ over St-orbits of lattices Λ with IsTerm ∧ P of μ(Λ)·om_d(Λ), where μ(Λ) = vol(K₀)/vol(St ∩ Stab Λ).
- om_d(Λ) = ψ_N(n)·ψ′_{N′}(n′)⁻¹, where Λ = n·stdLat = n′·stdLat′ (`CRC:135`).
- ψ_N(n) = ψ₀(θ⁻¹Σ_j h(n f_{j+1}, e_j)) is the **Bessel/generic character of N at this place**
  (`psiOf`, `CRC:78-79`); θ = ϖ at the level ("gg") places.
- InFF is the "second type": a nonzero defect β, the levels of the saturation reach exactly J ≥ 1, with β_J
  classes at level J (`CRC:192`).

**The kernel lemma** `exists_symm_invariant_kernel_hermitian_frames` (`FM/ExistsSymmInvariantKernelHermitianFramesStatement.lean`,
proof `FM/ExistsSymmInvariantKernelHermitianFrames.lean:17-33`). With δ = (24/7)q^{−(k−2r−4)}, there is a kernel
m(Λ, Λ₁) on the family with these properties:
- St-invariant;
- symmetric and ≥ 0;
- finitely supported rows;
- |Σ_{Λ₁} m(Λ,Λ₁) − 1| ≤ δ;
- |Σ_{Λ₁} m(Λ,Λ₁)·om(Λ₁)| ≤ δ.

**The averaging lemma** `norm_orbit_sum_le_of_symm_kernel` (`FM/NormOrbitSumLeOfSymmKernel.lean`) gives the
conclusion. Because m is symmetric and invariant, Σ_x μ(x)om(x) can be rewritten as
Σ_y μ(y)·Σ_x m(y,x)om(x) up to δ·mass, so |amp| ≤ 2δ·mass ≈ 6.9·q^{−(k−2r−4)}·mass. This is a symmetric Markov
operator with near-unit row sums that almost annihilates the phase. It is elementary and correct as stated.

### 6. The kernel and the actual character sum

The kernel is m(Λ, Λ₁) = cK·(normalised measure of the "moves" w carrying Λ to Λ₁) (`kern`, `NoLeak.lean:54`).
- **Moves** (`IsMove`, `CRC:236-241`; `MW`, `refA`, `NoLeak.lean:18-44`). A move is a w = (x, x′, u, s) with:
  - x + x′ at level exactly J in the span of the first J frame vectors;
  - u ∈ Λ ∩ (span of f_{<J}, f′_{<J})^⊥;
  - s + s̄ = h(u,u) and s ∈ ϖ^a·O.

  Each move acts by the Eichler (Siegel unipotent) transformation `eich(x,u,s)`. These elements stabilise the
  datum, so they preserve the family, apart from "leaking" moves.
- Under a move, om(Λ₁) = om(Λ)·χ(u), with χ(u) = ψ₀(h(y_b, u)) and y_b = −θ⁻¹(c·fr_{J} + c′·fr′_{J})
  (`chiM`, `NoLeak.lean:48-50`; `hermitianDoubleCoset_move_term_weight_character`). So the phase changes by a
  **linear additive character of u**.
- The three estimates (`hermitianMoves_total_measure_estimates`, `FM/HermitianMovesTotalMeasureEstimates.lean:169-253`)
  reduce by Fubini over (x,x′), u and s to one local lemma, **`term_integral_near_one_bound`**
  (`FM/TermIntegralNearOneBoundStatement.lean`). Let U = Λ ∩ perp(Ysp J), an O_E-lattice, and
  Z = {u ∈ U : h(u,u) ∈ ϖ^a O_F}. Then:
  - (i) |vol(Z)·q^a − 1| ≤ (8/7)q^{−(k−2r−4)};
  - (ii) vol(Z ∩ leak)·q^a ≤ (16/7)q^{−(k−2r−4)};
  - (iii) for every y such that u ↦ ψ₀(h(y,u)) is nontrivial on U,
    |∫_Z ψ₀(h(y,u)) du|·q^a ≤ (8/7)q^{−(k−2r−4)}.

  Nontriviality on U for the relevant y_b is `frameMove_character_ne_one` (it is where "second type", level exactly
  J, is used).

**So the cancellation is a Gauss sum on a hermitian quadric modulo ϖ^a.** It is the joint equidistribution of
(the norm form h(u,u) mod ϖ^a, a nontrivial linear character) on a hermitian lattice. It is not bare
orthogonality Σψ(ax) = 0: the restriction to the quadric Z is essential, and the saving is the Weil-type
q^{−(rank−1)} relative error.
- *I infer* the dimension count. perp(Ysp J) has E-rank k+2r+1−2J ≥ k+1 (J ≤ r). Its nondegenerate part has rank
  ≥ k+2r+1−4J ≥ k−2r+1.
- The true relative error is then ≈ q^{−(k−2r)} (see §7). The Lean's q^{−(k−2r−4)} is weaker by about q⁴,
  matching the constants 8/7 and 16/7 and the loss in the leak and fibre steps.
- So the exponent k−2r−4 is "rank of the hermitian space the moves see, minus the frame directions, minus a
  safety margin". It is not the dimension of the space on which the character is nontrivial: the character is
  nontrivial on a single direction.

The body of `FibU.shares` (`FM/TermIntegralNearOneBound.lean`) was **not opened**. It is the leaf that must prove
(i)–(iii) for a lattice U that is not necessarily unimodular.

### 7. Hand check (question (e))

Script: `numtest/thmb_hermitian_charsum.py`, run with `python3 -I`. The model is E/F unramified and
U = O_E^n with the standard unimodular hermitian form, reduced mod ϖ^a. Here A = vol(Z)q^a − 1, and C = the
relative character sum (iii) for a primitive y and, at a = 2, for y ∈ ϖO.

| q | a | n | A (exact) | C (exact) | q^{−(n−1)} |
|---|---|---|---|---|---|
| 3 | 1 | 2..5 | +0.222, −0.074, +0.0247, −0.0082 | 0.111, 0.0370, 0.0123, 0.0041 | 0.333 … 0.0123 |
| 5 | 1 | 2..4 | +0.16, −0.032, +0.0064 | 0.04, 0.008, 0.0016 | 0.2 … 0.008 |
| 3 | 2 | 2, 3 | +0.296, −0.066 | ≤ 0.037, ≤ 0.045 | 0.333, 0.111 |
| 3 | 2 | 1 | 0 | **1.0** (y ∈ ϖO) | 1 |

- At a = 1 the data fit exactly A = (−1)^n(q−1)q^{−n} and C = q^{−n}: a Weil/hermitian Gauss-sum identity.
  The relative error and the character sum are both ≈ q^{−n} for n = rank.
- At a = 2 the bound stays ≈ q^{−n} for n ≥ 2.
- **At n = 1 with y ∈ ϖO there is no cancellation (C = 1).** The character is trivial on Z = ϖO_E. So (iii) needs
  enough rank; the Lean's hypothesis k ≥ 4r+7 provides it (rank ≥ k−2r+1 ≥ 2r+8).
- The smallest admissible Lean case is r = 1, k = 11. The Lean bound is (8/7)q^{−5}. With effective rank ≥ 10, the
  model value is ≤ q^{−10}. **No violation, with a margin of about q⁵.**
- The model assumes U is unimodular. If U had many non-unit elementary divisors, the effective rank would drop.
  Whether `IsTerm` forces enough unit directions is the open question for the unread leaf.

### 8. Children (Part 2)

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `term_integral_near_one_bound` (`FibU.shares`) | `FM/TermIntegralNearOneBoundStatement.lean` | (i)–(iii) above: hermitian-quadric Gauss sum on U = Λ ∩ perp(Ysp J) | **core**, body unread; standard in shape (Weil sums for hermitian forms + Hensel), tested §7 |
| 2 | `frameMove_character_ne_one` | `FM/FrameMoveCharacterNeOneStatement.lean` | the move character is nontrivial on U for every level-J direction | core, unread |
| 3 | `hermitianDoubleCoset_move_term_weight_character`, `…_inFamily_moved_of_not_leak`, `frameMovesKernel_commonStabilizer_smul_eq`, `hermDoubleCosetMoveKernel_symm` | `FM/*Statement.lean` | moves preserve the family; phase × χ(u); kernel invariant and symmetric | core-structural, unread |
| 4 | `norm_orbit_sum_le_of_symm_kernel` | `FM/NormOrbitSumLeOfSymmKernel.lean` | symmetric invariant averaging ⇒ \|amp\| ≤ 2δ·mass | glue (partly read) |
| 5 | `hermitianMoves_total_measure_estimates` | `FM/HermitianMovesTotalMeasureEstimates.lean:169` | Fubini reduction to child 1 | glue (read) |

---

## 9. Oddities

1. **SUMMARY conflates two ThmB's** (see the top). `weighted_bound_rotated_uniform` is not on the slope or volume
   route.
2. **"Rotated" is a fixed diagonal renormalisation** (entries × (−1)^r(−i)^{a+b}), not a K-conjugation.
3. **Uniformity in k is bought through b.** The exponent m⁵ f log b has no k. The hypotheses force b ≳ n⁷ and the
   non-compact gaps ≳ m^{9/2}n³, so log b ≥ 7 log k. Whether the real content (child 2: Fourier decay with
   Λ ≤ b^{CΛm}, and germ exponents) is genuinely free of k is not visible at the level read. This is the claim to
   check: bounds on Bessel functions uniform in the rank of the compact part.
4. `orbSq` is a sup over representatives and quotient measures. If none exists it is 0, which makes the inequality
   easier. The consumer needs J² ≤ Cj·orbSq (`JointNormBoundRotated`), which shifts the burden to an unread tie.
5. The max(1, 1/G_v)^{40(r+1)²} singularity at the boundary G → 0 is compensated only globally, by integrality of
   G. Fine in the upper-bound direction.
6. Part 2 n = 1 counterexample to "nontrivial on U ⇒ cancellation on Z" (§7). It is harmless here because the rank
   is large, but it shows that the leaf's proof must use rank, and probably unimodularity of U mod ϖ.
7. Some sibling FM leaves (Siegel mass ratios, `SmallOnUnivUnconditional`) import `PublishedTheorems.*`. None of the
   files on the second-type chain that I read do.
8. Nothing false-looking as literally read.

## 10. Judgement

- **Part 1.** As far as read, correct, and proved from recognisable mathematics. The archimedean inputs are standard:
  Harish-Chandra, Zuckerman/Pieri, and Bessel multiplicity one proved in the tree for compact U(W). The architecture
  is a non-standard but coherent analytic argument:
  - singular orbital integral = germ coefficient of the big-cell relative character;
  - bounded via band-limitation, Poisson summation and degeneration of blocks (Lemma S);
  - plus Pieri-family derivative expansions.

  The uniformity is as claimed formally. Its substance sits in the unread Fourier-decay/germ leaves (child 2).
  It is used only crudely, as e^{O(m⁵ f log b)} against 2^{−k/2}.
- **Part 2.** An honest elementary cancellation: a Gauss sum on a hermitian quadric mod ϖ^a, averaged by Eichler
  moves through a symmetric invariant kernel. The exponent k−2r−4 is the rank available to the moves, less frame
  directions and a q⁴ margin. The hand check agrees: exact q^{−n}, with large slack.

## 11. Coverage

Read:
- `BWG/ThmBFinal.lean`, `WeightedBoundRotatedUniformOfHypsG.lean`, `WeightedBoundRotatedUniformOfCubicThreshold.lean`,
  `WeightedUniformRotatedOfExpansion.lean:1-60, 280-330`, `PowFourLeRpowNineHalves.lean:1-140`,
  `WaveInputsOfHypothesesGlobal.lean`, `EigStrOfMem.lean:100-175`;
- `WUR` (all); `LMK:1-200`; `Point.lean`; `FramesPt.lean:40-60`; `RMB` (all); `BSF:40-170`; `StatementG.lean:50-70`;
  `LongWeylElementSquare.lean:20-60`; `IsLowUnitH.lean:95-135`; `RelevantZeroGramTerms.lean:440-520`;
- `BSM:500-560, 815-1000`; `TBB:1-200`; `CutBP.lean:100-175`; `OnePointBasis…Volume.lean:480-500, 670-700, 935-947`;
- `IsDSOfIsDG.lean:1-120`; `InfinitesimalCharacterDiscreteSeries.lean`; `RankOne.lean:1-80`;
  `MultiplicityOne/ThmMOfXi.lean`, `InHolds.lean:7-13`, `StDiagExists.lean:151-162`;
- `ThmBUseR.lean:1-80`; `StatementPN.lean:236-250`; `UniformLocalFormulas/Closed.lean`;
- `FM/AmplitudeLeMassSecondTypeFamily.lean:1-80`; `ExistsSymmInvariantKernelHermitianFrames{,Statement}.lean`;
  `NormOrbitSumLeOfSymmKernel.lean:1-80`; `HermitianDoubleCosetKernelBoundByWeight.lean`;
  `HermitianMovesTotalMeasureEstimates{,Statement}.lean`; `TermIntegralNearOneBoundStatement.lean`;
  `CRC` (all); `NoLeak.lean`.

Not opened:
- bodies of `lemma_s_of_parts`, `point_bound_of_corollary_s`, `theorem_b_of_parts`, the Fourier-decay/germ suppliers,
  `bigCellDerivativeExpansion_of_isDS_of_coefOf`, `momL_le`, and the 25 `thmM` steps;
- `term_le`'s algebra and `theorem_B_second_bound_64` beyond its first lines;
- `FibU.shares`, `frameMove_character_ne_one`, the move/kernel structural leaves, and the tie lemmas of `ThmBUseR`.
