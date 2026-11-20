# NODE-PAIRB: near-orthogonality of Bessel periods — the estimates (`PairBound` and its four inputs)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `PB` = `Formalism/HermitianCurvature/StatementPB.lean`; `PN` = `Formalism/HermitianCurvature/StatementPN.lean`
- `GOB` = `Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean`
- `UBM` = `Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean`
- `FST` = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/`
- `CLO` = `Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/`
- `FM/` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`
- `PIH` = `Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/PoincareInHH.lean`
- `ITO` = `Formalism/SharpRestriction/CuspSpanNormBounds/IsTermOver.lean`
- `CSB` = `Formalism/FlagUnipotentLattices/CardSubmodulesAndLinearEquivBounds.lean`
- `GGM` = `CLO/GGMirabolic.lean`; `SND` = `Formalism/SharpRestriction/CuspSpanNormBounds/StandingNumericalData.lean`

## 0. Summary

- **What is Gram-ed (corrects the brief's direction).** P_u : C_u → HH is a *Poincaré-series* map, not a period map
  (`PIH:144-216`). C_u is a finite-dimensional space of ψ_N-equivariant, level-χ functions on the Bessel group
  R_u = U(W_u) ⋉ N; W_u is definite, so C_u is in effect forms on a finite class set, of dimension d_u.
  P_u(T)(x) = Σ_{δ ∈ R_u(F)\G(F)} Ph_T(δx), where at ∞ Ph_T uses the Bessel vector W_u. P_u lands in HH, the
  π∞-isotypic level-χ part of L²(G(F)\G(𝔸)) of dimension Dall (`InHH`, `PIH:192-197`). So P_u^* is the Bessel period
  map. The Gram kernel is `Kform` = (c_u c_u')^{−1/2}⟨P_u T, P_u' T'⟩ (`PIH:260-263`), i.e. K(u,u') = (c_u c_u')^{−1/2}P_u^*P_u'
  as a d_u × d_u' operator. The brief's picture is otherwise right.
- **The geometric side is a double unfolding of Poincaré series, not a spectral expansion.** No spectral decomposition of
  L² is used, so the continuous spectrum never appears. Non-compactness of G(F)\G(𝔸) is met by absolute-convergence
  lemmas. (U(V) has Witt index r ≥ 1 over F, so the quotient is not compact.)
- **The four estimates, opened:**
  - `NormBound` is an exact volume identity times **one** archimedean inequality, `InInfinity`: ∫ HS²(OO_t) ≤ 1/formal
    degree. That inequality is proved from an abstract Schur-orthogonality / Bessel-inequality lemma `EnergyAbs`.
  - The non-generic local saving q^{−(k−2r−5)} (`NGAt`) is a **counting** statement, not a cancellation. Lattices with
    nonzero "defect" relative to the 2r+2 frame vectors are rare: a sublattice count of order j^{k−1}, against a total
    defect-β mass ≤ β^{−(k−1)}. The proof then uses Cauchy–Schwarz.
  - The corank ≥ 2 saving comes **mainly from the level** (2/g)^{(s−1)kf}, with g ≥ (kb)⁸, not from a Siegel mass ratio.
    The mass-ratio factor (C/k)^{kf} ≈ 1/Γ(k)^f appears only in the degenerate class.
  - The Gauss-sum clause is Gelfand–Graev theory for GL_k(𝔽_g).
- **Sizes close**, with margin x^{ε/2} in the Lean (`RankNums.k_lo`), from k ≈ x^{9/2+10ε} against
  m⁵fL ≈ x^{9/2+9ε−5ε/16}. Every numeric step is proved (`GOB:67-210, 525-552`).

## 1. Statement

`PairBound` (`PB:220-238`) is an abstract theorem about a term system `Terms` (`PB:15-121`). It is proved
(`t_PairBound`, `GOB:525-552`) from `PairBoundAbstract` and the numeric lemmas. In words:

> Let K0 = Σ_{t ∈ id ∪ gen ∪ ng} op(t) be the non-degenerate part of an absolutely convergent term expansion. Suppose:
> - the norm expands through a Gauss-sum matrix GG on the index set I (`NormExpansionOn`);
> - (Pg·Γ1)·Id − GG ⪰ 0 with Pg = (1+3/g₁)^f(1+3/g₂)^f (`GGBound`);
> - terms in different rows with the same index are orthogonal (`RowOrth`); same-row non-degenerate pairs have
>   corank s0 ≥ 1 (`CorankPos`); the identity orbit contributes 0 (`IdZero`);
> - Γ1·Σ|⟨vec t, vec t'⟩| over same-row pairs of corank ≥ 2, and over generic corank-1 non-scalar pairs, is
>   ≤ e^{−(1/3)kf log k}·dd (`RowBig`, `RowNotScalar`);
> - Γ1·Σ Re⟨·,·⟩ over generic corank-1 scalar pairs is ≤ (1+δ)e1·dd, with δ ≤ b^{−7} and e1 ≤ exp(12f·2^{−(k−2r−2)})
>   (`RowMain`);
> - Γ1·Σ Re⟨·,·⟩ over non-generic corank-1 pairs is ≤ 2^{−(k−2r−5)}·e^{Cn(2r+2)⁵ f log b}·dd (`RowNG`).
>
> If in addition `SizeNumbers` holds (`PB:215-218`): b ≥ 16, k ≥ 32, f ≤ k, k ≥ 4r+12, g_i ≥ (kb)⁸, k ≥ 70 log b,
> 1 ≤ (5/3)f log k, and **k ≥ 8·Cn·(2r+2)⁵·f·log b**, then ‖K0‖² ≤ (1+b^{−6})·dd.

On the live path (`offDiagonalK0_of_rows`, `FST/LinkSFinalP.lean:58-114`) the system is the concrete `tO u u'` and
dd = d_u d_u'/D*. The conclusion is `TheoremSSelected`: ‖K0(u,u')‖²_HS ≤ (1+b^{−6})·d_u d_u'/D* for u ≠ u'.

**What "expected" means.** For isometries P_u, P_u' whose images are random subspaces of dimensions d_u, d_u' in a
space of dimension D, E‖P_u^*P_u'‖²_HS = d_u d_u'/D. So dd is the random-position value, and the claim is that the
correlation is at most random **to constant 1 + b^{−6}**. The companion clauses (NODE-THEOREMS `LinkS_at`) are:
- ‖K(u,u) − 1‖²_HS ≤ e0·d_u (each normalised P_u is a near-isometry);
- Dall ≤ (1+η1)D*;
- d_u ≍ D*/Γ²;
- |W| ≥ C0Γ²x^{CH}, so Σ_u d_u ≥ x^{CH}·D*. The sources overfill the target.

*I infer* the frame consequence. With S = Σ_u P_uP_u^* (normalised):
- tr S = Σd_u, and tr S² ≤ Σd_u(1+O(√e0)) + (1+b^{−6})(Σd_u)²/D*;
- rank S ≤ Dall ≤ (1+η1)D*, so tr S² ≥ (tr S)²/Dall.

Hence ‖S − (tr S/Dall)·1‖²_HS ≤ (b^{−6} + η1 + x^{−CH}+…)(tr S)²/D*. That is the near-tight frame. It explains why the
leading constant must be exactly 1 and why the dimension count must be exponentially precise (NODE-SLEAVES leaf 4).
Confirmed in outline; the consumer is NODE-RANK.

## 2. Argument

### (b) The kernel expansion (`KExpansion`, `CLO/TermOpStmt.lean:23-27`; terms `CLO/TermOp.lean:28-100`)
- **The Poincaré series.** Ph_T is:
  - left-invariant under R_u(F) (`Srat`);
  - ψ_N-equivariant;
  - χ₂-equivariant under the level group K₂ at the two primes g₀, g₁;
  - reproduced at ∞ by convolution with the discrete-series matrix coefficient ph: ∫ ph(z)Ph(y(z,1)) dz = Ph(y)
    (`PhProps`, `PIH:170-175`).

  P_u T = Σ_{δ ∈ R_u(F)\G(F)} Ph_T(δx). `InHH` asks for absolute summability, independence of transversal, L²-membership,
  and Re(Rph P) = P (`PIH:192-197`).
- **Unfolding.** ⟨P_u T, P_u' T'⟩ unfolds to a sum over t ∈ `GTerm`. A term is a pair of lattices (Λ ∈ what₂, Λ' ∈ rows')
  and a class of (x ∈ G(𝔸), γ ∈ U(V)(E)) with γΛ' = Λ and γ carrying the flag of u' to one compatible with u, modulo
  N_Λ × N_Λ' (`GCar`/`GRel`, `TermOp.lean:84-93`). That is, the double cosets R_u(F)\G(F)/R_u'(F), refined by lattice
  classes.
- **The terms.** Each term is scl·vol(K₂)·χ₂(k(ρ,ρ',t))·OO_t, where:
  - OO_t = ∫_Ω rk1(W_u(x), W_u'(γ⁻¹x)) dμ∞ is an operator-valued orbital integral of Bessel vectors (`TermOp.lean:28-30`);
  - the finite part enters through Levi data in ∏_v GL_k(𝔽_{g_v}).
- **The test function.** At ∞ it is the matrix coefficient ph of the discrete series, which is integrable under the
  large-gap hypothesis. At the level primes it is the character χ₂ of K₂ (the congruence subgroup unipotent mod g). There
  is no test function at the other places: the level is maximal there, as lattice stabilisers.
- **Convergence and the continuous spectrum.**
  - Convergence of both sides is separate named lemmas: `InHH` suppliers, `AbsConvC_outright`, `AbsConvTied`.
  - No continuous spectrum can enter, because the identity is an L² inner product of two explicit vectors of HH, not a
    trace. Whether HH meets only the discrete spectrum matters only for the count Dall (NODE-SLEAVES).
  - This is the standard way to do a relative trace formula with Poincaré series (as in Kuznetsov / Jacquet). It avoids
    the truncation issue entirely.

### The four estimates

**(1) RowMain / `NormBound`.** `NormBound` (`PN:20-22`) states, for a `MassData` record B with input clauses, that
Γ1·AA·(c0c0')^{−1}·IntN ≤ d d'/D*. Its proof `t_NormOfLemmas` (`UBM:51-91`) is:
- an **exact** identity Γ1·AA·(c0c0')^{−1}(volZZ/unitLevelVolume·Coo^{−1})·(1/deg) = d d'/D*, which is volume
  bookkeeping from `JacobianConstant`, `LocalProduct` and `Columns` (the mass formulae);
- times IntN = (…)·IntOO, with IntOO ≤ 1/deg (`InInfinity`, `MemParahoricTimesPrincipalCongruenceIff.lean:622`).

The inequality content is therefore `InInfinityX` (`CLO/RealObj.lean:172-173`): ∫ HS²(OO(h(c))) dν(c) ≤ 1/∏_v d_{π_v}.
It is proved in `inInfinityXAt` (`CLO/GaugeLatticeShifts/EnergyAt.lean:117-129`) from `EnergyAbs`
(`EnergyAbs.lean:58-78`). `EnergyAbs` is an abstract theorem: for a unitary representation σ with Schur constant d
(∫|⟨v,σ(g)w⟩|² = ‖v‖²‖w‖²/d), Følner Haar subgroups S, S', and Bessel vectors W, W' reproduced by the coefficient, the
disintegrated integral of HS² of ∫ rk1(W(x), W'(h⁻¹x)) dx is ≤ 1/d.
- *I infer*: this is a Bessel inequality / Plancherel for the relative pair, from Schur orthogonality. It is
  recognisable, and it is the right direction, since only an upper bound is needed.
- The exact `RowFormC` identity (MassDataForm) turns the scalar-pair sum into this integral times masses.
- e1 and δ are local-density corrections. I did not open their sources.

**(2) Corank ≥ 2 and non-scalar (`loopRowBounds_along_family_largeGaps` → `rows_along_family`,
`FM/LoopRowBoundsAlongFamilyLargeGaps.lean:19-41`).** This is glue over `rowCounts_uniform_constants_families`,
`amplitude_bounds_uniform_large_gap_families` (both consume `SiegelMassRatio`) and
`admissible_family_satisfies_row_estimates`. Its output `RowsND`/`RowsDeg`/`RowsOne` bounds each corank class by
explicit shapes (`FamilyPacketOfEquivalentStatement.lean:374-389`; `CSB:697-760`):
- ndRow(s) = (2/g)^{(s−1)kf}·(kv)^{kf}·Ξ(s)·C^{kf}·H^{C(s+m)m²}·(Csf)^{6sf}·Γ. `NonDegSum` gives Σ_{s≥2} ≤ g^{−kf/2}, and
  `GainSqrt` gives g^{−kf/2} ≤ e^{−4kf log k} from g ≥ (kb)⁸. **This saving is the level**: a corank-s Levi datum in
  GL_k(𝔽_g) costs g^{−(s−1)k} per place.
- degRow(s) has only (2/g)^{(s−2)kf} but an extra factor (C/k)^{kf}·e^{Cm⁶f log b}. Its sum is ≤ e^{−kf log k/2}·Γ^{−2}
  (`DegSum`). The (C/k)^{kf} ≈ 1/Γ(k)^f is the Siegel mass-ratio factor (`SiegelMassRatio`). Here NODE-SLEAVES's
  inferred mechanism is right, but only for this class.
- oneB (generic non-scalar corank 1) contains √((C g^{−(2r+1)} k^{−r})^{kf}): a level saving again (`SingleRowBound`).
- `ExpSumLe'` merges the three into e^{−(1/3)kf log k}.
- Constraint `XiHyp`: (kv)^{kf}·Ξ(s) ≤ H^C·C^{skf}. The Ξ(s) are counts of corank-s cells, supplied by unopened leaves.

**(3) Non-generic corank 1 (`RowNGJoint`, `PN:310-325`, proof `t_RowNGJoint` `UBM:1032`).** The structure is:
- class decomposition (`ClassInput`) and Cauchy–Schwarz within classes (`ClassCS`, `FirstBracket`, `SecondBracket`);
- per point γ, a local model `LocalNG` with `NGAt`, `MassRatioAt` and `Unfold` (`LocalInput`, `PN:246-248`);
- a global weighted height sum `PointSumInput` ≤ e^{CB m⁵ f log b}·Ire (`PN:262-264`), over γ ∈ Pts E r (compositions of
  r+1 with E-coordinates);
- conversion to dd by `NormBound`/`FramePassage`;
- absorption of all polynomial factors (g^{fA(r+1)²}, rd^{12r(r+1)f}, TT^{6f}, cSt ≤ b^{CSt m³ f}) into e^{Cn m⁵ f log b}
  (`NGNumbers`, `PN:280-287`).

The amplitude is ampNG = Σ_{∅≠A⊆Om} ∏_{p∈A} aN_p ∏_{p∉A} aZ_p (`PN:76-78`): inclusion–exclusion over the non-generic places.
One place in A suffices to extract q_p^{−(k−2r−5)} ≤ 2^{−(k−2r−5)} (`MeanAmpJoint`).

**The local lemma** (`LocNG.NGAt`, `ITO:202-209`; proof `AbstractBound.ngAt`,
`FM/HermitianDoubleCosetAmplitudeBoundLocal.lean:54-82`). V is a local hermitian space of rank k+2r+1 with a pair of
Bessel frames P = (A,B) in relative position `RelG` (`ITO:107-109`):
- X_A ∩ X_B = 0;
- the top minor D_{r+1} is a unit;
- the Gauss value G ≠ 0;
- every minor D_l is 0 or a unit;
- the characters agree on the stabiliser;
- `NormsOK`.

A term is a lattice Λ = n·Λ_std (n ∈ N_A) over the datum. "Non-generic" = `BBne` (`ITO:191-193`): Λ contains a vector of
the E-span of the 2r+2 frame vectors that is not in their 𝒪-span. Equivalently, Λ is not saturated along the frame:
"nonzero defect". The statement is:

> Σ_d wt(d)·|Σ_{t over d, BBne} μ(t)ψ(t)|² ≤ H_p^{C(r+1)²}·q^{−(k−2r−5)}·Σ_d wt(d)Σ_t μ(t),

with no saving for the generic part, and equality with H_p = 1 at places prime to everything. The proof is:
- `BasicInequality`: amp² ≤ mass × Σμ, which is Cauchy–Schwarz; **no cancellation in ψ is used**.
- A split into "first type" and "second type" defects (`TypesCS`).
- **First type** (`FM/HermitianFramesFirstTypeAmpSqBound.lean:44-110`): the mass of terms with image-cardinality j is
  ≤ H^{9(r+1)²+12(r+1)}·j^{k−1} (`hermitianDoubleCoset_mass_le_and_finite`). This is the classical count of index-j
  sublattices in rank k. The total defect-β mass is ≤ 4H^{4(r+1)}·β^{−(k−1)}·nn (`sumData_mass_be_eq_le`), and a
  defect-β term has image ≤ β/q (`small_image`). Summing the geometric series gives the relative mass ≈ q^{−(k−1)}.
- **Second type** (`family_bound`): (q^{1−(k−2r−3)})² = q^{−2(k−2r−4)}.
- Both are ≤ 98·…·q^{−(k−2r−5)}, and all H-powers are absorbed into H^{39(r+1)²}
  (`FM/NonzeroDefectHeightPowerAbsorbsConstants.lean:16-80`).

So the saving is **rarity of non-saturated lattices**. A lattice that meets the (2r+2)-dimensional frame span in a
strictly larger 𝒪-module is a codimension-≈k condition among rank-k overlattices. This is a recognisable local density /
sublattice-count statement, not a point count on a hermitian variety. The loss of 2r+4 in the exponent is the frame
dimension.

**(4) Gauss-sum matrix** (`GGM:13-140`).
- GG(i,j) = conj γ(d(i,j)), with γ(x) = |U|^{−1}Σ_y ψ_N(yxy⁻¹), the averaged Gelfand–Graev character of ∏_v GL_k(𝔽_{g_v}).
- By `ConvScalar` (from Gelfand–Graev multiplicity one), convolution by γ acts on an irreducible π as the scalar |U|/dim π
  if π is generic, and as 0 otherwise.
- `MirabolicBound`: a generic irreducible has dim ≥ ∏_{i<k}(q^i − 1), the Kirillov / mirabolic representation.
- `CardUni`: |U| = q^{k(k−1)/2}.

Hence the matrix is ⪯ ∏_{i<k}(1−q^{−i})^{−1}·γ(1)·Id ⪯ (1+3/q)·γ(1)·Id (`ratio_numeric`, `GGM:96-101`). These are
standard facts (Gelfand–Graev; Bernstein–Zelevinsky over finite fields).

### (d) Sizes, with the Lean's exponents
- **Where `SizeNumbers` comes from.**
  - `SizeNumbers` is a clause of `SizesAt` (`FST/TheoremSRecursion.lean:113-124`).
  - It is proved by `sizesAt_of` / `size_numbers_of_hypotheses` (`FST/RootLatticeThresholds/SzHypOf.lean:178-206`;
    `FST/ThmSOwn.lean:739-770`) from `StandingHypotheses` (`SND:106-138`), clause **C'·m⁵·f·L ≤ k**, with
    C' = sC' Fm ≥ max(256, 8·Cn) (`sizesRowS_of`, `SzHypOf.lean:228-251`).
  - Here m = D.R.m = 2r_S+2 (the number of lifts), f = D.R.f = 2n (`PolyConstantLeZBasePowFour.lean:30`), and L = log b.
  - The NG constant Cn is fixed before the datum D (quantifier order in `TheoremSDistinctWords`, `LinkSFinalP.lean:30-34`),
    so it is a genuine constant.
- **Where `C'·m⁵fL ≤ k` comes from.** It is derived eventually in x for any constant C from `RankNums.k_lo`:
  x^{ε/2}·m⁵·f·x^ε ≤ k (`SecondLabelsNonempty.lean:34-43`; `eventually_rankNums_imp_parameter_lower_bounds`).
- **Check against `RankVal` (`PairRowIffQdRows.lean:28-32`).**
  - m ≤ 2x^{1/2−ε/16} and f ≤ 4x^{2+8ε}, so m⁵fL ≤ 128·x^{9/2+9ε−5ε/16}.
  - k ≥ x^{9/2+10ε}.
  - The ratio is ≥ x^{21ε/16}/128 ≥ x^{ε/2} for large x.
  - Also: m⁴ ≈ 16x^{2−ε/4} ≤ f; f ≤ k; k ≤ x⁵ needs ε < 1/20 (ε < 1/52 is assumed). All consistent.
- **The NG term.** `NumNG` (`GOB:102`) uses k ≥ 8Cn m⁵ f log b:
  - 2^{−k/2}e^{Cn m⁵ f log b} ≤ e^{−0.347k+0.125k} ≤ e^{−k/5};
  - `NumExp`: k ≥ 70 log b gives e^{−k/5} ≤ b^{−14};
  - `NGExponent`: 2^{−(k−2r−5)} ≤ 2^{−k/2} when k ≥ 4r+10.

  So the comparison the brief asked about is **derived and closes**, but only because the margin is a power x^{O(ε)}.
  With k fixed at x^{9/2+9ε} it would fail against any constant C. The design exponent 9/2+10ε is exactly what makes it
  close: it beats m⁵f ≈ x^{9/2+8ε−5ε/16} times L = x^ε, with x^{ε/2} to spare.
- **The loop term.** e^{−kf log k/3} ≤ e^{−k/5} ≤ b^{−14} (`NumLoops`; needs (5/3)f log k ≥ 1). Inside the loop bounds:
  - g^{−kf/2} ≤ (kb)^{−4kf} must beat Γ = e^{C_Γ m⁵ f L}: k ≫ m⁵ holds;
  - the degenerate class (C/k)^{kf} must beat e^{Cm⁶ f L}·Γ³: k log k ≈ x^{4.5} ≫ m⁶L ≈ x^{3+ε}. It holds easily.
- **The Gauss sums and the final constant.** Pg ≤ e^{6b^{−7}} since f/g ≤ b^{−7} (`NumPrice`). The final constant is
  (√(Pg(A+2ε)) + √(Pg·2ε))² ≈ 1 + (7+2√2)b^{−7} ≤ 1 + b^{−6} for b ≥ 16 (`SqrtSumSqLeOneAddInvPowSix`).

All numeric lemmas are proved (`t_NumExp`, `t_NumLoops`, `t_NGExponent`, `t_NumNG`, `t_NumDens`, `t_NumPrice`, `GOB:67-210`).

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `t_PairBound`, `t_PairBoundAbstract` | `GOB:525, 464` | abstract assembly + numerics | glue (read 525-552) |
| 2 | `EnergyAbs` (`energyAbs_holds`) | `CLO/GaugeLatticeShifts/EnergyAbs.lean:58` | relative Bessel inequality: ∫HS²(orbital integral) ≤ 1/d_π from Schur orthogonality + Følner | core; standard in shape (Schur orthogonality) — body unread |
| 3 | `jacobian_natural_measure_constant`, `local_ratio_product`, `column_identity` | `UBM:1120` | mass/volume identities making NormBound an equality up to InInfinity | core-bookkeeping (Siegel–Weil / GHY masses) — unread |
| 4 | `GlobalTheory.HL.NonzeroDefect.ampSq_nonzero_defect` + `first_type_bound`, `family_bound`, `sumData_mass_be_eq_le`, `hermitianDoubleCoset_mass_le_and_finite` | `FM/NonzeroDefect…:49`; `FM/HermitianFramesFirstType…:44`; `FM/…SecondTypeFamilyAmpSqLe.lean:59`; `FM/MassDefectOrderLeStatement.lean:9` | non-saturated lattices have relative mass ≤ H^{39(r+1)²}q^{−(k−2r−5)} | **core** (E11); first type read, second type and mass counts unread |
| 5 | `PointSumInput` supplier | `PN:262` (def) | Σ_γ weights·heights^{A(r+1)²} ≤ e^{CB m⁵ f log b}·Ire | core — supplier not located |
| 6 | `NonDegSum`, `DegSum`, `SingleRowBound` + Ξ(s) counts (`XiHyp`) | `CSB:697-746` | level saving (2/g)^{(s−1)kf}, mass factor (C/k)^{kf} | core; numerics plausible, Ξ suppliers unread |
| 7 | `GGMatrixBound` from `GelfandGraevMultOne`, `MirabolicBound`, `CardUni` | `GGM:80-140` | Gauss-sum matrix ⪯ (1+3/q)·γ(1)·Id | standard (Gelfand–Graev; Gelfand–Kazhdan/Bernstein–Zelevinsky mirabolic) |
| 8 | `InHH` / `AbsConvTied` / `KExpansionC_holds` | `PIH:192`; `FST/LinkSFinalP.lean:62` | convergence of Poincaré series and of the term sum; the unfolding identity | core-standard — unread |
| 9 | `size_numbers_of_hypotheses`, `sizesAt_of`, `eventually_rankNums_imp_parameter_lower_bounds` | `FST/ThmSOwn.lean:739`; `SzHypOf.lean:178`; `FM/GlobalRankNumberBounds…Statement.lean:6` | SizeNumbers from k ≥ x^{ε/2}m⁵fx^ε | glue (read) |

## 4. Oddities

1. **The direction of P_u.** P_u is the Poincaré series C_u → HH (its adjoint is the period map). This is harmless, but
   d_u is the dimension of the *source*.
2. **"Non-generic" means non-saturated lattice, not "relative position of the Bessel data".** The relative position is fixed
   generic by `RelG`. The saving is pure counting (Cauchy–Schwarz, no character-sum cancellation). The constant H_p ≥ q_p
   at non-generic places is paid globally by the height sum.
3. **The corank ≥ 2 saving is mostly from the level g ≥ (kb)⁸.** NODE-SLEAVES attributed it to Siegel mass ratios. Those
   enter only the degenerate s = 2 class (`degRow`'s (C/k)^{kf}).
4. **`NormBound` is weaker than its name.** It is an identity plus the hypothesis-field `InInfinity`. The real inequality
   is `EnergyAbs`, whose body I did not read. It requires Følner subgroups S, S' at ∞, so the Bessel subgroup
   U(W_u)(ℝ)⋉N(ℝ) must be amenable. It is: compact ⋉ unipotent.
5. **Tightness.** The size closure has margin x^{ε/2}; with a constant-factor change in the k exponent it would fail. This
   is by design, not a defect. "e1 ≤ exp(12f·2^{−(k−2r−2)})" is consistent with k ≫ f.
6. **`IdZero`** (the identity orbit contributes 0 for u ≠ u') is a hypothesis. *I infer* it holds because T_u ≠ T_u' rules
   out γ = 1. I did not check its supplier.
7. Statements read literally: none seen false.

## 5. Judgement

The four estimates rest on recognisable mathematics:
- Schur orthogonality / a Bessel inequality at ∞;
- sublattice counting plus Cauchy–Schwarz at non-generic places;
- level savings in GL_k(𝔽_g) and Siegel mass ratios for higher corank;
- Gelfand–Graev for the Gauss-sum matrix.

The sizes close with the Lean's exact exponents and constants, and every numeric lemma is proved.

Ranked for expansion:
1. the local defect-mass counts (`sumData_mass_be_eq_le`, `hermitianDoubleCoset_mass_le_and_finite`, second type);
2. `EnergyAbs`;
3. the `PointSumInput` supplier and the Ξ(s) counts;
4. `InHH`/`AbsConv`.

Proved from recognisable mathematics *as far as read*. The two decisive inequality bodies (child 2, child 4's mass
counts) remain unread.

## 6. Coverage

Read:
- `PB:1-260`; `PN:1-374`; `GOB:525-552`;
- `UBM:40-130, 1110-1125`;
- `FST/LinkSFinalP.lean:1-140`; `FST/TheoremSRecursion.lean:1-188`; `FST/ThmSOwn.lean:1000-1030, 739-770`;
- `FST/RootLatticeThresholds/SzHypOf.lean:1-80, 178-251`;
- `SND:100-138`; `PairRowIffQdRows.lean:10-40`; `SecondLabelsNonempty.lean:34-52`;
- `FM/HypothesesOfGlobalRowsAndNodes.lean:13-20`; `FM/GlobalRankNumberBounds…Statement.lean:6` (statement);
- `ITO:100-213`; `FM/HermitianDoubleCosetAmplitudeBoundLocal{,Statement}.lean`;
- `FM/NonzeroDefectHeightPowerAbsorbsConstants.lean`; `FM/HermitianFramesFirstTypeAmpSqBound.lean`;
  `FM/HermitianDoubleCosetSecondTypeFamilyAmpSqLe.lean:15-60`; three one-line statement files;
- `FM/LoopRowBoundsAlongFamilyLargeGaps{,Statement}.lean`;
- `CSB:680-790`; `FamilyPacketOfEquivalentStatement.lean:374-395`;
- `GGM:1-140`; `CLO/TermOpStmt.lean:1-60`; `CLO/TermOp.lean:20-100`;
- `PIH:140-263`; `CLO/RealObj.lean:140-185`;
- `CLO/GaugeLatticeShifts/EnergyAt.lean`; `EnergyAbs.lean:58-78`;
- `MemParahoricTimesPrincipalCongruenceIff.lean:586-622` (grep).

Not opened:
- bodies of `EnergyAbs`, `family_bound`, the mass-count lemmas, `NonDegSum`/`DegSum`, `t_RowNGJoint`;
- the `PointSumInput` and Ξ suppliers; `KExpansionC_holds`; `InHH` suppliers; `IdZero` supplier;
- `RowFormC` sub-leaves and the e1/δ sources.
