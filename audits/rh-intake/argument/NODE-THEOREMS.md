# NODE-THEOREMS: "Theorem S" (`LinkS` / `TheoremSSelected`), the Bessel-period Gram kernel

Paths are relative to the source root `.../scratchpad/art/lean/src`. Abbreviations:
- `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `TSO` = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/ThmSOwn.lean`
- `LSP` = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/LinkSPos.lean`
- `OK0` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/OffK0Closed.lean`
- `PB` = `Formalism/HermitianCurvature/StatementPB.lean`
- `SZ` = `Formalism/HermitianCurvature/StatementSz.lean`
- `TOP` = `Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/TermOp.lean`
- `HS` = `Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/HidaSetting.lean`
- `SHF` = `Formalism/SharpRestriction/CuspSpanNormBounds/StandingHypothesesHoldFamily.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`

## 0. Summary

- **Live path (resolves the parent's open question).** The root's `shape_closed_link_n_of_green`
  (`TPS/TopShape.lean:33-55`) passes `link_alt_alt_bis` as the `hS` (LinkS) argument of `topDesWin`
  (`CharacterBoxes/DesWin.lean:21`). `link_alt_alt_bis` (`TPS/LinkAltAltBis.lean:16-48`) calls
  `theoremS_transport_link_zero` (`LSP:131`). Its two analytic inputs `sLp : LoopRowS` and
  `sO : Closed … TheoremSSelected` are `HypsAlt` fields. They are produced by `at_choice_alt` (`TPS/AtChoice.lean:16-23`)
  for **every** class 𝒜 and every raw selection σ, using only the Siegel–Weil hypothesis hSW.
  - `sO` comes from `GlobalTheory.CarrierGap.offDiag` (`OK0:673-684`).
  - `sLp` comes from `loopRows_of_rowsFinDim_alt` (`TPS/LoopRowsOfRowsFinDim.lean:11-17`).
  - hSW is supplied at the root by `siegelWeilU_unitary_convergent_of_literature O`, which ignores `O` and returns
    the in-tree theorem `GlobalTheory.CompanionTheory.SW.siegelWeilUnitaryConvergent`
    (`TPS/EveryCharacterOfLiteratureOfVWin.lean:581-582, 708`).
  - `theoremS_selected_of_loops` (`TSO:1026`) and `TheoremSSingle` are **not** on the live path. The live off-diagonal
    proof is `offDiagonalK0_of_rows` (`LinkSFinalP.lean:58`), fed by `theoremS_of_conj` of
    `TheoremSConclusion.TheoremSClosedHypotheses`.
  - That record's 19 conjuncts are all supplied by named `_holds` / `_outright` / `_of` theorems
    (`OK0:642-661`).
- **The groups.** The groups are a hermitian space V of rank n = k+2r+1 over a CM field E (the host), with
  - signature (k+r, r+1) at every real place of F = E⁺;
  - a Bessel subgroup U(W_u) ⋉ N, where W_u is a **positive-definite** k-dimensional space;
  - discrete series at ∞;
  - level and character at the two auxiliary host primes g₀, g₁.
- **The words.** The index set consists of binary words u of length k. Each word gives an anisotropic vector z_u with
  ⟨z_u, z_u⟩ = −T_u.
- **What makes the error small.** The large parameters are:
  - the rank k of the definite group, with k ≥ 70·log b = 70·x^ε and k ≥ C·m⁵·f·log b;
  - the level primes, with g₁, g₂ ≥ (k·b)⁸, where b = exp(x^ε).

  The weight does not play this role. The non-identity orbit pairs of corank ≥ 2 and the non-scalar pairs are
  ≤ exp(−c·k·f·log k) relative to the main term. The non-generic ones are ≤ 2^{−k/2}·exp(C m⁵ f log b). The
  finite-field Gauss-sum matrix costs ≤ (1+3/g)^{2f} ≤ exp(6b^{−7}).
- **The window.** The size window is not a vacuity on the live path. The family that `topDesWin` uses carries
  `ChosenE Fm 3 CH`, which contains `ChosenProviso`, from `DesignExists`. The `¬Win` branch of
  `linkS_of_standing_hypotheses` (`SHF:651-652`) is an `absurd` on a false antecedent, not a "theorem about
  zeros".
- **Judgement.** On the live path no `Closed` hypothesis of Theorem S remains open in the Lean: each one is
  discharged by a named theorem. But the mathematical content sits in leaves I did not read:
  - `RowMain` (mass-formula main term);
  - `loopRows_of_large_gap_discreteSeries`;
  - `RowNGP`;
  - the dimension count `row_counts_of_labels_alt`.

  An exponential-precision orthogonality theorem of this kind is not one I know from the literature.
  **Could not determine.**

## 1. Statement

### `LinkS` / `LinkS_at` (`GTI:145-157`, read)
```
def LinkS_at (L : SizeData₂ D) (C0 Gam eta0 eta1 e0 : ℝ) : Prop :=
  (∀ u, C0⁻¹ ≤ duS u * Gam^2 / Dstar ∧ duS u * Gam^2 / Dstar ≤ C0) →
  (∀ u u', u ≠ u' → L.hsSq u u' ≤ (1 + eta0) * duS u * duS u' / Dstar) ∧
  (∀ u, hsDiagFull D u ≤ e0 * duS u) ∧ Dall ≤ (1 + eta1) * Dstar
def LinkS Fm C0 := ∃ x0, ∀ x ≥ x0, ∀ i, ∃ eta0 eta1 e0, 0 ≤ e0 ∧ eta0, eta1, √e0 ≤ exp(−x^{ε/8}) ∧
  LinkS_at (Fm.L x i) C0 (GamOf (Fm.L x i)) eta0 eta1 e0
```
Definitions used:
- hsSq = `S.hsSqD D u u'` (`LocalRingCardinality/DataParamsS.lean:8`), the HS² of the Gram kernel. It is not a free field.
- hsDiagFull u = ‖KD(u,u) − id‖²_HS (`GTI:142`).
- Γ = GamOf = exp(C_Γ·m⁵·f·L) with L = x^ε (`GTI:152`; `SHF` `scL_eq`), so Γ is exponentially large.
- b = exp(L) = exp(x^ε) (`LocalRingCardinality/DataParams₂.lean:27-29`).

In words: when every source dimension d_u is within a factor C0 of D*/Γ², the normalised period maps of distinct words
are about as correlated as random subspaces of a D*-dimensional space. Each map is almost an isometry. The ambient
dimension Dall exceeds D* by at most a factor 1+exp(−x^{ε/8}).

### `TheoremSSelected` (`TSO:669-674`, read)
```
OwnEv Fm fun C' Cl x i => AdmissibleBoundsFromSource.hyp … →
  ∀ hx h0 (u u' : Word), u ≠ u' →
    ‖((s.2 x hx h0 i).Y.tO u u').K0‖^2 ≤ (1 + b^{-6}) * (duS u * duS u' / Dstar)
```
Here `tO u u'` is the term system `TermOp.tOf` (`TOP:337-351`) of the kernel expansion, and K0 is its non-degenerate
part (`PB:61`).

### The objects, unfolded

- **Hermitian space and group.**
  - (V, h) has rank n = B.I.n = D.R.r (`HS` `n_eq`) over the host CM field E, and SZ:59-61 gives
    n = k + m − 1 with m = 2r+2.
  - V carries:
    - r = rS hyperbolic pairs (e_a, f_a) (`HS:216-220`);
    - a lattice L0 = ⊕ 𝔡^{−(r−a)} e_a ⊕ L_b ⊕ ⊕ 𝔡^{r−a} f_a (`HS:222-224`);
    - for each word u, z_u ∈ L_b with h(z_u,z_u) = −T_u, orthogonal to the e and f vectors (`HS:226-229`).
  - At each real place the form is `Hpk k r` (`Formalism/PeriodIntegrals/UpqRep.lean:218-222`): r hyperbolic planes,
    k entries +1 and one entry −1. So G_∞ = ∏_v U(k+r, r+1). This is **not** a definite group.
  - W_u := ⟨e, f, z_u⟩^⊥ has dimension k and is positive definite (*I infer*, from the signature count).
- **Bessel datum.**
  - N is the unipotent radical of the isotropic flag e₁ ⊂ … ⊂ e_r (`HS` `InS`, `InN`).
  - The character is ψ_R(g) = exp(2πi·Σ_a (⟨f_a, g·e_{a+1}⟩ + c.c.)/g) with e_{r+1} := z (`HS` `psiR`, `rootCoord`,
    `nxt`).
  - This is the Gan–Gross–Prasad Bessel model for (U(n), U(W_u)), with its generic character on N.
- **Automorphic side.**
  - Each place carries discrete series with Harish-Chandra parameter lamS and lowest K-type (`HS` `ds`, `low`).
  - The level is at g = g₀·g₁, with an additive character ψ_Ef trivial on integral adeles (`HS` `g_eq`,
    `psiEf_*`).
  - The forms are vectors in an L²-space HH of dimension Dall. P_u : C_u → HH is the period map (NODE-RANK §3).
- **The index set W** = `D.what₂.Word`.
  - A word gives `Sz.IsWord k de`: de : ℕ → {0,1} with de(k−1) = 0 (`SZ:259`). So a word is a binary string of
    length k.
  - It determines z_u, the norm T_u, a flag F_u, and a K-type through `Vand k (u de)` (`SZ:534-536`).
  - Distinct words differ at some letter l with 1 ≤ l ≤ k−2 (`StatementJ.lean:420`).
  - The T_u satisfy T_u ≥ b^{cT·m} and T_u ≡ T_{u'} mod g_S² (`StatementJ.lean:421`; `TheoremSRecursion.lean:124`).
  - The words are **not** Hecke characters or twists. |W| ≥ C0·Γ²·x^{CH} is `ChCode_at`
    (`GlobalSchurBounds/Chosen.lean:58-59`).
- **D\*** = vol(n)·idxRow·∏_{w|∞} dσ(w) (`SZ:84`):
  - vol(n) is the covolume (mass) of U(n). Its recursion `MassRatios`, vol(M) = ((M−1)!(v/π)^M)^f·d_F^{−1/2}·L_v(M)·vol(M−1)
    (`SZ:92-95`), is the shape of the Prasad / Gan–Hanke–Yu mass formula for unitary groups.
  - idxRow is the index of the level at g₁, g₂ (`SZ:70-71`).
  - dσ is the formal degree of the discrete series at each real place.

  So D* is the limit-multiplicity main term vol × level index × formal degree.
- **d_u** = vol(k)·idxCol·∏ dim π_w·(T_u^k − 1)^f (`ColumnCount`, `SZ:102-103`). This is the analogous mass term for
  the definite group U(W_u). `ChoiceOfT` (`SZ:105-106`) is the window d_u ≍ D*/Γ², and `PropA` (`SZ:145-147`) is the
  explicit ratio D*/d_u.
- **c_u** is the unfolding constant c0X (`TOP:244`, `scl` = (c0_u c0_{u'})^{−1/2}).
- **Sizes.** η0 = b^{−6} is what is actually proved. The statement asks only for η0 ≤ exp(−x^{ε/8}), which is much
  weaker. NODE-RANK reports e0 ≲ C0/Γ and η1 = e^{−c r f log r} (from `Conclusion1`, ABS:212, and adm7).

## 2. Argument

### (a) The kernel expansion, a relative trace formula
`KExpansion` (`TermOpStmt.lean:23-27`) states that the Gram kernel K(u,u') (as `Kform` on Cu × Cu') is the HS sum
Σ_t aTerm(t). The terms t are `GTerm`s (`TOP:76-93`), indexed by:
- lattices Λ ∈ what₂ and Λ' ∈ rows';
- a class of pairs (x ∈ G(𝔸), γ ∈ U(V)(E)) with x and γ rationally linked (`RatLink`), γΛ' = Λ, and γ carrying the flag
  of u' to a flag compatible with u, modulo N_Λ × N_{Λ'}. This is a double coset R_u \ G / R_{u'}.

Each term is
- scl·vol(K₂)·χ₂(k(ρ,ρ',t))·OO_t (`blk`, `TOP:246-251`);
- with OO_t = ∫_Ω rk1(Φ(x), Φ'(γ⁻¹x)) dμ, the archimedean orbital integral of the discrete-series matrix coefficient
  (`TOP:28-30`);
- and with a finite part χ₂ through a "Levi" reduction k ↦ GL_k(𝔽_{g_v}) (`levi`, `TOP:306-310`).

`kExpTiedS_holds` (`TheoremSConclusion.lean:84-93`) proves the expansion from `FoldOKC_outright`, `OOIntAllC_outright`,
`KExpansionC_holds` and others.

### (b) The square of the main part, as abstract linear algebra (`PB:15-218`)
The terms split into four sets:
- id: the identity orbit;
- deg: G(t) = 0;
- ng: non-generic;
- gen: generic.

Then K = K0 + part(deg) (`SplitSum`), and part(deg) is `Kpp`, which vanishes off the diagonal (NODE-RANK).

`PairBound` (`PB:220-238`) is an abstract theorem. Its hypotheses are:
- **NormExpansion** on gen and ng: ‖part S‖² = Σ_{i,j} GG(i,j)⟨vecPart_i, vecPart_j⟩, where GG are finite-field Gauss
  sums on Iof = ∏_v GL_k(𝔽_v) (`GG`, `TOP:363`);
- **GGBound** with Pg = (1+3/g₁)^f(1+3/g₂)^f, which says the Gauss-sum matrix is ≤ Pg·Γ1·Id;
- **IdZero**: the identity orbit contributes 0 when u ≠ u';
- **RowBig** and **RowNotScalar**: the pairs of terms in the same row with corank s0 ≥ 2, or with s0 = 1 but not scalar,
  sum to ≤ exp(−c k f log k)·dd;
- **RowMain**: the scalar pairs (the diagonal main term) sum to ≤ (1+δ)e1·dd, with δ ≤ b^{−7} and
  e1 ≤ exp(12f·2^{−(k−2r−2)});
- **RowNG**: the non-generic pairs sum to ≤ 2^{−(k−2r−5)}·exp(C(2r+2)⁵ f log b)·dd.

Under `SizeNumbers` (`PB:215-218`):
- b ≥ 16, k ≥ 32, f ≤ k, k ≥ 4r+12;
- g_i ≥ (kb)⁸;
- k ≥ 70 log b;
- k ≥ 8C(2r+2)⁵ f log b.

The conclusion is ‖K0‖² ≤ (1+b^{−6})·dd. It follows from the numeric lemmas `NumPrice`, `NumExp`, `NumLoops`, `NumNG`
and `SqrtSumSqLeOneAddInvPowSix` (`PB:181-210`).

**Mechanism, answering question (b).** The exponential smallness comes from the rank k of the definite group W_u, with
k ≳ x^ε, and from the depth of the level, with g ≥ (kb)⁸. The weight plays no part in it.
- The terms that are not identity, not degenerate and not scalar are rare, by a factor 2^{−k/2} or e^{−c k f log k}.
- The Gauss-sum matrix of the level is almost scalar, with deviation ≲ f/g.
- *I infer* the reason: the double-coset terms are indexed through GL_k(𝔽_g)-valued Levi data, and the proportion of
  matrices of corank ≥ 2 decays like g^{−4}, or 2^{−k} in a count over k.

### (c) Where each input comes from on the live path
- `offDiag` (`OK0:673-684`) builds `TheoremSDistinctWords` from `theoremS_of_conj (theoremS_leaves_of_carrierG carrierP
  hNG hRF uniqGap_holds hSW)` and applies `offDiagonalK0_of_rows` with `sizesRowS_of`, `thrRow_holds`, `aSz`,
  `hA_of_ranks`, `hLp` and `absConvTied_holds`.
- `theoremS_leaves_of_carrierG` (`OK0:641-661`) carries the section variables `[Fact HermRepUnram] [Fact CoefWeightedLoc]
  … [Fact CoefCapAll]`. Each has a global instance from a theorem:
  - `FlagMeasures/HermRepUnram.lean:7-9`;
  - `WeightedGaugeFactors/FactsDS.lean:16-22`, `FactsCC.lean:85`, `FactsGV.lean:6`;
  - `KFinDenseMain.lean:10`, `RhsWLimOfLeaves.lean:49`.
- RowNG comes from `rowNGP_of_siegelWeil hSW`. RowMain comes through `RowFormAllP`, `rowsSum_of_formula_volume` and
  `massDataInputsAll_of` (mass data from SWXS = `swxs_of_siegelWeil hSW`). The latter is where D* is matched to a
  mass formula.
- `LoopRowS` (RowBig and RowNotScalar for the actual tO) comes from `loopRows_of_large_gap_discreteSeries` with the
  following inputs (`LoopRowsOfRowsFinDim.lean:15-16`):
  - `bessel_multiplicity_one_large_gap_and_whittaker_bessel`;
  - `discreteSeriesCoef_pointwiseBound_unconditional`;
  - `wuDecayOfGap`.
- Transport to LinkS. `theoremS_link_concrete` (`LSP:108-128`) combines four clauses (KppOff, KppDiag, Off, Diag) through
  `thmSOwn_of_clauses` into `ThmSOwn`. It then uses `standing_hypotheses_hold_family` (under TuSize) and
  `linkS_of_standing_hypotheses` (`SHF:628-652`).
  - The diagonal clause is `hypOwnL_diagP` (`LSP:47-92`), from `diagonal_positive_final hNG hM` (RowNG and RowMainEq,
    both from Siegel–Weil) and the same `LoopRowS`.
  - The Kpp diagonal clause is `hypOwnE_kppDiagP` (`LSP:20-40`), a Kloosterman-type diagonal bound.
- **adm7 / Dall ≤ (1+η1)D\*** enters through `CountOwn` (`SHF:604-605`), from `h30 : CountAllPointsClass`. Its supplier is
  the `HypsAlt` field `c30`/`h30`, from `row_counts_of_labels_alt hSW` (`TPS/LinkROfIsLinked.lean`, line 79 of that
  file). This is a dimension formula for HH with exponentially small error. I did not open it.

### (d) The `Closed` quantifier and the window
- `Closed 𝒞 P` (`ParamsHeightRankConstant.lean:159-161`): ∃ε₁ > 0, ∀ε ≤ ε₁, ∃ threshold K, every family in 𝒞 that is
  `Large K CH` satisfies P.
- `topDesWin` (`DesWin.lean:23-31`) takes the design family Fm from `hEx`, of class WithTw(WithSm(WithChN(𝒜 ∧ G.cls la)))
  and Large K, and feeds it with an explicit membership proof into the conjunction of all the `Closed` hypotheses. So
  the class is the one the family lives in.
- `hCh : ChosenE Fm 3 CH` comes from `hEx` and is passed to `aGL`. ChosenE contains `ChosenProviso`
  (`Chosen.lean:53-55, 73, 83-84`), which is exactly the antecedent of `LinkS_at` (C0 = 3 on both sides).
- In `linkS_of_standing_hypotheses` the ¬Win branch returns `fun h => absurd h hW` (`SHF:651-652`). That branch is never
  used by a consumer that holds Win.
- Whether `designExists_of_tuSize_aux4n_litThin` really produces families with Win and ChCode is upstream (NODE-FAMILY,
  NODE-ROOT) and was not re-checked here.

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `rowFormAllP_of`, `rowsSum_of_formula_volume`, `massDataInputsAll_of`, `normalizing_constants_all` | `OK0:656-660` (use) | the scalar (diagonal-orbit) pair sum is ≤ (1+δ)e1·d_u d_{u'}/D*; matches the RTF main term with the mass formula | core (unopened) |
| 2 | `GlobalTheory.T.loopRows_of_large_gap_discreteSeries` | `TPS/LoopRowsOfRowsFinDim.lean:15` (use) | corank ≥ 2 and non-scalar pairs ≤ e^{−ckf log k}·dd (RowBig, RowNotScalar) | core (unopened) |
| 3 | `rowNGP_of_siegelWeil` | `FlagMeasures/RowPositivityOfSiegelWeil.lean:10` | non-generic pairs ≤ 2^{−k/2}e^{C m⁵ f log b}·dd | core (unopened) |
| 4 | `row_counts_of_labels_alt` (adm7, `CountAllPointsClass`) | `TPS/LinkROfIsLinked.lean` (use, line 79) | Dall ≤ (1+e^{−c r f log r})·D*: dimension formula with exponential error | core (unopened) |
| 5 | `CompanionTheory.SW.siegelWeilUnitaryConvergent` | via `EveryCharacterOfLiteratureOfVWin.lean:582` | Siegel–Weil formula in Weil's convergent range for unitary dual pairs (statement `PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean:18-35`) | standard (Weil; Ichino, Yamana); in-tree proof unread |
| 6 | `KExpansionC_holds`, `FoldOKC_outright`, `OOIntAllC_outright`, `AbsConvC_outright` | `TheoremSConclusion.lean:84-93` | Gram kernel = Σ over double cosets of orbital integrals (relative trace formula, unfolding) | core-standard (unopened) |
| 7 | `t_PairBound` | `HermitianCurvatureProofs/GrowthOfBasic.lean:525` | abstract ‖K0‖² ≤ (1+b^{−6})dd from the row bounds (`PB:220`) | glue / elementary |
| 8 | `carrierP`, `vIndepAtAllP_ofG`, `ampVec_genG` | `OK0:30-148, 494, 665` | non-vanishing of the orbital integral against Bessel functionals (`OrbInt = κ·J`, κ ≠ 0), via Bessel uniqueness `UniqGap` | core (partly read) |
| 9 | `theoremS_link_concrete`, `hypOwnL_diagP`, `hypOwnE_kppDiagP` | `LSP:20-128` | K0-bound + Kpp bounds ⇒ LinkS | glue (read) |

## 4. Oddities

1. **Not a definite group.** At ∞ the group is U(k+r, r+1) with discrete series. Only the Bessel subgroup U(W_u) is
   definite. So the "finite sum on both sides" picture of the brief does not apply. The archimedean orbital integrals
   are real integrals over a fundamental set Ω (`TOP:28-30`), and their absolute convergence is a lemma
   (`AbsConvC_outright`).
2. **What is called D\*.** D* is a limit-multiplicity main term: covolume × level index × formal degree. "Dall ≤ (1+η1)D*"
   with η1 exponentially small is therefore an exponentially precise limit-multiplicity statement for discrete series
   of a non-compact unitary group at a deep level. I know no theorem of this precision in the literature; error terms
   are usually a power of the level. It is supplied by an unopened row count.
3. **Gap between statement and proof.** The proved error b^{−6} = e^{−6x^ε} is far stronger than the stated
   exp(−x^{ε/8}). Not a defect.
4. **Duplicate names.** There are two different `TheoremSClosedHypotheses` (`TSO:983` and
   `TheoremSConclusion.lean:58`). The live one is the latter. `theoremS_selected_of_loops` and `TheoremSSingle` are
   dead on this path.
5. **Hypotheses supplied without checking the class.** `at_choice_alt` proves `SelectionOrderBound` and `SelectionLpBound`
   for every class and every raw selection (`Row.of_sel`, `AtChoice.lean:24-26`). So these HypsAlt fields carry no
   assumption about 𝒜. Their content is entirely in hSW and the in-tree `_holds` lemmas. Only `TuSize` (from D3
   membership) and `LocTied` (a selection field) are used.
6. **Sizes forced by the proof.** The proof needs the rank of the definite group to satisfy k ≥ 70·x^ε and
   k ≥ C m⁵ f x^ε, and the level primes g ≥ (k·e^{x^ε})⁸. These sizes are forced on the design. Whether the D7 data
   meet them is in the `SizesAt` hypotheses (`TheoremSRecursion.lean:113-124`) and `SizesRowS`, supplied by
   `sizesRowS_of` / `hRw_of_ranks`. I did not open those.
7. `LinkS_at`'s window ChProviso is a real constraint (d_u ≍ D*/Γ²). It is met by choosing T_u (`ChoiceOfT`), not by
   anything automorphic.

## 5. Judgement

Is Theorem S proved on the live path? **Could not determine.**
- Every `Closed` hypothesis on the path is discharged by a named theorem: `offDiag`, `loopRows_of_rowsFinDim_alt`,
  `theoremS_transport_link_zero`, and the in-tree Siegel–Weil. Decisive quotes:
  - `exact ⟨hL, GlobalTheory.CarrierGap.offDiag (… swxs_of_siegelWeil hSW) (… rowNGP_of_siegelWeil hSW) … hB.1 hL, hB.2⟩`
    (`AtChoice.lean:22-23`);
  - `(_root_.GlobalTheory.Top.link_alt_alt_bis 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR)` in the hS
    slot (`TopShape.lean:55`).
- The architecture is recognisable: a relative trace formula / unfolding for GGP Bessel periods, the main term from
  the scalar orbits matched with a mass formula, and Gauss-sum control at the level. The decisive analytic leaves were
  not read: RowMain, LoopRowS, RowNG and the adm7 count.
- The claimed precision (exponential in x^ε, for a non-compact group, with the dimension equal to the mass term up to
  1+e^{−c r f log r}) goes beyond any published result I know. These four leaves are where an expert should look next,
  in the ranked order of §3.

## 6. Coverage

Read:
- `DesWin.lean:1-35`; `TPS/TopShape.lean:1-57`; `TPS/LinkAltAltBis.lean:1-50`; `TPS/AtChoice.lean:1-30`;
  `TPS/BothRowsFromSiegelWeil.lean`; `TPS/LoopRowsOfRowsFinDim.lean`;
- `TPS/NonemptyHypsOfAllRows.lean:1-80`; `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:30-64`;
  `TPS/LinkROfIsLinked.lean:50-80`; `TPS/CountsIrreducibilityConstants.lean:85-105`; `TPS/Hyps.lean:52-53` (grep);
- `TPS/EveryCharacterOfLiteratureOfVWin.lean:581-586, 708`; `PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean`;
- `OK0:1-80, 600-686`; `TheoremSConclusion.lean:1-95`; `TSO:380-430, 640-700, 975-1080`; `LSP:1-200`;
- `GTI:120-175`; `SHF:595-700`; `Chosen.lean:40-86`; `ParamsHeightRankConstant.lean:159-190`;
- `PB:1-260`; `SZ:25-150, 505-540`; `StatementJ.lean:418-440, 480-515`; `TermOpStmt.lean:1-60`; `TOP:20-380`;
- `HS:1-60, 170-260`; `UpqRep.lean:205-260`; `FlagMeasures/HermRepUnram.lean`; `TheoremSRecursion.lean:113-125`;
- `DataParams₂.lean:9-29` (grep); `DataParamsS.lean:8`; `SmoothBigCellSectionsExist.lean:145-148`.

Not opened:
- `theoremS_closedP` / `theoremS_rec*` bodies (`TheoremSClosedP.lean`, `TheoremSRecursion.lean`) and `t_PairBound`;
- `offDiagonalK0_of_rows`;
- `loopRows_of_large_gap_discreteSeries`, `rowNGP_of_siegelWeil`, `row_counts_of_labels_alt`;
- the mass-data leaves, `KExpansionC_holds`, `CompanionTheory.SW.siegelWeilUnitaryConvergent`;
- `designExists_of_tuSize_aux4n_litThin`, `sizesRowS_of`, `ABS` `Conclusion1`.
