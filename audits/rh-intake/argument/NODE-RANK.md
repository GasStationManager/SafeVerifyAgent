# NODE-RANK: does the slope inequality force the same B_u on the same N_u to be jointly of almost full rank? (E5, E7)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FTR` = `Formalism/SizeWindowBrackets/FrameTraceRatioFinEquiv.lean`
- `JD` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean`
- `TFS` = `Formalism/HarderNarasimhan/HarderNarasimhanProofs/TheoremFSharp.lean`
- `TD16` = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `SHF` = `Formalism/SharpRestriction/CuspSpanNormBounds/StandingHypothesesHoldFamily.lean`
- `ABS` = `Formalism/SharpRestriction/CuspSpanNormBounds/AdmissibleBoundsFromSource.lean`
- `TSO` = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/ThmSOwn.lean`

## 0. Summary

- `joint_a_ramified_holds` is a correct theorem of the geometry of numbers. Its proof is a layer-cake
  argument over Harder–Narasimhan filtrations, using Bost's slope inequality and one dimension-free
  linear-algebra lemma about frames. Nothing in it depends on rank or degree, so the rank-free error
  (E7) is genuine and not hidden in a normalisation. The `log|I|` term is not even needed: a sharp
  version without it is proved alongside (`JD:194`, `TFS:168`).
- The frame hypothesis (`InputSG`) is used **only to get a rank statement**. The changes of basis
  Y_u and Y' are free invertible matrices, so the hypothesis carries no metric content. What it
  delivers is robust near-surjectivity: for any K-subspaces of the N_u ⊗ K of small total codimension,
  the joint image ⊕B_u has codimension ≤ w·dim(RR) in RR^∨ ⊗ K.
- On the live path the frame matrices are built explicitly (`blockReal_at_of`, `TD16:1283`). The rows
  indexed by RR in the frame are **literally** `LinearMap.toMatrix (Nu u).b RR.dualB (div.Bk u)` at a
  complex place, up to Y', Y_u. These are the same `div.Bk` and the same `div.Nu u` that occur in
  `OneMapIntoCC` and in the height clause (`LatGeom`, `FTR:59-77`; `frameReal_at_of`, `TD16:679`).
- The frame **excludes B = 0**. If every Bk u = 0, the RR-rows of the frame are zero. The proved rank
  bound would then give |κ| ≤ (η+4√e)|κ⊔κ₁|, which contradicts (1−δ)|κ⊔κ₁| ≤ |κ| when δ, η and e are
  tiny. So E5 is closed *at the level of the slope node*, conditionally on the inputs below.
- The analytic content is **"Theorem S"**: approximate orthogonality of the Gram kernel of the
  period maps, K(u,u') = (c_u c_{u'})^{-1/2} P_u^* P_{u'}. Its off-diagonal Hilbert–Schmidt norm is
  ≤ (1+b^{-6}) d_u d_{u'}/D* and its diagonal satisfies ‖K(u,u) − 1‖² ≲ d_u/Γ (`ABS:212`, `Conclusion1`).
  It enters as `LinkS` (`GTI:145-157`). It is supplied by `ThmSOwn` ← `TheoremSSelected` (`TSO:669`),
  a bound on the main term K0 of an expansion `tO u u'` of the kernel. That expansion is the "relative
  trace formula". It is proved conditionally by `theoremS_selected_of_loops` (`TSO:1026`) from further
  closed-class hypotheses, which I did not unfold.
- δ is the fraction of the ambient Hilbert space HH (dimension Dall) that is not spanned by the
  Bessel-functional space EE ≅ RR⊗ℂ: Drows = (1−δ)·Dall (`DataRows.lean:69-71`). Its smallness is
  `LinkIRR` (`GTI:55`), supplied conditionally by `closed_linkIRR_of_join_count` from a row count.

## 1. Statement

### `JointARam` (`FTR:197-221`), proved as `joint_a_ramified_holds` (`JD:254`)
The data are:
- K, a totally complex number field (on the live path LL = what₂.LL);
- W, a K-space with basis b' (indexed by κ), metrics X'_w at the infinite places, and an
  O_K-lattice cc (here W = RR^∨ and cc = RR.dualL);
- a finite **nonempty** index set I (the words u);
- for each i ∈ I, a K-space V_i with basis b_i (indexed by ι_i), metrics X_i, a lattice N_i
  (here N_u = div.Nu u, the rescaled lattice), a K-linear map B_i : V_i → W (here div.Bk u), and a
  real number h_i;
- one infinite place v;
- invertible matrices Y_i and Y';
- an auxiliary finite set κ₁ ("padding" rows);
- matrices Ball_i ∈ M_{(κ⊔κ₁)×ι_i}(ℂ);
- weights γ_i > 0.

Hypotheses:
- **LatGeom** (`FTR:59-77`):
  - X', X_i, Y_i and Y' are invertible;
  - cc and the N_i are finitely generated of full rank;
  - Σ_i |ι_i| > 0;
  - **B_i(N_i) ⊆ cc**;
  - **B_i ≠ 0 ⇒ htMap(B_i) ≤ h_i**;
  - 0 ≤ δ < 1 and **(1−δ)|κ⊔κ₁| ≤ |κ|**;
  - the κ-rows of Ball_i equal Y'^{-1}·[B_i]_v·Y_i, the matrix of B_i at v in the bases b_i, b'.
- **LatNum** (`FTR:79-90`), with d_i = |ι_i| = rk N_i:
  - s·Σd_i ≤ Σ d_i(μ(N_i) − h_i);
  - u ≥ 0 and μ_max(N_i) − h_i ≤ s+u;
  - s − μ_min(cc) ≤ HH, with HH ≥ 0.
- Ball_i = Bf_i·Vr_i, where Vr_i^*Vr_i = 1, i.e. ι_i embeds isometrically into a larger ιf_i;
  Σ(|ιf_i| − |ι_i|) ≤ de·Σ|ιf_i| with de ≤ 1/4.
- σ ≤ 1/20, D*/σ ≤ Σ_i |ιf_i| (**the sources are overcomplete by a factor 1/σ**), and
  η0, η1 ≤ σ/2, √e0 ≤ σ/2.
- **InputSG Bf γ D* η0 η1 e0** (`FTR:30-35`). With K_{ij} = √(γ_iγ_j)·Bf_i^* Bf_j:
  - ‖K_{ij}‖²_HS ≤ (1+η0)·|ιf_i||ιf_j|/D* for i ≠ j (correlations are no larger than for random subspaces);
  - ‖K_{ii} − 1‖²_HS ≤ e0·|ιf_i| (each √γ_i·Bf_i is almost an isometry);
  - |κ⊔κ₁| ≤ (1+η1)·D*.

Conclusion (μ is the normalised Arakelov slope of NODE-SLOPE):

  s − log|I| − (1−δ)^{-1}·(4u·log(1+HH/u) + ((5σ+3√de) + 4√(2e0))·HH) ≤ μ(cc).

In words: the weighted mean of μ(N_i) − h_i bounds the **mean** slope of cc, up to an error
controlled by the spread u of source slopes above that mean and by the spread HH of target slopes below it.

## 2. Argument (`TFS:35-386`, `JD:164-257`)

1. **Frame → trace-ratio form** (`ramification_linear_case_holds`, `JD:164`).
   - InputSG on Bf, together with overcompleteness, gives tr(Q²) ≤ (1+5σ+3√de)·(tr Q)²/|κ⊔κ₁| for the
     frame operator Q = Σγ_i Ball_i Ball_i^*. This is `FrameTraceRatioLinear`, i.e. Q ≈ λ·Id in Frobenius norm.
   - The diagonal deviation for the compressed Ball is at most 2e0.
   - The constraint D*/σ ≤ Σd_i is needed to absorb the diagonal blocks into σ·(tr Q)².
2. **Robust rank** (`thmF_place`, `TFS:35-160`, through the linear-algebra lemma `FrameLA1`, not opened).
   Suppose the subspaces Ñ_i ⊆ V_i⊗_vℂ have total codimension ≤ ε·Σd_i. Then the joint image S of the
   Ñ_i under Ball has dim S^⊥ ≤ (η+4ε+4√e)|κ⊔κ₁|. Projecting away κ₁ loses ≤ |κ₁|. Therefore
   |κ| − rk(Σ_i B_i(Ñ_i)) ≤ (η+4ε+4√e)|κ⊔κ₁| ≤ (1−δ)^{-1}(η+4ε+4√e)|κ|.
   - *I infer* the proof idea: on S^⊥ the restricted frame operator vanishes, so tr_{S^⊥}Q ≤ ε·tr Q.
     Since Q ≈ λ Id, that bounds dim S^⊥. The bound is dimension-free.
   - The rank is computed over ℂ at v, but the subspaces come from K-subspaces, so it is a K-rank.
   - Y_i and Y' drop out, because they only change bases.
3. **HN pieces** (`theoremFSharp_of`, `TFS:168-386`). For τ ∈ [0,HH]:
   - Let Ñ_i(τ) be the HN piece of N_i with slopes ≥ s−τ+h_i.
   - A Markov-type share bound (`thmF_share`) uses mean ≥ s and max ≤ s+u. It shows that the total
     codimension of the Ñ_i(τ) is ≤ (u/(u+τ))·Σd_i.
   - Bost's slope inequality (`slope_inequality_mean`, not opened) puts B_i(Ñ_i(τ)) inside the HN piece
     of cc with slopes ≥ s−τ. Maps with B_i = 0 are skipped (`by_cases h0`); this is why the height
     clause may be conditional.
   - Step 2 then shows that the fraction of slopes of cc below s−τ is ≤ w(τ) = (1−δ)^{-1}(η+4u/(u+τ)+4√e).
4. **Layer cake** (`layer_cake_formula`). Every slope of cc is ≥ s−HH, so
   μ(cc) ≥ s − ∫_0^{HH} min(1,w) dτ ≥ s − (1−δ)^{-1}(4u·log(1+HH/u) + (η+4√e)HH).

**Judgement.** Each step is a correct statement:
- Bost's inequality is exact, with no constants, for Arakelov degrees;
- the frame lemma is dimension-free;
- the layer cake is elementary.

**E7.** The absence of a rank or degree term is genuine. The argument works through HN slopes, so no
Minkowski or Hermite constants enter. The term log|disc LL|/[LL:ℚ] in the normalised slope
(`StatementPl.lean:76-84`, per NODE-SLOPE) shifts every slope by the same constant, so it cancels.
The price is paid in the hypotheses: u, HH, δ, η and e must be small.

**Correction to NODE-SLOPE §2(b).** InputSG is imposed on Bf, the *full* period matrices (columns
indexed by Fin(duS u) ⊇ ι_u, rows by HH), not on the matrices of B_u themselves. Ball = Bf·Vr is a
compression of Bf, and only its RR-rows are B_u.

## 3. The key trace: where InputSG and δ are proved for the constructed family

Chain: `FrameF` ← `frameF_of` ← `FrameRealF` ← `frameRealF_of''` (`TD16:988`) ← `frameRealF_of'` ←
`frameRealF_of` (`TD16:695`) ← (`MatRealF` ← `matRealF_of` ← `MatSF` ← `matSF_of` (`TD16:862`) ←
`matS_at_of` (`TD16:821`) ← `MatKF` ← `matKF_of` (`TD16:1348`)). On the live path this is called in
`LossesSmallShares.lean:506-509` (and in `LinkPk.lean:281`, `LinkMin.lean:718,767`).

- **The frame matrices** (`blockReal_at_of`, `TD16:1283`, from `BesselId`).
  - Bf_u := PMat(f,u), with entries ⟨f_a, P_u e_j⟩ (`TD16:1013`):
    - P_u = D.s.Pu u : C_u → HH is the period map;
    - e_j is an orthonormal basis of C_u (dimension duS u);
    - f is an orthonormal basis of HH (dimension Dall) whose first Drows vectors are
      sEE(V(oE_k)), the images of an orthonormal basis of the Bessel-functional space EE.
  - besS u φ F = ⟨sEE F, P_u(ι φ)⟩ (`TD16:1113`). Hence the RR-rows of Bf·Vr are Bessel periods of an
    orthonormal basis of the forms space M_u (Vr is ι_u = Mu u ↪ C_u).
  - `block_eq` (`TD16:1245`) uses BuRational and adm13 (Bu = a_u·besS(Uφ)(VF), a_u ≠ 0). It
    identifies those rows with Y'^{-1}·[div.Bk u]_v·Y_u, where:
    - Y_u = a_u^{-1}·(change of basis from (Nu u).b, through jN, to the orthonormal basis of M_u);
    - Y' is the change of basis of EE.
  - Weights γ_u = 1/c0_u, where c0_u is the "unfolding constant", vol·vol/∏ dims (`TD16:1336`).
- **Near-tightness is "Theorem S"** (`LinkS_at`, `GTI:145-150`; `matKF_of`).
  - Assume ChProviso, i.e. every d_u·Γ²/D* lies in [C0^{-1}, C0] (`Chosen.lean:53-55`).
  - Then the kernel K(u,u') = S.KD = (c0_u c0_{u'})^{-1/2} P_u^*P_{u'} satisfies:
    - ‖K(u,u')‖² ≤ (1+η0) d_u d_{u'}/D* for u ≠ u';
    - ‖K(u,u) − 1‖² ≤ e0·d_u;
    - Dall ≤ (1+η1)D*.
  - Here η0, η1 and √e0 are all ≤ exp(−x^{ε/8}) (`GTI:152-157`).
  - `kp_eq` and `hs_opMat` (`TD16:1060-1080`) turn this into InputSG for PMat, exactly as stated.
- **The supplier of LinkS.** `linkS_of_standing_hypotheses` (`SHF:628`) applies `ThmSOwn` (`SHF:601`):
  standing hypotheses ⇒ `Conclusion1` (`ABS:212`). `Conclusion1` says:
  - K(u,u') − Kpp(u,u') has HS² ≤ (1+b^{-6})d_u d_{u'}/D* off the diagonal;
  - Kpp = 0 off the diagonal;
  - the diagonal satisfies ‖K − Kpp − 1‖² ≤ Γ d_u²/D* and ‖Kpp‖² ≤ d_u·exp(−k f log k).

  `ThmSOwn` is assembled from four clauses (`thmSOwn_of_clauses`, `TSO:65`). The off-diagonal clause
  comes from `TheoremSDifferentWords`/`TheoremSSelected` (`TSO:414,669`): ‖K0(tO u u')‖² ≤
  (1+b^{-6}) d_u d_{u'}/D*, the main term of a kernel expansion `tO u u'` tied to D.s by ConcTie.
  `theoremS_selected_of_loops` (`TSO:1026`) proves it from `TheoremSSingle`, `SizesRowS`, `LoopRowS`
  (RowBig, RowNotScalar), `AbsConvTied` and `SelOK`. Several alternative assemblies of LinkS exist
  (LinkSFinal, LinkSPos, CountT, BridgeCountE, `linkS_concrete`/`linkS_conc`/`linkS_selH`). I did not
  determine which one the root uses.
- **The `ramified share`.** Here de ≤ 2f/b. RamRank, du = duS·(1−1/(T_u−1))^f (`TD16:943-975`), is
  supplied by `ramRankF_of` from crystallineComparison.
- **δ.** LinkIRR (`GTI:55-57`): 0 ≤ delp ≤ exp(−x^{ez/7}), where Drows = (1−delp)·Dall
  (`DataRows.lean:69-71`). `matS_at_of` uses D_eq to give (1−δ)|RR.ι ⊔ Fin(Dall−Drows)| ≤ |RR.ι|. The
  supplier is `closed_linkIRR_of_join_count` (`Development/.../ThirdPlaceSeries/LinkIrr.lean:22`), from
  `CountAllRows` with an injective label count. Not unfolded.
- **The other inputs to `frame_at_of` (`TD16:538`).**
  - `ChCode`: |W| ≥ C0·Γ²·x^{CH}. Together with ChProviso this gives D*/σ ≤ Σ duS u (`word_count_bound_holds`).
  - `NuFull`, `RRFull` and `0 < rank Nu u` (from `MuRank`) supply the full-rank and positivity clauses.

**Same objects?** Yes.
- `frameReal_at_of` (`TD16:679-693`) puts into one LatGeom:
  - the RR-rows of the frame, built from `D.div.Bk u` and `(D.div.Nu u).b`;
  - the integrality clause `hOne : D.div.OneMapIntoCC`;
  - the height clause `hht`, taken from the same LinkDIV for the same `D`.
- The frame matrix is the matrix of B_u ⊗ K in K-bases. It does not see the O_LL-submodule (Nu u).L,
  so the rescaling by 𝔭^{-gain} has no effect on it. The archimedean metrics X do not enter the frame
  either (Y_u and Y' are free). They enter only through htMap and μ.
- So the frame is a statement at one complex place and the rescaling is an index change at finite
  places. These are independent, and this is fine.
- What does matter is that the K-space and basis of `div.Nu u` map, through jN, onto the Hilbert space
  M_u whose Bessel periods are orthogonal. The `jN_basis` field used in `bN` (`TD16:1208`) asserts this.

## 4. Vacuity and free parameters

| item | status |
|---|---|
| Index set I | `[Nonempty I]` instance; Σ rk N_u > 0 is proved (`frame_at_of`, from `hLat`) |
| Target rank 0 | excluded inside the proof: |κ| = 0 contradicts the diagonal frame bound (`TFS:181-196`) |
| B_u = 0 for all u | incompatible with the hypotheses (rows zero ⇒ dim S^⊥ ≥ |κ| ≥ (1−δ)|κ⊔κ₁|) |
| A single B_u = 0 | allowed; the theorem handles it (skips the piece); the height clause is guarded but harmless |
| Y_u, Y', κ₁, γ, Vr | existential in `FrameReal_at`, but constructed explicitly by `blockReal_at_of`/`matK_at_of` |
| η0, η1, e0, de | existential, with explicit upper bounds ≤ exp(−x^{ε/8}) |
| `LinkS_at` | an implication from Win/ChProviso; `linkS_of_standing_hypotheses` returns zeros when ¬Win (`SHF:651-652`). The consumer `matKF_of` discharges the antecedent with ChosenProviso, so it is not vacuous downstream. ChosenProviso is itself a "Chosen" hypothesis |
| δ | a field of `Rows.Data` with D_eq; bounded by LinkIRR |

Sizes:
- rk RR = Drows = (1−δ)Dall, and Dall ≤ (1+η1)D*;
- each duS u ≍ D*/Γ² (within a factor C0);
- |W| ≥ C0Γ²x^{CH}, so Σ duS ≥ x^{CH}·D*;
- rk N_u = du = duS(1−1/(T−1))^f ≥ (1−2f/b)·duS.

So the sources overfill the target by a factor of at least x^{CH}.

## 5. Judgement on E5

**Closed at this node, conditionally on LinkS, LinkIRR, ChosenProviso, ChosenCode and BesselId for
the same D.** Decisive quotes:
- The frame rows are Bk itself, `TD16:1089-1094` (`BlockReal_at`):
  `((PMat D f u).map ε * Vr u) (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j`.
- The integrality clause sits in the same LatGeom: `frameReal_at_of … hOne hht … ⟨…, hOne, hht, hd0, hd1, hcard, hblock⟩` (`TD16:691-693`).
- The rank consequence: `(Fintype.card κ : ℝ) - rkK (⨆ i, (Nt i).map …) ≤ (η + 4 * ε + 4 * Real.sqrt e) * card (κ ⊕ κ₁)` (`TFS:66-67`).

Whether LinkS (Theorem S) and LinkIRR are proved unconditionally on the live path: **could not
determine** in budget. Each is reached only through `Closed 𝒞 …` hypotheses (`TheoremSSingle`,
`LoopRowS`, `CountAllRows`, …).

## 6. Children (ranked)

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `TheoremSSelected` / `theoremS_selected_of_loops` (+ `TheoremSSingle`, `LoopRowS`, `SizesRowS`) | `TSO:669, 1026` | Gram kernel of the Bessel period maps: main term HS² ≤ (1+b^{-6})d_u d_{u'}/D* | core (relative trace formula; unopened) |
| 2 | ClDiag / ClKppDiag (`hypOwn_diag`, `DiagCW`) | `TSO:520-555` | ‖K(u,u) − 1‖² ≲ Γ d_u²/D* | core |
| 3 | `closed_linkIRR_of_join_count` | `Development/.../LinkIrr.lean:22` | Dall − Drows ≤ exp(−x^{ez/7})·Dall | core (unopened) |
| 4 | `FrameLA1` (`frame_linear_algebra_first`) | `TFS:388` | robust rank of a near-tight frame | standard-type linear algebra (unopened) |
| 5 | `slope_inequality_mean`, `hnStep`, `layer_cake_formula` | `ShiftInvariance.lean:47`; TFS | Bost slope inequality; HN; layer cake | standard |
| 6 | Count / `adm7` (Dall ≈ D*) | `SHF:201` | Dall ≤ (1+e^{-c r f log r})D* | core-ish |
| 7 | `blockReal_at_of`, `block_eq`, `kp_eq` | `TD16:1245-1310, 1060` | frame rows = B_u, Gram = KD | glue (proved) |

## 7. Oddities

1. The frame hypothesis has no metric content: Y_u and Y' are arbitrary invertible matrices. The
   theorem uses tightness only to deduce robust rank. This is correct, but "near-isometric" is not part
   of what is needed. The isometry lives entirely in the analytic Gram bound.
2. `joint_a_ramified_holds` returns the weaker form (with log|I|). The sharp form is proved in the same
   lemma (`JD:215-251`, `.2`) and is not used.
3. LinkS_at's antecedent can be false, and then the producer returns η = e = 0 trivially
   (`SHF:651-652`). This is harmless only because ChosenProviso is supplied downstream.
4. The rows of HH outside EE (κ₁ = Fin(Dall−Drows)) are the analytic complement of the Bessel functionals
   in HH. Their dimension is controlled only by LinkIRR.
5. The frame is at one infinite place v chosen from `embLL`. That is sufficient, because rank does not
   depend on the place.

## 8. Coverage

Read:
- `FTR:1-240`; `JD:1-60, 160-294`; `TFS:1-402`; `ShiftInvariance.lean:1-62`;
- `TD16:490-1420`; `GTI:40-60, 140-170`; `SHF:1-80, 186-230, 520-700`;
- `ABS:1-80, 190-240`; `TSO:1-130, 405-430, 480-600, 660-680, 860-1080`;
- `LossesSmallShares.lean:470-512`; `Chosen.lean:45-80`; `DataRows.lean:40-80`;
- `Development/.../ThirdPlaceSeries/LinkIrr.lean:1-46`;
- `Development/.../CountsIrreducibilityConstants.lean:85-110`.

Not opened:
- `FrameLA1`, `slope_inequality_mean`, `layer_cake_formula`;
- `TheoremSSingle`, `LoopRowS` bodies, `KppOffC`, `DiagC`;
- the producer of `LinkS` actually used by the root;
- `CountAllRows`/`linkIRR_of_join_ex`;
- `ramRankF_of`;
- the `D7` fields `s`, `sEE`, `jN_basis` and ConcTie semantics.
