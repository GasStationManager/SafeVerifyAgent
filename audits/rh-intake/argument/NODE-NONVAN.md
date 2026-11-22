# NODE-NONVAN: the non-vanishing side of step 7 (Bost), re-traced on the live path

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(inferred)* = my reading. [NODE] = taken from that node, not re-read. Nothing was compiled or run.

Abbreviations from LEDGER, LIVEPATH, RANK and THEOREMS (`MB`, `QLD`, `GTI`, `LSS`, `DA`, `TS`, `DW`, `DNV`, `TD16`, `LSP`, `OK0`, `TPS/`, `FM/`). New ones:
- `LMin` = `Formalism/SharpRestriction/GlobalSchurBounds/LinkMin.lean`
- `LXL` = `Formalism/SharpRestriction/GlobalSchurBounds/LogXLowerFamilyOfTheorems.lean`
- `LGl` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean`
- `Ch` = `Formalism/SharpRestriction/GlobalSchurBounds/Chosen.lean`
- `TWP` = `Development/AutomorphicArithmetic/ResidueCharacters/TwistedPlaces.lean`
- `BCE` = `Formalism/SharpRestriction/CuspSpanNormBounds/BridgeCountE.lean`
- `CCS` = `FM/CountConstantsOfSiegelWeil.lean`; `CTV` = `FM/CountTypedOfVolumeStep.lean`; `UAC` = `FM/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean`
- `LSF` = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/LinkSFinalP.lean`; `TSC` = `.../FlagStabilizerTensors/TheoremSConclusion.lean`; `TSt` = `.../FlagStabilizerTensors/TheoremS.lean`
- `AC` = `TPS/AtChoice.lean`; `RCT` = `TPS/RowCountsOfTies.lean`; `NHA` = `TPS/NonemptyHypsOfAllRows.lean`; `LRI` = `TPS/LinkROfIsLinked.lean`
- `LIx` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkIRROfJoinEx.lean`; `ACy` = `Formalism/SharpRestriction/LevelLetterCocycles/ArithmeticCylinders.lean`; `ICS` = `Formalism/LocalToGlobal/GlobalTheory/IrreducibleOfCountSizes.lean`

## 0. Verdict

1. **No ESCALATE.** The live Bost step consumes a *robust near-surjectivity* statement for the joint Bessel-period map. It does not consume injectivity. Every input has a live supplier that is a named theorem. The inputs are a near-tight frame (Theorem S plus the dimension count), a ramified share, overcompleteness of the word family, and δ_p < 1. The content leaves are unread (§5). The supplied precisions **exceed** what the Bost step uses.
2. **Correction (LEDGER §1, inferred hop).** The live `LinkGLOBAL` is not `linkGLOBAL7_pk` (LSS:468-511). The chain is `link_gl` (LGl:14-31) → `FamGLmin.link8` → `link7` (LXL:56-76) → `linkGLOBAL7_min` → **`linkGLOBAL7_items`** (LMin:693-737).
   - Its frame call is the same as in the pk twin (LMin:717-719 vs LSS:506-509), except that `ramRankF_min` replaces `ramRankF_of`. So RANK's frame analysis transfers.
   - The **L10 supplier differs**: it is `Loss7.stLoss7 eps Fm cTT cBad lG` (LMin:721), not the premise `hL7` (LSS:472). LEDGER's (L10) trace should be redone against `stLoss7`. That is outside this node.
3. **Correction (MAIN-ARGUMENT §0, §6.1, §6.4; REVIEW A3).** The "k/n²" term, m·Nc, does **not** come from non-vanishing or from Bost.
   - Nc enters only as an allowance in `LinkN_at`, the E2 congruence-length bound on etaSum (GTI:40-43; TWP:99-101). It reaches DIV through `DIVinN` (DNV:117-140) and then `LinkDIV_at` (vii) (GTI:82-84).
   - Nc appears in neither `Frame_at` (QLD:188-193) nor MB's `SlopeIneq` (MB:151-156).
   - Non-vanishing enters only indirectly. Theorem S forces k ≳ m⁵·f·log b, and the record clause k ≤ n²·x^{1/2−ε} keeps m·Nc within budget. Together they give n ≳ m⁴ (§2.4).
4. **Correction (MAIN-ARGUMENT §7, §9.4; RANK).** On the live path Theorem S is **not** "conditional via `theoremS_selected_of_loops`". THEOREMS had already found this; it is confirmed here.
   - The live chain is `at_choice_alt` → `offDiag` → `offDiagonalK0_of_rows`, with `theoremS_of_conj` → `theoremS_closedP` → `theoremS_rec` → `pbApplied` → `t_PairBound`. All closed hypotheses are discharged by named theorems from the Siegel–Weil input hSW.
   - `LinkIRR` is likewise proved by named theorems from hSW, from Green's parametrisation (a `Published` field) and from ties whose suppliers are unread.
   - So the honest status is "proved in-tree on the live path, content leaves unread", not "conditional".
5. **The precision actually used is polynomial** *(inferred from the formulas read)*.
   - The frame needs η0, η1, √e0 ≤ x^{−CH}/2 (TD16:529).
   - δ_p enters only as (1−δ_p)^{−1} and through δ_p < 1 (QLD:188-193; TD16:716-723).
   - The suppliers deliver more: Theorem S to 1 + b^{−6}, the count to e^{−n f log n/16}, and δ_p ≤ e^{−x^{ez/7}}.
   - Even the polynomial precision, uniform in rank n ≈ x^{4.5} and degree f ≈ x^{2}, is beyond the published literature (§3.3).

## 1. Statement: what L0 consumes

### 1.1 L0 itself
MB's `SlopeIneq` (MB:151-156) is a hypothesis on real numbers only:

  s − log|W u0| − (1−del)^{−1}·[4uF·log(1 + HH/uF) + (η + 4√e)·HH] ≤ muCC.

MB supplies the side conditions `HHBound` (MB:158-159: s − muMinCC ≤ HH ≤ x^{cHH}·b) and `FParams` (MB:161-163: del ≤ delBar, η ≤ etaBar, e ≤ eBar). The lattice content comes from `Frame_at D etaB eB` (QLD:188-193), which is the same inequality for:
- s = `sFrame Nu h`, the rank-weighted mean of μ(N_u) − h(u);
- uF = `uFrame`, the Harder–Narasimhan spread;
- target slope `RR.muDual` = μ(RR^∨) = μ(cc);
- δ_p = `D.what₂.delp`;
- W = `D.what₂.Word`.

It is supplied family-wise as `FrameF` (QLD:258-260), with (etaB + 4√eB)·x^{CH} ≤ 6.

### 1.2 The live supplier and what it consumes
`hFr := frameF_of … (frameRealF_of'' … lD lI lS cPr hNF hRank hTu (ramRankF_min Fm hE) (matKF_of … lS cPr lD)) hLat cPr cCo hNF` (LMin:717-719). Unfolded:

| input | content (Lean) | file:line |
|---|---|---|
| `FrameReal_at` | LatGeom (B_u(N_u) ⊆ cc, height clause, (1−δ_p)·\|κ⊔κ₁\| ≤ \|κ\|, κ-rows of Ball = Y′⁻¹·[B_u]_v·Y_u) and `InputSG Bf γ D* η0 η1 e0`, with η0, η1, √e0 ≤ sg/2, sg = x^{−CH}; ram share Σ(duS − du) ≤ de·RsG | TD16:519-531 |
| `MatK_at` (from LinkS + BesselId) | Ball = PMat·Vr; off-diagonal HS²(K(u,u′)) ≤ (1+η0)·duS u·duS u′/D*; ‖K_uu − 1‖²_HS ≤ e0·duS u | TD16:807-819; built by `matKF_of` TD16:1348-1390 via `blockReal_at_of` (BesselId = `(lD …).2.2.2.1`, TD16:1361) |
| \|κ⊔κ₁\| = Dall ≤ (1+η1)D* | the third clause of LinkS | `matSF_of` TD16:880-884, `matS_at_of` TD16:821-852 |
| (1−δ_p)·Dall = Drows = rank RR | `D_eq` | TD16:840 |
| 0 ≤ δ_p < 1 | from LinkIRR | `frameRealF_of` TD16:716-723 |
| overcompleteness D*/sg ≤ Σ_u duS u | `ChCode_at`: C0·Γ²·x^{CH} ≤ \|W\|; `ChProviso_at`: C0⁻¹ ≤ duS u·Γ²/D* ≤ C0; Γ = exp(CGam·m⁵·f·x^ε) | Ch:14, 53-57; `word_count_bound_holds` JD:279-291; used at TD16:549-562 |
| ramified share de ≤ 2f/b | du = duS·(1 − 1/(T_u − 1))^f | TD16:891-921 |

**What is consumed, mathematically.** Fix one complex place v of the totally complex field LL. P_u : C_u → HH are the Poincaré-series maps, with dim C_u = duS u and dim HH = Dall [PAIRB §0]. In orthonormal bases these give PMat.
- The κ-rows of PMat·Vr are, up to invertible changes of basis, the matrix of B_u : N_u ⊗ LL → RR^∨ ⊗ LL (TD16:1087-1093). The κ-rows are the Bessel-functional space EE ≅ RR^∨ ⊗ ℂ, of dimension Drows.
- The hypotheses make {√γ_u·P_u} a near-tight frame of HH.
- `joint_a_ramified_holds` (TD16:596-600) turns this into the **robust near-surjectivity** RANK read (TFS:66-67 [RANK]): for LL-subspaces Ñ_u ⊆ N_u ⊗ LL of total codimension ≤ ε·Σd_u, the LL-rank of Σ_u B_u(Ñ_u) is ≥ |κ| − (η + 4ε + 4√e)·Dall ≥ |κ|·(1 − (1−δ_p)^{−1}(η + 4ε + 4√e)).
- **No injectivity is used.** The sources overfill the target by a factor of at least x^{CH}·(1 − de) (TD16:549-562).

### 1.3 Sizes of W, BL and k/n²
- **W** = `D.what₂.Word`, binary strings of length k [THEOREMS §1]. Two bounds are imposed:
  - C0·Γ²·x^{CH} ≤ |W| (Ch:56-57);
  - log|W| ≤ (k−3)·log 2 (`Win_at`, QLD:237).

  So log|W| ≈ 2·CGam·m⁵·f·x^ε + CH·log x ≲ k ≈ x^{4.5+10ε}, which is ≪ U ≈ x^{2.5}·b.
- **BL** = (1−δ_p)^{−1}·[4uF·log(1 + HH/uF) + (η + 4√e)·HH].
  - HH is any bound with s − μ_min(cc) ≤ HH. It is supplied as x^{CH}·b by LinkDIV_at clause 2 (`sFrame + RR.muMax ≤ x^CH·b`, GTI:78) and `Lat_at` (μ_min^∨ = −μ_max, QLD:185-186).
  - Hence (η + 4√e)·HH ≤ 6b (QLD:258-260).
  - The uF-term is the HN spread. It is bounded in L8 by the ledger's three error families [LEDGER L8, L9], not by the frame.
- **k/n²** is m·Nc with Nc = |T2|·k·b·x^{2ε}/n² (`budgetNc`, `FactNc`, DA:204-210; `SizeData₂.Nc` = `budgetNc D.R x ε |T2|`, DP2:230 by grep).
  - k = D.R.k ≈ x^{9/2+10ε} is the rank of the definite Bessel space W_u. n = D.R.n = |A| ≈ x^{2+8ε}. T2 is the set of thick tops.
  - Producer: `LinkN_at` (GTI:40-43): etaSum_j ≤ dZ0_j·C·(f·m·b·L² + log²x·Nc) + Σ vvTerm. Here etaSum_j = Σ_{w twisted} lwP·e_w·η_j(w), the congruence lengths (TWP:99-101).
  - It passes through `divinN_of_hypV` (DNV:117-140) into `DIVinN_at` (GTI:59-60) and then into LinkDIV_at (vii) (GTI:82-84), i.e. L1.
  - **Bost (L0) does not see it.**

## 2. Argument: the trace down the live path, and the logic

### 2.1 Root to the consumers (all read)
- `shape_closed_link_n_of_green` (TS:33-55) calls `topDesWin … 2 3 2 0` (TS:52) with:
  - hIRR = `closed_linkIRR_of_join_count hGreen 𝒜 sel cIc hcI irrC` (TS:54);
  - hS = `link_alt_alt_bis … sLp sO h30 …` (TS:55);
  - hGL = `hgl.2` from `link_gl` (TS:35).
- `topDesWin` packs ⟨LinkG, LinkS, LinkIRR, LinkDIV, LinkMu⟩ = `GlobalTheoremInputs` (DW:30-31; GTI:158-160).
- `linkGLOBAL7_items` destructures that tuple (LMin:704) and feeds lS, lI, lD into the frame (LMin:717-719).
- TS's binders sLp, sO, h30, irrC are `HypsAlt` fields (TopShapeAlt greps :59-62, :86-90). They are filled in `nonempty_hyps_of_allRows_alt` (NHA:21, 49-80) from `AllRowsAlt`, which `allRows_of_open0_alt` builds (LRI:50-87):
  - `sLp := loc.1`, `sO := loc.2.1` with `loc = lg1_sLp_sO_hTF hSW …` (LRI:56, 74-75) → `at_choice_alt` (AC:16-28);
  - `c30 := row_counts_of_labels_alt hSW KPx _ _ _ o.lab` (LRI:79) → `row_counts_of_ties_alt` (RCT:12-21). This gives both h30 and irrC.

### 2.2 Each piece: live or dead, status, file:line

| piece | live supplier | status | twin(s) / transfer |
|---|---|---|---|
| **Theorem S, off-diagonal**: for u ≠ u′, ‖K0(tO u u′)‖²_HS ≤ (1 + b^{−6})·d_u·d_u′/D*, where K(u,u′) = (c_u c_u′)^{−1/2}·P_u*·P_u′ on C_u′ → C_u, the Gram kernel of Poincaré series in HH (dim Dall); constant exactly 1 up to b^{−6}; also hsSq ≤ same | `at_choice_alt` → `GlobalTheory.CarrierGap.offDiag` (AC:22; OK0:673-684) → `offDiagonalK0_of_rows` (LSF:58-112) with `TheoremSDistinctWords` from `theoremS_of_conj` (TSC:68-80) → `theoremS_closedP` → `theoremS_rec` (SpectralTiesReal.lean:202, grep) → `pbApplied` (TSt:19-46) → `t_PairBound` (GOB:525, grep) | proved by named theorems; all 19 conjuncts of `TheoremSClosedHypotheses` are supplied by `_holds`/`_outright` lemmas (OK0:636-661) from hSW, RowNGP, UniqGap, carrierP; leaves unread | `theoremS_selected_of_loops` (TSO:1026) and `TheoremSSingle` are **dead** [THEOREMS]. PAIRB's `PairBound` is the live `t_PairBound`, so PAIRB, COUNTS Part 2, THMB and SLEAVES transfer (same lemma names on the chain) |
| **Theorem S, diagonal and Kpp**: ‖K(u,u) − 1‖² ≤ e0·d_u | `hypOwnL_diagP`, `hypOwnE_kppDiagP`, `hypOwnE_kppOff` in `theoremS_transport_link_zero` (LSP:131-163) | read by THEOREMS; leaves `diagonal_positive_final`, `kernel_diagonal_positive` unread | — |
| **LinkS assembly** | `link_alt_alt_bis` (TPS/LinkAltAltBis.lean:16-48) → `theoremS_transport_link_zero` → `theoremS_link_concrete` → `theoremS_link_of_evaluation` → `linkS_of_standing_hypotheses` + `countOwn_of_rowsPEv` (LSP:97-128) | proved | RANK's alternatives (LinkSFinal, LinkSPos, CountT, …) are not on this chain |
| **Counting theorem** (`CountingTheorem`): \|D − d(π∞)·vol·e(1)\| ≤ e^{−(1/16)·n·f·log n}·main term, for very regular discrete series of U(J) with signature (p,q), q² ≤ n, noncompact gap ≥ C·n¹⁹·f⁵·log(b·rd) | h30 = `count_constants_of_siegelWeil hSW` (CCS:11-24; RCT:16, 19) → `count_typed_of_volumeStep` (CTV:12-19) → `unitaryAutomorphicCounting_of_compactDualVolumeRatio` (UAC-Statement:18-19) → **`CountFinal.countingTheorem_of_volumeStep`** (UAC:37-49) | proved conditionally on hSW (VolumeStep ← SW); near/far/deep/flag leaf bodies unread [COUNT] | same theorem COUNT read, so COUNT transfers. The tie to D's Dall is `RowsTieP PLevT' (Fm.D x i) X` from `rowsTiePT'_of` (LSP:150-153); its body is unread |
| what is counted | Dcount = dim Re·Hom_{G∞}(π∞, L²(G(F)\G(𝔸))): the e-fixed π∞-isotypic multiplicity [SLEAVES]. `CountAllPointsClass` quantifies over all `AutInst` (BCE:46-60, 72-73) | — | — |
| **FormulaGap** (lowest-K-type compression formula) | `lowestKType_compressionFormula_of_strictLowestKType` = `GlobalTheory.Jet.FormGapFree.formulaGap` (FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean:18, 22) | proved, read [FORMULAGAP] | **twin** `formulaGap : StrictLow → FormulaGap` (FM/EventuallyUJ.lean:182, grep) is dead. FORMULAGAP read the live one |
| **DecGap** | `decGap_of_formulaGap` (FM/LowestKTypeDecayGapOfCompressionFormulaGap.lean:11, grep; UAC:40) | proved, read [FORMULAGAP] | — |
| **germ_jet_zero** (Casimir inequality) | called at FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean:49; statement FM/HighestWeightGapBound.lean:391 | proved, read [GERMJET] | unique (grep) |
| **LinkIRR**: 0 ≤ δ_p ≤ e^{−x^{ez/7}}, where Drows = (1−δ_p)·Dall | `closed_linkIRR_of_join_count` (TPS/LinkIrr.lean:22-43) → `linkIRR_of_join_ex` (LIx:17-32) → `linkIRR_of_allRows` (ConcNP.lean:647, statement only) | proved from irrC, Green and hSW; bodies unread | — |
| irrC: an `AllRows` record with `LabelCountGoodInjective`, `AllJoinA` and `CountAllRows` at εC = e^{−c·r·f·log r} | `irreducibilityRow_of_concreteAutomorphicData hSW rowsFinDim_link` (RCT:17, 20; statement `…Statement.lean:13`, body `irr_row_closed` unread), under ties `AutTie ∧ RowDictTie ∧ LabTie` from `o.lab` | statement only (here) | — |
| Green: GL_d(F_g) cuspidal characters ↔ irreducible polynomials | `green_of_regular P.greenRegularCharacters` (TPS/SiegelEisensteinSecondTermHypotheses.lean:73); definition LabelDatum.lean:108-112 | literature field of the root record (J. A. Green's classification) | — |
| **Count5** (L5) | `countF_fam Fm h5` (LMin:711), with h5 = `family_part_five_of_explicit_constants (division_level_prime_family h2b h2v h3)` (LMin:734); `countF_fam` uses `logGam_le` (JointsL.lean:1152-1155) | the FamGLmin inputs (LXL:42-53) are unread | **not** the counting theorem: a lower bound on log T_u (§2.4). The pk twin built h5 from h24 (LSS:496) |
| ramified rank | `ramRankF_min Fm hE` (LMin:659, 718) | body unread | twin `ramRankF_of` (LSS:506) is dead |

### 2.3 Why near-orthogonality plus the count gives the rank Bost needs
*(Inferred mechanism; the Lean steps are `frame_at_of`/`joint_a_ramified_holds` [RANK §2].)*

Let Q = Σ_u γ_u·P_u·P_u* on HH, with γ_u = 1/c_u (TD16:1101).
- tr Q = Σ_u tr K(u,u) ≈ Σ_u d_u, since ‖K(u,u) − 1‖² ≤ e0·d_u.
- tr Q² = Σ_{u,u′} ‖K(u,u′)‖²_HS. This is ≤ Σ_u ‖K(u,u)‖² + (1+η0)·(Σd)²/D* by Theorem S.
- Overcompleteness gives Σd ≥ D*/σ with σ = x^{−CH}. So the diagonal sum is ≤ σ·(Σd)²/D*.
- The count gives Dall ≤ (1+η1)·D*. Hence tr Q² ≤ (1 + η0 + η1 + σ + O(√e0))·(tr Q)²/Dall.
- tr Q² ≥ (tr Q)²/Dall always, with equality iff Q is scalar. So Q is scalar up to relative Frobenius error O(η0 + η1 + σ + √e0). This is a near-tight frame, and the argument is dimension-free.
- For subspaces Ñ_u of small total codimension, tr_{S^⊥} Q ≤ ε·tr Q on S^⊥, where S = Σ P_u(Ñ_u). So dim S^⊥ ≤ (η + 4ε + 4√e)·Dall.
- The rows of HH split into EE (Drows rows, the Bessel functionals ≅ RR^∨ ⊗ ℂ) and the rest (δ_p·Dall rows). Projecting onto EE does not increase codimension.
- On EE the rows are exactly the matrices of B_u. Here Vr is M_u ↪ C_u, of codimension ≤ de·d_u (TD16:1092-1093).
- Hence: the B_u-image of any large HN piece of ⊕N_u has nearly full rank in RR^∨.
- Bost's slope inequality puts B_u(HN piece of slope ≥ s − τ + h_u) inside the HN piece of cc of slope ≥ s − τ. So only a fraction w(τ) of cc's slopes lie below s − τ. The layer cake then gives L0.

**Why the leading constant must be exactly 1 and the count must be precise.** A constant 1 + c in Theorem S, or a relative error c in Dall/D*, turns into η ≈ c. The Bost loss is then (η + 4√e)·HH = c·x^{CH}·b, against an allowed error of ≈ b ≪ U. So the needed relative precision is about x^{−CH}, where x^{CH}·b bounds the slope spread s − μ_min(cc) (GTI:78). In the Lean this is exactly FrameReal_at's η0, η1, √e0 ≤ x^{−CH}/2 (TD16:529). `matRealF_of` converts LinkS's e^{−x^{ε/8}} into this via E·x^{CH+1} ≤ 1 (TD16:769-805). Nothing stronger is used by L0.

### 2.4 Where the size constraints come from
- **k ≳ m⁵·f·log b.** This comes from two places:
  - PairBound's `SizeNumbers`: k ≥ 8·Cn·(2r+2)⁵·f·log b, with 2r+2 = m [PAIRB §1; THEOREMS §1];
  - the word count: log|W| ≤ (k−3)·log 2 together with log|W| ≥ 2·log Γ = 2·CGam·m⁵·f·x^ε (Ch:56-57; QLD:237).
- **k ≤ n²·x^{1/2−ε}** is a record clause (`Win_at`, QLD:241). It keeps the congruence allowance m·Nc ≈ m·k·b·x^{2ε}·|T2|/n² within the budget U·x^{1/2+O(ε)}.
- **n ≳ m⁴.** Combining the two with f = 2n gives n ≳ m⁴·x^{O(ε)}. In the Lean m⁴ ≤ n is a *proved size lemma* from SizeN and SizeM (`m_pow_four_le_n`, `m_pow_four_le_f`, `Formalism/LocalRingCardinality/FourthPowerRankLeNF.lean:8-61`). m⁴ ≤ f also appears as a *hypothesis* in Theorem-S-side parameter blocks: `GlobalTheory.Core.Deg.HypL` (`…/LatticeFrames/VanishingGramTermsBoundParams.lean:22-23`), `Params.m_pow_le` (`…/PoincareCuspForms/WordDerivativeBlocks.lean:200`), and others (grep in §6). Whether those blocks are live was not traced.
- **Count5 at relative 1/m.**
  - Count5 is `Count_at` (QLD:167-171): log T_u ≥ Σ_j mean_ρ log(w_{jρ}·v/π) + m·lg − C·(La + m²La/k).
  - T_u is the norm of the word's anisotropic vector [THEOREMS §1]. Its error ΣA·La is the "x/m" family relative to Main [LEDGER §2a].
  - *(Inferred)* T_u is the parameter that `ChoiceOfT` fixes so that d_u ≍ D*/Γ² (the Theorem-S window). The use of `logGam_le` in `countF_fam` (JointsL.lean:1155) and MB's `Count` term −2·logGam/(f·k) (MB:131-133) point that way.
  - So non-vanishing pins T_u, and T_u enters the height. It is not a multiplicity count.
- **The frame η.** This is the polynomial x^{−CH} of §2.3.

### 2.5 Non-compactness of U(k + r_S, r_S + 1)^f
- The signature (k + r_S, r_S + 1) at every real place, with m = 2r_S + 2, is COUNT's (k − 1 + m/2, m/2) [COUNT (a); THEOREMS §1]. Witt index ≥ 1, so the quotient is non-compact.
- How the Lean handles it [COUNT §2; PAIRB §0]:
  1. HH is the π∞-isotypic, level-e part of L², and π∞ is an *integrable* discrete series. So R(φ_e) with φ_e = d·⟨w, σ(g)w⟩‾ is an exact orthogonal projection, and its range consists of cusp forms (`CuspFrame`, Wallach's theorem in substance). No spectral decomposition and no truncation are used.
  2. The diagonal kernel is bounded pointwise region by region:
     - identity term = D*;
     - near terms: γ is forced unipotent (Kronecker + Minkowski, g₀ > 4n split); they contribute ≤ e^{−n f log n/4} through flag measures;
     - far terms ≤ e^{−h·ε²/16}, by `DecGap` (very regular weight);
     - the deep cusp is bounded by D times a sup-norm bound (≤ e^{−n²f}).
  3. The Poincaré series are unfolded twice with only absolute-convergence lemmas.
- **Mechanism of the exponential precision** [COUNT §2 (ii)-(vi)].
  - The weight kills only the far terms.
  - The near (unipotent) and thin/deep contributions are small because cuspidal regions have small relative volume in **rank**: e^{−n f log n/4}, from the hermitian Siegel mean value through `VolumeStep` ← Siegel–Weil.
  - So the brief's model ("very regular weight ⇒ only the identity term survives") is half right. The weight handles far γ, and the rank n·f ≈ x^{6.5} handles the cusp and the unipotent terms.
- **Literature** *(auditor knowledge, not from the tree)*. Limit multiplicity for discrete series is known:
  - with pseudo-coefficients: de George–Wallach (cocompact); Savin (non-cocompact, integrable discrete series, congruence towers); Clozel (non-cocompact, via the trace formula);
  - for GL_n/SL_n generally: Finis–Lapid–Müller;
  - with power-of-level error terms in some families: Shin–Templier.

  All of these are asymptotic in the level with the group fixed. None is uniform in rank n and degree f, and none has error e^{−n f log n}. The tree's theorem is **in-tree**, proved conditionally on `SiegelWeilUnitaryConvergent`, and goes well beyond the literature in rank-uniformity and error. The Bost step needs only relative x^{−CH}. That too is uniform in n ≈ x^{4.5}, f ≈ x^{2}, which is still beyond anything published.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `frame_at_of`, `frameF_of` | TD16:538-600, 606-646 | FrameReal_at + ChProviso + ChCode + NuFull + Lat ⇒ Frame_at with η = 5x^{−CH} + 3√de | the Bost/frame step | glue (read); core content in `joint_a_ramified_holds` [RANK] |
| `matKF_of`, `matSF_of`, `matS_at_of`, `matRealF_of` | TD16:1348-1390, 862-884, 821-852, 750-805 | LinkS + BesselId ⇒ InputSG on PMat; conversion e^{−x^{ε/8}} → x^{−CH}/2 | Theorem S → frame | glue (read) |
| `blockReal_at_of` | TD16:1283 [RANK] | κ-rows of PMat·Vr = matrix of B_u | ties the Gram to B_u | glue [RANK] |
| `TheoremSSelected` via `offDiagonalK0_of_rows` | LSF:58-112; OK0:673-684 | ‖K0‖² ≤ (1 + b^{−6})·d d′/D* | near-orthogonality | **core**; leaves unread |
| `t_PairBound` | GOB:525 [PAIRB] | abstract row bounds ⇒ ‖K0‖² ≤ (1 + b^{−6})·dd | Theorem S assembly | glue/elementary [PAIRB] |
| `countingTheorem_of_volumeStep` | UAC:37-49 | CountingTheorem from VolumeStep | Dall ≈ D* | **core**; leaves unread [COUNT] |
| `formulaGap`, `germ_jet_zero` | FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean:22, 49; FM/HighestWeightGapBound.lean:391 | compression formula; jet uniqueness | DecGap → far terms | core, read [FORMULAGAP; GERMJET] |
| `closed_linkIRR_of_join_count`, `linkIRR_of_join_ex` | TPS/LinkIrr.lean:22-43; LIx:17-32 | label counts ⇒ δ_p ≤ e^{−x^{ez/7}} | δ_p | core-ish; inner bodies unread |
| `irreducibilityRow_of_concreteAutomorphicData` | …Statement.lean:13 | hSW + RowsFinDim + ties ⇒ AllRows with CountAllRows(εC) | irrC | core, statement only |
| `rowsTiePT'_of` | LSP:150-153 (use) | the selection's RowsAut X satisfies RowsTie with D (Dall = X.D) | ties the count to *this* HH | core link, unread |

## 4. Oddities

1. **The k/n² mislabel** (§0.3). The term MAIN-ARGUMENT calls "non-vanishing" is the E2 congruence allowance in `LinkN`. Its hypothesis status is that of `nRest` (a `HypsAlt` field, NHA:47), not that of Theorem S.
2. **Over-delivery.** Theorem S gives 1 + b^{−6}, the count e^{−n f log n/16}, and LinkIRR e^{−x^{ez/7}}, where L0 needs x^{−CH}/2, x^{−CH}/2 and δ_p < 1 (TD16:529, 716-723; QLD:191-193). This is harmless. It means a reviewer can test a much weaker claim: a polynomial-precision, rank-uniform count and orthogonality would suffice for L0 *(inferred)*.
3. **The count is stated over all `AutInst`** (BCE:46-60), not about D. Its application to D's Dall rests entirely on `RowsTieP`/`AutTie` (`rowsTiePT'_of`, unread). If that tie failed, Dall ≤ (1+η1)D* would concern another space.
4. **LinkS's own e0, η0 are discarded** in `matSF_of` (`_t0`, `_t1`, TD16:880). They re-enter through `matKF_of` from the same LinkS (TD16:1358). This is consistent, not a gap.
5. **Stale statements upstream.** MAIN-ARGUMENT §9.4 and RANK still say Theorem S and LinkIRR are "proved only conditionally (`theoremS_selected_of_loops`)". On the live path both are carried by named theorems; THEOREMS had shown this for Theorem S. LEDGER's LinkGLOBAL hop points to a twin (§0.2).
6. **What "IRR" is** *(inferred)*.
   - The labels are polynomials over F_{g_k}; Green's theorem identifies irreducible ones with cuspidal characters of GL_r(F_g).
   - δ_p is the share of HH whose level-type label tuple is not `goodTuple` (ACy:271-275). Its bound comes from the label weights `lawL` (ACy:283-290): non-squarefree labels carry weight ≤ 3/g.
   - The bad-share formula `Wg` (ICS:57-62) is 3f/g + 23·f·log g/√g + 2fm(·) + (N/2)·(7/8)^f + e^{−f/(5 log N)}. Under `SizesAt` (g ≥ e^{8x^ε}, f ≥ x², min(q,d) ≥ e^{x^{ε/6}}, ICS:66-68) this is tiny.
   - I did not unfold `goodTuple`.

## 5. What on this side rests on statements only
1. Theorem S leaves: `rowFormAllP_of`/`massDataInputsAll_of` (RowMain, the mass-formula main term), `loopRows_of_rowsFinDim_alt`'s inputs (LoopRowS), `rowNGP_of_siegelWeil`, `KExpansionC_holds`/`FoldOKC_outright`/`OOIntAllC_outright`, `carrierP`/`uniqGap_holds`, `exists_symm_invariant_kernel…`, `theoremBRotated` [THEOREMS; PAIRB; COUNTS; THMB; SLEAVES].
2. The counting-theorem leaves: `nearModerate`, `farBound_of_ptBound`, `deepRegion_kernelDiagonal_bound`, the flag and volume bounds, and `VolumeStep` ← SW [COUNT].
3. `SiegelWeilUnitaryConvergent` itself. The root supplies an in-tree theorem [THEOREMS]; not re-read here.
4. `rowsTiePT'_of` (count ↔ D) and `BesselId` (rows ↔ B_u; it arrives as LinkDIV (iv) and its supplier was not traced here).
5. LinkIRR: `irr_row_closed`, `linkIRR_of_allRows`, the ties `RowDictTie`/`LabTie` from `o.lab`; Green (literature).
6. `FrameLA1`, `slope_inequality_mean`, `layer_cake_formula` [RANK].
7. `ramRankF_min`; ChosenProviso/ChosenCode (design existence, upstream); the Count5 inputs `division_level_prime_family`(h2b, h2v, h3).

## 6. Coverage
Read in this pass:
- PROTOCOL; MAIN-ARGUMENT §0, §1 table, §5, §6, §7, §9; NODE-LEDGER, LIVEPATH, RANK, THEOREMS (all); COUNT, COUNTS (all); PAIRB:1-80; SLEAVES:1-60; FORMULAGAP:1-70; GERMJET:1-70; THMB:1-60; HIGHERRANK:1-60; ADMB2:1-40; SLOPESN:1-90; ROWSU:1-90.
- Lean:
  - MB:80-229; QLD:140-275; LSS:440-515; GTI:40-168; DA:170-212; TWP:85-125; DNV:1-30, 100-140;
  - TS:1-57; DW:1-35; LGl:1-33; LXL:1-110; LMin:690-737 (and its declaration list); TD16:515-664, 679-1008, 1087-1108, 1348-1469; Ch:14, 53-81; JD:279-291;
  - TPS/LinkAltAltBis.lean:1-50; TPS/LinkIrr.lean:1-46; TPS/TopPlug.lean:1-19; TopShapeAlt greps; NHA:1-90; LRI:40-90; AC:14-30; TPS/RowCountsOfLabels.lean:1-16; RCT:12-22; TPS/CountsIrreducibilityConstants.lean:80-115;
  - CCS:1-26; BCE:40-100; CTV:1-21; UAC-Statement:1-19; UAC:1-51; LSP:95-163; OK0:636-686; LSF:1-112; TSC:55-95; TSt:15-50;
  - FM/LowestKType…Statement tails; LIx:1-80; ACy:240-290; ICS:55-70, 175-200; IrreducibilityRow…Statement.lean:13-20; TPS/SiegelEisensteinSecondTermHypotheses.lean:66-76; LabelDatum.lean:108-112;
  - FourthPowerRankLeNF.lean:1-63; VanishingGramTermsBoundParams.lean:1-35; WordDerivativeBlocks.lean:190-205; StandardLattice.lean:575-640; JointsL.lean:1152-1175; TheoremThreeOfExplicitAndCompact.lean:199-211.

Greps run:
- `theorem (…)?formulaGap|germ_jet_zero|decGap_of_formulaGap|t_PairBound` (twins; one twin of formulaGap found);
- `m *\^ *4 *≤` (m⁴ ≤ f sites);
- `\.Nc\b|budgetNc` together with `LinkS|Frame_at|InputSG|delp|LinkIRR` (no non-record use of Nc in frame files);
- `pbApplied`, `theoremS_rec\b`, `link8`, `linkGLOBAL7_min`.

Not opened:
- `joint_a_ramified_holds` and `FrameLA1` bodies (taken from RANK);
- `theoremS_closedP`/`theoremS_rec` bodies beyond the grep line;
- `rowsTiePT'_of`, `irr_row_closed`, `linkIRR_of_allRows`, `ramRankF_min`, `Loss7.stLoss7`;
- the Count5 producers;
- the `SiegelWeilUnitaryConvergent` proof.
