# NODE-TDIV: is the T-adic integrality of the π̄_T^{−nBr}-scaled last map genuine?

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(mine)* = my own computation or inference. [NODE] = taken from that node and not re-read. Nothing was compiled or executed.

Abbreviations: as in NODE-TU (FSN, IPF, PFZ, AGP, LPk, DK). New ones:
- `SLU` = `Formalism/LocalToGlobal/Columns/StdLatUnimodular.lean`
- `DF` = `Formalism/LocalRingCardinality/DataForms.lean`; `DKr` = `Formalism/LocalRingCardinality/DataKernels.lean`
- `ONS` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OrthogonalNormSquareSum.lean`; `PBL` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodBoundLastLog.lean`
- `FMT` = `Formalism/SharpRestriction/GlobalSchurBounds/FiniteModelOfAdmissibleTransports.lean`
- `EIP` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsIntegralPendingObjectSymmetricFormsLevel.lean`
- `GI/` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`
- `TS` = `Formalism/LocalToGlobal/HermitianForms/TiedSym.lean`; `TStep` = `Formalism/LocalToGlobal/HermitianForms/TiedStep.lean`; `LCU` = `Formalism/LocalToGlobal/HermitianForms/LastCoordinateUniformizerVectorSpansOrthogonalLi.lean`
- `RP` = `Formalism/LocalToGlobal/HilbertRowConditions/RowPin.lean`; `LIT` = `Formalism/SharpRestriction/SmoothDesignExistence/LatticeIndexTer.lean`; `REF` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/ReferenceChainEvaluationAtBundlePoints.lean`

## 0. Verdict

**Genuine, and understood at the level of mechanism. It rests on unread record-existence statements (§3). No ESCALATE.**

1. **No T-adic divisibility is claimed for free.** The live level-T column point is the lattice L = N ⊕ O_E·z0 with h(z0, z0) = T. It is not the unimodular lattice N ⊕ O_E·e_last.
   - The Lean says this in `TilTied.til_lat`, `hermitianForm_lastCoordinateUniformizerVector_self` (LCU:109-120) and `TilBaseLat` (LCU:122-125).
   - It is the same lattice as FSN's mirabolic decoration: `Deco.L` (SLU:121-122), the kernel of x ↦ h(π_T e_last, x) mod P over P ∈ vT, is N ⊕ O·π_T e_last *(mine, from SLU:165-177 and `hT`: π̄_T ∉ P, FSN:161)*.
2. **Integrality is defined at that point's own lattice.** The record lattice of column forms is *defined* by integrality of values in coordinates of a local basis of the **dual** lattice of each point (`ValTied.lat`, TStep:118-123).
   - The last-map coordinate is y ↦ h(z0, y) = π̄_T·y_last.
   - So the "π̄^{nBr}-divisibility in standard coordinates" is the standard integral structure Sym(L) at a level-T point, not a property of the forms.
3. **The archimedean bound is a Fock-norm identity, counted once.**
   - The metric is taken in orthonormal frames (`ValTied.ipV`, TStep:107-111).
   - In z0-coordinates the Gram matrix carries T on the last row (`Pend.ipV_co`, `gFull` = …·lastGL(√T), PFZ:472-473, 500-503).
   - FSN's scalar π̄^{−nBr} on unimodular coordinates (FSN:137, 197-198) is the same map as the unscaled branching map `brOne` on z0-coordinates (`LowerMapTieS`, RP:16-26).
   - In periodFun_le the factor T^{−nBr} is the scalar |τ(π̄)|^{−2nBr}, plus the norm of brStd, which is `LastMapNorm` at g = 1 (PBL:26-43; IPF:36-47, 82-83). There is no second factor T^{−a}.
4. **The cost is in the source slope, not at the finite places.** Integral forms at level-T points have larger orthonormal-frame norms.
   - In rank one the gain and the cost cancel exactly (§2.3).
   - In rank N the cost is the *average* weight per dimension, ≈ (|λ|/N)·log T ≈ (a/k + b′)·log T per top. The gain is the degree of the *extracted* component, nBr ≈ a_t.
   - This matches the Lo5 floor term c·|TT|·m·(a/k + b′)·log T (QSB:12-14 [TU]). The net is ≈ a(1 − O(m/k))·log T. That is a legitimate gain in Bost's inequality, because the period functional reads only the heavy component.
5. **What stops a larger T is rank.** The source dimension d*_u(T^k − 1)^f would exceed e·D*Γ^{−2} (clause 1 of `VandermondeCountExplicit`, T3E:158-174 [TU]). The joint map into a target of fixed dimension then cannot be injective, so it cannot frame. That is a real obstruction. *(The consumer of the upper half in RANK was not re-read.)*

## 1. Statement (transcriptions)

**`brAt`** (FSN:137)
- brAt_t = (∏_τ t_τ^{−nBr(λ_τ, σ_τ)})·brStd.
- brStd = brConst·proj_{VV(σ)} ∘ coefLast_b (FSN:92-94, 128-135). Here coefLast_b keeps the monomials whose last-row exponents are b and whose last column is zero (`IsTop`, FSN:87-88).
- nBr = |λ| − |σ| (FSN:57) is the total last-row degree, and brConst = ∏ cBr·κ (FSN:53-55, 119).
- `brC` takes t_τ = τ(star π_T) = τ(π̄_T) (FSN:197-198). So **π̄_T^{−nBr} multiplies the functional.**
- **`deg`** = nBr − m(t+1)/2 (DF:249-250). So deg ≈ a_t at a top.

**"Translated by π_T"** (`DecoSet.til`, SLU:165-177, 700-701; `tilQ`/`tilC`/`evzC`, FSN:204-213). There is no isogeny and no torsion translate. A row point (N unimodular, with level data at the g-places) goes to the column point:
- with lattice tilN = N ⊕ O_E·e_last;
- with mirabolic level datum f_P(x) = h(π_T e_last, x) mod P at each P ∈ vT (π̄_T ∉ P). This datum is the vector z0 = π_T e_last.

`evzC` restricts a column form to these points (seesaw restriction U(n) ⊂ U(n+1)). `PtilFF` (FSN:215-218) is the class sum Σ_{d′} ⟨brC(F(til d′)), G(d′)⟩.

**`LastMapNorm`** (ONS:48-60). Take a Fock space VV(λ) whose Gram is G′ ⊕ g (last coordinate weighted by g), and t with t̄·g·t = T. Then brAt_t is a scaled coisometry onto VV(σ) with Gram G′, of factor ∏ T^{−nBr/2}|cBr|√κ, and it has op-norm² T^{−ΣnBr}·∏cBr²κ.
- *(mine)* Rank-one check: ‖z^n‖²_g = n!·g^n gives |t^{−n}c|² = ‖f‖²/(n!(|t|²g)^n) = T^{−n}‖f‖²/n!.
- Proved: `lastMapNorm` (`.../DivisorProofs/LastMapNorm.lean:395`, via `BrNorm`; body not read).

**`periodFun_le`** (IPF:26-88). |s(Ptil(ψ, F))|² ≤ e^{lastLog}·‖ψ‖²·‖F‖².
- Here ψ = column form ∘ til on row points, with the unimodular-coordinate Fock norm `sqAt` at Gram 1 (IPF:60-67).
- The proof:
  - uses |s(τ π̄_T)|² = T (IPF:37-46);
  - applies `coefOpLe_brAt`, which is `LastMapNorm` at G′ = 1, g = 1 (PBL:26-43);
  - then applies Cauchy–Schwarz over the class sum (`sum_pair_le`, PBL:52-57).
- So the archimedean T^{−nBr} is the bare scalar.

**`Conclusion6`** (PFZ:330-343), with Pt = P.lowerMap ∘ P.evz. All of the following are abstract record fields: `PeriodMap` (DKr:163-182), `ptLat`, `ptEmb`, `ipP`, `beOn` (DF:199-212). It asserts:
- `til` injective and `stabMap` bijective;
- Pt maps Fi_m into ptC;
- ∃ PRat with **PtilIntegral**: PtL(lat_m.L) ⊆ ptLat.L at *all* finite places (DF:264-273);
- the majorant bound ‖PtL x‖²_v ≤ ptB·‖x‖²_v, ptB = ∏_τ T^{−deg τ}·beOn_τ² (PFZ:332);
- the same bound with ipP / ipC.

## 2. Argument

### 2.1 Live supplier of Conclusion6

| step | name | file:line | content |
|---|---|---|---|
| 1 | `pt0` / `aPt0` | AGP:301-303; REF:16-19 | Closed family statement ∀u Conclusion6, consumed by `admissible_level_two` → adm2 (AGP:276-284) |
| 2 | `referenceChainEvaluation_bundlePoints_overColumns` | GI/ReferenceChainEvaluationBundlePointsOverColumnsA.lean:12-20 | at every constructed point β: `property_at_constructedPoints_of_trueColumnsView` with `aux_of_ok_of_pins` |
| 3 | `formsMap_at_every_trueColumnMember` | GI/FormsMapAtEveryTrueColumnMember.lean:15-26 (wrapper GI/FormsMapAtEveryTrueColumnMemberStatement.lean) | gets `FormsTiedSym` C from `colsTiedSym_std`, `lowerMap_tie`, `beOnTie_true`, roots of unity |
| 4 | `formsMap_of_symmetricComparison_lowerMap_finiteChar` | GI/FormsMapOfSymmetricComparisonLowerMapFiniteChar.lean:12-15 | ∃ Pend with ArchimedeanSignatureMatching (EIP:291-333); `symmetric_level_clauses_hold` gives `ClassMapInjectiveBijectiveNorms` |
| 5 | `classMap_estimate_of_partial` | FMT:2259-2263 | Conclusion6 := ⟨…, PRat_of, **Pt_integral**, norm bound⟩ |
| 6 | `Pt_integral` ← `Pt_loc` | FMT:2240-2247, 2192-2199 | at each w: `pt_co` ∘ `Pt_eq` ∘ `blk_IntSpan` (br preserves IntSpan) ∘ **`lat_co`** |
| 7 | `lat_co` in EIP | EIP:303-327 | from `(Tf.val m).lat` (TStep:118-123): the values of integral forms lie in IntSpan in the coordinates of any local basis of the **dual lattice** of the point; the level character is absorbed by a root of unity r^{−1} ∈ O_w |

`s10` (LPk:229) and `LevelPrimeItems` (LIT:56-58) are family *hypotheses*. They are consumed in `muRank_pk`/`prvF_…`, and their only producer is a further hypothesis (`FamGL.s10`, `.../LinkGLOBALPk.lean:21-26`). The live `FamGLmin` has no s10 field (`.../LogXLowerFamilyOfTheorems.lean:39-50`). So the live supplier is the `aPt0` chain above. `PerDec0` was not located (see §5).

### 2.2 Why integrality at T holds *(mine, on the Lean definitions)*

- The point lattice at til c is K.lat c ⊕ O·z0 with h(z0, z0) = T (LCU:111-115).
- Its dual contains z0/T. The coordinate dual to z0 is y ↦ h(z0, y).
- `LowerMapTieS` (RP:16-26) says lowerMap is the unscaled branching map brTen on the polynomial P with column value fnOf(mZ(z0)) P, i.e. in these coordinates.
- So the scaled value is the coefficient of an integral polynomial. Integrality holds by the definition of the lattice at w, uniformly at every w, including the places above T. No step is specific to T.

### 2.3 Rank-one model *(mine)*

Setting: E ⊇ K, T = ππ̄ split. Use a hermitian line E with h(x, y) = x̄y and point lattice L = O·z0, z0 = π. Then L^# = π̄^{−1}O. Take a weight-n function f(y) = c·y^n, written in the orthonormal coordinate.

- **Integral at L** (`ValTied.lat`): write y = Y·π̄^{−1}, so Y = π̄y = h(z0, y) and f = (cπ̄^{−n})Y^n. Integral ⇔ p := cπ̄^{−n} ∈ O. At the unimodular point O, integral ⇔ c ∈ O.
- **Last map**: f ↦ p = π̄^{−n}c. This is brAt with t = π̄ (FSN:198). It is integral by definition.
- **Archimedean**: ‖f‖² = n!|c|² (Fock), so |p|² = T^{−n}‖f‖²/n!. This is LastMapNorm at g = 1, and also Conclusion6's ptB.
- **Product formula**: for integral f ≠ 0, c = π̄^n p gives ‖f‖² ≥ n!·T^n. So the source lattice's slope drops by (n/2)·log T, exactly the gain: Bost reads 0 ≤ 0.
- Brief's option (i): applying π̄^{−n} to forms integral at the *unimodular* point would leave a pole of order n at π̄. The Lean does not do this. Its source lattice is integral at the level-T points.
- Option (ii) is the Lean's mechanism, with the lattice changed from O to πO, i.e. "degree" T, not a T-isogeny pullback.
- Rank N: the source cost is the average per-dimension weight (|λ|/N)·log T. The gain is the extracted component's last-row degree, nBr. The net is (nBr − |λ|/N)·log T > 0, a true gain because φ sees only the T^{nBr}-heavy component.

### 2.4 Task 4: doubling T

The gain grows by a·Δ log T. The costs grow by m·EatT·Δ log T (WDS:887-901 [TU]) and c|TT|m(a/k + b′)·Δ log T (Lo5), which are smaller. What fails is clause 1 of `TorusPairsWithVariant`/`VandermondeCountExplicit`, d*_u(T^k − 1)^f ≤ e·D*Γ^{−2}: the source has more level-T points than the target has dimensions.

- This is the rank obstruction: an injective, framed joint map ⊕B_u needs Σ d_u ≲ dim target.
- The lower pin T ≥ T* is what the main term needs: −a·log T ≤ −a·log T*, via Count5.
- The upper pin is what the frame needs.
- *(inferred; the RANK consumer was not re-read.)*

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `colsTiedSym_std` | not opened | a `FormsTiedSym` exists at constructed points | supplies `lat`, `ipV`, `til` (z0), `evz`, `per` | **core, unread** |
| `ValTied.lat`, `.ipV` | TStep:93-123 | integral = dual-lattice coordinates; metric = orthonormal frames | the level-T integral structure | definition (read) |
| `TilTied`, `TilBaseLat` | LCU:109-125 | the column point is K.lat ⊕ O z0, h(z0, z0) = T | the "translation" | definition (read) |
| `LowerMapTieS` / `lowerMap_tie` | RP:16-26 | lowerMap = brOne in z0-coordinates | ties FSN to the record | statement read; producer unread |
| `ipV_co_ofS` | `.../BlockActions/NfAllSmulReB.lean:237` | the metric in z0-coordinates is Fock(gFull) | Gram T on the last row | body unread |
| `Pt_integral`, `Pt_loc`, `classMap_estimate_of_partial` | FMT:2192-2263 | as in §2.1 | integrality | glue (read) |
| `lastMapNorm` | `.../LastMapNorm.lean:395` | the Fock coisometry identity | archimedean factor | standard (Fock/Bargmann); body unread |
| μ(M_u) floor (L3) and the Lo5 (a/k + b′)·m·log T term | MB:140, QSB:12-14 [LEDGER, TU] | must be proved for the **same** level-T lattice (fm u).lat m | where T is paid | **core, unread** |

## 4. Oddities

1. **Two models of one point.** FSN (`Deco.til`, a unimodular lattice plus a functional, with a scalar π̄^{−nBr}) and the record (`TilTied`, the lattice N ⊕ O z0, unscaled) describe the same map only through `LowerMapTieS` and `Deco.L` = N ⊕ O·π e_last. I checked this identification by hand, not through a Lean lemma.
2. **NODE-TU's "ledger is monotone in T" needs one correction.** The source-slope cost at level T is *not* absent: it is the Lo5 term, whose size matches the honest cost (a/k + b′) per level. The monotonicity is real (a ≫ m·a/k), and only rank stops it. That is consistent with a correct Bost inequality.
3. `deg` subtracts m(t+1)/2 from nBr (DF:249-250). The small loss is unexplained.
4. `MemberForms` admits degenerate instances (`ptLat := oneHLat`, `beOn := 0`; e.g. `.../SpanPowerMembership/TrivialColumnsRamifiedTop.lean:308-324`). I did not check whether any is live.

## 5. Coverage

**Read:**
- FSN:1-240; SLU:20-200, 695-720; DF:1-290; DKr:160-200;
- PFZ:1-40, 300-355, 440-555, 555-607; FMT:2192-2300;
- ONS:30-75; PBL:20-60; IPF:1-120;
- AGP:240-320; LPk:195-270; LIT:1-95; `.../FamilyLevelPrimeInputsOfSizes.lean` (all); `.../LinkGLOBALPk.lean` (all); `.../LogXLowerFamilyOfTheorems.lean:1-110`;
- `.../PrvFOfFamilyTheoremTiesEventualIncidenceTransport.lean` (all); `ParamsHeightRankConstant.lean:140-175`;
- REF (all); the GI files of §2.1 (all); EIP:285-335;
- TS:1-140; TStep:85-130; LCU:100-170; RP:1-60; `.../KernelLattices/InterlaceAll.lean:115-140`.

**Greps run:**
- `def DecoSet.til|def til|til_smul|abbrev DecoSet`;
- `PtilIntegral|PRat|ptLat :|beOn :|til :`; `structure PeriodMap`;
- `def LastMapNorm|coefOpLe_brAt|lastMapNorm`; `Conclusion6`; `MemberChainIntegral|…ShareFamilyAtConstant…`;
- `LevelPrimeItems|levelPrimeItems_of_proved|integrality_last_map|product_first_zeroth_parts.ConclusionOnFamily`;
- `product_first_zeroth_parts.KudlaFamilyStatement|family_statement_of_pointwise_const`; `ClosedPacketCrystallineStatement`;
- `FamGL 𝒞|s10 :=`; `Adm2InU|pt0 :=|aPt0`; `ReferenceChainEvaluationAtBundlePoints`;
- `aux_of_ok_of_pins`; `classMap_estimate_of_partial|LowerMapTieS|BeOnTie|exists_integralPendingObject…`;
- `ipV_co_ofS|FormsTiedSym|coMTS|lastGL|sqrtT`; `TilTied|ValTied`; `Pt_loc`.
- **`PerDec0`: not located.** It was not among these greps, and I did not grep for it separately.

**Not opened:**
- `colsTiedSym_std`; `lowerMap_tie`; `beOnTie_true`; the body of `ipV_co_ofS`; `blk_IntSpan`; `symmetric_level_clauses_hold`;
- the L3 floor producer; the RANK frame's use of the dimension upper bound.
