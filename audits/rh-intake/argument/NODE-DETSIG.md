# NODE-DETSIG: the determinant identity det ι = κ^D·∏_j det θ_j (H1) and the layer signatures (k+j−1, m−j) (H4)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `SO` = `Formalism/DivisorInequality/StatementObj.lean`
- `QMS` = `Formalism/QuotientMetricDivisors/Statement.lean`
- `SPD` = `Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SpecDet.lean`
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`; `IU` = `…/IndefiniteForms/IndefUse.lean`
- `PO` = `Formalism/LocalToGlobal/IndefiniteReal/PartsOrth.lean`; `CXL` = `…/IndefiniteReal/CxLemmas.lean`;
  `CXC` = `…/IndefiniteReal/CxCore.lean`; `CT2` = `…/IndefiniteReal/CutTuples2.lean`
- `RL` = `Formalism/LocalToGlobal/Divisibility/RowLat.lean`
- `BLP` = `Formalism/LocalToGlobal/IndefiniteReal/BaseLiftsPackageOfPrimitiveLinks.lean`;
  `ZPE` = `…/IndefiniteReal/ZeroPartEigenvalueConvention.lean`; `HIE` = `…/IndefiniteReal/HasInfExpF.lean`
- `DLP/` = `Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/`
- `RLK` = `Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/RealLowestKTypeCoeffSquareIntegrable.lean`
- `LSS` = `Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/LabelSettingScalars.lean`
- `ECA` = `Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsCarries.lean`
- `FRA` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinRepApply.lean`
- `PRM` = `Formalism/LocalRingCardinality/Params.lean`; `SPC` = `Formalism/LocalRingCardinality/DataSpaces.lean`
- `INF` = `Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/InfinityTypes.lean`
- `TWA` = `Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ThetaWeightArithmeticAtPlaceProof.lean`
- `ZON` = `Formalism/LocalToGlobal/Divisibility/ZscOfNum.lean`; `ABS` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/AnchorBoundStatement.lean`
- `DHB` = `Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean`

"The Lean says" = I read the line. *(inferred)* = my reading. Nothing compiled. Status tags:
**[proved, read]** proof body read; **[proved, stmt]** in-tree proof, only statement/top-level call read;
**[hyp]** hypothesis/field passed down; **[not found]**.

## 0. Verdicts

| Q | Answer |
|---|---|
| H1(a) | The hypothesis is an equality of **metric determinants** at the archimedean places: (det Gram of ι(e_i) in the EE-metric)/(det Gram of e_i in the top metric) = κ_v^D·∏_j (same ratio for θ_j). It is a hypothesis of `BoundsMu`, but `BoundsMu` itself is a proved theorem (`slope_bounds`). |
| H1(b) | Supplier on the live route: `IndefSide.boundsMu` (IU:271), called from `divClauses_of` (DHB:779). It gets the identity from `IndefRows.detId` (IU:196), which is the **proved linear-algebra lemma `SpecDet`** (SPD:160) applied to three inputs: ι is a (κ·∏_jλ_{j,p})-similitude on each Hecke part p; θ_j is a λ_{j,p}-similitude on the matching part; and dim(part p of EE) = dim(part p of W_j). Going down: `CxLinks` → `CxCore` → `PrimRows3` fields `thmB` (ΘΘ* = κ∏λ), `thmA` (θθ* = λ), `dimParts`, `scalConj`. `thmB` is proved from **`Scal`**, i.e. from two Rallis inner-product theorems (AForm, BForm) with the **same partial L-values**. `dimParts` is proved from **`MultEq`**, a multiplicity-equality theorem between the inner forms U(Y_0) and U(W_j). Both rest on `Published.*` inputs. |
| H1(c) | **Not** a block-triangular glue. ι is the m-fold row descent Θ, and the θ_j are separate theta lifts on the layers. Nothing factors ι through the θ_j as maps. The identity is a **Rallis-type identity, part by part**: on each Hecke-isotypic part c, ‖Θx‖² = κ₀·∏_{j=1}^m L^S((1+t)/2, π_c ⊗ μ_j^{−1})·‖x‖², and ‖θ_j y‖² = a_j·L^S((1+t)/2, π_c ⊗ μ_j^{−1})·‖y‖². The same L-value appears because both theta steps have rank gap t, the same eigensystem c and the same splitting character μ_j. The determinant identity then follows by taking determinants over parts, once the multiplicities agree. |
| H1(d) | Partly definitional, but not a stand-in. (i) ι_{μ₀} = **identity matrix** by the choice of coordinates on EE (`rowMat_base`, CXL:352). (ii) At places v ≠ v₀ the EE-metric XE_v is **defined** (`rowXE`, RL:320) as the top metric rescaled by κ_v∏_jλ_{j,p,v} on each part. So there the ι-half of the identity is true by construction. (iii) κ is pinned as "the" constant in ΘΘ* = κ∏λ (uniqueness, `IsKap.unique`). What carries content: at v₀, the Rallis identities `thmB`/`thmA` (one κ, uniform in c and in t); at v ≠ v₀, `GalD`; at every v, `dimParts`/MultEq. |
| H4(a) | `sigW j := (k + j − 1, m − j)` is a **definition** (PRM:46). W_j is a free datum of `Spaces` (SPC:121-132): rank r, signature sigW j at every real place, isometric to Y_0 at all finite places. The signature is not derived from the row tower. It is the unique signature for which the layer theta weights work out. The proved lemma `arithAt` (TWA:186) needs exactly p = k+j−1 strictly positive and q = m−j strictly negative entries in the centred HC parameter, and this is forced by the gap conditions b_j < e_j < b_{j+1}. |
| H4(b) | *(inferred, on Lean shapes read)* (U(V_j), U(W_j)) with V_j definite of rank n = r+t is a compact dual pair. By Kashiwara–Vergne, a weight on U(V_j) of the form (a_1..a_p > 0, 0^t, −b_q..−b_1 < 0) lifts to the holomorphic-type discrete series of U(p,q) with lowest K-type (a + n/2 ; −b − n/2) (shifted by e_j). `INF:62-67` encodes exactly this. Twisting the fixed Y_0 HC parameter (v, −b) by the character μ_j with archimedean exponent −e_j moves the zero line between b_j and b_{j+1}. That leaves k−1+j positive and m−j negative entries, hence the signature (k+j−1, m−j). |
| H4(c) | Σ_{j=1}^m (p_j − q_j) = Σ_j (k + 2j − 1 − m) = mk (arithmetic). It is consumed as l3m j = Σ_τ (p_j − q_j)·e_j(τ)·logΩ (ZON:64-66, ABS:112-117), the covolume main term of layer j. The total is Σ_j(p_j−q_j)Σ_τ e_j logΩ = mk·ē·logΩ + Σ_j(2j−1−m)Σ_τ(e_j − ē)logΩ, so only the residual depends on the j-variation of e_j (NODE-ACCOUNT C2). |

## 1. Statement

### H1(a): the hypothesis in `BoundsMu` (SO:17-79, read)
The Lean says (SO:38-41):
```lean
(∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
(∀ t, detRatio (XQ t) XE (ι t) v0 = (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
```

Types:
- K is a totally complex number field (= LL);
- D ≥ 1;
- ι t, θ j t : K^{D×D} invertible;
- XQ t, XE, XT j t, XW j : (archimedean places) → ℂ^{D×D} invertible "frames", i.e. square roots of inverse Gram matrices (`IsRatHerm`, QMS:66-69);
- κ : places → ℝ_{>0};
- ρr t > 0 with ρr μ₀ = 1.

**`detRatio`** (QMS:42-46, read): detRatio(XS, XT, φ)(v) = det Gram_{XT,v}(φe_1, …, φe_D) / det Gram_{XS,v}(e_1, …, e_D). So it is |det φ|² measured from the XS-metric to the XT-metric at v. As mathematics, with H_E, H_Q, H_{T_j}, H_{W_j} the hermitian metrics at v:

  det(ι*H_E ι)/det H_Q = κ_v^D · ∏_{j∈J} det(θ_j* H_{W_j} θ_j)/det H_{T_j}

This is stated for t = μ₀ at every infinite place, and at the base place v₀ for every tuple t (with an extra ρr_t). On the live call ρr ≡ 1 (IU:316, `fun _ => 1`). `BoundsMu` is proved (`slope_bounds`, `BaseLevelBoundsWithCovolumeHolds.lean:47`; not opened). Its conclusion (SO:72-79) is μ(RR^∨) ≤ meanLog κ + Σ_j lcv(XW_j, M_j)/D + 2Σ lw·Fy + LG + E. *(inferred)* The proof is the product formula: covol(RR) = covol(image of the top lattice under ι), with |det ι| traded for κ^D∏|det θ_j|, and then the θ_j-images traded for M_j through the index hypotheses.

### H1(b): the supplying lemma, `SpecDet` (QMS:132-150, statement read; SPD:160-178, proof read) **[proved, read]**
Let Q = ⊕_p Q_p and T_j = ⊕_p T_{j,p} be direct-sum decompositions (`iSupIndep`, sup = ⊤) with dim Q_p = dim T_{j,p} for all j. Suppose:
- majAt_E(ιx, ιy) = (s·∏_jλ_{j,p})·majAt_Q(x, y) for x ∈ Q_p and all y;
- majAt_{W_j}(θ_jx, θ_jy) = λ_{j,p}·majAt_{T_j}(x, y) for x ∈ T_{j,p} and all y.

Then detRatio(XQ, XE, ι)(v) = s^D·∏_j detRatio(XT_j, XW_j, θ_j)(v).

The proof (SPD:162-178) computes each side as ∏_p (scalar_p)^{dim} and regroups the products. This is honest linear algebra: if G′(x, ·) = c_p·H(x, ·) on Q_p, then det G′/det H = ∏_p c_p^{dim Q_p}. The parts need not be orthogonal.

## 2. Argument (the trace, consumers first)

### 2.1 Consumer of BoundsMu → detId → SpecDet
- `divClauses_of` (DHB:751-779, read) calls `P.base.boundsMu Formalism.DivisorInequality.boundsMu specDet …` with P : IndefCore. The same proof uses −log κ_v − min_p Σ_j log λ_{j,μ₀,p,v} on the height side (DHB:742-748). κ enters once with + (covolume) and once with − (height).
- `IndefSide.boundsMu` (IU:271-330, read) takes `hdet0 := S.detId hS wf μ0 v (Or.inl rfl)` and `hdet1 := S.detId hS wf t v0 (Or.inr rfl)` and feeds them to `hM` at exactly the det-hypothesis slots.
- `IndefRows.detId` (IU:196-205, read) is `specDet_rect` (IU:173-194, read) applied to:
  - `S.l1c.1`, `S.l1c.2.1` (ι_t, θ_{j,t} bijective);
  - `Qpart t p := (Ep p).comap ι_t` and `Zpart j t p := (Wp j p).comap θ_{j,t}` (IS:271-275), with their decompositions (IU:162-170, read; proved from l1c and the base decomposition);
  - `part_dim` (IU:118, grep line only), from `l1d : DimensionsOfPartsAgree` (IS:313-314);
  - the scalar clauses `S.l1c.2.2.2.2.1/2` = the last two clauses of `RowLatticeBoundForBasis` (IS:304-311, read).

  These hold only for (t = μ₀ ∨ v = v₀). That is exactly the range of the two BoundsMu hypotheses.

### 2.2 Who proves l1c and l1d for the live record
- `rowsOf` (CXL:484-515, read) builds `IndefRows` from `CxData.data` (PO:171-185, read: ι := rowMat, θ := liftMat, κ := X.κ, lam := X.lam). Its fields are:
  - `l1c := ⟨rowMat_bij, liftMat_bij, h4pos.1, h4pos.2.1, scal_rows, scal_lifts⟩`;
  - `l1d := hL.l1d b`.
- `scal_rows` (CXL:411-447, read):
  - **at v = v₀**: from `hL.h4`, i.e. `H4` (PO:226-231): ⟨Θ_t x, Θ_t y⟩_EE = nP·κ_{v₀}∏_jλ_{j,t,p,v₀}·⟨x, y⟩_{XQ_t} when Θ_t x lies in the EE-part p. XE_{v₀} = frameOf(Gram(Θ_{μ₀}e_i)/nP) (`XE_spec`, CXL:390-409) is the genuine Petersson Gram of the descended basis. **This is content.**
  - **at v ≠ v₀, t = μ₀**: rowMat μ₀ = 1 (`rowMat_base`, CXL:352-353), and `rowXE_part` with `partsOrth` closes it. XE_v is *defined* by `rowXE` (RL:320-324, read) as `rowFrame v0 Y 1 (partPr) (κ_v∏_jλ_{j,p,v}) XQ`, i.e. the top metric rescaled part by part. **Definitional** (oddity 1).
- `scal_lifts` (CXL:449-482, read):
  - at v₀ from `ewNorm` + `thmA` (PO:265-269): ⟨θ′x, θ′y⟩ = nP·λ_{j,t,p,v₀}·⟨x, y⟩_{XT}, with XW_{v₀} the Gram of the layer basis bW;
  - at v ≠ v₀ from `galD` (PO:271-276), the same identity for the conjugate-place Gram of bW. Both are content.
- The suppliers of `H4`/`ThmA` are `cutRows`/`CutLifts` (CT2:107-109, 136-138; read as statements): ThmBop ∧ PartsE ∧ IsoR … ⇒ H2 ∧ H4. Here
  - **`ThmBop`** (CT2:99-101): Θ_tΘ_t* e = κ_{v₀}∏_jλ_{j,t,p,v₀}·e for e ∈ EE_p ∩ EE_level;
  - **`ThmAop`** (CT2:128-130): θ′_jθ′_j* w = λ_{j,t,p,v₀}·w on W_{j,p};
  - **`DimParts`** (CT2:140-142): dim(W_{j,p} ∩ good) = dim(EE_p ∩ EE_level).
- `prims_of_core` / `links_of_core` (CXC:162-195, read) copy `thmBop`, `thmAop`, `galD` and `dimParts` from `CxCore`. On the RealDat3 route, `complex_data_conditions_base_level_of_primitive_links` and `base_lifts_package_of_primitive_links` (BLP:240-345, read) set:
  - `thmBop := RealDat3.thmBop_of hP.thmB`;
  - `thmAop := thmAop_of hC.phase hP.thmA`;
  - `galD := hP.scalConj`;
  - `dimParts := hP.dimParts`;
  - κ := constant `R.kap`, lam := `R.lam3` (ZPE:120-150, read).

  `thmBop_of` / `thmAop_of` (BLP:174-196, read) are only the transport through the Tw-twist and a unit phase.

### 2.3 The real content: PThmB, PThmA, DimParts
- `PThmB` (BLP:71): `Lift.IsKap m (Θ_t∘Θ_t*) EEp3 lamN kap`. `IsKap` (HIE:182-184, read) says ΘΘ* = κ·∏_{j=1}^m λ_{j,t,p} on every part p, for all t. `PThmA` (BLP:68-69): θ_jθ_j* = λ_{j,t,p} on W_{j,p} (`IsLamP`, HIE:163-165).
- **`PThmB` is proved [proved, stmt].** `thetaLift_theoremB_publishedHypotheses` (`DLP/ThetaLiftTheoremBPublishedHypothesesStatement.lean:30`) = `pThmB_short` (`DLP/ThetaLiftSecondHypotheses.lean:37-47`, read). That obtains `Scal` and `MatchUp` from `thetaLift_scalarIdentity_matching_adjointInjective` and then applies `ThmBFromScal.pThmB` (ECA:51-112, **read**):
  - `Scal` provides lam_{i,t,c} and a single κ > 0 with θ_iθ_i* = lam_{i,t,c} on W_{i,c} and ΘΘ* = κ∏_i lam_{i,t,c} on EE_c (RLK:50-53);
  - `act_on_part` identifies R.lam3 with lam via `hC.scal.lam0` (uniqueness);
  - R.kap = κ via `hC.scal.kap` (uniqueness of the IsKap constant).

  So κ and λ are pinned, not chosen.
- **`Scal` is proved from AForm and BForm** (`DLP/ThetaLiftScalarIdentityMatchingAdjointInjective.lean:36-42`, read: `scal_of_aForm_bForm`).
  - **AForm** (RLK:41-43): ∃ a_i > 0 such that on W_{i,c}, θ_iθ_i* = a_i·z, where z = `IsLval R i t c z`. Here **`IsLValue R t B (i+1) l`** (LSS:30-33, read) means l > 0, the Euler product converges, and l = L^{S}((1+t)/2, B ⊗ μ_{t,i+1}^{−1}), with B the rank-r parameter of the eigensystem c and S = badPl t. This is supplied by `thetaInnerProduct_eq_const_mul_LValue` = `aFormL` (`DLP/ThetaInnerProductEqConstMulLValue.lean:47-53`, read), built from `twistedThetaLift_innerProductFormula_of_hypotheses`, `fockVector_matrixCoefficient_formula`, `finiteZetaIntegral_thetaLift_eq_partialLValue`, … That is the **Rallis inner product formula** (Siegel–Weil + doubling zeta integrals) for the layer lift U(W_i) ↔ U(V_i). **[proved, stmt]**
  - **BForm** (RLK:45-47): ∃ κ₀ > 0 such that on EE_c, ΘΘ* = κ₀·∏_i z_i with the same z_i. This is supplied by `upInj` (`DLP/ThetaLiftAdjointScalarFormulaInjective.lean:33-38`, read) from `thetaChainStep_positive_scalar_standingHypotheses`, giving `Scalars R` (LSS:62-74, read), and then `ChainScalar.bForm` (`…/TwistedOperators/LevelGroupActionOnAdelicFunctionsEqZeroOfNoLift.lean:350-354`, read to line 354), which sets κ₀ = ∏_i κ(i+1).
  - `Scalars` says: for each step k of the row tower, the lift from level k to level k+1 multiplies inner products by κ(k+1)·L^S((1+t)/2, B ⊗ μ_{t,k+1}^{−1}) (`StepScalar`, and `TopScalar` for the last step). **[proved, stmt]**
- **`DimParts` is proved** by `baseLevel_goodForms_dims_agree_partwise` (`…/DivisorProofs/BaseLevelGoodFormsDimsAgreePartwiseStatement.lean:17-18`, read), called at `…/DivisorProofs/PrimRows3OfParts.lean:50` (read). The key premise is **`MultEq`** (FRA:118-130, read): for each layer i, each irreducible admissible "good" σ of U(Y_0)(𝔸_f), and a finite-adelic isometry Φ: U(Y_0) ≅ U(W_i), we have cuspMult(σ ⊗ π_∞^{Y_0}) = cuspMult(σ∘Φ⁻¹ ⊗ π_∞^{W_i}). `MultEq` is proved by `multiplicity_equality_statement` (`…/TwistedOperators/MultiplicityEqualityStatementStatement.lean:31`) and `multEq_of_classicalTheorems` (`…/DivisorProofs/PublishedLocalTheoryConsequence.lean:33-39`, read). That proof is a trace-formula comparison from Published inputs (PseudoCoefficientUpq, LabesseWaldspurger, …). **[proved, stmt]**
- `scalConj` (GalD) is a `PrimRows3` field filled by the argument `hGal` of `primRows3_of_parts`. **[hyp, supplier not traced]**

### 2.4 The mathematics of H1 *(inferred from the shapes above)*
Fix a Hecke eigensystem c (a "part p"). Let π_c be the corresponding forms on U(Y_0), with A-parameter B of rank r.
1. **Row side.** The m-fold descent Θ goes from the top definite forms down to EE ⊂ L²(U(Y_0)). Its adjoint is the m-fold lift, and each up-step Y_k → Y_{k+1} has rank gap t. Rallis: ‖lift u‖² = c_k·L^S((1+t)/2, Π_k ⊗ μ_{k+1}^{−1})·‖u‖². *(inferred)* The Lean writes the L-value with B, the **bottom** parameter, not the level-k one. This is legitimate if Π_k's parameter is B ⊕ (Hecke characters), the extra character factors being independent of c and absorbed into κ(k+1). So ΘΘ* = κ₀∏_k L_k(c).
2. **Layer side.** W_j is an inner form of Y_0, isometric at every finite place (SPC:126-132), so c also labels forms on U(W_j) (MultEq gives the same multiplicity). The lift U(W_j) → U(V_j) has the same rank gap t, so Rallis gives θ_jθ_j* = a_j·L^S((1+t)/2, B ⊗ μ_j^{−1}) on the c-part.
3. **Matching.** The same L-value L_j(c) appears on both sides. Setting λ_{j,c} := a_jL_j(c) and κ := κ₀/∏a_j, the identity ΘΘ* = κ∏_jλ_{j,c} holds with κ **independent of c and t**. That independence is the whole content of "one κ".
4. **Determinants.** Take the determinant over the parts, with multiplicities dim EE_c = dim (W_j)_c. This is SpecDet. It yields |det ι|² = κ^D·∏_j|det θ_j|² in the metrics.

So the row descent and the layers are linked through **one L-value per (step, eigensystem)**, not through a map. This answers ARCH §7.1: "the λ_j of io_j equal the Rallis scalars of θ_j" is not proved as an equality of two maps' constants. Each is separately proved equal to a constant times L^S((1+t)/2, B ⊗ μ_j^{−1}).

### 2.5 H4: where the signature comes from
- **Definition sites.** `sigW j := (k+j−1, m−j)` (PRM:46, read). `Spaces.W` / `W_rank` / `W_sigval` / `baseSpace_isometric_graded` (SPC:121-132, read) make W_j a datum: rank r, signature sigW j at every τ, finite-adelically isometric to Y_0. `FactKaBlocks` (`DataRows.lean:247-248`, read) is the trivial unfolding, proved as `factKaBlocks` (`RankBoundMonotoneInDimension.lean:244`, grep). A toy inhabitant (m = 2) exists (`SpanPowerMembership/Spaces.lean:457-471`, read).
  - *(inferred)* Existence for general m: by Landherr, a hermitian space with prescribed local invariants exists iff the number of places where the determinant sign flips relative to Y_0 is even. Here the flips occur at all f = [F:ℚ] = 2n real places or at none, so W_j exists.
- **Forced by the theta weights [proved, read].** `ArithAt D i τ` (INF:46-80) fixes, for the layer i+1 = j:
  - the V_j weight `thetaWt` = (aP_0, …, aP_{p−1}, 0^t, −aM_{q−1}, …, −aM_0) (INF:38-41), a weight of U(n) with n = r + t;
  - the U(p,q) discrete-series weight `kapW`: + part aP + (r+t)/2 − e_j, − part −aM − (r+t)/2 − e_j (INF:62-67).

  This is the Kashiwara–Vergne K-type correspondence for the compact dual pair (U(n), U(p,q)). It requires exactly p strictly positive and q strictly negative entries (`aPlus_pos`, `aM_pos`: aP, aM ≥ 1). `arithAt` (TWA:186-215, read) proves this from `sig_eq` (TWA:40-46, i.e. W_sigval) together with:
  - `one_le_aPlusQ` (TWA:87-94), using `gap_be` (e_j − b_j ≥ (t+3)/2, PRM:61);
  - `one_le_neg_dRowQ` (TWA:96-106), using `gap_eb` (b_{j+1} − e_j ≥ (t+3)/2, PRM:63).

  Here aPlusQ(a) = lamAt(a) + e_j − (p − a − 1) − (t+1)/2 (INF:31). *(inferred)* The centred parameter λ + e_j with λ = (v_1..v_{k−1}, −b_1..−b_m) has positive entries exactly v_1..v_{k−1}, −b_1+e_j, …, −b_j+e_j. That is k−1+j = p_j of them, and m−j = q_j negative ones. With any other split (p, q) with p + q = r, one of the positivity lemmas fails. So the signature is chosen as a parameter but is **the only one compatible** with lifting the fixed HC parameter twisted by μ_j.
- **Why the seesaw needs it.** V_j (definite, rank r+t, the type parts, Galois dimension nV) is the compact member of the dual pair. θ_j sends forms on U(V_j) of weight thetaWt to holomorphic-type discrete-series forms on U(W_j), and these lie in the same L-packet as Y_0's (same infinitesimal character, `INF:114-125` example). Y_0 itself has signature sigW(m/2) (`SignatureBaseMiddleEq`, PRM:83), so only the middle layer is Y_0's group at ∞. The other layers are the inner forms on which the j-th L-value L^S((1+t)/2, B ⊗ μ_j^{−1}) is realised by a *non-zero* archimedean theta lift. *(inferred)* W_m (q = 0) is definite: the base of the descending covolume induction (NODE-COVOL).
- **Use in the covolume [proved, read: definitional].**
  - `ZscOfNum.l3m j = Σ_ρ ((k+j−1) − (m−j))·w_{j,ρ}·logΩ` (ZON:64-66). `ABS:112-117` rewrites it by `show` as Σ_τ (p_j − q_j)·e_j(τ)·logΩ. So w_{j,ρ} = e_j(τ), the archimedean exponent of the very character μ_j that sets the signature.
  - `l3main_ofNum` (ZON:84-90) sums it over j.
  - Σ_j(p_j − q_j) = mk exactly. The residual Σ_j(2j−1−m)·Σ_τ e_j(τ)·logΩ is what NODE-ACCOUNT C2 bounds by about m·B0. It cancels against the m column steps' k·w·logΩ (NODE-WHYHALF §1.5, NODE-ACCOUNT C2; not re-read here).

## 3. Children

| # | Name | file:line | Statement (math) | Status | Weight |
|---|---|---|---|---|---|
| 1 | `SpecDet` / `spectral_determinant_formula` | QMS:132; SPD:160 | partwise similitudes + equal part dimensions ⇒ det identity | proved, read | glue (linear algebra) |
| 2 | `ThmBFromScal.pThmB` | ECA:78 | Scal ⇒ ΘΘ* = R.kap·∏λ on every part; pins κ, λ | proved, read | glue |
| 3 | AForm: `thetaInnerProduct_eq_const_mul_LValue` / `aFormL` | `DLP/ThetaInnerProductEqConstMulLValueStatement.lean:26` | θ_jθ_j* = a_j·L^S((1+t)/2, B⊗μ_j^{−1}) on the c-part of U(W_j) | proved, stmt | **core** (Rallis inner product formula for U(r) ↔ U(r+t)) |
| 4 | BForm: `upInj` ← `thetaChainStep_positive_scalar_standingHypotheses` (`Scalars`) + `ChainScalar.bForm` | `DLP/ThetaLiftAdjointScalarFormulaInjective.lean:32`; LSS:62-74 | each row step multiplies ‖·‖² by κ(k+1)·L^S((1+t)/2, B⊗μ_{k+1}^{−1}), with B the **bottom** parameter | proved, stmt | **core**; check that the level-k L-function reduces to B's up to c-independent factors |
| 5 | `MultEq` ← `multEq_of_classicalTheorems` | FRA:118; `PublishedLocalTheoryConsequence.lean:33` | equal cuspidal multiplicity of σ⊗π_∞ on U(Y_0) and on U(W_j) for all good σ | proved, stmt | **core** (trace-formula comparison of inner forms) |
| 6 | `GalD` (`scalConj`) supplier | PO:271; BLP:221 | θ_j is a λ_{j,p,v}-similitude at the conjugate places v ≠ v₀ | hyp, not traced | core for v ≠ v₀ |
| 7 | `arithAt` | TWA:186 | centred HC parameter has exactly (k+j−1) positive and (m−j) negative entries; K–V weight matching | proved, read | core for H4 (elementary) |
| 8 | `slope_bounds` (BoundsMu itself) | `BaseLevelBoundsWithCovolumeHolds.lean:47` | product-formula covolume bound given the det identity | proved, not opened | glue |

## 4. Oddities

1. **XE at v ≠ v₀ is synthetic.** `XE := rowXE …` (PO:146-147; RL:320-324). At non-base places the EE metric is the top definite metric rescaled on each Hecke part by κ_v∏_jλ_{j,p,v}, with ι_{μ₀} = 1. So at v ≠ v₀ the ι-half of the det identity is true by definition. This is legitimate in Arakelov terms (one may choose the metrics at other places), provided the height side uses the same XE_v. It does: DHB:742-748 uses −log κ_v − min_p Σ_j log λ_{j,μ₀,p,v} at every v, and L6 bounds log λ at every v. The content then sits in GalD (the layer side at v) and L6.
2. **ι_{μ₀} = identity** (CXL:352) by the choice of EE-coordinates (images under Θ_{μ₀} of the top type basis). So "det ι" at μ₀ and v₀ is just the Petersson Gram determinant of the descended basis relative to the top metric. The content is Rallis (ThmBop).
3. **κ is "the" constant.** `kapOf`/`kapNew` (`IntertwinersExistScalarUpdateInvariant.lean:48-50`; `InGeoGeoScalIff.lean:76`, read) define κ by choice as the IsKap constant if one exists. On the live route κ is pinned by `hC.scal.kap`. The non-trivial claim is **existence of one κ for all eigensystems c and all tuples t**. That is AForm + BForm with c-independent a_j, κ(k).
4. **The row step L-values use the bottom parameter B** (LSS:69-72), not the parameter of the level-k form. *(question for an expert)* This needs (i) the Adams-type description "parameter at level k = B ⊕ characters" and (ii) the extra factors L(χ_block μ^{−1}, (1+t)/2) being independent of c. Both are plausible. Neither is visible at the statement level.
5. **MultEq is strong.** It asserts equal multiplicities for **every** irreducible admissible good σ, with the fixed discrete series of signature (k+m/2−1, m/2) on Y_0 versus the fixed one of signature (k+j−1, m−j) on W_j. *(question for an expert)* By Arthur's multiplicity formula this holds for stable (simple) parameters. For endoscopic parameters the multiplicity depends on the character of the archimedean member, and that changes with the inner form. Whether "IsGoodRep" or the trace-formula proof restricts to the stable case I did not check. The type parts on V_j are non-simple (ρ ⊕ χ's), but the parts here are rank-r eigensystems on Y_0/W_j. Not an ESCALATE: the proof route exists in-tree (child 5), I did not read it.
6. **IsLValue demands l > 0 and convergence** at s₀ = (1+t)/2 (LSS:30-33). With t ≥ k+m+4 this is far into absolute convergence, so l ≠ 0 is automatic. Reality and positivity rest on θθ* ≥ 0. Consistent.
7. The det identity is used only for (t = μ₀, all v) and (all t, v = v₀). The clause `RowLatticeBoundForBasis` (IS:308-311) is stated only on that range too. Consistent.

## 5. Coverage

Read:
- SO:1-90; QMS:25-150;
- IU:150-330; IS:225-380;
- PO:1-345; CXL:340-515; CXC:140-195; CT2:60-150; RL:290-345;
- BLP:60-75, 160-345; ZPE:80-170; HIE:155-195;
- `DLP/ThetaLiftTheoremBPublishedHypothesesStatement.lean` (all); `DLP/ThetaLiftSecondHypotheses.lean:35-49`; ECA:1-112;
- `DLP/ThetaLiftScalarIdentityMatchingAdjointInjective{,Statement}.lean` (top level); RLK:20-70; LSS:1-110;
- `DLP/ThetaInnerProductEqConstMulLValue{,Statement}.lean` (top level); `DLP/ThetaLiftAdjointScalarFormulaInjective{,Statement}.lean` (top level);
- `ChainScalar.bForm` lines 350-356; `IntertwinersExistScalarUpdateInvariant.lean:30-100`; `InGeoGeoScalIff.lean:60-100`;
- `RestrictedCharacterDataValid.lean:40-60`; `PrimRows3OfParts.lean` (all); `BaseLevelGoodFormsDimsAgreePartwiseStatement.lean:17-18`;
- FRA:60-135; `MultiplicityEqualityStatementStatement.lean:31-32`; `PublishedLocalTheoryConsequence.lean:33-39`;
- SPD:160-178;
- PRM:1-90; SPC:60-168; `DataRows.lean:244-256`; `SpanPowerMembership/Spaces.lean:430-475`;
- INF:1-130; TWA:40-215; ZON:55-100; ABS:95-120; DHB:740-790.

Greps run:
- `BoundsMu\b`; `\.boundsMu\b|\.divCore\b`; `def detRatio`;
- `l1c :=|RowLatticeBoundForBasis`; `cxPkg|CxLinks`; `thmBop :=|thmAop :=|dimParts :=`;
- `thmB :=|PThmB`; `def Scal|def MatchUp`; `def IsLValue`;
- `W_sigval`; `FactKaBlocks`; `ArithAt`; `MultEq` suppliers.

Not opened:
- bodies of `aFormL`, `thetaChainStep_positive_scalar_standingHypotheses`, `multiplicity_equality` and `dimParts` (DimPartsFull);
- `slope_bounds`;
- the supplier of `hGal`/GalD;
- which `IndefCore` the root actually passes to `divClauses_of`. I followed the RealDat3/PrimRows3 producer that matches NODE-JOIN's `RowsAt4` (`CovolumeOntoIsometryConditions`, BLP:230-238). Several parallel producers exist (`LinksLemmas.lean:401`, `ConcretePkgSpec.lean:179`), and they share the same `PThmB` shape.
