# NODE-MULTEQ: MultEq (FRA:118), the row-step L-value (IsLValue / Scalars), and GalD

Paths are relative to `.../scratchpad/art/lean/src`. `DAV/` = `Development/AbelianVarietyTheory/`. Abbreviations from NODE-DETSIG (FRA, LSS, RLK, PO, …) are reused. New ones:
- `SOP` = `Formalism/LocalToGlobal/IndefiniteReal/ScalarOnPartsFull.lean` (DSModel, Mult)
- `HTV` = `DAV/Definitions/Divisors/HasTypeVec.lean` (TRCusp, HasTypeVec, RealStable)
- `EPT` = `DAV/BlockTheory/TwistedDiscreteSeries/EllipticPartTestData.lean` (XSet, PhiReal, NoFixed, Gap, EllipticPart)
- `TFH` = `DAV/Proofs/DivisorProofs/TraceFormulaOfHyp.lean`; `CTM` = `DAV/Proofs/DivisorProofs/CuspidalTraceMultiplicityGiven.lean`
- `ADM` = `DAV/Proofs/TwistedOperators/AtDatMultEq.lean`; `RRW` = `DAV/Definitions/AutomorphicMembership/RowRatW.lean`; `DII` = `DAV/Proofs/IwasawaDecomposition/DoublingInputsImply.lean`
- `ILM` = `DAV/Definitions/LatticeFrames/IsLevMeas.lean`; `SEN` = `DAV/Definitions/LatticeFrames/StepExactNS.lean`; `CPS` = `DAV/Definitions/LatticeFrames/ChainParSucc.lean`
- `SGD` = `DAV/Proofs/DecoratedLatticeProofs/ScalarsOfGivenData.lean`; `HFN` = `DAV/Definitions/LatticeFrames/HeckeFormNSOfHeckeForm.lean`
- `EAP` = `DAV/Definitions/Foundations/ExistsAuxiliaryPlaceNotMemFinset.lean`; `DSC` = `DAV/PublishedTheorems/TwistedTraceFormula/DiscreteSeriesCharacter.lean`

Tags: **[proved, read]**, **[proved, stmt]** (in-tree proof exists, only the statement or top-level call read), **[hyp]**, **[Published]** (a `GlobalTheory.Published.*` leaf, discharged only at the root as a field of the root hypothesis structure).

## 0. Verdicts

| Q | Answer |
|---|---|
| Q1 | **Plausible. Not ESCALATE.** MultEq compares two inner forms **of the same rank** (odd rank r), isomorphic at every finite place. The cusp multiplicity of σ⊗π_∞ on U(Y₀) equals that of σ∘Φ⁻¹⊗π′_∞ on U(W_i), where π_∞ and π′_∞ are discrete series with the **same Harish-Chandra parameter** λ on groups of different signature. "Good" means: σ has a vector of a level type τ = ⊗_{v∈S}τ_v at **split** places (irreducible representations of GL_r(F_q)), and for each 0<a<r some τ_v has no fixed vector under the unipotent radical of P_{(a,r−a)} (`NoFixed`, EPT:227). That condition kills every non-simple Arthur parameter (§2.3), so only stable/simple parameters survive. On the live route the proof is a simple-trace-formula comparison, not Arthur's multiplicity formula. Its inputs are 14 `Published` leaves. |
| Q2 | **Proved in-tree (statements read), not assumed.** The level-k parameter is **defined** as the Adams/Kudla iterate `chainPar c B k` = (B twisted) ⊕ ⊕_{i≤k} μ_i·(segment of length t) (CPS:121-126). `LFull` (ILM:179) is a theorem stating L^S((1+t)/2, chainPar(B,k)⊗χ_{k+1}^{−1}) = L^S((1+t)/2, B⊗μ_{k+1}^{−1})·H. Here H = ∏_{i=1}^k∏_{n=1}^t L^S(n, μ_iμ_{k+1}^{−1}) (`IsHval`, ILM:123). H contains no c and no B. Independence from t (and from the bad set) is a separate proved theorem, `RUnif` (SEN:74), built on `Restore` (ILM:202). So "κ(k+1) independent of c and t", which is part of the *statement* `ScalarsWith` (LSS:67), is discharged by proof. The Rallis inputs are the convergent-range Rallis inner product formula (`HeckeFormNS`, HFN:202, derived from Published Siegel–Weil, doubling and unramified-doubling leaves). They match Li 1992 / Ichino / Piatetski-Shapiro–Rallis in shape. One range question is listed under Oddities. |
| Q3 | `GalD` (PO:266) says: at every archimedean place v ≠ v₀ of the coefficient field, the K-rational layer-lift matrix θ_j(μ₀), embedded at v, is a λ_{j,p,v}-similitude from the top metric XT_v to the layer Petersson metric XW_v. Live supplier: `stage4` (`DAV/Proofs/DivisorProofs/RealDataWeightVectorFamily.lean`) → `doubling_method_consequence` → `galD_of_inputs`. It combines (i) `ConjRatLift5`, a hypothesis-free in-tree theorem: the σ-conjugate of the rational theta lift is the theta lift of the σ-conjugate datum; and (ii) `ConjScalarAt`: the Rallis scalar identity θθ* = l on Hecke parts for that conjugate datum. So GalD is **Galois equivariance of the rational theta lift, plus Rallis at the conjugate datum**. It is **not** "λ_v = σ(λ_{v₀})". |

## 1. Statement

### Q1(a) MultEq (FRA:118-126, read)
```lean
def MultEq (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (j : Matrix …) (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)),
    IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ →
    ∀ W σ, σ.IsIrreducible → IsAdmissible σ → IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC …) σ →
      cuspMult R.θ M₀ σ = cuspMult R.θ (R.MW i (sg0 D A)) (σ.comp Φ.symm…)
```
- **Groups.** U(Y₀) = `Yc D 0` = `D.sp.Y 0`, and U(W_i) = `Wc D i` = `D.sp.W (i+1)` (`LinksDefs.lean:358,362`). `IsFinIso` (FRA:73-86) gives a lattice-compatible finite-adelic isometry, and its `frame` field contains `V.rank = V'.rank`. **Same rank**, so these are inner forms that differ only at ∞ (signatures (k+r_S, r_S+1) and (k+i, m−i−1) per NODE-DETSIG). There is no Speh or rank-changing issue.
- **Multiplicity of what.** `cuspMult θ M σ` = dim Hom_{G(𝔸_f)}(σ, `allMaps θ M`) (FRA:60-66). `allMaps` is the span of multilinear maps T: ⊗_τ (smooth vectors of the archimedean model M_τ) → cusp forms on G(F)\G(𝔸) that are G(F_τ)-equivariant at every real place (`IsMultMap`, SOP:82-89; `Mult`, SOP:91). So it is m_cusp(σ ⊗ ⊗_τπ_τ).
- **Archimedean types.** `DSModel V S` (SOP:51-62) is a discrete series of U(V_τ) at each τ, with HC parameter `lam τ` and sign pattern `ε τ` (`IsDS`). On Y₀ the model M₀ is **arbitrary** with parameter `parA (Ptw D) 0`. On W_i it is the fixed model `R.MW i (sg0)`. `discrete_series_odd_rank_gap` (`DAV/Proofs/DivisorProofs/DiscreteSeriesOddRankGapStatement.lean:16`, stmt) supplies: Odd rank; one λ with M₀.lam = λ = MW.lam; and `Gap λ` (λ_i − λ_{i+1} ≥ r, EPT:230).
- **"Good".** `IsGoodRep` (FRA:109-112): σ has v ≠ 0 fixed by the level group `levG(flag1L L)` with Σ_g c_g σ(κ_g)v = v, i.e. v lies in a prescribed isotypic component for the finite group G ≅ G0 at the places Pg. `exists_typeVector_of_good_level_representation` (Statement file :17, stmt; uses Published GreenCuspidal) converts this to ∃T, `NoFixed T ∧ HasTypeVec T σ`. Here:
  - `TypeData` (EAP:399-410): a finite set S of **split** places (`frame : SplitAt`), with irreducible τ_v of GL_r(k_v);
  - `HasTypeVec` (HTV:27-30): K_v-spherical outside S and τ_v-isotypic at v ∈ S;
  - `NoFixed` (EPT:227-228): S ≠ ∅ and ∀ 0<a<r ∃ v∈S, τ_v has no `unipBlock a` (= U_{(a,r−a)}(k_v)) fixed vector.

### Q2 IsLValue / Scal / AForm / BForm (LSS:30-33; RLK:37-53, read)
- `IsLValue R t B j l` holds when: the Euler product of B⊗μ_{t,j}^{−1} converges at (1+t)/2 outside badPl t; l > 0; and L^{badPl t}((1+t)/2, B⊗μ_{t,j}^{−1}) = l. B is a rank-r parameter of the eigensystem c at **level 0** (`IsSysParamD … D.R.r c B`, used in `IsLval`, RLK:37-38).
- `AForm`: ∃ a_i > 0 with θ_iθ_i* = a_i·z on W_{i,c}, where z = IsLval(i, t, c). `BForm`: ∃ κ₀ > 0 with ΘΘ* = κ₀∏_i z_i on EE_c. `Scal`: the combination with λ = a·z and κ = κ₀/∏a.
- `Scalars` (LSS:67-74): ∃ κ : ℕ → ℝ_{>0} such that for **every** t and c, step k→k+1 of the row tower multiplies Petersson products by κ(k+1)·IsLValue(B, k+1) (`StepScalar`, LSS:57-60). κ(k+1) is quantified **outside** t and c.

### Q3 GalD (PO:266-272, read)
For all j, all archimedean v ≠ v₀, every Hecke part p, and x in the p-part:
⟨wC_{j,v}(θ_j(μ₀)x)_v, wC_{j,v}(θ_j(μ₀)y)_v⟩ = λ_{j,μ₀,p,v}·maj_{XT_{j,μ₀},v}(x,y).
This is the v-analogue of `ThmA` (PO:260-264), which is stated at v₀.

## 2. Argument

### 2.1 Q1(b) Live route of MultEq (consumers first)
1. `primRows3_of_parts` (`…/DivisorProofs/PrimRows3OfParts.lean:24-50`, read) takes `hME : MultEq` as a hypothesis and feeds it to `dimParts`, `levW` and `sumW`.
2. Its caller `primRows3_typesSep3` (`…/RealDataWeightVectorFamilyCore.lean:22-38`, read) takes MultEq as a hypothesis. It is passed up through `holds_of_ties` (`…/RationalDataSizedFamily.lean:18-31`, read) and `atDat_holds` (`DAV/Proofs/IwasawaDecomposition/HoldsFromPrintedInputs.lean:58-90`, read) to `holdsW` (same file :92-96). Its source there is the `multW` field of `HypH` (`…/AutomorphicMembership/MultW.lean:35-41`, read).
3. `HypH` is built by `hypH_of` (RRW:64-68, read). Its `multW` comes from the `MultL` argument (RRW:53-55). `hypH_of_rowRatW` (DII:17-20, read) fills MultL with **`atDat_multEq`** (ADM:15-41, read).
4. `atDat_multEq` copies the datum (same group) and calls `multiplicity_equality_statement` (`…/TwistedOperators/MultiplicityEqualityStatementStatement.lean:31`) → `MultEqFinal.multiplicity_equality` (`…/MultiplicityEqualityStatement.lean:33-36`, read) → `published_local_theory_consequence` = `multEq_of_classicalTheorems` (`…/PublishedLocalTheoryConsequence.lean:33-39`, read) → `multEq_of_trCusp` (CTM:56-74, **read**) with `TRCusp` from `trCusp_of_classicalTheorems` (TFH:45-62, **read**).
5. The 14 Published leaves form the structure `PrM` (RRW:35-49). They are filled from the root hypothesis structure `S0.HypothesesUE` in `member_bundles_large_ue` (`…/DivisorProofs/LinkedBundleConstructionExists.lean:37-40`, read). **[Published]**

`multEq_of_trCusp` (CTM:58-74) works as follows:
- it gets (T, NoFixed, HasTypeVec) from IsGoodRep;
- it replaces Φ by a product of local isometries j_v up to an inner automorphism b (`exists_localIsometries_innerAut_adelicFrameIsometry`, stmt);
- it gets λ, Odd and Gap;
- it rewrites both cuspMult as `mCuspDS` (`cuspidalMultiplicity_eq_discreteSeriesModel_maps`, stmt);
- it applies `TRCusp` (HTV:39-50, read);
- it transports by b (`conjEquiv`, CTM:16-35, read).

So **MultEq ⇐ TRCusp**, where TRCusp says: for V, V′ of the same odd rank, isomorphic at all finite places by lattice-compatible j_v; discrete-series models M on V and M′ on V′ with the same Gap-regular λ; and σ irreducible admissible with a NoFixed type vector, we have m_cusp(σ⊗M) = m_cusp(σ∘Φ⁻¹⊗M′).

### 2.2 Proof of TRCusp (TFH:45-62, top level read; children stmt)
It is the simple trace formula with:
- f_∞ = ⊗_τ pseudo-coefficient of M_τ (`IsTestArchG`, EAP:784-786);
- f_f = the type idempotent at S, spherical elsewhere, and one auxiliary place U.

The steps:
- **Spectral side** (`trace_inputs_imply_cuspidal_trace`, `pseudo_coefficient_separation`, `cuspidal_spectrum_finiteness…`). Only cuspidal σ⊗π_∞ contribute. Gap ensures that π_∞ = M is the only unitary representation with that infinitesimal character on which tr(f_∞) ≠ 0 *(inferred: with all gaps ≥ 2 every A_𝔮(λ) has compact Levi and is discrete series; then pseudo-coefficient orthogonality applies)*.
- **Geometric side.**
  - `hyperbolic_terms_vanish` and `non_field_type_vanishing` remove all non-elliptic γ and all elliptic γ whose characteristic polynomial is reducible over E.
  - `elliptic_trace_of_inputs` / `EllipticPart` (EPT:307-321, read) write the rest as Σ_P vol(T_P(F)\T_P(𝔸))·∏_v Φ_v(f_v)·∏_w Φ_w(f_w). Here Φ_v = Σ over `XSet` = (𝔽_P⊗F_v)^{+,×}/norms realisable in V_v (EPT:93-95) of the local orbital integrals, i.e. the **local stable orbital integral**.
  - `real_stable_of_characters` (from Published HarishChandraCharacters; DSC:301) gives `RealStable` (HTV:102-110): Φ_w(f_{π_w}) = conj(χ_{F_λ}(γ))/vol(T_w) (`PhiReal`, EPT:220-222). This depends only on λ, not on the packet member or the signature.
  - So both groups have the same geometric side (`trace_equality_of_geom_expansion`).
- **Separation** (`trace_separation_of_iwahori_trace`; Published GeometricLemma, ZelevinskyPolynomialRing) isolates each σ.

### 2.3 Q1(c) Why "good" excludes endoscopy *(inferred, checked against the Lean shapes)*
- **Type side.** Fix 0<a<r and the split place v_a where τ_{v_a} has no U_{(a,r−a)}-fixed vector.
  - Suppose σ's global parameter is non-simple: ψ = ψ₁⊞ψ₂ of dims (a, r−a), or a Speh block μ⊠S_d with a = r/d. Then σ_{v_a} is a subquotient of Ind_{P_{(a,r−a)}}(π₁⊗π₂) on GL_r(F_{v_a}).
  - Depth-zero K(1)-invariants commute with parabolic induction: (Ind_Pπ)^{K(1)} = R_M^G(π^{K_M(1)}). So every GL_r(k_v)-constituent τ of σ_{v_a}^{K(1)} lies in some R_{M_a}^G(X).
  - Such a τ has non-zero Harish-Chandra restriction to M_a, hence U_a-fixed vectors. That contradicts NoFixed.
  - So every σ with a NoFixed type vector has a **simple generic** parameter. That is exactly the case where Arthur / Kaletha–Mínguez–Shin–White give multiplicity 1 to every member of the packet on every inner form, so the statement is true.
- **Geometric side.** The same mechanism appears in the in-tree proof as `non_field_type_vanishing`. Elliptic γ with K′ = K′₁×K′₂ are exactly the tori transferred from U(a)×U(r−a), and they are killed through the constant term of f_{v_a}. For P irreducible over E (K′ a field, F′ its fixed field), the global G(F)-classes in the stable class biject with ∏_v XSet_v:
  - ker¹ is trivial, by the Hasse norm theorem for K′/F′;
  - the global reciprocity obstruction ∏_w ε_{K′_w/F′_w}(x_w) equals ∏_v ε_{E_v/F_v}(disc V_v·d_P), which is 1 by the product formula, because XSet_v pins disc V_v;
  - Landherr gives the global form.

  So the product form of `EllipticPart` is legitimate for these tori, and no κ-terms arise. This is consistent with K(T/F) = 1, since π₀(T̂^Γ) → π₀(Z(Ĝ)^Γ) is an isomorphism when F′ is a field.
- **Counterexample search.** I tried endoscopic (a, r−a) parameters, Speh / one-dimensional parameters, and non-tempered A_𝔮(λ) at ∞. The first two are excluded by NoFixed, the third by Gap. A sign mismatch (−1)^{q(G_∞)} between inner forms is ruled out by odd rank (see Oddity 1). I found no shape that the hypotheses fail to exclude.

### 2.4 Q2 Row-step L-value: where c-independence comes from
- `Scalars` is supplied by `thetaChainStep_positive_scalar_standingHypotheses` → `ScalarsRow.scalars` → `scalars_of_heckeFormNS` (`DAV/Proofs/DecoratedLatticeProofs/ThetaChainStepPositiveScalarStandingHypotheses.lean:29-41`, read) → `thetaChain_steps_positive_multiple_of_LValue` = `ChainTw.scalars_of_given_all` (SGD:48-67, read).
- The last of these assembles proved in-tree theorems (stmt):
  - `UpParQ`: a lift of a form of parameter B has parameter `stepPar χS χT t B` = B·χS/χT ⊕ seg(χS, t) (CPS:121-123). This is Kudla's unramified theta correspondence, from `HoweUnram` (itself proved: `howeUnram_holds`, used at DII:19). `chainPar` iterates it (CPS:125-126).
  - `LFull` (ILM:179-187), `twistedThetaLift_LValue_quotientFactorization`, has **no hypotheses**. It says L^S(z+½, chainPar(B,k)⊗χ_{T,k+1}^{−1}) at z = t/2 equals L^S((1+t)/2, B⊗μ_{k+1}^{−1})·H, with H ≠ 0 and H = ∏_{i=1}^k∏_{n=1}^t Λ_i(n), where Λ_i = the continuation of L^S(·, μ_iμ_{k+1}^{−1}) (`IsHval`, ILM:123-126). *(inferred)* This is exactly the Adams-type factorisation: segment pieces μ_i|·|^{(t−1)/2−j} shift (1+t)/2 to the integers 1..t. **H involves neither c nor B.**
  - `StepExactNS` (SEN:89-95), proved from `HeckeFormNS`: the Rallis formula with the **level-k** parameter (so it is not B there). `StepLam` (ILM:214-222) combines it with LFull, so that the step scalar equals conj(kapOf·L^S((1+t)/2, B⊗μ_{k+1}^{−1})), where kapOf = vol·H₀/d^{S₀}·(archimedean zeta)/(local corrections) (ILM:197-200).
  - `Restore` (ILM:202-206) moves H and d^S from S = badPl t to the fixed S₀ = Pg places, using the explicit local Euler factors `blockL` and `zinv` at Q t (ILM:84-89).
  - `RUnif` (SEN:74-80), `twistedChain_step_constants_tuple_indep`: kapOf is a single constant K, the same for all t.
- So the c-independence is **proved** (from the definition of chainPar plus LFull), and the t-independence is **proved** (RUnif). Neither is assumed. The dependence on B is legitimate: the level-k parameter is B ⊕ characters by construction.
- **Published inputs.**
  - BForm path: `HeckeFormNS` (HFN:202-217) = Rallis inner product formula for U(A) → U(B) with rank gap t ≥ 2 and wittIndex B = 0 or < t, ⟨θ(Φ₁,u₁), θ(Φ₂,u₂)⟩ = vol·L^{S}((1+t)/2, par⊗χ_B^{−1})/d^{S}(t/2)·∫_{S} (Weil coeff × matrix coeff). It is supplied from `heckeForm_of_doubling₂` over Published WeilRepresentationUnitaryPair, CuspRapidDecay, **WeilSiegelFormulaUnitary**, SiegelWeilUnitaryConvergent, **DoublingMethod**, **UnramifiedDoublingGL** (`DAV/Definitions/LatticeFrames/LatticeFramesOfHyps.lean:27-29`, read).
  - AForm path: `aFormL` (`DAV/Proofs/DecoratedLatticeProofs/ThetaInnerProductEqConstMulLValue.lean`, top level read) over WeilSiegelFormulaUnitary, SiegelEisensteinContinuation, UnramifiedDoublingGL and BernsteinZelevinskyFiniteness. The definite target V_i makes this Weil's anisotropic case.
  - The definitions read are:
    - `WeilSiegelFormulaUnitary` (`…/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:56-69`): Weil convergence when B is anisotropic or rank A + witt B < rank B, and the Siegel–Weil identity only when 2·rank A < rank B. This is Weil 1965 / Ichino.
    - `DoublingMethod` (`…/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean:36-46`): continuation and pole bounds of Siegel Eisenstein series, plus the basic identity. This is Piatetski-Shapiro–Rallis.
    - `UnramifiedDoublingGL` (`…/TwistedTraceFormula/PairwiseDisjointCell.lean:314-324`): the unramified doubling zeta integral equals L(s+½,α)L(s+½,α⁻¹)/normaliser. This is Piatetski-Shapiro–Rallis / Li.

  All have the shape of the published theorems. None is visibly stronger. Gan–Qiu–Takeda and Yamana are **not** used: only the convergent range is invoked.

### 2.5 Q3 GalD supplier (live route, read top level)
- `primRows3_of_parts` field `scalConj := hGal` (PrimRows3OfParts.lean:48). `hGal` comes from `real_data_weight_vector_family` (RealDataWeightVectorFamilyCore.lean:30), i.e. `Stage4.stage4` (`…/RealDataWeightVectorFamily.lean:20-33`, read).
- `stage4` calls `doubling_method_consequence` = `ScalConj.scalarConjRow` (`…/TwistedOperators/DoublingMethodConsequence.lean:31-37`, read) → `ScalConjRow.galD_of_inputs` (`…/ConjugateBaseLevelOfHoweUnramifiedCorrespondence.lean:20-27`, read) → `liftScalarIdentity_offFixedPlace_baseLevel` (Statement :12, stmt). That final step has three inputs:
  - `conjugatesOfRationalThetaLift_from_characterisation : ConjRatLift5` (no hypotheses; Statement :10). `ConjRatLift5` (`DAV/Definitions/Divisors/FormalDegreeUpperC.lean:101-108`, read) gives `GalOut` (same file :86-94, read):
    - the rational lift is unique;
    - for every embedding σ over K, the σ-conjugate of the rational lift is the lift of the σ-conjugate datum (`ConjAt`);
    - for σ not over K, the metric is the complex conjugate of the metric at c∘σ.
  - `conjugateDatum_lift_scalar_of_innerProductFormula : ConjScalarAt` (Statement :10). `ConjScalarAt` (`DAV/Definitions/TwistedInnerProducts/ConjScalarAtOf.lean:15-21`, read) says that for every conjugate datum (`IsConjDatum R i σ …`), th∘th* acts by a scalar l on each Hecke part. It is proved from the same inner-product, Fock and finite-zeta inputs as AForm.
  - Ties `TiesG` (fw, BarTie, IoExt, pins, oneMap, phase), built by `TiesG.of_dat` in `atDat_holds` (HoldsFromPrintedInputs.lean:85-90).
- **Meaning.** The K-rational theta lift θ_j(μ₀), read at the place v, is the theta lift for the Galois-conjugate archimedean data. The Rallis identity for that datum makes it a similitude with its own constant λ_{j,p,v}. The constant at v is whatever that Rallis scalar is. The Lean neither asserts nor needs λ_v = σ(λ_{v₀}). The height side bounds log λ at every v separately (NODE-DETSIG oddity 1, NODE-L6).

## 3. Children

| # | Name | file:line | Statement (math) | Status | Weight |
|---|---|---|---|---|---|
| 1 | `TRCusp` / `trCusp_of_classicalTheorems` | HTV:39; TFH:45 | simple-trace-formula multiplicity equality for inner forms of the same odd rank, Gap-regular λ, cuspidal-type σ | proved (top level read) from 13 Published | **core**; standard shape (Clozel / Harris–Taylor-style inner-form comparison) |
| 2 | `hasTypeVec_of_goodRep` | `…/ExistsTypeVectorOfGoodLevelRepresentationStatement.lean:17` | IsGoodRep ⇒ ∃ NoFixed type vector | proved, stmt (GreenCuspidal) | core (this is what makes "good" mean "simple") |
| 3 | `discrete_series_odd_rank_gap` / `params_match` | `…/DiscreteSeriesOddRankGapStatement.lean:16` | M₀ and MW_i have the same λ; rank odd; Gap | proved, stmt | core (definitional bookkeeping, worth one check) |
| 4 | `EllipticPart`, `RealStable`, `non_field_type_vanishing` | EPT:307; HTV:102; TFH:52-54 | product-of-local-stable-orbital-integrals form; SO(f_π) = χ̄_F/vol | proved, stmt | core / standard (Kottwitz, Clozel–Delorme) |
| 5 | `LFull` | ILM:179 | level-k L = B-L × H(μ's), H free of c | proved, stmt | **core** for Q2 |
| 6 | `RUnif` + `Restore` | SEN:74; ILM:202 | step constants independent of the tuple t | proved, stmt | core for "one κ" |
| 7 | `HeckeFormNS` | HFN:202 | Rallis inner product formula, convergent range | proved from Published | standard (Li 1992; Ichino) |
| 8 | `ConjRatLift5` | FormalDegreeUpperC.lean:101 | Galois conjugate of the rational theta lift = theta lift of the conjugate datum | proved, stmt (no hypotheses) | **core** for GalD |
| 9 | `ConjScalarAt` | ConjScalarAtOf.lean:15 | Rallis scalar identity for the conjugate datum | proved, stmt | core for GalD |

## 4. Oddities

1. **RealStable has no (−1)^{q(G_w)} sign.** PhiReal = conj(χ_{F_λ}(γ))/vol (EPT:220-222). The Published character formula does carry (−1)^{halfDim ε} (`dsChar`, DSC:176-177). The true stable orbital integral of a discrete-series pseudo-coefficient on U(p,q) is (−1)^{pq}χ̄_F/vol. RealStable is stated only for `Odd V.rank` (HTV:103), and p+q odd ⇒ pq even. So it is consistent, but only because of the odd-rank restriction. If odd rank ever became even, this would be false per place. In the comparison the product of signs would still agree across finite-adelically isomorphic inner forms (∏_v e(G_v) = 1).
2. **NoFixed is "∀a ∃v", not one cuspidal place.** For each a a different split place may kill U_a. The argument in §2.3 works place by place, but it relies on the depth-zero compatibility (Ind_P π)^{K(1)} = R_M^G(π^{K(1)}). That compatibility is inside `GreenCuspidal` / `non_field_type_vanishing`, which I did not open.
3. **Range of Siegel–Weil vs the row steps.** `WeilSiegelFormulaUnitary` gives the Siegel–Weil identity only for 2·rank A < rank B. For row step k ≥ 1 (rank A = r+kt, rank B = r+(k+1)t) this fails once kt ≥ t − r. The HeckeFormNS hypotheses (rank gap t, witt B < t) are Weil's convergence condition, not absolute convergence of the Eisenstein series. The bridge is `heckeForm_of_doubling₂`, which also uses Published `SiegelWeilUnitaryConvergent` (Ichino's Weil-range Siegel–Weil, presumably). I did not open that bridge. **Question for the Rallis node**: does SiegelWeilUnitaryConvergent state Ichino's theorem in the full Weil range, or more?
4. MultEq quantifies over **every** model M₀ with parameter `parA (Ptw D) 0`. That is harmless, since the conclusion holds for each member of a simple packet.
5. MultEq is vacuous for an i where no `IsFinIso` Φ exists. On the live route Φ is supplied downstream (not traced here).

## 5. Coverage

**Read:**
- FRA:1-128; SOP:1-130; `BesselHermitianTheta/IsAutFunDef.lean:20-60`;
- `MultiplicityEqualityStatement{,Statement}.lean` (all); `PublishedLocalTheoryConsequence.lean` (all); `CuspidalTraceMultiplicityGivenStatement.lean`, `PublishedInputsImplyTraceFormulaStatement.lean` (all); CTM (all); TFH (all);
- HTV (all); EPT:10-128, 130-344; EAP:255-300, 380-420, 770-800; DSC:270-330;
- `PrimRows3OfParts.lean` (all); `RealDataWeightVectorFamily{,Core,CoreStatement,Statement}.lean` (all); `RationalDataSizedFamily.lean:12-31`; `HoldsFromPrintedInputs.lean:15-100`; `MultW.lean:1-50`; RRW (all); DII (all); ADM (all); `LinkedBundleConstructionExists.lean:20-60`;
- RLK:20-70; LSS:1-110; `ThetaChainStepPositiveScalarStandingHypotheses{,Statement}.lean` (all); `ThetaLiftAdjointScalarFormulaInjective.lean` (all); `ScalarsOfGivenData{,Statement}.lean` (all);
- ILM:120-230; SEN:40-110; CPS:121-133; `DAV/…/UpNonzero.lean:33-45`; HFN:150-224; `LatticeFramesOfHyps.lean:15-45`;
- `ThetaInnerProductEqConstMulLValue{,Statement}.lean` (all); `WeilSiegelFormulaUnitary.lean:56-69`; `EisRegularAtOfEisPoleLE.lean:36-46`; `SiegelEisensteinContinuationOfDoublingMethod.lean:14-22`; `PairwiseDisjointCell.lean:314-324`;
- PO:255-272; `DoublingMethodConsequence{,Statement}.lean` (all); `ConjugateBaseLevelOfHoweUnramifiedCorrespondence{,Statement}.lean` (all); `ConjugatesOfRationalThetaLiftFromCharacterisatioStatement.lean:10`; `ConjugateDatumLiftScalarOfInnerProductFormulaStatement.lean:10`; `LiftScalarIdentityOffFixedPlaceBaseLevelStatement.lean:12`; `FormalDegreeUpperC.lean:86-115`; `ConjScalarAtOf.lean:15-25`.

**Greps run:**
- `primRows3_of_parts`; `primRows3_typesSep3\b`; `real_data_weight_vector_family_core\b`; `holds_of_ties`; `rational_data_sized_family`; `\bholdsW\b`; `multW\b`; `HypH\b`; `hypH_of\b|MultL`; `hypH_of_rowRatW|PrM`;
- `def TRCusp|multEq_of_trCusp|trCusp_of_classicalTheorems|structure Given`; `def PhiReal|Gap|NoFixed|IsTestArchG|HarishChandraCharacters|mCuspDS`; `def GeomExpansion|EllipticPart|XSet|IsTestData`; `structure TypeData|TypeDataG|ResF`;
- `thetaChainStep_positive_scalar_standingHypotheses`; `HeckeFormNS`; `def LFull|Restore|RUnif|StepLam|StepExactNS`; `def stepPar|chainPar|blockL`;
- `doubling_method_consequence`; `scalarConjRow`; `ConjScalarAt|ConjRatLift5`; `def GalOut`; `def dsChar`.

**Not opened (proof bodies):**
- `pseudo_coefficient_separation`, `elliptic_trace_of_inputs`, `non_field_type_vanishing`, `real_stable_of_characters`, `hasTypeVec_of_goodRep`, `params_match`;
- `twistedThetaLift_LValue_quotientFactorization` (LFull), `twistedChain_step_constants_tuple_indep` (RUnif), `chainTwistEulerFactorsRestore_proof`;
- `heckeForm_of_doubling₂`, `SiegelWeilUnitaryConvergent`;
- `conjugatesOfRationalThetaLift_from_characterisation`, `liftScalarIdentity_offFixedPlace_baseLevel`;
- the Published definitions other than those listed under Read.
