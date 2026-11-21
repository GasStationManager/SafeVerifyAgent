# NODE-SEESAW: the identity that joins the column chain to the Bessel pairing

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `DTH` = `Formalism/LocalRingCardinality/DataTheta.lean`
- `ROWS` = `Formalism/LocalRingCardinality/DataRows.lean`
- `D7F` = `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean`
- `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`
- `SO` = `Formalism/DivisorInequality/StatementObj.lean`
- `ADR` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AdelicDataRowMeasureScaleTrivialTuple.lean`
- `REC` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/StepZeroTwistReferenceTupleEqId.lean`
- `IPH` = `Formalism/LocalToGlobal/IndefiniteReal/IsometricPeriodsOfHypotheses.lean`; `IPU` = `…/IsometricPeriodsOfUnitHypotheses.lean`
- `CT2` = `Formalism/LocalToGlobal/IndefiniteReal/CutTuples2.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `VLX` = `Development/AbelianVarietyTheory/Definitions/LatticeFrames/ValLastX.lean` (namespace `GlobalTheory.SeeSaw`)
- `FAZ` = `TPS/FormsAtZero.lean`

"The Lean says" = I read the line. *(inferred)* = my reading. Nothing compiled.

## 0. Verdict (short)

1. **The four named objects are not where the join happens.**
   - `TieBm` (DTH:747) has no consumer anywhere in the tree (grep `TieBm`: only its definition, two `tieBm` lemmas and `thetaZero_bm`).
   - `BuDef` (ROWS:226) is consumed only through `AdmBuRat`/`buDef_of` (`WeightDegreeSizes.lean:1349,1413`). It also has a
     degenerate proof `buDef_iff` (`NontrivialReferenceForms.lean:428`) for a stand-in record whose `Bu = 0`.
   - So ARCH's worry "TieBm is a structure field whose supplier was not traced" goes away. The field is never used.
2. **The live join is a different identity, `MIid`** (IPH:97-101). It feeds `IndefCols.l1b` (`PairingFactorsThroughPeriods`,
   IS:383-386) and `l1e` (IS:388-395), and also BesselId's `adm13`:

   ζ_{u,t}·Pt_u(φ, F) = a_u·⟨sEE(V·Θ_t(F)), P_u(U_u φ)⟩_HH.

   On the left is the column period, which is perCol by `dcPt`. On the right is a Bessel period on U(Y_0) of the descended
   row form against the Poincaré series.
3. **`MIid` is supplied by a real seesaw theorem chain.** The chain is
   `miStar2_at_realisation_alt` (TPS/MiStar2AtRealisation.lean:84) ← `JointCondition` (FAZ:67) ← `joint_of_famAllQ_alt`
   ← `mainX_of_lawsX` (`…/DecoratedLatticeProofs/SeesawTransportRelationsOfFamilyLaws.lean:25`). That last theorem is an
   honest m-step seesaw, done two levels at a time, and every intermediate column level is realised automorphically there
   (`Tup.rd j`, VLX:113). Its per-step period identities `ValX`/`ValLastX` are in turn theorems (`pins_finiteIntegrals`).
   So **the two halves do talk to each other**, through a theorem, conditional on that chain's hypotheses.
4. **The constant is not identified with κ∏λ_j.** The seesaw yields only "linear relations among top periods ⇒ the same
   relations among bottom periods". So a_u ≠ 0 exists, but its value is never computed. It does not need to be. B_u is
   *defined* as the period pairing pulled back along ι (`Bdef`, CT2:160-162), and the scalars a_u, κ and λ_j are never
   divided out of B_u.
5. **p-adic normalisation.** RR is the image lattice ι(Λ) (IS:281-282). So B_u(N_u) ⊆ RR^∨ is literally perCol
   integrality, with no λ term. λ_j is ℝ-valued per infinite place (IS:262 region: `lam : J → Tup → Ix → InfinitePlace K → ℝ`)
   and has no p-adic valuation in the Lean. Its finite-place shadow is the index idx(M_j : θ_j T_j) in `BoundsMu`:
   - it is forced to be 0 at untwisted places (SO:54-58);
   - it is bounded by (2F + err)·D at twisted places (SO:65-67), where the F part is cancelled by −Fo.

   That is an assertion that θ_j is integrally near-unimodular at the gain primes. Its supplier (`IndefSide.on`,
   `IndefExtra.untw`) is the decisive untraced child for the reviewer's concern in (d).

## 1. Statements

### (a1) `TieBm` (DTH:747-752) and its intended content (ADR:499-502)
```lean
def TieBm : Prop := ∀ u μ φ F, D.what₂.perCol u μ φ F =
  (X.mY μ D.R.m : ℂ) * X.Btop (D.sp.X D.R.m) (D.sp.Y D.R.m) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap)
    (X.conjAF _ (X.colAF u μ D.R.m φ)) (X.rowAF μ D.R.m ((D.what₂.multTop μ).symm F))
```
`Btop` is an abstract `ThetaX` field (DTH:665). The concrete version is `RecFun.TopTie` (ADR:499-502). It says perCol_u(μ, φ, F) is
the quotient integral over [U(Y_m)] = [U(X′)], with measure mY·petC, of col_m φ(s(h)) · row_m F(h). Here s embeds U(X′) into
U(X_m). In mathematical terms this is the **codimension-one Gross–Prasad period** ∫_{[U(X′)]} (K_{m−1}⋯K_0 φ)|_{U(X′)} · F.
`tieBm` (ADR:735) derives TieBm from TopTie. TopTie is a field of `RecFun.OfRecord` (ADR:504-507), whose only use is
`RecordIsForms` (`ExistsSplittingCharacterSelf.lean:502-504`). grep finds no consumer of that.

### (a2) `BuDef` (ROWS:226-227)
For F ∈ V0(μ₀), perCol_u(μ₀, φ, F) = B_u(φ, ι_{μ₀}F). Here ι is the composite of the row descents io_j (ROWS:180-186).

### (a3) `BesselId` (GTI:65-67) = `BuRational` ∧ `TR_at`
- `BuRational` (D7F:364-365): Bu(jN φ, jEE x) = embLL(Bk φ x). This is the LL-rational form.
- `TR_at`: there is an isometry V of EE such that for every u there exist a ≠ 0 and an isometry U of Mu u with
  B_u(φ, F) = a·besS_u(Uφ, VF). Here besS = ⟨sEE F, P_u φ⟩_HH.

### (a4) The live join, `MIid` / `MIstar2` (IPH:97-104; IPU:27-28)
```lean
def MIid eV sEE d := ∀ u t φ F, d.ζC u t * v0.embedding (Dc.Pt u t φ F) =
  d.a u * ⟪sEE (d.V (X.Θ t (X.jR t (eV t F)))), Sp.Pu u ((d.U u).mulVec (cpt v0.embedding φ))⟫_ℂ
```
- `MIstar2` adds the following: V is an isometry of EE, U_u is an isometry for the column metric Xc, ζ_{u,t} ≠ 0 with ζ_{u,μ₀} = 1 and
  v_w(ζ_{u,μ(w)}) = 0, and a_u ≠ 0.
- `Dc.Pt u t φ F` is the column-side period. It is tied to perCol by `ColBrF.Tied.dcPt` (`Formalism/LocalToGlobal/GroupLattices/ServJointF.lean:43-44`).
- Θ_t is the descent of a top form into EE.
- So **MIid is the seesaw statement in the form "top period = a × Bessel period of (descended F) against P_u φ"**, up to the
  root-of-unity-like twist ζ at twisted tuples.

What is built from it:
- `cutMI_cols` (IPH:328-339) gives ζ such that, with B := `colDef ζ⁻¹` (CT2:164-165), both `PairingFactorsThroughPeriods` and
  `L1e` hold.
- `B` is *defined* as `Bdef u = Pt_u(·, μ₀) ∘ rinv(Pq μ₀)` (CT2:160-162). So l1b, i.e. Pt = ζ·B(ι Pq F) (IS:383-386), is
  near-definitional. It needs only `BtVanish` (Pt kills ker ι) and `MatrixIdentityOffBase`.
- L1e (B ∝ bes) carries the seesaw content.
- `indefinite_realisation_column_facts` (TPS/BurrbColFacts.lean:24-46) turns MIstar2 into `ColFacts` (l1b).
- `adm13_of_joinSI` turns it into BesselId (NODE-ROWSU).

## 2. Argument: why it should be true, and how the Lean proves it

### Standard picture
For dual pairs (U(X_j), U(V_j)) and the see-saw formed by X_j ⊂ X_{j+1}, the following holds. Integrating the theta lift of a
column form at level j against a row form at level j+1 equals integrating the column form against the row form's lift down. The
Bessel period alternates with a Fourier–Jacobi period, because codim(X_j ⊂ Y_j) changes parity (DTH:657-664, `Bper_odd`). The
Lean therefore groups the steps **in pairs** (Bessel → FJ → Bessel), the "two-step chain" `Chain.hand` (VLX:126-131). Here
m = 2n+2 and n = r_S, and the bottom Bessel datum `bes 0 n` has 0 + 2n + 2 = m, which matches Y_0 = X_0 ⊕ ⟨z⟩ ⊕ r_S·H.

Schematically, for one pair of steps (the smallest case m = 2, n = 0):

  ⟨ψ_top = K_1K_0ψ , F⟩_{[U(X′)]}  
  = cP·a·tail(K_1K_0ψ, F)                                   (PerX)
  = Σ (iterated integral over [U(V_1)] × [U(V_2)] of θ-kernels × rd_0ψ × F)      (KerX: K_j realised as θ-integrals)
  = cV_0 · Bes_{0,0}( rd_0 ψ , io_0 ioT F )                    (ValLastX: unfold, swap integrals)

That last term is the Bessel period on U(Y_0) ⊃ U(X_0) ⋉ N of the level-0 form against the m-fold descent of F.
For general m, `ValX` (VLX:175-181) moves a Bessel period at level j+2 down to level j through one two-step block, with scalar cV_j.
`StepX` (VLX:248-255) iterates this. Each step multiplies by cV_j·cK_j·cK_{j+1} and on the other side by cI_j·cI_{j+1}. The
scalars cK_j are the KerX constants, i.e. the column step K_j realised as a theta integral (VLX:192-195).

### What the Lean proves (`MainX`, VLX:268-273)
MainX is stated as *transport of linear relations*. Suppose Σ_i α_i·cTop·tail(up ψ_i, F_i) = 0 for families of tuples. Then
Σ_i α_i·cBot·Bes_{0,n}(ψ_i, dn ioT F_i) = 0.

`mainX_of_lawsX` (`…/SeesawTransportRelationsOfFamilyLaws.lean:25-37`) proves it from:
- `LawsX` (VLX:221-230): `ValX`, `ValLastX`, `KerX`, `PerX`, `RdX`, and `RealEq`;
- `Published.CuspRapidDecay` and `Published.HarishChandraModules`;
- the closed lemmas `seeSawDoubleLiftCombination_of_laws`, `seeSaw_doubleStep_linearRelations_periods` (which uses
  `besselPeriod_double_step_unfolding_of_descent` and `weil_data_descend`), `seeSaw_lastTwoSteps_transport_linear_relations`
  and `mainX_of_stepX_lastX`.

LawsX itself is supplied in `lawsLinks_of_geo_rows_cols_alt` (TPS/LawsLinksOfGeoRowsCols.lean:120):
- `val`/`last` come from `seeSaw_latticeFramePins_finiteIntegralLaws` = `SeeSaw.pins_finiteIntegrals`. That theorem works over a
  nonarchimedean local field k with local type data `TDat`, `ShapeOff` and `GPin`, and per-tuple conditions `VForm`, `WeilOK`,
  `QLaw`/`QLast`/`QFin` and `CVEq`.
- `ker`/`per`/`rd` come from `seeSawKernelLiftCombination_of_definiteClassData`, `seeSawLastPeriodFactorization_of_classData` and
  `seeSaw_scalarForms_continuous_automorphic_central`.

`joint_of_famAllQ_alt` (TPS/JointOfFamAllQ.lean:21-30) then gives `JointCondition` (FAZ:67-69). Its `BottomData.Rel` (FAZ:58-63) says
that a linear relation between p(φ₀) and c_t·perCol(φ, F) implies the same relation between the bottom Bessel periods
`d.per` (FAZ:55-57: `B.lev.per ψ (level-0 column form) (translate of row form)`). `miStar2_at_realisation_alt` uses
`DiscreteSeriesClassification`, `CuspRapidDecay`, `PuNZ`, `BottomHypotheses` and `pairForm_of_conjVec_of_botHyp` (κ ≠ 0, an
identification of the d.per pairing with ⟨sEE·, P_u·⟩). From a single nonzero anchor pairing b₀ it extracts constants p, b₀ and
builds `MIstar2` (MiStar2AtRealisation.lean:43-81, 84-140 read).

### `colAF = 0` for 0 < j < m (REC:342-345)
This is harmless on the live path. colAF belongs to the `ThetaX`/`TieBm` scaffolding, which nothing consumes. In the
seesaw that is used, every level is realised: `Tup.rd j α ψ y : GA(X_j) → ℂ` (VLX:113), with `RdX` (continuous,
automorphic, central character; VLX:215-217) and KerX tying rd_{j+1}(K_jψ) to the theta lift of rd_j. *(inferred)* The REC
constructor realises only levels 0 and m (colZero, colTop) because only TopTie needed them.

## 3. (c) The link between towers

- **`LevelLink` is `rfl`.** `CxLemmas.lean:528`: `level := ⟨rfl, rfl, rfl⟩`. The base and column IndefData are both
  `X.data cr b` of one `CxData`, with `κ := X.κ`, `lam := X.lam`, `ι := X.rowMat cr b`, `θ := X.liftMat cr b`
  (`IndefiniteReal/PartsOrth.lean:171-185`). So "the descent scalars equal the layer scalars" holds by construction: there is
  one λ. What has content is that ι = rowMat is a κ·∏_jλ_j-similitude on Q-parts and θ_j = liftMat is a λ_j-similitude on
  Z-parts (`RowLatticeBoundForBasis`, IS:304-311, field `l1c`), with λ_j the Rallis θθ* eigenvalue (NODE-L6, `PThmA`). I did
  not trace who proves l1c for X.data.
- **Determinant hypothesis** (SO:38-41): detRatio(XQ_{μ₀}, XE, ι_{μ₀})(v) = κ_v^D·∏_j detRatio(XT_j, XW_j, θ_j)(v) at every
  infinite place v, and at v₀ for twisted t with an extra ρr_t. *(inferred)* It follows from l1c together with
  `DimensionsOfPartsAgree` (IS:313-314; l1d) by taking determinants part by part. I did not find that derivation.
- **Signature (k+j−1, m−j).** It is only stated, as `FactKaBlocks` (ROWS:250-251). *(inferred)* The reason is the covolume
  count: Σ_{j=1}^m (p_j − q_j) = Σ_j (k + 2j − 1 − m) = mk. That matches the m column steps of weight-k blocks (NODE-ARCH §7.7)
  and the Chowla–Selberg weights pq_j·w·logΩ in L3. W_m is definite and W_{m/2} has the signature of Y_0.
- So the row descent ι and the layer lifts θ_j are linked **only** through the shared λ in one CxData record and the
  similitude clauses. No theorem I saw factors ι through the θ_j as maps.

## 4. (d) Normalisations across the join

- **B_u is not "chain/(κ∏λ)".** B_u(φ, ι_t Pq_t F) = ζ^{−1}·Pt_u(φ, F) (CT2:160-171; IS:383-386). That is the column period
  itself, in coordinates of the image ι(Q-part).
- **RR = glueLat(matLat(ι_{μ(w)}, abelian₂ μ(w)))** (IS:281-282), the image of the integral top lattice. Together with BtVanish,
  B_u(N_u) ⊆ RR^∨ becomes exactly `adm2` on perCol over F ∈ Mtilde ∩ V0 (`ServJointF.lean:84-108`). **No v_p(λ_j) or v_p(a_u)
  enters the integrality.** a_u is used only in BesselId (Theorem S, frame), not in OneMapIntoCC.
- **Archimedean.** h(u) = hu − meanLog κ (RecBridge `hTie`). hu contains −Σ_j hX_j, the hook lower bound from L6. The covolume
  bound is μ(RR^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + 2Σ lw·Fy + LG + E (SO:72-74).
  - κ cancels exactly in μ(RR^∨) + h.
  - λ_j does **not** appear explicitly in the covolume. It sits inside det θ_j and hence inside lcv(M_j), which L3 bounds
    directly by Σ pq_j w logΩ.
  - In h it appears explicitly, as −Σ log λ_j, and cancels against the factorial growth of the Fock kernel norms hB_j
    (NODE-HEIGHT).
  - All three are inequalities proved separately (L3, L6 and the kernel norms), so the chain is valid as a chain of
    inequalities. Consistency of sizes is then a matter of whether each proven bound is true. It is not a sign error.
- **p-adic size of the Rallis constant.** The finite-place counterpart of λ_j in BoundsMu is idx_y(M_j : θ_j T_j) + jw:
  - = 0 at y ∉ Sy and at y ∈ Sy∖Tw (SO:54-58);
  - ≤ (Σ_j(2Fy + erry) + 2/ℓ²)·D at y ∈ Tw (SO:65-67).

  The served gain primes are twisted places (NODE-CONGMOD §2a.5). Fy is the small FInert ≈ Σ(k−1)w/(p²−1) and is cancelled
  by Fo. So the Lean asserts that θ_j maps T_j onto M_j with index o(gain·D) at the gain primes. If the integral normalisation
  of θ_j carried v_p of hook/Γ-size, this hypothesis would be false and the main term would move. **This is where your
  concern lives.** It is supplied by `IndefSide.on`/`ON` (IS:318-323) and `IndefExtra.untw`/`Untwisted` (IS:329-330).
  CxCore copies `on := hC.on` (`IndefiniteReal/CxCore.lean:187`). I did not trace further.

## 5. Children (ranked)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `IndefSide.on` / `Untwisted` supplier (`hC.on`) | IS:318-330; CxCore.lean:187 | idx(M_j : θ_jT_j) = 0 off Tw and ≤ (2F+err)D on Tw | **core**, untraced; it decides the p-adic λ question |
| 2 | `SeeSaw.pins_finiteIntegrals` (ValX, ValLastX) | `…/SeeSawLatticeFramePinsFiniteIntegralLawsStatement.lean:13` | two-step seesaw: iterated θ-integral = cV × Bessel period two levels down | **core**, standard in shape (seesaw + Bessel/FJ unfolding), not opened |
| 3 | `mainX_of_lawsX` and its four lemmas | `SeesawTransportRelationsOfFamilyLaws.lean:25` | m-step transport of linear relations, top → bottom | core, read at top level |
| 4 | `miStar2_at_realisation_alt` (+ `pairForm_of_conjVec_of_botHyp`, `botRel_of_botHyp_of_pin_central`) | TPS/MiStar2AtRealisation.lean:84 | JointCondition ⇒ MIid with a ≠ 0 | core, partly read |
| 5 | `lawsLinks_of_geo_rows_cols_alt` and the `AllFamilyConditions` supplier | TPS/LawsLinksOfGeoRowsCols.lean:36 | builds LawsX for the live family | core, read 36-140 |
| 6 | `RowLatticeBoundForBasis` (l1c) for `X.data` | IS:304-311 | ι is a κ∏λ-similitude, θ_j a λ-similitude | core, untraced |
| 7 | det identity in BoundsMu | SO:38-41 | det ι = κ^D ∏ det θ_j | glue (inferred from 6) |
| 8 | `cutPairing`, `cutMI_cols` | CutPassage.lean:37; IPH:328 | B := Pt∘rinv(Pq) satisfies l1b | glue |

## 6. Oddities

1. `TieBm`, `TopTie`/`OfRecord`/`RecordIsForms` and the `ThetaX` Btop/Bper fields form an **orphaned** seesaw formulation, with no
   consumer. Several `ThetaX` instances set `Btop := 0` (`ExtraTheta.lean:168`, `ThetaFullColIsom.lean:160`,
   `ThetaXNonemptyProvisional.lean:136`). Harmless, because unused.
2. **Stand-in row records.** `StandIn` (`SameForm.lean:40-56`) has EE = 0 (Dall = Drows = 0), io = 0 and Bu = 0. `exists_all`
   (`NontrivialReferenceForms.lean:435-439`) produces the rec7 record with `StandIn Z.W`, and `buDef_iff` makes BuDef
   ⇔ perCol = 0 there. `exists_rows_prescribedUnitaryForms_standIns` is used in `LatticeFrames/AmbIsTrueOfAmbTrue.lean:70`.
   - If the live D's `what₂` were such a stand-in, then BesselId (on what₂.Bu) would be vacuous (Bu = 0 = a·besS on EE = 0).
   - I could not determine whether the D fed to `LinkDIV_at` uses a stand-in what₂. The live slope data run through
     `DivisionPackageFace` (its own RR, tied by `HLatTie`), which hides this. **This needs a reviewer.**
3. The seesaw constant a_u is existential and depends on the word. MainX transports relations, not equalities with a
   computed constant. Nothing ties a_u to κ∏λ_j. That is fine for integrality and height, which do not use it. It matters only if
   the frame/Theorem-S argument (NODE-RANK) needs a_u uniform across words; I did not check this.
4. `pairForm_of_conjVec_of_botHyp` supplies κ ≠ 0 ("PairingFormCondition", FAZ:89-97): the bottom Bessel pairing b equals
   κ⁻¹⟨sEE e, P_u x⟩. This is the unfolding of the Bessel coefficient against the Poincaré series. It is a theorem here, from
   `DiscreteSeriesClassification` and `CuspRapidDecay`. Not opened.

## 7. Coverage

Read:
- DTH:640-758; ROWS:180-274; D7F:355-393; GTI:55-92; MainSup.lean:120-135;
- LocalQuadraticParts.lean:326-336; MainIn.lean:36-46;
- ADR:440-530, 700-760; `ExistsSplittingCharacterSelf.lean:390-540`; REC:230-467;
- `ExtraTheta.lean:140-200`; `NontrivialReferenceForms.lean:405-440`; `SameForm.lean:36-75`;
- `WeightDegreeSizes.lean:1340-1430`; RecBridge.lean:400-650 (parts); ServJointF.lean:1-130; IS:225-474; SO:15-80;
- IPH:60-135, 300-339; IPU:15-60; CT2:150-185; PartsOrth.lean:160-215; CxCore.lean:170-190;
- BurrbColFacts.lean:20-46; ColFacts.lean:55-80; MiStar2AtRealisation.lean:1-140; FAZ:1-120;
- JointOfFamAllQ.lean (all); FamAllQ.lean:20-35; VLX:1-300; SeesawTransportRelationsOfFamilyLaws(+Statement) (all);
- SeeSawLatticeFramePinsFiniteIntegralLawsStatement.lean (all); LawsLinksOfGeoRowsCols.lean:36-140;
- ExistsLayeredDataOfGoodScaleContextsStatement.lean.

Nodes: ARCH, THETA, ROWSU (all); L6 §0-1; DIV §1; CONGMOD §2a.

Not opened:
- `pins_finiteIntegrals` and the four mainX lemmas' bodies;
- `pairForm_of_conjVec_of_botHyp`;
- suppliers of `on`/`untw`/`l1c`/`hC`;
- whether the root's family is built through the MIstar2 route above, or through another producer (several exist:
  `miStar2_of_allTrue`, `miStar_row`, … in `DecoratedLatticeProofs/`);
- whether the live what₂ is a stand-in.
