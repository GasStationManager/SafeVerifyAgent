# NODE-LIVEPATH: which producers the root actually uses (MIstar2, BoundsMu det identity, MultEq), and the `True` slots

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the line. *(inferred)* = my reading. Nothing compiled.
Abbreviations as in NODE-ROOT / JOIN / DETSIG / MULTEQ / SWRANGE (`TPS/`, `ECL`, `BLP`, `IU`, `IS`, `DHB`, `FRA`). New ones:
- `LTD/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/`
- `DLP/` = `Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/`
- `CGT` = `Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`; `RB` = `Formalism/LocalToGlobal/Divisibility/RecBridge.lean`
- `W4F` = `TPS/Wire4F.lean`; `TS` = `TPS/TopShape.lean`

Method note: many links are `first | exact @X | …` wrapper theorems whose body is a single named lemma X; I count such a wrapper as one step and name X.

## 0. Verdicts

| Q | Answer |
|---|---|
| (a) seesaw `MIstar2` | **live producer = `miStar2_at_realisation_alt` fed by `JointCondition` from `joint_of_famAllQ_alt`, whose `MainX` is `SeeSaw.mainX_of_lawsX`. Confirmed by a 20-step trace** from `every_character_of_literature_of_vWin` (table A). The consumer is confirmed too: `RowsAt4.miStar` → `CovolumeOntoIsometryConditions.miStar` in `wire4F_alt` (W4F:63-65) → `base_lifts_package_of_primitive_links.miStar` (BLP:335). |
| (b) `BoundsMu` determinant identity | **live consumer = `divClausesR_of` (CGT:184-211, `IndefCoreR`), not `divClauses_of` (DHB:752, `IndefCore`)**. Both call the same `IndefSide.boundsMu` (IU:271). The `IndefSide` is `Pk.core.base` with `Pk = primitivePackageFullHecke … = packageFullHecke (base_lifts_package_of_primitive_links hOk hsep hC hP)` (`…/IndefiniteReal/PrimitivePackageFullHecke.lean:29-37`). That is the producer DETSIG read (BLP:288-347: `thmBop := thmBop_of hP.thmB`, `thmAop`, `galD := hP.scalConj`, `dimParts := hP.dimParts`). Confirmed by a 14-step trace (table B). `LinksLemmas.lean:361-401` (`cxLinks_of_prims`) and `ConcretePkgSpec.lean:179` (`cxLinks`) produce `(R.toCx F).CxLinks` for the non-"3" `RealDat`. The live record is built on `RealDat3`/`toCx3`, so neither is on the live path. |
| (b′) where `PrimRows3` comes from | `hP.toPrimRows3 := prows` with `prows` from `hPA : AllRealisationsPrimitive` (W4F:61-63). `hPA` is the HypsAlt field fed by `linkedAt_hPA_prmR` → `PrimAt.linkedAt_hPA` → `of_wit_alt`, which **reads `PrimRows3` off the bundle witness** (`w.y.intersectionNumber_baseChange.prim`, `TPS/HermWCellLastMulMulVecEqOfInWb.lean:9-13`). So on the consumer side PrimRows3 is a *membership condition* of the parameter class, and its content sits in the existence proof. That proof (`member_exists_baseLattice_alt`) reaches `primRows3_of_parts` through the LTD chain in table C. **I did not confirm** that the `Holds` produced there is the object stored as `intersectionNumber_baseChange.prim` (stopped; next step: unfold `exists_baseLattice_of_pair_alt` / `memberE_closing_alt_alt` to the witness constructor). |
| (c) `MultEq` | **live producer = `LTD/TwistedLocalMultiplicityEq.lean:twisted_local_multiplicity_eq` → `T.twisted_multiplicity_one` → `MultEqFinal.twisted_multiplicity_eq` → `UpperTheory.Lit.I5.unitary_theory_of_harishChandra_langlands_alt` → `PsCo.Pc.multEq_of_sides`** (pseudo-coefficient / trace-formula sides). It is reached from the root by an 11-step trace (table C). It feeds `primRows3_of_parts` (hM) through `MultiplicityCoverHypotheses.multW` → `w_of_weight_residue_char` → `atDat_holds_alt` → `holds_of_ties_alt` → `primRows3_typesSep3_alt`. **MULTEQ's route is dead w.r.t. the root.** That route is `member_bundles_large_ue` / `S0.HypothesesUE` / `hypH_of_rowRatW` / `atDat_multEq` / `multEq_of_trCusp`. Its only entry is `nonempty_hyps_of_classicalTheoremsUE`, and that is called only from `FockModels/EveryCharacterE.lean:65` (`hypsE₂`/`everyE₂`), which nothing references. The live MultEq lemma differs in name from the one MULTEQ read (`multEq_of_sides` vs `multEq_of_trCusp`). I read only the top of `unitary_theory_of_harishChandra_langlands_alt`, so MULTEQ's Q1 analysis has to be re-checked against `multEq_of_sides`. |
| `True` fed to a consumer needing content? | **No.** `siegelEisensteinSimplePole : UnusedSlot72` with `abbrev UnusedSlot72 : Prop := True` (`LTD/DiscreteSpectrumResidualClassification.lean:7`). It is a field of type `Prop`-defined-as-`True`, filled by `trivial` (ECL:505-506, 718). Its **only live consumer chain** is `member_bundles_large_unramified_exponents_alt` (`TPS/MemberBundlesLargeUnramifiedExponents.lean:52`) → `compatibleSystem_member_rationalWeights` → `twisted_siegel_weil_identity_of_siegel_weil_formula` → `twisted_siegel_weil_identity_of_formula` → `doubling_zeta_of_eisenstein_facts q2 e1 e2` → `ResidueKilled.dm_of_two`, which binds the argument as `_` and never uses it (`…/AnisotropicGlobalForms/DmOfHyp.lean:24-25`). The conclusion `DM` itself contains a literal `True` conjunct in place of the simple-pole clause (DmOfHyp:18). So the pole statement has been removed from both the hypothesis and the conclusion. Nothing downstream can extract pole information from it, and every live consumer is typed to accept the weakened `DoublingMethodLocalZetaIntegrals` (verified in `miStarRow_alt_alt`'s signature, `TPS/MainTheoremPublishedInputsThird.lean:22`). No ESCALATE. |

## 1. Statement

The root term (NODE-ROOT, re-read ECL:810-813) is
`every_character_of_literature_of_vWin O hV = every_character_of_theta_integrals_local_matching (published_results_eigen O) (published_results_first O) hA hM hX (local_langlands_gl_recT_exists_of_literature O) hV`.
This node asks only which lemma supplies three intermediate facts on that term:
- `MIstar2` (seesaw: top period = a·Bessel period, SEESAW §1(a4));
- the determinant hypothesis of `BoundsMu` (DETSIG §1);
- `MultEq` (MULTEQ §1).

It also asks where the root's `True` slots go.

## 2. Argument (trace tables)

### A. MIstar2 (root → producer, then the consumer)

| # | name | file:line | carrier of MIstar2 | next |
|---|---|---|---|---|
| 1 | `every_character_of_literature_of_vWin` | ECL:810-813 | `P := published_results_eigen O` | `every_character_of_theta_integrals_local_matching` |
| 2 | `every_character_of_theta_integrals_local_matching` | `TPS/SiegelEisensteinSecondTermHypotheses.lean:69-73` | 3rd argument of `every_character_of_green_v_win` | `nonempty_hyps_definite_side_of_closed_bound P …` |
| 3 | `nonempty_hyps_definite_side_of_closed_bound` | same file :44-68 | final `exact` (:68) | `hypotheses_nonempty_of_unramified_exponents_alt P hRat hL …` |
| 4 | `hypotheses_nonempty_of_unramified_exponents_alt` | `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:41-58` | `hO := open0_of_unitary_group_hypotheses P hL cDep` (:46); `hO' := hmono.2 hO` (:51, extension monotonicity); `hAll := allRows_of_open0_alt … hO' …` (:54); `nonempty_hyps_of_allRows_alt … hAll` (:57) | 5 and 13 |
| 5 | `T.open0_of_unitary_group_hypotheses` | `TPS/OpenOrbitOfUnramifiedExponents.lean:75-76` | wrapper | `open_orbit_of_unramified_exponents_alt` |
| 6 | `open_orbit_of_unramified_exponents_alt` | same file :39-69 | `hMi := main_theorem_published_inputs_third_alt_alt P.harishChandraFinite … P.doublingMethod …` (:50-53); `mi := hMi.2` (anonymous constructor :69 against `OpenParameterStatements` field order, `TPS/GeometricWeakTies.lean:39-51`: 10th field `mi`) | 7 |
| 7 | `T.main_theorem_published_inputs_third_alt_alt` → `miStarRow_alt_alt` | `TPS/MainTheoremPublishedInputsThird.lean:34-35`, :22-28 | `hE := main_theorem_published_inputs_variant_alt_alt …`; `.2` is `RowMultiplicityCondition` from `RowE.row hE` | 8 |
| 8 | `T.main_theorem_published_inputs_variant_alt_alt` → `miStarRowClosing_alt_alt` | `TPS/MainTheoremPublishedInputsVariant.lean` (all) | calls `main_theorem_published_results_final_alt_alt … (point_lines_of_cusp_rapid_decay …)` | 9 |
| 9 | `T.main_theorem_published_results_final_alt_alt` → `Fam.miStar_row_alt_alt` | `TPS/MainTheoremPublishedResultsFinal.lean:9-21, 28-29` | per bundle: `main_theorem_from_published_results_alt⁵ … (packB_alt b) H.1.2 H.1.1.rS H.2`, with TruePackAlt from `true_pack_of_bundle_witness` and PuNZ from `puNZ_of_truePack` | 10 |
| 10 | `alt⁵` → `miAt_of_truePack_alt_alt` | `TPS/MainTheoremFromPublishedResultsAltAltAltAltAlt.lean:15-19, 32-33` | `cases hW` (TruePackAlt.mk W hA, `TPS/TruePack.lean:8-13`); result type `RealPackageCondition W` := `MIstar2 …` (TruePack.lean:14-16) | 11 |
| 11 | `alt⁴` → `miStar2_of_allTrue_alt_alt` | `TPS/MainTheoremFromPublishedResultsAltAltAltAlt.lean:11-16, 25-26` | `exact mi_star2_of_pu_nz hDSCl hCusp hHCM W hA.pk.bot hA.pk.lev hFam hS hPu` with `hFam := true_geometry_family_row_data_alt …` | 12, 14 |
| 12 | `T.mi_star2_of_pu_nz` → `MiTop.miStar2_of_bot_lev_fam_served_puNZ` | `TPS/MiStar2OfFamiliesStatement.lean:13-14`; `TPS/MiStar2OfFamilies.lean:23-25` | `joint_star_product_nonvanishing_alt hDS hCR W hB (descent_eV_mem_level_alt …) (joint_of_famAllQ_of_servedQ hCR hHC W hFam hSv) hPu` | 12a, 12b |
| 12a | `T.joint_star_product_nonvanishing_alt` → **`MiTop.miStar2_at_realisation_alt`** | `TPS/MiStar2AtRealisationStatement.lean:13-14` (body read by SEESAW, `TPS/MiStar2AtRealisation.lean:84-140`) | JointCondition ⇒ MIstar2 | — |
| 12b | `T.joint_of_famAllQ_of_servedQ` → `MiTop.joint_of_famAllQ_alt` | `TPS/JointOfFamAllQStatement.lean:13-14`; `TPS/JointOfFamAllQ.lean:13-21` | `hMain : MainX f.t := T.seesawTransportRelations_of_familyLaws hCusp hHC D _ _ f.t hLaws` (:18) | 12c |
| 12c | `T.seesawTransportRelations_of_familyLaws` → **`SeeSaw.mainX_of_lawsX`** | `DLP/SeesawTransportRelationsOfFamilyLawsStatement.lean:12-13`; `DLP/SeesawTransportRelationsOfFamilyLaws.lean:25-37` | TwoX, StepX, LastX ⇒ MainX | — |
| 12d | `LawsX` supplier: `famAllQ_of_allTrue_alt` → `T.true_geometry_family_column_data_alt` → `Fam.lawsLinks_of_geo_rows_cols_alt` | `TPS/FamAllQOfAllTrue.lean:38-51` (hLaws :46-47); `TPS/LawsLinksOfGeoRowsColsStatement.lean:22-23` | SEESAW read `lawsLinks_of_geo_rows_cols_alt` 36-140 | — |
| 13 | `allRows_of_open0_alt` | `TPS/LinkROfIsLinked.lean:50-86` | `rRows := … o.mi … row_rRows_stage0_alt …` (:80-85); projections `t.2.2.1.1` = `o.mi` → argument `hMi` | 13a |
| 13a | `row_rRows_stage0_alt` → `row_rRows_of_parts_alt … hMi …` | `TPS/TupAllUsedAtPart.lean:46-48` | `hMi` = 7th Row argument | 13b |
| 13b | `row_rRows_of_parts_alt` | `TPS/RowRRowsOfParts.lean:21-63` | builds `RowsAt4` with `miStar := hM x …` (:60) | consumer below |
| C1 | `nonempty_hyps_of_allRows_alt` | `TPS/NonemptyHypsOfAllRows.lean:19-…` | `hA.rRows` → `HypsAlt.rRows` | `TS` |
| C2 | `shape_closed_link_n_of_green` | TS:33-48 | `rRows` → `rr` in `hBR`, passed as `(rr hc)` to `wire_sel_alt` (:46) | C3 |
| C3 | `GlobalTheory.Top.wire_sel_alt` | `TPS/WireSel.lean:20-50` | `exact wire4F_alt … Fm hc CH` (:50) | C4 |
| C4 | `wire4F_alt` | W4F:26-99 | `hRows` → `ra` (:58); `hP : CovolumeOntoIsometryConditions := {toPrimRows3 := prows, …, miStar := ra.miStar, …}` (:61-63); `packageOfPrimitiveLinks … hP ra.pass` | C5 |
| C5 | `base_lifts_package_of_primitive_links` | BLP:288-347 | `miStar := hP.miStar` (:335) | (SEESAW: → ColFacts/BesselId) |

So **(a): `mainX_of_lawsX` is on the live path**, via `joint_of_famAllQ_alt` (not via the identically shaped `DLP/JointOfFamilyAndService.lean:24`, which I did not trace). The other names SEESAW listed (`miStar2_of_allTrue`, `miStar_row`) are the `_alt_alt` versions on this chain.

### B. BoundsMu determinant identity (consumer at the top → producer)

| # | name | file:line | carrier | next |
|---|---|---|---|---|
| 1 | `shape_closed_link_n_of_green` | TS:44-48 | `hDIV := closed_linkDIVt_of_closed_bridge_kernel … hBR`; `hDIV` passed to `topDesWin` | 2 |
| 2 | `closed_linkDIVt_of_closed_bridge_kernel` → `linkDIVt_of_bridge_kernel` → `linkDIVt_of_rowsT` → `linkDIVt_of_rowsF` | `TPS/DIVRecBridgeSel.lean:192-209`; `…/Divisibility/RecBridgeTied.lean` (linkDIVt_of_rowsT, 4 lines); RB:656-690 | `B.pkg` (`DivisionPackageKernel'`) → face package `P`; `P.wordFacts` (RB:690) | 3 |
| 3 | `DivisionPackageFace.wordFacts` | RB:633-640 | `linkDIV_L2R_face P.Pk …` | 4 |
| 4 | `linkDIV_L2R_face` | `…/Divisibility/LinkDIVL2R3Col.lean:19-24` | `divClausesR_of wf0 wf1 Pk.core …` | 5 |
| 5 | **`divClausesR_of`** | CGT:184-211 | `P.base.boundsMu Formalism.DivisorInequality.boundsMu specDet …` (:211) | 6 |
| 6 | `IndefSide.boundsMu` | IU:271 (body read by DETSIG IU:271-330) | `hdet0/hdet1 := S.detId …` | `IndefRows.detId` = `specDet_rect` (DETSIG) |
| 7 | where `P.Pk` comes from: `hBR` | TS:41-46 | `wire_sel_alt` result | 8 |
| 8 | `wire4F_alt` → `ptK_of_real_alt` | W4F:83; `TPS/PtKOfReal.lean:46-68` | `pkg_of_rowsK_alt R hR … (packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI) …` | 9 |
| 9 | `pkg_of_rowsK_alt` | `TPS/DIVRecBridgeSel.lean:113-161` | `DivisionPackageColumns.ofTied … Pk …` | 10 |
| 10 | `DivisionPackageColumns.ofTied` → `DivisionPackageFace.ofOpen` | `…/Divisibility/RecBridgeSel.lean:63-91`; `…/Divisibility/RecBridgeMkF.lean:15-64` | `Pk := Pk` (:42) | 11 |
| 11 | `packageOfPrimitiveLinks` | `TPS/PtKOfReal.lean:19-25` | `= primitivePackageFullHecke hOk hsep Q.Rl … hP hI` | 12 |
| 12 | `primitivePackageFullHecke` | `…/IndefiniteReal/PrimitivePackageFullHecke.lean:29-37` | `packageFullHecke (base_lifts_package_of_primitive_links hOk hsep hC hP) …` | 13 |
| 13 | **`base_lifts_package_of_primitive_links`** | BLP:288-347 | `thmBop := RealDat3.thmBop_of hP.thmB`, `thmAop := thmAop_of hC.phase hP.thmA false`, `galD := hP.scalConj`, `dimParts := hP.dimParts` (:329-334) | 14 |
| 14 | `hP` in W4F | W4F:61-63 | `toPrimRows3 := prows`, `prows` from `hPA Fm (d3_a hc) x hx h i` | (b′) |

`pkg_of_rowsK_alt`'s `hRows : HEq Pk.core.base.toIndefRows (Classical.choose R.hr.rows0)` (DIVRecBridgeSel:117) makes this IndefRows coincide with the one `R.hr` already holds. That is consistent, not a second producer.

### C. MultEq and the existence of PrimRows3 (root → producer)

| # | name | file:line | carrier | next |
|---|---|---|---|---|
| 1 | `hypotheses_nonempty_of_unramified_exponents_alt` | `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:43` | `⟨hP, hMem, hEx⟩ := large_unramified_exponent_bundles_exist_alt P hR hL cDep A hA` | 2 |
| 2 | `T.large_unramified_exponent_bundles_exist_alt` → `member_bundles_large_unramified_exponents_alt` | `TPS/MemberBundlesLargeUnramifiedExponents.lean:69-70, 34-63` | `hPM : MemberHypotheses := ⟨P.harishChandraAnalyticity, …⟩`; `hH := compatibleSystem_member_rationalWeights hPM … P.siegelEisensteinSimplePole … hR` (:50-53); `member_exists_baseLattice_alt hA hE hH hW hL hN cDep hM` (:61) | 3, 6 |
| 3 | `T.compatibleSystem_member_rationalWeights` → `Mem.member_hodgeHyp_of_localInputs_rationalWeights` | `LTD/MemberHodgeHypOfLocalInputsRationalWeights.lean:12-25` | `condition_of_memberHypotheses dc (twisted_siegel_weil_identity_of_siegel_weil_formula …) … (twisted_local_multiplicity_eq m.m1 … m.m14) r` | 4 |
| 4 | `condition_of_memberHypotheses` | `LTD/ConditionOfMemberHypotheses.lean:25-30` | `multL := m`; `multW := (StepW.and (… .trans m) r).trans (… ⟨G.1 …, G.2 …⟩)`, so the MultEq component of multW is from `m` | 5 |
| 5 | **`MultAt.twisted_local_multiplicity_eq`** | `LTD/TwistedLocalMultiplicityEq.lean:13-34` | `equalMultiplicities_rowTest_of_sameGroupTransfer …).1` (copy transport) applied to `T.twisted_multiplicity_one …` | 5a |
| 5a | `T.twisted_multiplicity_one` → `MultEqFinal.twisted_multiplicity_eq` → `UpperTheory.Lit.I5.unitary_theory_of_harishChandra_langlands_alt` → **`PsCo.Pc.multEq_of_sides`** | `LTD/TwistedMultiplicityOne.lean:9-12, 21-22`; `LTD/UnitaryThetaCorrespondenceOfHyp.lean:15-18` | `multEq_of_sides localPseudoCoefficientExistence_unitaryGroup rd hf dm gc (SpecX.main ds tc) (trace_separation_of_iwahori_trace …) (ellipticSideDirect tc) ellipticT R F hG` | stop |
| 6 | `T.member_exists_baseLattice_alt` → `Bl.exists_baseLattice_of_prime_alt` | `TPS/ExistsBaseLatticeOfPrime.lean:80-81, 56-73` | `holdsW := w_of_weight_residue_char hH.h1 hH.h3 hH.multW` (:62) | 7 |
| 7 | `T.w_of_weight_residue_char` → `w_of_multEq_and_test_at_weights` ⊃ `atDat_holds_alt` | `LTD/WeightSetResidueCharacteristic.lean:68-69, 53, 12-45` | `rational_data_sized_family_alt hP hL` (:21) | 8 |
| 8 | `T.rational_data_sized_family_alt` → `PrimIn.holds_of_ties_alt` | `LTD/RationalDataSizedFamily.lean:12-34` | `real_data_weight_vector_family_core_alt hP hHL eps heps` | 9 |
| 9 | `T.real_data_weight_vector_family_core_alt` → `Closing3.primRows3_typesSep3_alt` | `LTD/RealDataWeightVectorFamilyCore.lean:12-46` | `hPrim := primRows3_of_parts P.q2 P.q1 R F … hM … hGal` (:33) | 10 |
| 10 | `primRows3_of_parts` | `DAV/Proofs/DivisorProofs/PrimRows3OfParts.lean:24-50` (DETSIG/MULTEQ read) | `dimParts` from `hME : MultEq` | stop |

The `hGal` (GalD) supplier on this route is `T.real_data_weight_vector_family_alt` (LTD), not the `Stage4.stage4` that MULTEQ §2.5 followed. I did not open it.

### D. Every `True`/`trivial` in the root records (T2)

| slot | type of slot | filled by | consumers on live path | needs content? |
|---|---|---|---|---|
| `UnitaryGroupThirdPlaceHypotheses.siegelEisensteinSimplePole` (`TPS/BernsteinUnitaryProductIrreducible.lean:74`) | `UnusedSlot72`, an `abbrev … : Prop := True` | `siegel_eisenstein_simple_pole O := trivial` (ECL:505-506; record ECL:718) | only `member_bundles_large_unramified_exponents_alt:52` → … → `dm_of_two`'s 3rd argument (`_`, unused) | no |
| `doubling_method O` (ECL:371-372) | the 3rd explicit argument of `dm_of_two`, type `True` | `trivial` | `dm_of_two` ignores it | no |
| conclusion `DoublingMethodLocalZetaIntegrals = ResidueKilled.DM` (`LTD/DiscreteSpectrumResidualClassification.lean:6`) | a Prop whose second conjunct is literally `True` (DmOfHyp:18) | — | the record fields `doublingMethod` (ECL:654, 678, 740) and `rallis_of_dm` (ECL:486) | a consumer of `.2.1` would get nothing. All live consumers are typed against DM, not against the pole-bearing `Published.DoublingMethod` |
| `TopShapeAlt True True …` V and NR slots (`TPS/TopShapeAlt.lean:10, 36, 70`) | `V := True`, `NR := True` | `trivial trivial` (`TPS/TopPlug.lean:11`) | `shape_closed_link_n_of_green` binds them as `hVC`, `nR` (TS:34) and never uses them (body TS:35-48 read) | no |
| `OpenLiteratureStatements` (ECL:215-218) | three real Props | `⟨h, recTExists, h⟩` | — | not True |
| all other `…_of_literature O` fields (ECL:219-809) | I located the definitions of all 182 field types with a script (`scratchpad/tools/ecl_types.py`, `chk_true.py`). Only `UnusedSlot72` is defined as `True` | closed in-tree terms | — | — |

## 3. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `PsCo.Pc.multEq_of_sides` (+ `localPseudoCoefficientExistence_unitaryGroup`, `SpecX.main`, `ellipticSideDirect`, `ellipticT`, `GivenOfTop.given_of_top`) | `LTD/UnitaryThetaCorrespondenceOfHyp.lean:17` (use site) | the live MultEq: simple-trace-formula comparison of inner forms | **core; not opened**. MULTEQ's analysis was of `multEq_of_trCusp`, which is not live |
| 2 | witness constructor storing `intersectionNumber_baseChange.prim` | via `exists_baseLattice_of_pair_alt` / `memberE_closing_alt_alt` (`TPS/ExistsBaseLatticeOfPrime.lean:53-73`) | ties the `PrimRows3` read in `of_wit_alt` to `primRows3_of_parts` | core link, untraced |
| 3 | `T.real_data_weight_vector_family_alt` | `LTD/RealDataWeightVectorFamilyCore.lean:30` (use) | live GalD (`hGal`) | core for v ≠ v₀, not opened |
| 4 | `miStar2_at_realisation_alt`, `mainX_of_lawsX`, `lawsLinks_of_geo_rows_cols_alt` | as in table A | seesaw | already read by SEESAW; now confirmed live |
| 5 | `base_lifts_package_of_primitive_links` → `packageFullHecke` → `IndefSide.boundsMu`/`detId` | BLP:288; IU:271 | det identity | DETSIG's reading applies to the live path |

## 4. Oddities

1. **MULTEQ's MultEq trace is off the live path.** The live MultEq lemma is `multEq_of_sides` (LTD), and the live PrimRows3 producer chain runs through the LTD twins (`primRows3_typesSep3_alt`, `holds_of_ties_alt`, `atDat_holds_alt`), not the DAV ones. MULTEQ's "good ⇒ simple parameter" argument should be re-checked against `GivenOfTop.given_of_top` and `multEq_of_sides`.
2. **SWRANGE's open question is settled.** The `HypothesesUE` / `member_bundles_large_ue` producer is reachable only from `EveryCharacterE.lean`, whose two theorems have no callers. The file is imported by `TPS/SiegelEisensteinSecondTermHypotheses.lean:1`, but nothing in it is used.
3. **The simple-pole clause is removed, not proved.** `DM` replaces the `DoublingMethod` pole clause with `True` (DmOfHyp:18). The root feeds `trivial` into a slot named `siegelEisensteinSimplePole`. This is harmless only because no live consumer uses that clause. If a reviewer believes some step (Rallis inner product in the Weil range, `rallis_of_dm`, ECL:486) mathematically needs "at most a simple pole at (b−n)/2", that step cannot be getting it from here.
4. **PrimRows3 (κ, λ, MultEq-dimensions, GalD) enters the consumer as a bundle-membership condition** (`of_wit_alt`), not as a theorem applied at the use site. The real content is the existence proof (table C), and the final link of that proof is untraced (child 2).
5. DETSIG named `divClauses_of` (DHB:752, `IndefCore`) as the consumer. The live consumer is `divClausesR_of` (CGT:184, `IndefCoreR`). Both call the same `IndefSide.boundsMu`, so DETSIG's mathematics is unaffected.

## 5. Coverage

Read:
- PROTOCOL, NODE-ROOT, NODE-JOIN, NODE-SEESAW, NODE-DETSIG, NODE-MULTEQ, NODE-SWRANGE; ECL:200-814;
- `TPS/`: SiegelEisensteinSecondTermHypotheses.lean:39-76; HypothesesNonemptyOfUnramifiedExponents.lean:36-64; NonemptyHypsOfAllRows.lean:15-80; RowRRowsOfParts.lean (all); TupAllUsedAtPart.lean:26-69; LinkROfIsLinked.lean:40-88; OpenOrbitOfUnramifiedExponents.lean:20-78; GeometricWeakTies.lean:36-54;
- MainTheoremPublishedInputsThird/InputsVariant/ResultsFinal/FromPublishedResultsAlt⁵/Alt⁴ (all); TruePack.lean (all); MiStar2OfFamiliesStatement, FamAllQOfAllTrueStatement, MiStar2OfFamilies.lean:1-28, MiStar2AtRealisationStatement, JointOfFamAllQStatement, JointOfFamAllQ.lean (all); FamAllQOfAllTrue.lean:38-56;
- TopShape.lean:20-50; TopShapeAlt.lean (greps 10, 36, 60-85); TopPlug.lean (all); WireSel.lean (all); Wire4F.lean:26-99; PtKOfReal.lean:17-90; DIVRecBridgeSel.lean:113-209; MemberBundlesLargeUnramifiedExponents.lean (all); HermWCellLastMulMulVecEqOfInWb{,Statement}.lean (all); ExistsBaseLatticeOfPrime.lean:50-85; BernsteinUnitaryProductIrreducible.lean:70-76;
- `DLP/`: SeesawTransportRelationsOfFamilyLaws{,Statement}.lean (20-40; 10-16);
- `LTD/`: DiscreteSpectrumResidualClassification.lean:1-12; TwistedSiegelWeilIdentityOf{SiegelWeilFormula,Formula}.lean (all); DoublingMethodOfEisensteinFacts.lean (all); MemberHodgeHypOfLocalInputsRationalWeights.lean (all); MultiplicityCoverHypotheses.lean:10-40; ConditionOfMemberHypotheses.lean:12-45; TwistedLocalMultiplicityEq.lean (all); TwistedMultiplicityOne.lean (all); UnitaryThetaCorrespondenceOfHyp.lean (all); RealDataWeightVectorFamilyCore.lean (all); RationalDataSizedFamily.lean (all); WeightSetResidueCharacteristic.lean:1-72;
- DmOfHyp.lean (all); `DAV/…/EqualMultiplicitiesRowTestOfSameGroupTransferStatement.lean:10-16`; `DAV/…/LinkedBundleConstructionExistsStatement.lean:8-16`; `DAV/…/NonemptyHypsOfPublishedUE.lean` (grep); `FockModels/EveryCharacterE.lean` (greps);
- `Formalism/…`: DivisionHeightBoundStatement.lean:885-1010; ConstantGeTwentyEight.lean:184-215; LinkDIVL2R3Col.lean:19-24; RecBridge.lean:630-640, 656 and 690 (grep); RecBridgeTied.lean (linkDIVt_of_rowsT); RecBridgeSel.lean:63-91; RecBridgeMkF.lean (all); PrimitivePackageFullHecke.lean:14-57; BaseLiftsPackageOfPrimitiveLinks.lean:230-347; LinksLemmas.lean:361-431; ConcretePkgSpec.lean:170-190; IndefiniteRealisationChoice.lean:117-133; `GlobalTwisting/BhattScholzeCrystallineLattices.lean:80-84`.

Not opened:
- `multEq_of_sides` and its inputs; `real_data_weight_vector_family_alt`;
- the witness constructor of `intersectionNumber_baseChange`;
- `classSel`; the `hPA` projection inside `classSel`'s output (type-matched only);
- `linkDIVt_of_rowsF` beyond the line-690 call; `BridgeRowsT.toF`;
- `DLP/JointOfFamilyAndService.lean` (parallel, not on the traced chain).
