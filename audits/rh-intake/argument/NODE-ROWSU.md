# NODE-ROWSU: is "the period pairing on the enlarged lattice is p^{gain}-divisible" proved, for a nonzero pairing?

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `DA` = `Formalism/LocalRingCardinality/DataArith.lean`
- `RB` = `Formalism/LocalToGlobal/Divisibility/RecBridge.lean`
- `RBT` = `Formalism/LocalToGlobal/Divisibility/RecBridgeTied.lean`
- `LQP` = `Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean`
- `PTK` = `Formalism/LocalToGlobal/PtKOfReal.lean`
- `SPL` = `Formalism/HarderNarasimhan/StatementPl.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `MOK` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/ModelsOK.lean`
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`

## 0. Verdict (short)

The height of B_u splits cleanly in the Lean:
- the **non-archimedean part** is `OneMapIntoCC`, which says B_u maps the enlarged lattice N_u into RR^∨;
- the **archimedean part** is `htMap ≤ h`, where htMap sums over infinite places only (`SPL:60-62`).

The two halves are proved from different hypotheses:

| Part | Clause | Proved from | Kind of input |
|---|---|---|---|
| Non-archimedean | `OneMapIntoCC` | `adm2` (`LQP:206-210`) | a valuation bound on the actual period columns |
| Archimedean | `htMap ≤ h` | `RowsU` (`PTK:141-160`) | operator-norm bounds |

`adm2` is supplied on the live path by a chain that ends in formal-group "LowAt" valuation bounds on the family's own chain map, not on `zeroCh`. Those bounds come from per-site `FormalGroupSystem.admitted` data (13 conditions). This **corrects NODE-SLOPESN**, which said `twU` has no constructor. It has one, through `ServH`/`RowTwU` (§2a).

There is no free archimedean scalar that cancels the divisibility:
- Both clauses constrain the same LL-bilinear map `Bk u`.
- h(u) = `hExpl6` is a fixed formula.
- The scalar `a ≠ 0` in BesselId is a fixed realisation datum (d.a·λ), and it multiplies both sides.
- The free reals `logOmτ` only redistribute a bound across embeddings. Their mean is fixed at logΩ.

**Nothing in LinkDIV forces B_u ≠ 0 or injective.** `adm2` allows "period = 0". The height clause is guarded by `Bk u ≠ 0`. Rank and injectivity have to come from elsewhere (LinkS/SlopeIneq, LinkIRR). That is outside this node.

**Answer to (d): could-not-determine, leaning "conditionally yes in form".** On the live path the divisibility is a genuine-looking p-adic statement about the real period columns of the actual chain. Its depth, though, sits in `sysTw_sites` and in the per-site `admitted` package, which I did not open. It is not a definition, and it is not `zeroCh`.

## 1. Statement (the objects, as mathematics)

**`LinkDIV_at`** (`GTI:77-89`). Its relevant clauses are:
- (i) `D.div.OneMapIntoCC`;
- (iv) `BesselId D`;
- (v) `RRFull`;
- (vi) `∀ u, D.div.Bk u ≠ 0 → htMap (Nu u).b (Nu u).X RR.dualB RR.dualX (Bk u) ≤ D.div.h u`.

**`OneMapIntoCC`** (`DA:180`): `∀ u, (D.Nu u).L.map ((D.Bk u).restrictScalars (𝓞 K)) ≤ D.cc`. In words, B_u sends the O_LL-lattice N_u into cc = RR^∨. This is integrality at every finite place. N_u = I_u·NuLat_u is enlarged by 𝔭_w^{−⌊e_w sg⌋} (NODE-SLOPESN). So this clause **is** the divisibility statement.

**`htMap`** (`SPL:55-62`): (1/nPl)·Σ_{v ∈ InfinitePlace} log ‖X'_v^{-1}·(matrix of φ)^v·X_v‖². It is **archimedean only**.

**`adm2 D L`** (`LQP:206-210`), quoted:
```
∀ u w (φ ∈ L.NuLat u), ∀ F ∈ Mtilde(muAt w) ∩ V0(muAt w),
  ∃ y : LL, embLL y = perCol u (muAt w) (jN u φ) F ∧ (y = 0 ∨ ⌊ur D w (sg u w)⌋ ≤ v_w(y))
```
In words: every period column of an un-enlarged lattice vector against an integral test vector is LL-rational, and it is either 0 or divisible by 𝔭_w^{⌊e_w·sg(u,w)⌋}. Here sg = Σ_j(gain_j + F_j − E_j). This is "periods divisible by p^{gain}".

**`BesselId D`** (`GTI:65-67`) = `BuRational ∧ adm13`. Here `adm13` (`LQP:330-332`) and `TR_at` (`MainIn.lean:40`) say: ∃ isometry V of EE such that ∀u ∃ a ≠ 0 and an isometry U of Mu u with Bu u φ F = a·besS u (Uφ)(VF).
- besS (`RhoDetPrimeEqMuTildeMulChiPow.lean:353-354`) = ⟨sEE F, s.Pu u(…φ…)⟩, where sEE, s and Pu are D7 fields.
- `BuRational` (`:364-365`): Bu(jN φ, jEE x) = embLL(Bk u φ x). This ties the complex pairing to the LL-bilinear Bk.

**`DivTied3`** (`Formalism/LocalToGlobal/Divisibility/DivisionCompatibleToSub2Indef2.lean:172-197`) is a structure of identification ties only:
- `ranks`: m, r, t equal D.R's;
- `grp`, `tup`, `mu1`, `sharp`/`base` (RowSideTie), `mt`, `th`, `num`, `cols` (ColTie).

It says that the three-sided realisation's groups, tuples, row sides, theta maps and columns are the D7's. **It contains no divisibility and no norm bound.**

**`RowsU c Pk R w Nu`** (`PTK:141-160`) says the following exists:
- a column chain `ch` with a tie `T`, and `FirstCols`;
- metrics X0_v with (X0_v^{-1})^*·X0_v^{-1} = HV_v. That is, X0 is a square-root frame of the side's hermitian form, so it is pinned;
- `hn : HtNums R Emb` with ‖ch.PtL‖²_v ≤ exp(hn.hPn) at every infinite v (PtL: the period functional at the top of the chain);
- `cb : CBData ch.X ch.Kj` with log cb.sq(j, v) ≤ Σ_{l: lf l = j} hn.sz(l, v) (squared operator norms of the chain maps K_j at v);
- the matrices Xc at w invertible, a w > 0, and Nu a lattice.

**RowsU is purely archimedean.** The factorisation RBT:150-163 gives PtL(chainMat(K)·φ) F = colPerL(…colMu…φ…) F. So the period pairing is PtL ∘ K_m ∘ … ∘ K_1. Submultiplicativity then gives htMap(B_u) ≤ mean_v[hPn + Σ_j log cb.sq] = hu − meanLog κ = h(u) (DIV §2 step 5).

**`HtNums`** (`Formalism/LocalToGlobal/Divisibility/Inputs.lean:210`) and **`CBData`** (`:342`): see NODE-DIV. These are existential numerical records. `logOmτ` is free per embedding, but `i1` fixes its mean to logΩ.

**`DefiniteSideCondition`** (`TPS/DefiniteSideCondition.lean:25-40`): for each bundle b and all the package data, `DivTied3 … NuC I → HEq I b.P.I → ∀ u, RowsU …`. So: if the realisation is tied to D, the archimedean row bounds hold.

## 2. Argument / suppliers on the live path

### (a) Non-archimedean: who proves OneMapIntoCC, from what

1. `LinkDIV_at` (i) comes from `WordFacts` clause 1 (`RB:128-129`), via `linkDIV_at_words` (`RB:327-337`).
2. `DivisionPackageFace.wordFacts` (`RB:633-644`) feeds
   `val2 := val2AllAtRF D L _ P.brTied hcut h2 u (P.Nu u) (nu_into L hN u … (P.shift u))`.
   - `h2` is `adm2`.
   - `shift` says NuC = shiftLat(Nu, sgRec), i.e. the coordinate form of the enlargement.
   - `hN` is `NprimeDef`.
   So integrality on the enlarged lattice is reduced, by an honest span induction (NODE-SLOPESN), to `adm2` on the un-enlarged lattice with exponent sg. The enlargement and the exponent are the same sg. *I checked the call; I did not reread `perToVal2`.*
3. `adm2` is the field `B.adm2` of `DivisionKernelConstantBounds` (`TPS/DIVRecBridgeSel.lean:173`). In `TopShape.lean:41` it is `hA2 := closed_family_admissible_twist_link_alt 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ`. NODE-SLOPESN unfolds the chain from there: famU → admissible_off_twist_places → `Conclusion1` (ServF) → `UAt` + `CmpV`.
4. **`hServ` has a supplier.** It is a `HypsAlt` field (`TPS/Hyps.lean:76`). The supplier chain:
   - `allRows_of_open0_alt` (`TPS/LinkROfIsLinked.lean:76`) sets `hServ := … hServ_of_linkR hA …`;
   - → `row_hServ_of_link_alt` (`TPS/RowHServOfLink.lean:17-23`), whose premise is `Published.GlobalArtinReciprocity`;
   - → `reciprocity_kernel_of_artin` → `servH_row_linkR_alt` (`TPS/ServHRowLinkR.lean:14-20`);
   - → `ServH` = `RowTwU Fm ∧ Pdv.At …` (`…/GaloisGeometry/HasPartAnd.lean:45-46`).
   
   A second producer exists at `…/GlobalInterpolation/LinkedBundlesOfCasselmanWallach.lean:78`. *I did not confirm which of the two producers the root's HypsAlt uses.*
5. **`RowTwU`** (`MOK:41-44`): ∃ a chain LC with `CmpV` and `SysTw` for `reW (Fm.Gy x i) LC`. It is proved by `rowTwU_of_models` (`…/SatakeParameters/UnitaryWeightModels.lean:15-30`) from three inputs:
   - `OrbitLetterBoundsAll 11 1`;
   - `Shape`;
   - **`ModelsOK`** (`MOK:56-62`): ∃ LC such that at every used site, `CmpLite` (`MOK:46-55`) and `SiteAdm` hold.
   
   `CmpLite` says the comparison maps intertwine D's twisted chain `(D.chTw u μ).K j` with `Ch.Kz j`. Its last clause, quoted:
   ```
   vGeLat … (cmp m y) s → VGe D w (lat m).L y s
   ```
   So valuation information on the model chain transfers back to the actual lattice. *I infer* that LC cannot be taken to be zero unless D's own chain vanishes on the lattice, because then VGe would hold for every s.
   
   `ModelsOK` comes from `ModelsAt` (`HasPartAnd.lean:13-14`), which is built by `builtC_hasPart` for `IsBuilt` contexts (not opened).
6. **`SysTw`** (`MOK:24-39`): at each site there is a formal-group system Y5 with `FormalGroupSystem.admitted D _ Y5` and functions Fn with:
   - `Y5.LowAt j v (Fn v (j+1))` (`FGS:529-533`): every coefficient of the D-operator applied to the theta power series ThZA(expS(−PhAt)·U) has valuation ≥ g;
   - lowS ≤ Σ_j Σ_v Fn − Σ dG.
   
   This is the "iterated-lift valuation ≥ gain" statement, a Dwork-exponential/formal-group integrality on the actual chain. It is proved by `local_systems_lower_bounds_second_real_place` (`…/LocalSystemsLowerBoundsSecondRealPlaceStatement.lean:11`) → `SiteSys.sysTw_sites`, **not opened**, from `SiteAdm` (`…/IsPlaceCofactorValuationLowerBound.lean:10-14`: ∃ Y5 admitted with dG 0 = 0 and dG j ≤ v_p(DGam)).
   
   `admitted` (`FGS:771-773`) is a conjunction of 13 local conditions: adm1, adm2, adm2b, adm2c, adm3, adm3b, ArchimedeanSignatureMatching, adm5, MinkowskiCounting, adm6, adm7, adm8, adm11. I did not unfold them.

Classification: **(ii)→(i)**. It is a hypothesis field (`hServ`, and `aPt0…aAtG` for the period-integrality step) whose supplier is a theorem. That theorem rests on a formal-group valuation computation (`sysTw_sites`) over per-site `admitted` data, which in turn comes from the D7 construction (`IsBuilt`) and the `GlobalArtinReciprocity` premise. It is **not** (iii): the exponent sg is the gain, and the bound is asserted for the real perCol. It is also **not** `zeroCh` (NODE-SLOPESN §0.4, and LC here is `reW (Fm.Gy x i) LC`).

I did not check whether the lowS/Fn bound is quantitatively ≥ gU − Pr at every served place. That is the decisive numeric step, and it lives in `sysTw_sites` together with `UAt` (`WJS:161-170`, per NODE-SLOPESN).

### (b) Archimedean size, nonvanishing, free scalars

- **The archimedean upper bound is pinned.**
  - h(u) = `hExpl6` (`Fm.h_eq`, used in `RB:672`).
  - htMap ≤ h comes from RowsU.
  - RowsU is **proved** on the live path by `definiteSideCondition_of_nprimeDef_of_nuFull` (`TPS/PointEvaluationSide.lean:43-63`), via `kernel_columns_from_ties_alt` (not opened). Its inputs are PointEvaluationSide, `HtRowsS`, `NprimeDef`, `NuFull`, `∀ u, 0 < rank (Nu u)`, and `C0 ≤ c`.
  - It is installed by `linkedAt_df_of_parameters` (`:64-85`).
- **Product formula.** Scaling Bk by an integer N makes integrality easier but raises htMap by 2 log N. Scaling by 1/N lowers htMap but breaks integrality. Since both clauses are about the same `Bk u`, and h is fixed, no free scalar trades one against the other.
  - The `a ≠ 0` of BesselId is produced in `adm13_of_colJoin`/`adm13_of_joinSI` (`Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/AdmissibleOfTransported.lean:150-187`) as d.a(m u)·λ from a kernel join. It is the same scalar on both sides.
  - The metric X0 in RowsU is pinned to HV.
  - `logOmτ` is free only up to its mean.
  - *I did not trace* whether N_u's own metric Xc is pinned beyond invertibility. It is tied through `HLatTie` (`RB:613`) to the column data. If it were free, μ(N_u) and htMap would shift oppositely, so it would also cancel in the chain.
- **Nonvanishing / rank: not forced here.**
  - `adm2` allows y = 0, and `OneMapIntoCC` holds for B = 0.
  - Clause (vi) and `WordFacts` (`RB:130`) are guarded by `Bk u ≠ 0`.
  - BesselId's a ≠ 0 does not stop besS from being 0, because sEE and Pu are D7 fields.
  - Only ranks are bounded below: `0 < rank Nu u`, `NuFull`, `RRFull`.
  - Injectivity/near-isometry must come from LinkS/SlopeIneq (`InputSG`) and `LinkIRR` (delp ≤ exp(−x^{ez/7}), `GTI:52-54`). These are outside this node.

## 3. Children (ranked)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `SiteSys.sysTw_sites` / `local_systems_lower_bounds_second_real_place` | `…/LocalSystemsLowerBoundsSecondRealPlaceStatement.lean:11` | per-site admitted formal-group data ⇒ LowAt chain valuations sum to ≥ lowS (≈ gain) | **core**, not opened |
| 2 | `FormalGroupSystem.admitted` (13 conditions) and `SiteAdm` from `ModelsAt`/`builtC_hasPart` | `FGS:771`; `IsPlaceCofactorValuationLowerBound.lean:10`; `HasPartAnd.lean:13` | local integral models of theta series at each site | core, definition to unfold |
| 3 | `UAt` + `CmpV` → `Conclusion1` → `period_geTU` (with `aPt0, aPtTw, aPer0, aPerTw, aP10, aAtG`) | NODE-SLOPESN; `TopShape.lean:41` | chain valuation ⇒ column valuation ⇒ period valuation ≥ sg | core |
| 4 | Injectivity / near-isometry of B_u (LinkS, SlopeIneq, LinkIRR) | `TopShape.lean:55`; `GTI:52` | B_u is almost an isometry; delp tiny | core, outside LinkDIV |
| 5 | `kernel_columns_from_ties_alt` (RowsU) | `PointEvaluationSide.lean:47` | operator norms of the PtL and K_j at each infinite place ≤ exp(sz) | core (archimedean), not opened |
| 6 | `adm13_of_joinSI` (BesselId) | `AdmissibleOfTransported.lean:183` | B_u is proportional to besS via kernel join | glue/structural |

## 4. Oddities
1. **Correction to NODE-SLOPESN §0.3.** `twU` is supplied, by `ServH`/`RowTwU` ← `rowTwU_of_models` ← `ModelsOK`, under `Published.GlobalArtinReciprocity`. It is not a constructor-less binder.
2. `adm2` and `OneMapIntoCC` are satisfied by the zero pairing. The height clause is conditional on Bk ≠ 0. LinkDIV by itself is consistent with B_u = 0.
3. BesselId gives Bu ∝ besS with a ≠ 0, but besS is built from D7 fields (sEE, s.Pu). Its nonvanishing is not stated.
4. DivTied3 is only identification ties, so DefiniteSideCondition is an "under the ties, the norm bounds hold" implication. Its real content is in `kernel_columns_from_ties_alt`.
5. Two producers of HypsAlt.hServ exist (`LinkROfIsLinked.lean:76`, `LinkedBundlesOfCasselmanWallach.lean:78`). Which one the root uses is unconfirmed.

## 5. Coverage
Read:
- `GTI:55-100`; `DA:55-100, 170-185`; `SPL:55-90`;
- `RhoDetPrimeEqMuTildeMulChiPow.lean:340-372`; `PTK:80-175`;
- `TPS/DefiniteSideCondition.lean` (all); `DivisionCompatibleToSub2Indef2.lean:140-240`;
- `TPS/PointEvaluationSide.lean:1-90`; `TPS/GServT.lean`; `TPS/TopShapeAlt.lean:60-110`; `TPS/ServTIff.lean:55-80`;
- `TPS/CountsIrreducibilityConstants.lean:85-130`; `TPS/LinkROfIsLinked.lean:40-100`;
- `TPS/RowHServOfLinkStatement.lean`; `TPS/RowHServOfLink.lean`; `TPS/RowHServOfKerServ.lean`; `TPS/ServHRowLinkRStatement.lean`; `TPS/ServHRowLinkR.lean`;
- `HasPartAnd.lean:13-75`; `MOK:1-80`; `UnitaryWeightModels.lean`;
- `FGS:447-470, 525-535, 765-800`; `LocalSystemsLowerBoundsSecondRealPlaceStatement.lean`; `IsPlaceCofactorValuationLowerBound.lean:10-40`;
- `TPS/SiegelEisensteinSecondTermHypotheses.lean:40-70`; `TPS/DIVRecBridgeSel.lean:150-207`; `RBT:150-240`;
- `RB:120-135, 290-372, 590-720`; `LQP:200-215, 326-336, 425-435`;
- `MainSup.lean:100-160`; `MainIn.lean:36-46`; `TPS/TopShape.lean:30-60`; `TPS/SelectionClosedOfWuDecay.lean`;
- `AdmissibleOfTransported.lean:100-200`.

Not opened:
- `sysTw_sites`; `admitted` components;
- `kernel_columns_from_ties_alt`; `builtC_hasPart`; `cmpV_of_cmpLite`;
- `val2AllAtRF` body; the `closed_family_admissible_twist_link_alt` chain (relied on NODE-SLOPESN);
- Nu's metric Xc provenance; LinkS injectivity.
