# NODE-WHERECONG: where the congruence / Selmer / U(3) machinery enters the slope inequality

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the line. *(inferred)* marks my reading. Nothing was compiled.

Abbreviations:
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `DTC/` = `Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/`
- `IE/` = `Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/`
- `SO` = `Formalism/DivisorInequality/StatementObj.lean` (`BoundsMu`)
- `IU` = `Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean`
- `CGT` = `Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`
- `TPE` = `Formalism/LocalToGlobal/Divisibility/TwistedPlaceEtaSumLeExtended.lean`
- `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `DNV` = `Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean`; `DW` = `Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean`
- `W4F` = `TPS/Wire4F.lean`; `TS` = `TPS/TopShape.lean`; `IFT` = `TPS/ImportsFurtherTail.lean`; `APE` = `TPS/AdmissibleParameterEventually.lean`

## 0. Verdict

**No ESCALATE.** Every term of the final inequality has a live supplier.

**Answer: candidate (ii).** Seven pieces were traced. All of them are live. All of them reach the slope chain through **one scalar per lift, E2_j**. The pieces are `CongBound_at`, `KillAt`, `LinkN`, `VWin`, `OneCharU`, `AutEnd3Alt` and `Row0b`. Together with residual irreducibility, they feed nothing else.

What E2_j is:
- At each twisted place y ∈ Tw, take the lattice T_j obtained by projecting the integral lattice onto the Hecke-eigen type part Z_j.
- Its dual index jw(T_j) is bounded by Hida's congruence module η = etaJW (`jw_le`), plus a term J0·D for how far the ambient lattice is from self-dual. That J0·D term goes to E1, not E2.
- E2_j is the weighted sum Σ_{y∈Tw} lw·η/D.

Where E2 is used:
- It enters `BoundsMu`, the upper bound on μ(RR^∨) (SO:67, 70, 72-74).
- The **same** E2 also enters the base→column passage constant Q (`Qb`, `deQ`; CGT:99, 214, 225-227).
- It enters the final DIV error budget `errB` (CGT:89).

What this rules out:
- (i) is **not** where `AutEnd3Alt` enters. `T3`/`sig_all` is supplied by `sig_all_of_sideB`, a linear-algebra argument that identifies the good part with an explicit model (§2c). That argument takes no Galois-deformation input.
- (iii) is reached only through the copy of E2 inside Q.
- (iv) does not apply: none of the seven pieces is dead.

**Prominent finding about our reconstruction.** The machinery is not dead, but its whole footprint on the slope chain is the error term E2. The pieces are:
- the congruence ⇒ Selmer bound (`CutCoreUnit.main`);
- Selmer killing by a tame tower (`KillAt`);
- residual irreducibility;
- the Ш bound (`VWin`), and inside VWin the residually reducible U(3) R = T (`OneCharU` ← `GdEndAlt` ∋ `AutEnd3Alt`) and `Row0b`.

None of them touches:
- the height of the evaluation map;
- the main term of the covolume, lcv(M_j);
- the twisted-place indices (E1);
- the Rallis scalars;
- Theorem S / the frame;
- non-vanishing.

Within E2, VWin's Ш contribution is ≤ √b against an allowance of order x^{2.5+O(ε)}·b (CONGMOD §3). So the entire U(3)/`AutEnd3Alt` branch bounds a summand for which any bound ≤ b would do. It is wired in with no alternative, but numerically it is nearly idle.

## 1. Statement (what was traced)

For each piece: its consumer chain up to `BoundsMu`/`DivClausesR` on the live path (top: NODE-LIVEPATH tables A–B), and the term of the final inequality it controls.

The final inequality on the live path is `divClausesR_of` (CGT:184-245). Its clause (iii) reads:

  μ(RR^∨) − meanLog κ + h(u) − 2Fo ≤ rhs.

Its pieces are as follows.
- **(a) BoundsMu, the covolume of RR^∨** (CGT:211 → IU:271-334 → SO:17-77). It gives
  μ(RR^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + 2Σ lw·F + LG + Σ_j(E1_j + E2_j) + E3.
  The hypotheses that matter here:
  - SO:65: index at Tw ≤ (2F + err)·D + 2/ℓ²;
  - SO:67: jw ≤ Jy·D + ηy;
  - SO:69: Σ lw·(err + Jy) ≤ E1;
  - SO:70: Σ lw·ηy/D ≤ E2;
  - SO:71: Σ lw·2/ℓ² ≤ E3.
- **(b) The height clause** (CGT:205, `height_chain_atR`): Fock/jet norms, κ and the Rallis λ, via `eig6 : Σ hX ≤ Σ l6` (CGT:52).
- **(c) The covolume main term** `L3main` (Σ l3 ≤ Σ pq·w·logΩ + El3), with l3 ≥ lcv/D (IU:333-334).
- **(d) The passage to columns** (CGT:214, 225-227). Here 3·de·Q ≤ 1 and Q ≥ boundBR(LG, E3, **E2**) + hh + 28la (CGT:99).
- **(e) `errB`**: El3 + LG + Σ(E1 + **E2**) + E3 ≤ R.errB (CGT:89). It is closed by `R.divIneq` (CGT:245).

The non-vanishing and Theorem S inputs are not in DIV. They enter the Bost/frame side (`LinkS`, `LinkIRR`; DW:16, 21).

## 2. Argument (consumer chains, read upward)

### 2a. The common trunk: E2 ← InEta ← DIVinN ← {LinkN, HypV}

| # | step | file:line | content |
|---|---|---|---|
| T1 | `IndefSide.boundsMu` | IU:271-334 | takes `hiv` (jw clause, IU:281) and `hE2` (IU:283), and passes them to `BoundsMu` (IU:332) |
| T2 | `divClausesR_of` | CGT:211 | calls it with `I.biv`, `I.borderedMinorImage` (fields CGT:78, 81 of `DivInputs0R`) |
| T3 | `DivInputsDef3.toDivInputs0R` | TPE:247-286 | `biv := lift_index_bound_extended … I.h11` (TPE:273); `ηy := etaYOf …` (TPE:270); `E2 := etaSumBound bd dg s` (TPE:268); `borderedMinorImage := twisted_place_eta_sum_le_extended … I.hN` (TPE:274) |
| T4 | `lift_index_bound_extended` | TPE:30-61 | jw(T_j) ≤ etaJW + D·(JJW + v(DG) + v(s)), using `jw_le` (TPE:48); JJW ≤ ramw·J0 from `LiftExponentAtTwisted` (TPE:36, 41-43, 56) |
| T5 | `twisted_place_eta_sum_le_extended` | TPE:63-96 | from `InEta` (Σ_{Tw} lw·etaJW ≤ bd·D) it derives Σ lw·ηy/D ≤ bd + log dg + log s |
| T6 | `DivisionInputsWithoutNorm.toDef` | TPE:299-302 | inserts `hN : InEta` |
| T7 | `inpAt_of_alt` | `TPS/InpAtOf.lean:17-56` | `hN := inEta3_num … Ce hDIV …` (:49-50), with `hDIV : ∀ j, DIVinN_at L j Ce` (:25); builds `inp` via `.toDef hN` (:54-55) |
| T8 | `inEta3_num` → `inEta_num` | `Formalism/LocalToGlobal/Divisibility/SumLeEtaSumNum.lean:78-84, 60-74` | Σ over Tw ≤ etaSum (`sum_le_etaSum_num`) ≤ D0·divSize (DIVinN_at), giving bd_j = C·x^ε(B0 + Nc) |
| T9 | `wire4F_alt` | W4F:42-43, 87 | `hN : DIVinN Fm` is intro'd (:42), destructured (:43) and passed as `hCe x hx3 i` to `inpAt_of_alt` (:87). The result goes into `ptK_of_real_alt` as `hInp` (`TPS/PtKOfReal.lean:55, 70-71`) → `pkg_of_rowsK_alt`'s `hOpen` (`TPS/DIVRecBridgeSel.lean:120-131, 155`) → `DivisionPackageColumns.ofTied`/`DivisionPackageFace.ofOpen` (`…/Divisibility/RecBridgeSel.lean:63-87`; `…/Divisibility/RecBridgeMkF.lean:30-32, 58`) → `wordFacts` (`…/Divisibility/RecBridge.lean:633-640`) |
| T10 | `LinkDIVt` | GTI:94-95 | `LinkEta → DIVinN → LinkDIV`; the DIVinN premise is the `hN` of T9 (via `TS:46`, `pkg := fun hN => wire_sel_alt … hN`) |
| T11 | `topDesWin` | DW:11-31 | `hD := aD hT hDG aE (divinN_of_hypV Fm h0 (hV …) aN aZ)` (DW:29). This is the **only** place DIVinN is produced |
| T12 | `divinN_of_hypV` | DNV:117-130 | HypV (VVle E t √b, DNV:10-11) + LinkN + SmallLevelRankEq ⇒ DIVinN. VVle is used only as Σ' vvTerm ≤ √b ≤ b (DNV:126-128) |
| T13 | `LinkN_at` / `DIVinN_at` | GTI:40-47, 59-63 | etaSum ≤ dZ0·(C(f·m·b·L² + log²x·Nc) + Σ' vvTerm), resp. ≤ D0·C·x^ε(B0+Nc) |

The `hV` and `hN` of `topDesWin` come in from `TS:34, 52-53`: `hV`, and `nRest` as `hN`.

DIVinN also appears, as a premise only, in the `onto` and `fun0` fields of `IndefiniteRealisationConstantBounds` (`TPS/IndefiniteRealisationChoice.lean:74, 77`; supplied at W4F:62 as `ra.onto hN`, `ra.fun0 hN`). I did **not** trace whether the producers of ON/FUN use that premise. Their visible inputs are P-derived: `hOL` at `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:45, 55`, and `row_rRows_of_parts_alt` (`TPS/RowRRowsOfParts.lean:34-36, 57, 61`), where the premise is discharged by `ev_prem`. None of the seven pieces appears among them.

### 2b. Each piece, up to the trunk

**`LinkN`** (live).
- Root side: `hNrow := GalC.final_alt_alt …` (`TPS/HypothesesNonemptyOfUnramifiedExponents.lean:47-48`) → `hN'` (:52-53) → `allRows_of_open0_alt … hN'` (:54-56), whose field is `nRest := hN` (`TPS/LinkROfIsLinked.lean:86`) → `TopShapeAlt` slot `nRest : N (D3 3 𝒜)` (`TPS/TopShapeAlt.lean:85`) → `topDesWin` `hN` (TS:53) → T12.
- Proof of LinkN: `final_alt_alt` (`TPS/CFinal.lean:19-22`) → `final_of_alt` (`TPS/LinkNFam.lean:75-86`) → `linkN_of_twGood_galoisPreconditions` (:37-53). That uses `conclF_of_family_facts_and_bound_at_two_three … (twGood_gd Fm c hTw) …` (:51), which is the wrapper (`TPS/ImportsFurtherTailStatement.lean:11-12`) of `NLinkClose.main_alt_alt` (IFT:30-110).
- **Role.** LinkN bounds the weighted congruence-module sum etaSum_j by dZ0·(f·m·b·L²-scale local terms + Σ_l log l·len Ш).

**`CongBound_at`** (live).
- `hE := eventually_congBound_of_facts hP Fm` (IFT:52) → `hCong` (IFT:73) → `localBoundZeroAtLargePrimes_of_congruenceBound … hCong … hS.kill hSha` (IFT:74) → the `large := hlarge` field of ConclF (IFT:102) → LinkN.
- Supplier: `NLinkE.main_alt_alt` (APE:30-57). It ends in `congruenceBound_extended_of_rationalBound` applied to `globalCongruenceCount_of_rootDifference_unit hP.artin … gno gunr gS gQ hloc` (APE:56-57), the wrapper of `CutCoreUnit.main` (`IE/GlobalCongruenceCountOfRootDifferenceUnitStatement.lean:12`).
- `NoChiOff` comes from `noChiOff_and_unrOut_of_large_good_place` (APE:47).
- **Role.** For l > lStar, l ∉ Exc, the Hida congruence ideal vcc(π) is bounded by sPi + ΣШ + v_l(h_E) + epsQ, with no local-at-l term. That is the StarE row of ConclF: Ribet–Wiles direction, congruence ⇒ extension classes.

**`KillAt`** (live).
- `hkill := chosenTwist_annihilates_selmerGroups (Fm.D x i) … X.I X.ρ hfa.nct (hI ▸ hgood) h6` (`TPS/ExistsSetupLarge.lean:40`).
- Its inputs:
  - `hgood` is GoodTw at the twisted places, from `hTw : TwGood Fm` (:24-26);
  - `h6 := JointSix.main …` (:38-39) consumes **residual irreducibility** (`residualAbsIrredGoodPoint_of_residualIrred _ hfa.rhoBar`, :39).
- Consumer chain: setup `hS.kill` (`exists_hubData_admJ_setup`, IFT:49; wrapper `TPS/ExistsSetupLargeStatement.lean:12-13`) → ConclF fields:
  - `kill := hS.kill` (IFT:94);
  - inside `large` (IFT:74);
  - `ram := starG_of_thmB … hS.kill hSha` (IFT:105-106).
  - From there → LinkN.
- **Role.** It makes the ρ-block Bloch–Kato term sPi ≤ ν_l + 1/l² and the tame term ≤ 1/l² in every vcc bound, so it is again a piece of etaSum → E2.
- It shares `GoodTw` with `IdxAt`, so one twist pack serves E1 (via IdxAt) and E2 (via KillAt). KillAt itself feeds only E2.

**`VWin`** (live).
- Root: `everyCharacter_of_row h = every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)` (NODE-ROOT, ECL:810-814).
- Then `every_character_of_green_v_win hG hV` (`TPS/TopPlug.lean:16-18`) → `supplyChi ψ (hV ψ)` gives `HostExW` (`TPS/TopPlug.lean:15`) → `zeroFreeAll_of_topG` → `hypV_of_cls` (`Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:12-17, 30`) → the `hV` of `TopG` → `topDesWin` `hV` (TS:52-53) → T12.
- **Role.** It supplies Σ' vvTerm = Σ_l log l·Σ_{e<t} len Ш_l(e) ≤ √b, the Ш summand of LinkN, and hence part of E2.

**`OneCharU`** (live, inside VWin).
- `vwin_of_hypotheses_H_E_alt` (`DTC/WindowBoundOfLiteratureLevel.lean:25-29`) passes `count_i_of_printed_bound_k_kato_automorphy …` to `of_four_alt` as `h1 : CountI` (`DTC/HVCore.lean:18-22`).
- CountI = `U3.countI (U3.corGK (propGK_of_numberU3U_of_oneCharU … (oneCharU_of_katoTwoW_rig_admI_automorphy hC … hKa … h3)))` (`DTC/LinkedUnlE.lean:49-54`).
- **Role.** It bounds the plus part of Ш by Eisenstein–cusp congruences on U(3). That is one summand of VWin → E2.

**`AutEnd3Alt`** (live, inside VWin).
- `GdEndAlt` contains `AutEnd3Alt` as a conjunct (`DTC/AutEnd3AltAlt.lean:20-26, 35-40`).
- `hE := ends0_alt hH` (`DTC/WindowBoundOfLiteratureLevel.lean:27`; `DTC/DnEndsTop.lean:15`).
- `hE.1` → `automorphyUnramified_of_litN_of_gdEnd hH.litN hE.1` = `h3` (`DTC/WindowBoundOfLiteratureLevel.lean:29`) → the last argument of `oneCharU_of_katoTwoW_rig_admI_automorphy` (`DTC/LinkedUnlE.lean:49, 54`) → CountI.
- `hE.2` → CountV (`DTC/WindowBoundOfLiteratureLevel.lean:29`; `DTC/LinkedUnlE.lean:55-61`).
- **Role.** "Every ordinary point of the residually reducible U(3) deformation ring is automorphic". It is used only to make OneCharU's congruence count cover the deformation points. Its only effect on the slope chain is through VWin → E2.

**`Row0b`** (live as a field; the bundle identity was not unfolded).
- `vwin_of_row h` (`DTC/VwinOfRow.lean:4-5`) → `gal := gal` in `LiteratureAutomorphyHypothesis` (`DTC/TopMainZj.lean:39, 47, 68-71`).
- One consumer on the VWin proof: `katoTwoW_of_printsH P = … rowOf' P.toClassicalTheorems.litN.aut.gal …` (`DTC/KatoTwoWOfPublishedH.lean:48-49`) → `hKa` of OneCharU (`DTC/WindowBoundOfLiteratureLevel.lean:29`).
- I did not unfold whether `P.toClassicalTheorems.litN` is the bundle that carries `h`. NODE-VWIN oddity 1 records that a closed `litN` also exists.
- **Role.** It supplies Galois representations for the automorphic side of the U(3) congruence count. That again feeds only E2.

### 2c. Why candidate (i) is not the R = T entry point

`T3` is derived from `sig_all` + `HkSS` (NODE-MIRABOLIC §2b.4). `sig_all` is supplied by `sig_all_of_sideB` (`IE/GoodPartEigensystemIsTripleEigensystem.lean:137-158`, read; wrapper `…Statement.lean:10-11`). Its hypotheses are:
- `SideB` (`Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/RingSpecNormalisedCharacterEq.lean:185-215`, read in part). This gives the good-part forms space as ≃ an explicit model `Fm S` (`eF`), with Hecke operators matched (`hkEq`), the G-action matched (`act`), and character data.
- `NoFormsOff`, `MeetsAll`, `CommAll`, `FullAll` (`Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NoFormsOff.lean:28-36`).

The proof shows that an eigenvector with no listed signature must vanish (`eq_zero_of_joint`), because the good part lies in the span of the explicit "triple" eigenvectors (`good_part_le_span_triple_eigenvectors`, :152). This is a **model identification plus linear algebra**, not a deformation-ring statement. A grep of these three files for `AutEnd3Alt|GdEndAlt|OneCharU|CongBound_at|LinkN` found nothing. *(Inferred)* Whatever R = T-like content T3 carries sits in the construction of the `SideB` model (`eF`, `hkEq`), which I did not unfold. It is not `AutEnd3Alt`.

## 3. Corrected dependency map of the slope chain (live path)

| term of the final inequality | where it sits (Lean) | live supplier(s) | Galois/congruence machinery? |
|---|---|---|---|
| height h(u) of the evaluation map | DivClausesR clause 2, `height_chain_atR` (CGT:205) | Fock/jet norms, κ, Rallis λ; NODE-HEIGHT/JETA/L6 | none |
| Rallis scalars λ_j | `eig6` (CGT:52), `lamLow` (W4F:62) | L6 product formula (NODE-L6) | none |
| covolume main term Σ lcv(M_j)/D | `L3main`, `l3` (IU:333-334); `covol` (W4F:62) | NODE-COVOL/VOLUME/HS (`FlatDegree`, Hilbert–Samuel) | none |
| det identity det ι = κ^D ∏ det θ_j | BoundsMu hypotheses; `detId` (IU:288-289) | `specDet_rect`, PrimRows3/MultEq (NODE-DETSIG, LIVEPATH) | none (MultEq is trace-formula; `multEq_of_sides`) |
| LG (Gram valuation) | SO:62-63; `gram_valuation_le_extended` (TPE:20-28, 271) | v(\|G\|·s) | none |
| index at Tw (2F + err) and E1 (incl. J0) | SO:65, 69; `hon` (IU:313, 332) | ON: test lattice + discriminant budget (INDEXBUDGET) + mirabolic chain + `IdxAt` (Hecke Euler-factor determinants, `T3`/`sig_all`, ThURel) (MIRABOLIC, TWSET); J0 from `LiftExponentAtTwisted` (TPE:32) | shares the twist pack (GoodTw) with KillAt; no congruence module, Selmer, Ш or U(3) |
| 2F | SO:73; cancels as `foTie` | NODE-JOIN/SLOPE | none |
| **E2 (dual index / congruence module at Tw)** | SO:67, 70; T1–T13 | `jw_le` + DIVinN ← LinkN (ConclF: `CongBound_at`/`CutCoreUnit.main`, `KillAt` ← GoodTw + residual irreducibility, Wach local lengths, l = 2, 3 bound) + HypV ← VWin (`OneCharU` ← `AutEnd3Alt`, `Row0b`, ThmBab, ThmBcFree, counts II/III/V) | **all of it** |
| E3 | SO:71; `places_ell_weighted_sum_le_one` (TPE:276) | elementary | none |
| passage constant Q (base → columns) | CGT:99, 214, 225-227 | contains boundBR(…, E2) | through E2 only |
| DIV error errB | CGT:89, 245 | Σ(E1 + E2) + … ≤ errB (`errB_of_units`, CONGMOD) | through E2 only |
| near-orthogonality / Theorem S | `LinkS`, `sO`, `sLp` (DW:21; `TPS/TopShapeAlt.lean:59-61`; `TPS/LinkROfIsLinked.lean:55, 74-75`) | double unfolding of Poincaré series (PAIRB/COUNTS/THMB) | none |
| non-vanishing / frame | `LinkIRR` (DW:16), `oneMap`, `BuRational` (TS:38-39, 54) | row count (RANK, JOIN) | none |

**Which earlier accounts this corrects.**
1. **The working picture in the brief** (heavy Galois machinery enters through the theta-image index) is wrong, as NODE-MIRABOLIC said. This node confirms it and shows the complement: the machinery enters only through E2.
2. **NODE-MIRABOLIC oddity 1.** It wrote "CONGMOD feeds only jw ≤ J·D + η (SO:69) and E2". The jw clause is at SO:67 (E1 is SO:69). The J·D part of the jw bound is charged to **E1**, from `LiftExponentAtTwisted`, not to the congruence chain. E2 additionally sits in the passage constant Q. MIRABOLIC's "(i) T3 smells like R = T" does not hold for `AutEnd3Alt`: T3's supplier is a model identification (§2c).
3. **NODE-CONGMOD.**
   - The live consumer is `divClausesR_of` (CGT:184-245) with `DivInputsR`, not `DivClauses` (DHB:779-813).
   - The live `InEta` producer is the TPS `inpAt_of_alt` (`TPS/InpAtOf.lean:17-56`, via `inEta3_num`), not `LL/InpAtOf.lean`.
   - DIVinN is produced in exactly one place, `topDesWin` (DW:29).
   - CONGMOD's mathematics (jw ≤ congruence module; η ≤ D0·(…)) stands.
4. **MAIN-ARGUMENT §8 / §5.2.** "Index and congruence terms" should be split:
   - indices and J0 → E1, which carries no Galois input;
   - congruence → E2, which carries all of it.
   - §8 should add that `AutEnd3Alt`/`OneCharU`/`Row0b` reach the inequality only as the Ш summand of E2. That summand is ≤ √b and would also be served by any bound ≤ b.
5. **NODE-KILLAT / NODE-LINKN.** These describe KillAt and residual irreducibility as load-bearing for the slope chain. That is true only for E2; neither touches E1, even though KillAt shares GoodTw with IdxAt.

## 4. Children

| # | name | file:line | statement | role | weight |
|---|---|---|---|---|---|
| 1 | `lift_index_bound_extended` / `jw_le` | TPE:30, 48 | jw(T_j) ≤ etaJW + D(JJW + v DG + v s) | dual index ⇒ congruence module | core; `jw_le` body unread (CONGMOD child 4) |
| 2 | `twisted_place_eta_sum_le_extended`, `inEta3_num`, `inpAt_of_alt` | TPE:63; SumLeEtaSumNum:78; `TPS/InpAtOf.lean:17` | InEta ⇒ E2 = bd + log dg + log s | glue | glue, read |
| 3 | `divinN_of_hypV`, `topDesWin` | DNV:117; DW:11 | LinkN + VWin(√b) + rank eq ⇒ DIVinN | joins the Galois side | glue, read |
| 4 | `NLinkClose.main_alt_alt` (ConclF) | IFT:30-110 | assembles StarE (CongBound_at), kill, ram, mid, two | LinkN's local table | core assembly, read 30-110 |
| 5 | `NLinkE.main_alt_alt` → `CutCoreUnit.main` | APE:30-57 | CongBound_at at l > lStar | congruence ⇒ Selmer | core (LINKN/BEYONDFL) |
| 6 | `exists_setup_large_alt` → `chosenTwist_annihilates_selmerGroups`, `JointSix.main` | `TPS/ExistsSetupLarge.lean:14-41` | KillAt from GoodTw + residual irreducibility | Selmer killing | core (KILLAT) |
| 7 | `vwin_of_hypotheses_H_E_alt`, `count_i_…`, `ends0_alt` | `DTC/WindowBoundOfLiteratureLevel.lean:25-29`; `DTC/LinkedUnlE.lean:49-54`; `DTC/DnEndsTop.lean:15` | VWin from OneCharU (∋ AutEnd3Alt via GdEndAlt), Row0b via KatoTwoW | Ш bound | core (VWIN/ONECHARU/RT3/MODU3) |
| 8 | `sig_all_of_sideB` | `IE/GoodPartEigensystemIsTripleEigensystem.lean:137` | model identification ⇒ all type-part eigensystems are known | T3 for IdxAt (E1) | core; `SideB` construction **definition to unfold** |

## 5. Oddities

1. **Footprint versus weight.** Four nodes' worth of deep Galois theory (CONGMOD, LINKN, KILLAT, VWIN/ONECHARU/RT3/MODU3/FINEND) bounds one error scalar, E2. Within E2 the Ш part is slack by a factor of about x^{2.5}√b. The non-Ш congruence terms (≈ f·m·b·L²) are what fill the allowance (CONGMOD §6.1). So on the route as built, `CongBound_at`/`KillAt`/local lengths are the quantitatively relevant part, and `AutEnd3Alt` is only a qualitative requirement.
2. **E2 is used twice:** in μ(RR^∨) and in the passage constant Q (3·de·Q ≤ 1). An overly large E2 would therefore also break the base→column passage, not only DIV.
3. **DIVinN is a premise of ON and FUN** (`TPS/IndefiniteRealisationChoice.lean:74, 77`), so the twisted-index record is formally conditional on the congruence bound. I saw no use of the premise in the visible producer inputs. A reviewer should confirm that `ev_prem` (`TPS/RowRRowsOfParts.lean:34, 36`) discharges a premise that the producer ignores. If the producer did use DIVinN, E1 would also depend on the Galois side.
4. **`Row0b`'s live use** goes through `P.toClassicalTheorems.litN.aut.gal`. Whether that `litN` is the bundle built from `h` was not unfolded (cf. VWIN oddity 1).

## 6. Coverage

Read:
- PROTOCOL; NODE-MIRABOLIC, CONGMOD, LINKN, KILLAT, VWIN, SLOPE, LIVEPATH (all); INDEXBUDGET, TWSET, LARGETW, BEYONDFL (§0–1); MAIN-ARGUMENT §5, §8; NODE-ROOT (grep).
- SO:1-130.
- IU:255-334.
- CGT:40-262.
- `LinkDIVL2R3Col.lean:1-40`.
- `RecBridge.lean:625-700`; `RecBridgeMkF.lean` (all); `RecBridgeSel.lean:1-100`.
- `TPS/DIVRecBridgeSel.lean:100-209`; `TPS/PtKOfReal.lean` (all); W4F (all); `TPS/InpAtOf.lean` (all).
- TPE:1-110, 174-330; `SumLeEtaSumNum.lean:55-90`; GTI:25-100; DNV:1-20, 112-132; DW (all).
- TS:1-57; `TPS/WireSel.lean:15-51`; `TPS/TopShapeAlt.lean` (all); `TPS/TopPlug.lean` (all); `ZeroFreeAllOfTopG.lean:1-38`.
- `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:30-64`; `TPS/LinkROfIsLinked.lean:50-88`; `TPS/RowRRowsOfParts.lean:18-65`.
- `TPS/IndefiniteRealisationChoice.lean:71-135`; `LocalQuadraticParts.lean:437-445`.
- `TPS/CFinal.lean` (all); `TPS/LinkNFam.lean:30-89`; `TPS/ImportsFurtherTailStatement.lean` (all); IFT:30-111.
- `TPS/ExistsSetupLarge.lean:14-41`; `TPS/ExistsSetupLargeStatement.lean:12-13`; `TPS/AdmissibleParameterEventuallyStatement.lean:8-13`; APE:25-58.
- `DTC/VwinOfRow.lean`; `DTC/WindowBoundOfLiteratureLevel.lean:18-35`; `DTC/HVCore.lean:10-25`; `DTC/LinkedUnlE.lean:40-63`; `DTC/AutEnd3AltAlt.lean:1-43`; `DTC/TopMainZj.lean:36-75`; `DTC/KatoTwoWOfPublishedH.lean` (grep, 38-49).
- `IE/GoodPartEigensystemIsTripleEigensystem.lean:125-175` and its Statement:1-14; `RingSpecNormalisedCharacterEq.lean:185-215`.

Greps run:
- `KillAt`; `CutCoreUnit.main`; `CutDetOrd.main`; `LinkV_at|LinkV`;
- `localBoundZeroAtLargePrimes_of_congruenceBound|exists_hub_data|exists_setup_large`; `exists_hubData_admJ_setup|eventually_congBound_of_facts`;
- `shape_closed_link_n_of_green`; `def NL`; `toRows_alt`; `\.aut\.gal`; `sig_all_of_sideB`; `good_part_eigensystem_is_triple_eigensystem`;
- `AutEnd3Alt|GdEndAlt|OneCharU|CongBound_at|LinkN` in the IdxAt/T3 files;
- `def LinkDIVt|DIVinN|LinkN|topDesWin`; `DIVinN` in the onto-chain files (no hits).

Not opened:
- the bodies of `jw_le`, `row_rRows_stage0_alt` (the ON/FUN producers) and `ev_prem`;
- the `SideB` construction;
- `rowOf'` and the identity of `P.toClassicalTheorems.litN`;
- `oneCharU_of_katoTwoW_rig_admI_automorphy`;
- `linkN_of_gd`, `LinkFam.main`.
