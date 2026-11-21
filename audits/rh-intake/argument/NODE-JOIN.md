# NODE-JOIN: stand-in row records, and integrality of the layer theta lifts at the gain primes

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the line. *(inferred)* = my reading. Nothing compiled.
Abbreviations:
- `SO` = `Formalism/DivisorInequality/StatementObj.lean`
- `QMS` = `Formalism/QuotientMetricDivisors/Statement.lean`
- `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`
- `LD` = `Formalism/LocalToGlobal/IndefiniteReal/LinksDefs.lean`
- `GCT` = `Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean`
- `FWT` = `Formalism/LocalToGlobal/IndefiniteReal/FWTie.lean`; `FWE` = `…/IndefiniteReal/FWExist.lean`
- `ONL` = `Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean`
- `PB` = `Formalism/LocalToGlobal/ProjectiveLattices/PlaceBelow.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `SF` = `Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SameForm.lean`
- `NRF` = `…/AutomorphicMembership/NontrivialReferenceForms.lean`

## 0. Verdicts

| Question | Verdict |
|---|---|
| Q1 (i): is the live row record nondegenerate (EE, RR, B_u ≠ 0)? | **closed, conditional on the frame inputs.** The same `D` that carries `Bk`, `Dall` and `Drows` must satisfy LinkS, ChosenProviso and LinkIRR. Those force `Dall > 0` and `Drows > 0`, and the frame's rank bound forces some `Bk u ≠ 0`. `StandIn` (Dall = Drows = 0, Bu = 0) is incompatible with them. |
| Q1 (ii): where is `StandIn` consumed? | **Sanity inhabitant only.** It is used only inside existence theorems (`NRF.exists_all`, `exists_ambIsTrue`) and inside the structure `ZDef`/`CoreB`. A grep finds no consumer of any of these on the route traced. It cannot replace the live record. |
| Q1 (iii): which `MIstar2` producer does the root use? | **partly traced (open).** Live chain: `RowsAt4.miStar` ← `row_rRows_of_parts_alt` ← `RowMultiplicityCondition` ← `miStarRow_alt_alt` ← `miStar_row_alt_alt` ← `main_theorem_from_published_results_alt⁵` ← `alt⁴` ← `miAt_of_truePack_alt_alt`. I did not reach `miStar2_at_realisation_alt`/`mainX_of_lawsX`. |
| Q2 (a, b): what `idx` is, and the untwisted places | **closed, but "idx = 0 off Tw" holds by definition, not by a theorem.** `idx` is a signed local length index of θ_j(T_j) against M_j. M_j is the **geometric** lattice. Its supplier is not an integral-theta theorem: Tw is *defined* to contain every place where the index (or jw, or F) is nonzero. The content moves to "that set is {resChar ≤ X″} ∪ {d, g₀, g₁}". |
| Q2 (c): twisted places, including the gain primes | **mechanism located; one structural point confirmed; the decisive depth theorem not opened.** The index is bounded by a Taylor/derivative-content exponent ("depth") E of test vectors in integral charts on the layer Shimura variety. That exponent is ≤ F + err (`LeafDepthGood`), proved from formal-group chart theorems. F = (k−1)Σw/(p²−1) involves only the **layer weights w**, never a. It enters exactly twice with opposite signs (source sg ∋ +F; target BoundsMu ∋ +2F; DIV −Fo, Fo = 2FoOfR), so it cancels. The a-sized factorial lives only in the column steps. No defect seen. |

## 1. Q1 — stand-in records

### 1a. What `StandIn` is (SF:40-56; read)
```lean
structure StandIn {C : Cols B} (W : RowsRest B C) : Prop where
  drows : W.Drows = 0
  d0 : W.D0 = 0
  dall : W.Dall = 0 ...
  bu : ∀ u φ F, W.Bu u φ F = 0 ...
```
`buDef_iff` (NRF:428-434) uses `Rw.std.bu` to reduce BuDef to `perCol = 0`. This is degenerate, as the parent said.

### 1b. Consumers (grep `StandIn\b|exists_all\b|RowsDef\b|ZDef\b|CoreB`)
- `NRF.exists_all` (NRF:436-439) is a bare `∃ B X I l hX Z e A, … ∧ StandIn Z.W ∧ …`. A grep for `exists_all` finds **no consumer** of this theorem; the other theorems named `exists_all` are unrelated.
- `AmbIsTrueOfAmbTrue.lean`:
  - `rowsDef_ex` (:43) calls `exists_rows_prescribedUnitaryForms_standIns` (:70);
  - `exists_divStage_standIn` builds a witness for `exists_ambIsTrue` (:311-325). This existential concerns `AmbIsTrue` (the top ambient forms equal the true lattice `MtHL`). That content does not depend on B_u.
  - `exists_ambIsTrue` has **no consumer**.
- `ExistsIsBIffCoreB.lean:32-37`: `ZDef.std : StandIn Z.W` is a field of `CoreB` (:56-61). `CoreB.isB` and `IsB` have no consumer outside the file.
  - `GlobalTheory.Core.DefKer.exists_kerTie` (`DecoratedLatticeProofs/ExistsKerTie.lean:83`) takes a `CoreB` argument, but nothing outside its own file calls it.
  - The `exists_kerTie` that is on the live path is the different lemma `WPt.exists_kerTie` (`TPS/ExistsRecPinE.lean:26`).
- **Classification: sanity inhabitant.** It discharges no existential on the route from the root.

### 1c. Why the live record cannot be a stand-in (same record)
- D7 ties: `s_HH : finrank ℂ s.HH = what₂.Dall` (`RhoDetPrimeEqMuTildeMulChiPow.lean:231`). `jEE_basis` makes `div.RR.b` a ℂ-basis of `what₂.EE` (:185-187). Rows: `D_eq : Drows = (1 − delp)·Dall` (`DataRows.lean:71`).
- `LinkS_at` (`GlobalTheoremInputs.lean:145-149`) reads `(∀ u, C0⁻¹ ≤ duS u·Γ²/Dstar ≤ C0) → … ∧ (∀ u, hsDiagFull D u ≤ e0·duS u) ∧ Dall ≤ (1+η1)·Dstar`, with √e0 ≤ e^{−x^{ε/8}}.
- *(inferred)* ChosenProviso discharges the antecedent (NODE-RANK). It forces Dstar > 0 and duS u > 0.
  - If Dall = 0, then P_u : C_u → HH = 0. Then hsDiag = ‖0 − 1‖² = duS u, which is > e0·duS u.
  - So Dall > 0, and with LinkIRR, Drows > 0.
- The frame (NODE-RANK, `TD16:1089-1094`) puts `D.div.Bk u` as the RR-rows of the **same** `D`. Its rank bound excludes `Bk ≡ 0`.
- `BesselId` (Bu = a·besS, a ≠ 0) is on `D.what₂.Bu` of that `D`. So it is not vacuous.
- BoundsMu also needs `0 < D` (SO:20). In IndefData, D = `dQ μ0` (`PartsOrth.lean:174`), with `IndefRows.pos : 0 < Df.dQ Bs.μ0` (IS:104, 347) and `RankRows S : 0 < S.D ∧ ∀ j, S.dW j = S.D` (ONL:236).

### 1d. The root's MIstar2 producer (Q1 iii)
- `RowsAt4.miStar : (Q.Rl.toCx3 Q.F).MIstar2 …` (`IndefiniteRealisationChoice.lean:127`) is a field of the same record as `covol`/`onto`/`w1`.
- It is filled by `row_rRows_of_parts_alt … miStar := hM …` (`TPS/RowRRowsOfParts.lean:60`). Here `hM` comes from `RowMultiplicityCondition` (`TPS/RowGood.lean:33`), the premise `hMi` of `row_rRows_stage0_alt` (`TPS/TupAllUsedAtPart.lean:46-48`).
- It is produced by `miStarRow_alt_alt` (`TPS/MainTheoremPublishedInputsThird.lean:22`), which goes through `miStar_row_alt_alt` (`TPS/MainTheoremPublishedResultsFinal.lean:24-37`, via TruePackAlt/`puNZ_of_truePack`) to `…from_published_results_alt⁵` (`TPS/MainTheoremFromPublishedResultsAltAltAltAltAlt.lean:19,33`) and then to `miAt_of_truePack_alt_alt`.
- I stopped there (budget). Name similarity is not evidence, and I did not confirm that this ends in `miStar2_at_realisation_alt`.

## 2. Q2 — integrality of the layer theta lifts

### 2a. Exact finite-place hypotheses of `BoundsMu` (SO:17-79)
- `idx y A B = lidx y.asIdeal A B` (QMS:86-87). `lidx p A B = len(A_p/(A∩B)_p) − len(B_p/(A∩B)_p)` (`HermitianLattices/StatementLat.lean:92-96`). This is a **signed** generalised index [A : B] at y.
- `jw H y A = lidx(A, dual_H A)` (StatementLat:98) is the dual index.
- The hypotheses are:
  - y ∉ Sy: `lw y·(vw(Gm) + Σ_j(idx_y(M_j, θ_jT_j) + idx_{ȳ}(…) + jw(T_j))) = 0` (SO:51-52);
  - y ∈ Sy∖Tw: `idx + idx_conj + jw = 0` (SO:53-54) and `Fy = 0` (SO:57);
  - y ∈ Tw: `Σ_j (idx_y + idx_{ȳ}) ≤ (Σ_j (2Fy + erry) + 2/ℓ_y²)·D` (SO:61-63) and `jw ≤ Jy·D + ηy` (SO:65).
- Here `matLat (θ j (μ y)) (Tl j (μ y))` is the image of T_j **under the matrix θ_j itself**. No rescaling enters.
- So θ_j is used in its *coordinate normalisation*:
  - `liftMat` = the K-matrix of the complex theta map θ′_j = `R.thG i t` (LD:698), from the T_j-coordinate basis to the basis bW of the layer forms (`PartsOrth.lean:152-162`);
  - with `l1c` it is a λ_j-similitude at the archimedean places (IS:304-311).
- Because idx is signed and only bounded **above** on Tw, denominators in θ_j (θT ⊋ M) are not penalised by ON. They are favourable for the covolume.
- *(inferred)* λ_j never appears at a finite place. BoundsMu is the product formula, with det θ_j converted into lcv(M_j) + idx + jw.

### 2b. What M_j is: the geometric lattice
- `M b i := (R.FW i).Mcoord P ψ⁻¹ e (R.bL F b i)` (LD:701).
- `Mcoord` = coordinates of `Mj = span(MK) ∩ typeP ∩ good` (GCT:116-121, 133-135).
- `MK = {f ∈ WK | ∀ lp (y : Pt lp), nrm lp y f ≤ 1}` (GCT:51-53).
- `FWTie` pins this:
  - `e i : T.cuspA (i+1) (wtA κ_i) n ≃ (R.FW i).WK`;
  - `pt : (R.FW i).Pt la ≃ T.PtM (i+1) la`;
  - `nrm_eq` (FWT:21-33).
- `FWTie.mem_MK` (FWE:654-666): `e f ∈ MK ↔ ∀ la (y : T.PtM (i+1) la), 0 ≤ y.1 f`.
- **So M_j is the lattice of cusp forms integral at every valuation point of the layer model.** This is the same `latW`-type lattice as in NODE-COVOL. It is **not** the theta-image lattice.

### 2c. Supplier of `Untwisted` and of `on`/ON

**Untwisted.**
- `CutTuples2` (`CutTuples2.lean:203-204`): `X.H0 → (∀ w, X.W1 … w → w ∈ X.Tw) → Untwisted`.
- `W1 w := ∃ j, Iw j μ0 w ≠ 0 ∨ … ∨ jw … ≠ 0 ∨ … ∨ N.F0 w j ≠ 0` (:188-192). It is proved by `cutTuples2` (`CutPassage.lean:63-77`).
- On the live record, `MuDef … : ∀ w, w ∈ X.Tw ↔ X.W1 cr N w` (CutTuples2:196-198) holds. It is used as `hw : SingleIndexPlacesAreTwisted b.pt := … (b.muDef 0 0).2.2.2 w` (`TPS/RowEPartTies.lean:29`).
- **So "idx = 0 at untwisted places" is the definition of Tw.** What it must deliver is the coincidence Tw = {resChar ≤ X″} ∪ {d, g₀, g₁} that NODE-CONGMOD saw (`ExtraFinal.lean:25`). That coincidence is equivalent to a real theorem: idx(M_j, θ_jT_j) = 0 and jw(T_j) = 0 at every good p > X″.
- I did not find where this coincidence is proved for the live record (see Children #1).

**ON (y ∈ Tw).**
- The supplier is `SurjectiveOntoX` (`TPS/ExportSt.lean:47`): `DIVinN → … EventuallyAtPoints … More p → ∀ C ≥ C0, (p.S false).ON (p.N C CH)`.
- It is proved by `ontoX_of_hypotheses_alt_alt` (`TPS/OntoXOfPrints.lean:28-46`) from Export/Twist/Share/Bad/Exp statements. It reaches `RowsAt4.onto` through `row_rRows_of_parts_alt` (`hON`).
- The proof pattern is `on_of_leaves` (ONL:873; instance `onto_of_leaves`, `IndefiniteReal/LeafObjects/MirabolicInclusion.lean:214-218`), applied to an `OnObj` whose fields are:
  - `Ms j := span(MK)` (MirabolicInclusion:96), `Mt v j := Tl j (μ v)`, `θ' v j := φ_j ∘ θ_j`;
  - `TieCoord`: φ_j(M_j) = Zg_j ∩ Ms_j and φ(θT) = ImageLattice (ONL:229-233). Zg is a ψ-eigenspace of the mirabolic group `Mir R`, which makes this a Kirillov/Whittaker-type projection *(inferred)*.
- The chain of leaves:
  - `LatticeIndexBoundAtPairs`: `lix(cut W Ms, cut W Th1) ≤ E·dim W + r` (ONL:262-271). Explicit test forms Th1 span Ms up to p^E;
  - `LeafLemmaS`: `Th ≤ sc σ ThK`;
  - `LeafData`/`LeafRankJ`: |U|·cut ⊆ Th0 ⊆ ThJ;
  - `LeafTW1`/`TW2`: X₃ ⊆ Im = e(θ′ Mt), with `lix(cut Zg Ms, X₃) ≤ lix(…, eJ) + ramw·ε0` (ONL:284-294).
- Net effect: idx(M_j, θ_jT_j)/ramw ≲ e0 = (E − v(σ))/ramw, plus |U| and ε0 terms.
- **`LeafDepthGood`** (ONL:298-306) requires, for p ≤ Y, `e0 w j ≤ N.F0 w j + aE j p + 1`, and for p > Y, `e0 = 0`. Here:
  - `aE j l = A1/l + Akw·th l + T·ad l + [l > X2]·Akw/l²` (ONL:156-158);
  - A1 = C(log k·m·wt + f·k·Se), Akw = C·k·wt, wt = 2fb (`RunTie.wt_eq`);
  - Σ th(p) log p ≤ C/k, and ad = 0 (`RunTie.ad_eq`).
- E and σ are pinned by `IsRec.depth`/`RunTie` (`Jets/CmQuadraticFormEqAlternatingForm.lean:40-60`): `E_eq : O.E v j = EAt (depOf …) v (ι j)` and `σ_eq : O.σ v j = sigAt …`.
  - `EAt = expE Q (nuStarAt)` (PB:190-193). `nuStarAt = nuN(DF, nuW/ram, p)` (PB:184-186, 103-107), and `nuW = max 0 (sup_{CM-type points y} inf_{charts} nuLocC)` (PB:57-70).
  - `nuLocC` is the infimum over integral power series f in an integral chart, and over weight-a polynomial operators P, of `nval(constantCoeff(DpolyN … f))`. DpolyN composes `pderiv` along the formal group law (PB:20-36, 50-55).
  - **So E is the p-adic content of Taylor-derivative functionals at integral points, with the factorials included.**
  - `sigOf = π̄^Dp π^Dm · q^{f r n′} · Z1` (PB:119-123). So v_w(σ) = 0 at a good inert/served p.
- `LeafDepthGood` is proved by `leafDepth_all_record` (`DivisorProofs/LeafDepthAllRecord.lean:17-27`) ← `leafDepth_all_run` from three formal-group chart theorems:
  - `colength_bound_split_place_chart : ∀ p, AvFSt p`;
  - `hodgeTate_inclusion_chart : HTFSt p`;
  - `unramified_companion_chart_characters : UpFSt p`.

  Their statements (`ReciprocityTheory/…/PlaceDivisors/StChartF.lean:133-175`) are:
  - HTFSt: c·f ∈ span(dlog of characters) whenever v(c)^{p−1} ≤ v(p). This is a Fontaine-type Hodge–Tate cokernel bound by p^{1/(p−1)};
  - AvFSt: ∏ x_j ≥ |p|^{n·rm(1/(p−1)+vd/2)} at split places.
  - Not unfolded further.

### 2d. Reconciling with the column gain (the main term)
- **Gain** (`gainP`, `IsResidueClassZero.lean:224-229`, `askG` :238): `Σ_{e odd} max(0, a_s/p^e − fill)`. Only odd powers of p appear, and a appears.
- **F** (`Numbers.lean:170-173`): `FInert j p = Σ_z (k−1)·w_{jz}/(p²−1)` at inert p ≤ X″. It depends on the layer cap weights w, **not on a**.
- `Fo = Σ_j Σ_{p∈suppP} log p·FjP j p` (Numbers.lean:205).
- The same F appears in:
  - the source enlargement sg = Σ_j(gain + F − E) (NODE-FAMILY);
  - the target cost in BoundsMu, `2 * (∑ j, ∑ y ∈ Tw, lw y * Fy y j)` (SO:75);
  - DIV, as −L.Fo with `foTie : 2·FoOfR = L.Fo` (NODE-DIV).
- **So F appears once on each side and cancels. The a-factorial is counted only in the column steps (gain).** The layer lattices M_j are the geometric (integral-at-points) lattices, and the layer depth is bounded by derivative content of the layer weight alone (≈ F + err).
- *(inferred)* This matches the brief's reading in a refined form:
  - the column step K_j carries derivatives in the source weight a (Σ_e a/p^e);
  - the layer lift only has to absorb the content of derivatives in the layer weights;
  - the even-power part (k−1)w/(p²−1) is booked as F. It is the shape v_{p²}(·!) expected from a height-2 (inert, supersingular) formal group;
  - the remainder goes into err ≈ A1/p ≈ C·m·f·b·log k/p.
- Size check, per lift and per dimension (NODE-ARCH sizes):
  - Σ_p lw·err ≈ A1·log Y ≈ x^{2.5+O(ε)}·b, against a gain of Σ_p |TT|·a·log p/p ≈ x^{3+O(ε)}·b;
  - the error is smaller by about x^{−1/2} ≈ 1/m. This is consistent with DIV's budget C·m(B0+Nc)x^{Cε} against MAIN ≈ m|TT|a.
- **Split primes.** F_jP = FOrb/ordP (Numbers.lean:174) when p is not inert. The split-place depth bound is AvFSt (rate 1/(p−1)). *(inferred)* The same derivative content there is the full 1/(p−1) rate, and it is not a gain. I did not unfold this.

## 3. Children (ranked)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | supplier of `MuDef`/`SingleIndexPlacesAreTwisted` and of `hmt` for the live record | CutTuples2:196; `TPS/RowEPartTies.lean:29`; `InertJacobiLevels/ExtraFinal.lean:25` | W1 (idx ≠ 0 or jw ≠ 0 or F ≠ 0) = Tw = {resChar ≤ X″} ∪ {d, g₀, g₁}. Equivalently, an **integral theta-unimodularity theorem at every good p > X″** (θ_j T_j = M_j up to signed index 0, T_j self-dual) | **core, untraced** |
| 2 | `leafDepth_all_run` with `AvFSt`/`HTFSt`/`UpFSt` | `LeafDepthAllRecord.lean:19`; `StChartF.lean:133-175` | derivative content E ≤ F + aE + 1 at inert p ≤ Y, and 0 above Y | **core** (formal-group / Hodge–Tate). Statements read, proofs not |
| 3 | `hasIndexBound_of_runs`, `runsHold_of_ties` | `DivisorProofs/HasIndexBoundOfRuns.lean:129`; `RunsHoldOfTies.lean:20` | test forms Th1 span the geometric Ms up to p^E | core (q-expansion / Taylor-jet principle); not opened |
| 4 | `ontoX_of_twist_shares_exp_alt` and the Twist/Exp statements | `TPS/OntoXOfTwistSharesExp.lean:21` | assembles ON from the leaves | glue plus core (LeafTW1, Jp) |
| 5 | `miAt_of_truePack_alt_alt` → … → (?) `miStar2_at_realisation_alt` | `TPS/MainTheoremFromPublishedResultsAltAltAltAltAlt.lean:33` | the root's MIstar2 | core, trace incomplete |
| 6 | ChosenProviso, LinkS, LinkIRR for the same D | `GlobalTheoremInputs.lean:145-157` | exclude a stand-in record | already ranked in NODE-RANK |

## 4. Oddities
1. **"Untwisted ⇒ idx = 0" holds by definition.** Tw is defined as the set of places where something is nonzero (MuDef). All of the content sits in the size of that set (child 1). The parent's "forced to 0" reading is correct only in that sense.
2. **The index is signed and bounded only above on Tw.** If θ_j had p-adic denominators (θT ⊋ M), ON would still hold. Its effect on μ(RR^∨) is favourable, so it is not a soundness risk for this inequality.
3. `recF_more`/`recF` (`ExtraFinal.lean:15-30`) takes `h0 : ∀ u, finrank Mu0 = 0` and `hA : Aj = 0`. These are degenerate stand-ins of another kind. I did not check whether they are on the live path.
4. Counterexample files `ExistsCharNotOnto.lean:49-56` and `NotOntoOfCharAlone.lean:57` show that `Char` alone does not imply ON. So ON genuinely needs the leaves. This is a healthy sign.
5. λ_j (archimedean, hook/Γ-sized; NODE-L6) has **no** finite-place counterpart in the Lean. The finite-place quantity is the index of the coordinate matrix θ_j against the geometric M_j, and it is bounded by derivative content of the layer weights.

## 5. Coverage
Read:
- PROTOCOL and the nodes SEESAW and ARCH in full; RANK, FAMILY, COVOL and DIV in full; CONGMOD 1-140; L6 1-60; greps of the others;
- SO:1-90; QMS:20-100; StatementLat:70-105; IS:225-474;
- CxCore.lean (all); LinksLemmas.lean:330-440; IndefiniteRealisationChoice.lean:100-200; FunTop.lean:1-90;
- `TPS/SiegelEisensteinSecondTermHypotheses.lean` (all); `TPS/HypothesesNonemptyOfUnramifiedExponents.lean:41-70`; `TPS/SurjectiveAndLowWeight….lean`;
- `TPS/ExportSt.lean` (all); `TPS/OntoXOfPrints.lean` (all); `TPS/GeoStOfPageSt.lean` (all);
- `SingleIndexPlacesAreTwisted.lean:1-140`; `RealisedChainTorusEq.lean:1-100`;
- ONL:30-330; MirabolicInclusion.lean (all); PartsOrth.lean:150-215; LD:516-710; GCT:1-160; FWT (all); FWE:620-700;
- `CmQuadraticFormEqAlternatingForm.lean:1-60`; PB:1-215; DepRun.lean:1-140; LeafDepthAllRecord.lean:17-27; ThBounds.lean;
- ColengthBoundSplitPlaceChart.lean:1-40; StChartF.lean:90-190; Numbers.lean:160-210; IsResidueClassZero.lean:215-240;
- CutTuples2.lean:180-215; CutPassage.lean:55-90; ExtraFinal.lean:15-40;
- SF:30-80; NRF:400-445; AmbIsTrueOfAmbTrue.lean:25-90, 300-340; ExistsIsBIffCoreB.lean:20-115;
- RecAtOfTwoPasses.lean (all); RowRRowsOfParts.lean (all); TupAllUsedAtPart.lean:20-60;
- MainTheoremPublished{InputsThird,ResultsFinal,InputsVariant}.lean (parts); MainTheoremFromPublishedResultsAltAltAltAltAlt.lean (greps);
- RhoDetPrime…:184-190, 231, 354-368; GlobalTheoremInputs.lean:145-157; DataRows.lean:66-83.

Not opened:
- `on_of_leaves` body; `leafDepth_all_run`; the chart-theorem proofs; `hasIndexBound_of_runs` body;
- `OnObjLevelCompatibility`; the producer of `MuDef` on the live point; `miAt_of_truePack_alt_alt` and below;
- `V4.ExTrue`/`hlg` (the live RowsRest W′).
