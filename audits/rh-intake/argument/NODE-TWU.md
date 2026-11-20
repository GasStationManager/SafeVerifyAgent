# NODE-TWU: where `SelectionServed.twU` is built, and what the inert divisibility proves

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- `IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `MV/` = `Formalism/SharpRestriction/GrowthBounds/MultisetValuation/`
- `SP/` = `Development/AbelianVarietyTheory/Proofs/SatakeParameters/`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`
- `GG/` = `Development/AbelianVarietyTheory/Definitions/GaloisGeometry/`

## 0. Verdict (short)

**(i), a real divisibility theorem. It is not built in by rescaling generators.** twU is constructed. Its chain divisibility is proved by
`FormalGroupSystem.Pf.stmt_proved` (`MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:107`). That theorem says: if the pending
theta datum Y5 is `admitted` (13 clauses, among them that the family's own chain maps are theta-kernel integrals), then
chainK^m ∘ (Hecke operator)^m gains γ_p·Σ(weight gaps) minus truncations.
- The explicit factors p^{⌈Sv⌉} in the NP generators (`IRZ:470`) **cannot** hide a cost. NP is a *span*, and extra generators only make it bigger.
- The colength of NP is capped from above by the VV′ = VV generators alone, which carry no explicit factor. These are yProd(VV)(M) = (T_r-Hecke)^m(M).
- The proved colength bound `admG1` clause 2 (`SmallOrderPrimes.lean:226-227`) says length(Mram/NP) ≤ vUnit·d·(τ+io), with d = rank = duS.
- So, I infer, the bookkeeping is honest: the slope gains Σgain from the 𝔭^{−sg} rescaling and pays d·(τ+io) in colength. Ga is *defined* net of τ (Ga = Σ sz(Σgain − τ)).

The divisibility is therefore a genuine statement about the chain on (essentially) all of Mram: chainK^m(Mram) ⊆ ϖ^{Σgain − τ}.
Its arithmetic burden sits in three inputs:
- (1) `admitted` for the constructed Y5 (`pendG`), supplied by `AdmAtEnt2` ← `CM2` ← `GlobalArtinReciprocity`;
- (2) the existence of local chain models tying the family's global chain to Y5 (`ModelsOK`, `modelsAt_bpt`);
- (3) the colength/Hecke-image bound (`OrbitLatticeBounds`/`LPprime`).
I did not open the proofs of (1)–(3).

## 1. Statement (as mathematics)

**Local setting** (`IRZ:441-480`, `FGS:264-365`, `DataG.lean:120-200`). Fix an inert place w over p and a word u.
- G = `D.gat u w hg` is a DVR O ⊂ K_f with:
  - a set of lattice tuples on a product of local buildings (`P.Tup`);
  - a finite set of components with arithmetic groups Γ.
- M = `G.M` is the O-module of Γ-equivariant functions Tup → Xsp with values in the local lattices HtupW (`DataG:138-140, 189-190`).
  This is a space of p-adic *algebraic modular forms* on a definite group at w. d = rank M; `gat_d` identifies d with duS(u)
  (`PlaneCountTheoremWithConstants.lean:755`).
- `G.yv v F (L) = p^{ArV v} · Σ_{L'' at edge-distance r from L_v} F(L with L_v replaced by L'')` (`DataG:148-151, 196`). This is the
  normalised Hecke operator T_r at the vertex v.

**Chain.** `LatInst` gives local levels `Lv`, i.e. lattices Int_j ⊂ Fm_j for j = 0..m, and a chain `Ch` of K_f-linear maps
Kz_j : Fm_j → Fm_{j+1}, with chainK_m = Kz_{m−1}∘…∘Kz_0.
- vKge(F, g) means chainK_m(F) ∈ ϖ^{⌈g·v(p)⌉}·Int_m (`IRZ:441-444, 461-463`).
- `reW Y LC` replaces the levels/chain by an existential family LC indexed by twisted tuples μ; at μ = muAt(w) it is the family's own
  (`GG/ModelsOK.lean:12-22`; `WJS:107-118`).

**NP** (`IRZ:470-476`). With VV = VV(p) the "served" orbit representatives:
NP = span_O{ ∏_{t0∈VV′}(yv_{t0})^m · (p^{Σ_{t0∈VV∖VV′}⌈Sv(t0)⌉} F) : VV′ ⊆ VV, F ∈ M } ∩ p^{⌈τ⌉}M ∩ Vram.

**UAt** (`WJS:161-170`). For VV′ ⊆ VVs ⊆ reps and F ∈ M:
v_chain(yProd(VV′)F) ≥ Σ_j [Σ_{VV′} max(gU − Pr, g0⁺) + Σ_{rest} g0⁺] + low.

**gainP** (`IRZ:355-359`) is the same sum with VV′ = VV. Here:
- gU = γ_p·Σ_{tops} a_s − Σ_{odd e} min(a_s/p^e, cap) − dl, with γ_p = p/(p²−1) (`IRZ:89, 254-260`);
- g0 = Σ_{odd e} max(0, a_s/p^e − cap) − dl (`IRZ:247-252`);
- Sv = ⌈Σ_j max(0, gU − Pr − g0⁺)⌉ (`IRZ:336-337`).

So max(gU − Pr, g0⁺) = g0⁺ + (excess). That excess is supplied by the explicit p^{Sv} for t0 ∉ VV′ and by (T_r)^m for t0 ∈ VV′.

**CmpV** (`WJS:156-159`). A chain-valuation bound at (u, w, μ) on c.cmp(x) implies the column bound ColGe(x, s).

**SysTw** (`GG/ModelsOK.lean:28-41`). There is a formal-group system `Sys.mk(G, Fl, Lv, Ch, …)` and a pending theta datum Y5 with:
- `FormalGroupSystem.admitted D _ Y5`;
- functions Fn with LowAt(j, v, Fn) at the vertices outside the reps;
- lowS ≤ ΣFn − Σ dG_j.

**twU = RowTwU** (`GG/ModelsOK.lean:43-46`, verbatim the field at `TPS/GServT.lean:13-16`). Eventually in x, there is an LC
with CmpV ∧ SysTw.

**Conclusion1** (`WJS:97-101`): x ∈ NP ⇒ ColGe(x, totS), with totS = Σ_j(gainS + F − E) + vDG. **adm2** = period valuations ≥ ⌊e·sg⌋ (parent).

## 2. Argument / construction trace (live path)

1. `allRows_of_open0_alt` sets `hServ := LinkedAt.of_row (hServ_of_linkR hA …)` (`TPS/LinkROfIsLinked.lean:76`). The chain from there:
   - → `row_hServ_of_link_alt` (`TPS/RowHServOfLink.lean:17-23`)
   - → `row_hServ_of_kerServ_alt` (`TPS/RowHServOfKerServ.lean:13-22`), which unpacks a `ServH` row into `SelectionServed`
   - ← `servH_row_linkR_alt` (`TPS/ServHRowLinkR.lean:14-19`)
   - ← `servH_row_of_artin` (`SP/BundleBothPartsOfStandardKernelOfGlobalArtinReci.lean`)
2. `ServH ker := (Closed 𝒜 RowTwU) ∧ AtAll Pdv.At` (`GG/HasPartAnd.lean:45-46`). So **twU = RowTwU**.
3. `servH_row_of_artin` makes the following derivations:
   - GlobalArtinReciprocity ⇒ `CM2` (`cmGoodModel_of_globalArtinReciprocity`);
   - CM2 ⇒ six hypotheses, among them `AdmAtEnt2` (`inert_theta_admissibility_of_complex_multiplication` = `admissible_entries_small_chain`,
     `Formalism/LocalToGlobal/InertKernelTheory/InertCoprimeLemmas/AdmissibleEntriesOfKernelLaw.lean:106`, from
     `first_kernel_law_global_small`) and `CurveEx`;
   - from these, `servH_row` (`SP/BundleBothPartsOfStandardKernelAndSixHypotheses.lean:15-25`) gives `rowTwU` from
     `ModelsAt`, which comes from `tuplesHaveLocalModels_at_constructedPoint_over_trueColumns` = `modelsAt_bpt`
     (`SP/TuplesHaveLocalModelsAtConstructedPointOverTrueC.lean:10-19`, via `tuplesHaveLocalModels_of_standardColumnObjects`).
4. `rowTwU` (`SP/RowTwUHolds.lean:15-27`) → `rowTwU_of_models` (`SP/UnitaryWeightModels.lean:14-31`). It uses:
   - `ModelsOK`: ∃ LC with CmpLite ∧ SiteAdm (`GG/ModelsOK.lean:48-74`; `GG/IsPlaceCofactorValuationLowerBound.lean:10-14`).
     SiteAdm is ∃ Y5 admitted, with dG_0 = 0 and dG_j ≤ v_p(DGam);
   - **CmpV** = `cmpV_of_cmpLite`. CmpLite is a compatible system of semilinear maps cmp_j from the family's twisted lattices into
     the local Fm_j. These maps intertwine the global chain `D.chTw.K` with Ch.Kz, agree with c.cmp at level 0, and transfer
     local divisibility at level m to the global VGe;
   - **SysTw** = `local_systems_lower_bounds_second_real_place`, from `OrbitPlaces.Shape` (with `entStd`, `split_bound_eleven_one`) and SiteAdm.
5. Consumption: twU ⇒ `sumOverPrimesService_of_servT` (`TPS/GServT.lean:20-22`) ⇒ `unit_bound_of_sum_over_primes`
   (`JointsTw.lean:243-270`):
   - it applies `hS.1 _ _ Y5 hA` with hS = `stmt_proved`, i.e. admitted ⇒ `Conclusion₂` (`FGS:775-777`);
   - it extracts VolumeRatio₂, adm11 and **LowTermBound** (`FGS:708-716`);
   - `UAt_of` (`JointsTw.lean:23-~215`) instantiates LowTermBound with Gn = gU and PRn = Pr, using
     `SmallResidueCharComparison` gU ≤ gB, g0 ≤ gA, Pr_FG ≤ Pr. It notes yProd(VV′)F ∈ Iprod(S, BB) and sums.
6. `stmt_proved` (`MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:79-111`). From `admitted`:
   - FormB, Rests (Ent ← `second_lemma_place_bound`/`hecke_place_bound` ← `RestGc p`, a Dwork-exponential/Lubin–Tate
     factorisation with vp^{p²−1} = p, `MV/DworkExponentialRestrictions.lean:19-27`; `MV/FirstTheoremPlaceBound.lean:20-30`);
   - ⇒ MassRatio₂ (Kz_j G ≥ gB − alEven + Σ′gA − dG for **all** G ∈ Int_j, `MV/RamifiedLatticeOfChainEstimates.lean:122-138`);
   - ⇒ PointsLemma (Hecke-twisted Tt(Kz G) ≥ gB + …);
   - ⇒ KernelCommutationUpToUnits / Conclusion4: Zop(chainK F) = p^{PrZ}·chainK(yv F), with Zop a polynomial in level-(j+1) Hecke operators (`FGS:671-695`);
   - ⇒ LowTermBound by `lift_bound_of_integrality`.

   The mechanism is: *the chain intertwines T_r with a Hecke polynomial at the next level, and Hecke operators applied to
   theta-kernel coefficients gain γ_p·Σ al.* `admitted` includes `ArchimedeanSignatureMatching` = ExpansionEquality/Decomposition
   (`FGS:566-588`): the family's Kz_j **equals** the sum over lattice classes of theta-kernel integrals ker(…). This is what ties the real chain to theta series.

**(c) Sizes.**
- NP ⊇ yProd(VV)(M) ∩ p^τM ∩ Vram. The colength theorem (admG1 clause 2, proved via `gluing_statement_holds` from
  `OrbitLatticeBounds`/`LPprime(…⌈tv⌉, Dp, kapv…)` and `LatticeSandwich`, `CornerGLContinuity.lean:180-196,226-233`;
  `AdmissibleFamilyNoKernel.lean:189-195`) gives lenMN ≤ duS(τ+io).
- NP ⊆ p^τ Mram already forces lenMN ≥ d·τ, so NP ≈ p^τ Mram up to d·io. Here io = 2·Sig·max Sv with Sig ≤ x^{−ε} (`IRZ:292-293, 348-352`).
- Thus the colength is **not** ≈ rank·gain. It is rank·(τ + small), and τ is already subtracted inside Ga.
- `CutSizes` (`CornerGLContinuity.lean:205-210`) bounds tv and Dp by C·Nv·a/p. That is the same order a/p as gain. The margin
  gain − τ ≥ ASK is NODE-LOSS's StarAt bookkeeping, which I did not recheck.
- Consequence: Σgain − τ of divisibility must hold for chainK on all of Mram (up to io). No vacuity is available on this
  branch: if the local chain were 0, CmpLite's last clause would force every global column to 0 (vGeLat of 0 holds for all s).

**(d) Legendre structure.**
- γ_p = p/(p²−1) = Σ_{odd e} p^{−e} appears in gB (`FGS:51, 57-61`). Subtracting min(a/p^{2e+1}, cap) leaves exactly
  Σ_{odd e} max(0, a/p^e − cap), i.e. the ASK shape.
- The divided-power structure is in `RestGc`/`RestBeta`/`DworkLemma` (`FGS:225-233`; `MV/DworkExponentialRestrictions.lean`).
  They factor the Dwork-type exponential exp(−G(c, σc)) in a height-2 Lubin–Tate parameter (vp^{p²−1} = p, `lamF`) as
  exp(−(vp^{p+1}/p)·h(u))·V, with v_p(vp^{p+1}/p) = 1/(p−1) − 1.
- The derivation that turns this into the γ_p·a coefficient bound (`ea_A1U`/`ea_A2U`/`ea_BU`) is unopened.

## 3. Children

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `admissible_entries_small_chain` / `first_kernel_law_global_small` (AdmAtEnt2 ← CM2) | `…/AdmissibleEntriesOfKernelLaw.lean:62-106` | for every local chain tied to the family, the pending theta datum pendG is `admitted` (13 clauses incl. ExpansionEquality: Kz = Σ theta-kernel integrals; Dwork; adm7 frames) | **core** |
| 2 | `modelsAt_bpt` / `tuplesHaveLocalModels_of_standardColumnObjects` | `SP/TuplesHaveLocalModelsAtConstructedPointOverTrueC.lean:10-19` | at constructed points, local chain models LC exist with CmpLite and SiteAdm | **core** (ties global chain to local theta system) |
| 3 | `stmt_proved` (`Rests`, `ea_A1U/A2U/BU`, `RestGc`, `lift_bound_of_integrality`, `theorem_of_alternate_form`) | `MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:79-111`; `MV/FirstTheoremPlaceBound.lean` | admitted ⇒ chain/Hecke divisibility LowTermBound with γ_p | **core** (local p-adic engine; proved, skeleton read) |
| 4 | colength: `gluing_statement_holds`, `OrbitLatticeBounds`/`LPprime`, `LatticeSandwich` | `TopChoiceBounds.lean:1639`; `CornerGLContinuity.lean:180-196` | Hecke images (T_r)^m M have colength ≤ m(tv+Dp) outside a κ-small set | **core** (makes the divisibility non-trivial) |
| 5 | `cmGoodModel_of_globalArtinReciprocity` | `SP/BundleBothParts…OfGlobalArtinReci.lean` | Artin reciprocity ⇒ CM good-model package CM2 | standard? (CM theory: Shimura–Taniyama/Deuring); unopened |
| 6 | `local_systems_lower_bounds_second_real_place`, `cmpV_of_cmpLite`, `UAt_of`, `unit_bound_of_sum_over_primes` | `SP/UnitaryWeightModels.lean:14-31`; `JointsTw.lean:23-270` | bookkeeping | glue (read) |
| 7 | `SmallResidueCharComparison` (gU ≤ gB, g0 ≤ gA, Pr) | `FGS:741-754` | family numbers ≤ formal-group numbers | glue, supplier not traced |

## 4. Oddities

1. The NP generators with factor p^{⌈Sv⌉} (VV′ ⊊ VV) are harmless: they enlarge NP. The parent's worry (ii) does not apply.
   The costly direction (colength) is bounded through the factor-free generators (T_r)^m M.
2. Name drift:
   - `ArchimedeanSignatureMatching` (`FGS:587`) is the kernel-expansion identity Kz = Σ ker, not anything archimedean;
   - `Sys.Conclusion₂ v j` (`FGS:327`) is the number Pr, not a proposition;
   - `PlaceB`'s i = 0 branch (`MV/PlaceB.lean:27-28`) grants g ≤ gB − alEven with no hypothesis on Y. The work is then carried by
     `EntCondition` (`MV/RamifiedLatticeOfChainEstimates.lean:15-17`).
3. The colength is proved on the `zeroCh` branch (`AdmissibleFamilyNoKernel.lean:173-195`). That is legitimate, because NP depends
   only on vOf, Vram and yv, not on Ch. The chain divisibility actually used comes from the twU branch with the real chain.
4. `entStd D := ⟨nuD D, nuRowOK D, nuD_rows D, 0, 0, 0, 0⟩` (`SP/RowTwUHolds.lean:13`): four zero fields in the OrbitPlaces entry used for Shape. Unexamined.
5. tv and Dp are bounded only by C·Nv·a/p (`CutSizes`), the same order as the gain. The positivity gain − τ ≥ ASK rests on NODE-LOSS's StarAt arithmetic.
6. The GRH-strength claim is now concentrated in children 1, 2 and 4. Child 1 is a 13-clause local theorem for every chain "tied" to the family, derived from CM2.
   I could not check whether `KerFam`/`TiesAt` hypotheses restrict the family enough to make ExpansionEquality true for real theta lifts.

## 5. Coverage

Read:
- `TPS/GServT.lean`; `TPS/CountsIrreducibilityConstants.lean:40-105`; `TPS/Hyps.lean:60-90`;
  `TPS/RowHServOfLink.lean`; `TPS/RowHServOfKerServ.lean`; `TPS/LinkROfIsLinked.lean:1-80`; `TPS/ServHRowLinkR(Statement).lean`;
- `GG/HasPartAnd.lean:1-80`; `GG/ModelsOK.lean`; `GG/IsPlaceCofactorValuationLowerBound.lean`;
  `GG/ThetaSeriesDataHypothesesBelowMaximalLevel.lean:1-160`;
- `SP/RowTwUHolds.lean`; `SP/UnitaryWeightModels.lean`; `SP/BundleBothPartsOfStandardKernelAndSixHypotheses.lean`;
  `SP/BundleBothParts…OfGlobalArtinReci(Statement).lean`; `SP/InertThetaAdmissibility….lean`;
  `SP/TuplesHaveLocalModels…(Statement).lean`;
- `…/AdmissibleEntriesOfKernelLaw.lean:60-106`; `WJS:15-200`; `IRZ:141-480`; `FGS:20-108, 225-365, 447-790`;
- `JointsTw.lean:1-270`; `MV/PrvAndKernelCommutationUpToUnitsOfRests.lean:1-113`; `MV/RamifiedLatticeOfChainEstimates.lean:1-150`;
  `MV/PlaceB.lean`; `MV/DworkExponentialRestrictions.lean:1-60`; `MV/FirstTheoremPlaceBound.lean`;
- `DataG.lean:120-200`; `SmallOrderPrimes.lean:205-240`; `AdmissibleFamilyNoKernel.lean:160-260`;
  `PlaneCountTheoremWithConstants.lean:718-880`; `GlobalTheoremInputs.lean:118-135`; `CornerGLContinuity.lean:150-260`;
  `InertJacobiLevels/TiesLat.lean` (sanity instances, not live); `DataDIVDefs.lean:1-80`; `FormalGroupJets.lean` (a different Stmt).

Not opened:
- `first_kernel_law_global_small`; `tuplesHaveLocalModels_of_standardColumnObjects`; `local_systems_lower_bounds_second_real_place` body;
- `ea_A1U/A2U/BU`, `RestGc` proof; `lift_bound_of_integrality` body; `gluing_statement_holds` body;
- `LPprime`; `cmGoodModel_of_globalArtinReciprocity`; the supplier of `SmallResidueCharComparison`; `kapI` pinning (`kapIDefF`).
