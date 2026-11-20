# NODE-FAMILY: what a "family" is, and where ASK meets the lattices

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations: `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`,
`TG` = `Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean`, `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`,
`D7F` = `Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean`, `MB2` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`,
`SUT` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean`, `CB/` = `Development/AutomorphicArithmetic/CharacterBoxes/`.

## 0. Summary

The worry is that the family is a free witness. That worry is **half right**. There are three layers.

1. **`SizeData₂` on the abstract record carries no content by itself.** `exists_data_completion`
   (`Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:163-311`) proves the following. Take any `Data` that satisfies the
   single inequality `ASK ≤ Main + cDiv·(…) + LoP`. Put `Ga := ASK − LoP` and `muN = muMaxN = muCC = muMinCC := ASK − LoP`, and set
   the other fields to 0. Then all 11 clauses of `SizeData₂` hold. So `SizeData₂` is a factorisation of "ASK ≤ Main + Err" into steps.
   Any content has to come in through the pinning clauses `TieLocal`, `TieGlobal` and `Ident`.
2. **The pinning is real.** In `ChainTied`, `Ident` pins `Dd.ASK` to the honest prime sum of the host's Artin data. `TieLocal` pins
   every slope field to an actual Hermitian lattice stored in the `D7` datum.
3. **Two of the three links in the chain hold by construction.** (i) The gain `Ga` is *defined* as a local prime-power count, so
   `ASK − Ga ≤ LoP` is bookkeeping. (ii) The division lattice is *defined* as `N′_u = I_u · NuLat_u`. Here
   `I_u = ∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋}`, with sg = Σ_j(gain + F − E). This is the lattice enlarged at each place by its gain, so
   "μ(N′) ≥ μ(M) + Ga + …" is the degree of a fractional ideal. **The only non-definitional link is the upper bound on N′.**
   That bound is `LinkDIV_at`: the period pairing `Bk u` restricted to the *enlarged* lattice has height ≤ h(u), and
   μ^∨(RR) + h(u) − Fo ≤ MAIN(u) + err. Together with the slope inequality (`SlopeIneq`, fed by `LinkS`), it says the
   period/Bessel pairings of the tower are divisible at the inert primes by exactly the local prime counts. That statement is where
   the proof has content or does not. It is supplied by the HypsAlt selection fields (see NODE-THETA), not by `classSel`.

## 1. Statement

### (a) The type of a family

`FamClass := ∀ {eps}, FamP eps → Prop` (`Formalism/SharpRestriction/ParamsHeightRankConstant.lean:157`).
`FamP eps` extends `FamCore eps` (`Formalism/SharpRestriction/ParConsts.lean:31-60`, `Formalism/SharpRestriction/FamCore.lean:71-145`).

| Component | Determined by E, x, ε? |
|---|---|
| `x1`, `Win` (unbounded), `Ix x` (nonempty on Win), `J` | free scaffolding. `G.cls la` (`CB/Supply.lean:22`) forces `Win ⊇` windows [Y, Y^la] |
| `D x i : D7` | the datum (below) |
| `L x i : SizeData₂ (D x i)` (DP2:76-185) | `sc : Scale` is pinned to x, ε (`L_x`, `L_eps`). Then `aT, bT` (windowed integers), **free real functions** `gain, F, E, tau, io` on places, `supp`, `drop`, `NuLat` (a free sublattice), `TTw`, `wPart`, constants `Sc, etaSz, Cc, CGam, Ct, de2, LaG`. Constraints are support, vanishing, window and sign conditions only. `logDerivativeAtOne = dlogL D 1` is pinned (DP2:139) |
| uniformity fields (`R_eq`, `q_eq`, `TT_eq`, `art_eq`, `coverS`, …) | force all i at the same x to share the host invariants. `coverS` gives one i for each u0 ∈ A |
| `params, parT, sizes, ties, gatT, X, Gx, Gy, GK, supp_sat, tw_supp` | auxiliary parameter records (not unfolded) |

`D7` (D7F:76-317) is **not** a free tower. Its fields are:
- `R : Ranks` and `host : Host R`, which hold the host field E with its Artin data (NODE-HOSTS);
- `sp : Spaces … host.E …`, Hermitian spaces over E with prescribed signatures (`Y_sigval`, D7F:313);
- `what₂ : Rows.Data R`, the abstract inner-product tower (EE, Amb, Mult μ j, …; see NODE-THETA);
- `mem u : Member` (ColumnChain / ColumnsAtT / PeriodMap) and `fm u : MemberForms`;
- the **division data** `div : DivData LL Word`, with lattices `Nu u`, `RR`, a pairing `Bk`, and heights `h`;
- a number field `LL ⊇ E` (`embE`, `embE_φ₀`, `hostField_le_fixedField`), with places of LL identified with
  `HeightOneSpectrum (𝓞 LL)` (`plEq`, `val_eq`, `ram_eq`).

The tie fields link the abstract tower to E-objects:
- `jEE`, `jN`: bases of RR and Nu map to ℂ-bases of EE and Mu u;
- `nuIn`: Nu u ↪ (fm u).lat 0, isometric (`nuIn_norm`);
- `eMu_isom`, `perCol_base_eq_PtilCol`: the tower's period columns equal the PeriodMap columns;
- `relDet_smul`, which refers to `Matrix.unitaryGroup (Fin N) host.E` acting on self-dual lattices `SDLat host.E N`;
- `rest_detCharacter_on_unitary_eq`, `etaJ_tie`, `s_HH`, `nd/ntw/nth`, and others.

So the tower is tied to E through D7. Many of these ties are equalities between data that are themselves fields, so the D7
type does not by itself force "these are automorphic forms on U(V)". *I infer*: that identification is whatever the D7 constructor
(`RecExP`, below) builds.

### (b) How ASK connects to `Data`

`ChainTied` (TG:97-114) has three pinning clauses.
- **`Ident`** (`Formalism/SizeWindowBrackets/SChain.lean:26-31`):
  `∀ u0, Dd.ASK u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j)`, with `D = arithOf host` (TG:34), the CFT/Artin data of E.
  It also pins `aT = a∘eT`, `w = w∘eP`, `gam = γ`, `LpL = Re ell(chC)`.
- **`TieArith`** (TG:82-91): a, TT, T2 and w are read off the host and the D7 (`w = wj D j τ`, built from the `hc τ` parameters).
  `ell ψ = L′/L(1,χ)` for the matching primitive χ.
- **`TieGlobal`** (TG:50-61): a, b, b′, k, L, La, B0, Nc, γ, LpL, v, lg = log g0g1, logGam, X″, η, X′ come from `L.sc` and the host.
  All of these are explicit functions of x, ε and the host (DP2:9-56, 221-235).
- **`TieLocal`** (TG:63-80): `d = rank(div.Nu u)`, `T = level prime`, `muN/muMaxN = slope/max slope of div.Nu u`, `h = div.h u`,
  `muM/muMaxM = slopes of (fm u).lat 0`, `EeJ = Σ sz(E)`, `muCC/muMinCC = RR.muDual/muMinDual`, **`Fo = L.Fo`, `Ga = L.Ga`**,
  `Ta = Σ sz(tau)`, `IO = Σ … io`, `del = what₂.delp`.

`L.Ga = Σ_{w∈supp} sz(w, Σ_j gainD j w − tau w)` (DP2:221). Here `gain` is a free field of `SizeData₂ D`.

Fields of `Dd` that are **not pinned**: `HH`, `η`, `e`, `delBar`, `etaBar`, `eBar` (MB2:71-76). They only enter through
`HHBound` (s − μmin^∨ ≤ HH ≤ x^{cHH}b), `FParams` and `SlopeIneq`. The "unpinned" fields that matter are therefore the
**D7/L-level** free fields: `gain, F, E, tau, io, NuLat, div`.

### (c) Where the unpinned values come from on the live path

The supplier chain for `hEx`:
- `TopShape.lean:34` takes `hEx` from HypsAlt;
- the HypsAlt producer uses `classSel` (`CB/ClassSel.lean:14-35`), which produces `ExD 𝒜 cT` by `recS` (`CB/ObjCTrue.lean:30-37`);
- `recS` uses `hostWW`, `kitS` and `designS` (`CB/DesignS.lean:22-102`), with `hR = memberTop_final_contextParameters`
  (`…/IwasawaDecomposition/MemberTopFinalContextParameters.lean:15-24`);
- that in turn uses `existsLayeredData_of_goodScaleContexts ∘ layeredAutomorphicData_exists_of_twoPasses` (not opened).
- `RecExP` (`…/ValidForConstructedPointClassesEventuallyWorking.lean:190-200`) says: for every scale s and every pre-chain P (host + ranks)
  satisfying `ChGood`, there exist D : D7 and Y : Lay D **over P** (`Over D P Lv`, SUT:66, so D.host = P's host). Every ledger part p
  then gives a point with `p.pt.D = setDiv D (nPrime p.L) p.ht` (SUT:381-403).

The free fields are filled as follows.
- **Gain.** `exists_refill` (`…/GlobalInterpolation/ExistsRefill.lean:272-315`; *I infer* it is on the live path, I did not trace the
  call) sets `gain j w := gainP X K a b p j` for inert or signal p, and `tau := tauP`, `io := ioP`.
  `gainP` (`Formalism/LocalToGlobal/GlobalTheory/IsResidueClassZero.lean:224-229`) is built from
  `g0 = Σ_{s∈tops} Σ_{e odd, not excluded} max(0, al(s)/p^e − capU) − dl`, i.e. **the local inert-prime-power count itself,
  minus a defect**. This is the same max(a/p^i − w, 0) shape as ASK (`askG`, `:238`). **So Ga is ASK localised and summed, by
  definition.** `LossBounds` (`ASK − Ga ≤ LoP`) is then a defect estimate. `LinkG_at` (GTI) states the corresponding local comparison.
- **The division lattice.** `nPrime L u = span(Iu D L u · L.NuLat u)` (SUT:372-374), with
  `Iu D L u = ∏_{w∈supp} 𝔭_w^{−⌊e_w·sg u w⌋}` (`Formalism/LocalRingCardinality/DataDIVDefs.lean:17-20`). `setDiv` (SUT:25-30) installs it
  as `div.Nu u`. Its height is `h := hExpl6` (`Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean:25-28`), an explicit
  formula (kernel-place means, log-Γ hook terms, κ_R). **So μ(Nu u) − μ(NuLat u) ≈ Σ sz(sg) = Ga + Fo − Ee holds by construction.**
  This is `LinkMu`/`NprimeMuR` (GTI:69-74), and with `NuDef` (NuLat ≤ M_u locally) it gives `QuotientSlopeBoundsWith`.
- **What remains is `LinkDIV_at`** (GTI:77-89). Quoted:
  ```
  ∀ u, D.div.Bk u ≠ 0 → htMap (Nu u).b (Nu u).X RR.dualB RR.dualX (Bk u) ≤ D.div.h u
  ∀ u, D.div.RR.muDual + D.div.h u - L.Fo ≤ L.MAIN u + C·|TT|·a·La + C·m·(B0+Nc)·x^{Cabs·ε}
  ```
  together with `OneMapIntoCC`, `BesselId` (Bu equals a besS pairing up to unitary change; `BuRational`) and `RRFull`.
  Because Nu u is the gain-enlarged lattice, a height bound for `Bk u` on it is a **divisibility statement**: the period pairings
  of the tower vectors against RR are divisible at each inert place w by about 𝔭_w^{gain}. Combined with the Bost/HN-type
  `SlopeIneq` (MB2:151-156, near-orthogonality supplied by `LinkS`), the chain becomes
  ASK ≲ Ga ≲ μ(N′) − μ(M) ≲ μ^∨(RR) + h ≤ MAIN + err.
  `LinkDIV` is supplied in `TopShape.lean:46-47` by `closed_linkDIVt_of_closed_bridge_kernel`
  (`…/ThirdPlaceSeries/DIVRecBridgeSel.lean:197-207`). Its input is `DivisionKernelConstantBounds`, built from the HypsAlt selection
  fields `sel, selS, selP, selDH, selC, selB, hRB, hPA, hDivG, hDcPtG, rRows` (`TopShape.lean:41-45`).

### (d) Degenerate cases
- **m.** `TiePts` forces m = R.m (TG:38-46). `RestSize` (`SChain.lean:53-58`, a ChainTied clause) requires x^{1/2−ε} ≤ m, so m = 0
  is excluded for large x. HostGood/RankVal also give m ≍ √x·x^{−ε/16} (NODE-HOSTS).
- **TT, T2.** `RestSize` requires #TT ≥ x^{−ε/8}n/2 and #T2/n ≥ x^{−ε}. n = |A| ≍ x^{2+8ε} comes from RankVal (via `HostExW`,
  `G.cls la`). So both sets are non-empty.
- **Words.** The word type is non-empty (`u₀`, TG:16). `CodeUpF` fixes `#Word = ⌈3·Γ²·x^{CF}⌉` (`CB/DesignS.lean:53`).
- **Rank / dimension 0.** Not excluded by anything I read. dim EE = rank RR (`jEE_basis`). `LinkDIV`'s height clause is vacuous
  when `Bk u = 0`, and `OneMapIntoCC` (not unfolded) is the only guard. `SlopeIneq` uses rank-weighted means `wmean (d u0)`
  with d = rank Nu u. **Check:** if all `Nu u` or `RR` had rank 0, would `muDual`, the HN quantities and `SlopeIneq` read trivially?

### (e) Overall reading
The hosts E are genuine and the family's D7 data are built over them (`Over D P Lv`). The prime sum ASK enters `Data` only through
`Ident`, and it is matched to lattice data only through gains, which are *defined* to be the local prime-power counts. The lattice
`Nu u` is *defined* as the gain-enlarged lattice, so the lower slope bound is free. All of the arithmetic burden falls on
**`LinkDIV_at`**: the period/Bessel pairing `Bk u` on the enlarged lattice has height ≤ h(u), and μ^∨(RR) + h − Fo ≤ MAIN + err.
That is a divisibility of theta/period pairings at inert primes, of exactly the size of the prime count. Together with
`SlopeIneq`/`LinkS`, it is the single substantive statement. It is supplied by HypsAlt selection fields, so through NODE-THETA's
theta inputs, not by `classSel`, whose `True` selection predicate is harmless.

## 2. Argument (as mathematics)
`topDesWin` (`CB/DesWin.lean:11-31`) takes a K-large family from `DesignExists`, combines the nine Closed link properties, and
applies `LinkGLOBAL` (GTI:162-164). LinkGLOBAL is obtained from `FamGLmin.link8` → `link7` → `linkGLOBAL7_min`
(`Formalism/SharpRestriction/GlobalSchurBounds/LogXLowerFamilyOfTheorems.lean:39-80`, `…/LinkMin.lean:723-735`). Those build `Dd` by
TieLocal/TieGlobal from the D7 and L, with the slope estimates from `SlopeLow/SlopeMax` (columns of `(fm u).lat 0`,
`IntegrableOfContinuousCircleMeasure.lean:1528-1541`). `link_gl` (`…/GlobalInterpolation/LinkGl.lean:14-31`) is glue: it uses
`famGLmin_of_realPlaceSecondLayer` with the HypsAlt fields `tie, hU, hG` (mass formulas) and `hduty`.

## 3. Children

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `closed_linkDIVt_of_closed_bridge_kernel` ← `DivisionKernelConstantBounds` (from HypsAlt sel*, hRB, hPA, hDivG, hDcPtG, rRows) | `…/ThirdPlaceSeries/DIVRecBridgeSel.lean:197`; `TopShape.lean:41-47` | LinkDIV: on the gain-enlarged lattice the period pairing has height ≤ h, and μ^∨(RR)+h−Fo ≤ MAIN+err | **core: the whole arithmetic content** |
| 2 | `link_alt_alt_bis` (LinkS) + SlopeIneq inside `linkGLOBAL7_min` | `TopShape.lean:55`; `LinkMin.lean:723` | near-orthogonality of Bessel vectors ⇒ a Bost-type slope inequality | core (geometry of numbers, standard in shape) |
| 3 | `existsLayeredData_of_goodScaleContexts`, `layeredAutomorphicData_exists_of_twoPasses` | via `MemberTopFinalContextParameters.lean:20-23` | D7 over each host exists (the theta tower, lattices, periods) | core, **definition to unfold** |
| 4 | `exists_refill` / `gainP` | `ExistsRefill.lean:272,315`; `IsResidueClassZero.lean:224` | gain := local prime-power count | glue (definitional) |
| 5 | `nPrime`, `Iu`, `setDiv`, `hExpl6` | SUT:25,372; `DataDIVDefs.lean:17`; `KernelPlaceMeanBound.lean:25` | Nu := I_u·NuLat, h := explicit | glue (definitional) |
| 6 | `exists_data_completion` | `PChain.lean:306` | SizeData₂ ⇔ (essentially) ASK ≤ Main+Err for free Data | glue (shows that SizeData₂ alone is empty) |
| 7 | `classSel`, `recS`, `designS`, `kitS`, `hostWW` | `CB/ClassSel.lean:14`; `CB/ObjCTrue.lean:30`; `CB/DesignS.lean:22` | assemble FamP from per-scale kits | glue |

## 4. Oddities
1. `SizeData₂` (Data-level) is satisfiable for *any* Data with ASK ≤ Main + Err (PChain `compl`). It is a re-encoding, not a lemma.
   The model files in the same PChain file (`modelData`, `DE`, `textData`, with Ga := 0, m = 1) are sanity models, not on the live path.
2. Gains and the division lattice are defined from the prime counts. So "the lattice slope sees the prime sum" holds by
   construction, and all the risk sits in LinkDIV (child 1). A reviewer should open `DivisionKernelConstantBounds` and check that the
   height bound is proved on `nPrime L` and not on an un-enlarged lattice. `pt_D` (SUT:403) shows that the enlarged lattice is the one
   installed.
3. `LinkDIV_at`'s height clause is conditional on `Bk u ≠ 0`. A zero pairing would make it vacuous unless `OneMapIntoCC` forbids it
   (not unfolded).
4. `classSel`'s `IsSel … (fun _ => True)` is harmless. The family still satisfies `G.cls la` (windows plus EAtH/VVle at its host) and
   the DesignChoices conditions.
5. The unpinned Data fields HH, η, e enter only as one-sided slack. Setting η = e = 0 and HH at its minimum is allowed by `FParams`/`HHBound`.

## 5. Coverage
Read: PROTOCOL Explainer; NODE-HOSTS; NODE-THETA:1-140; NODE-COREGM:1-120. `LinkGl.lean`; `CB/ClassSel.lean`, `CB/DesWin.lean`,
`CB/ExS.lean`, `CB/Supply.lean`, `CB/ObjCTrue.lean`, `CB/DesignS.lean`, `CB/DivinNOfHypV.lean`; `FamCore.lean:60-200`;
`ParConsts.lean:20-60`; `ParamsHeightRankConstant.lean:130-200`; D7F:1-317; DP2:1-260; TG:1-116; GTI:1-100,120-164;
`SChain.lean:1-70`; `QuotientSlopeBoundsWith.lean:15-40`; MB2:37-165; `PChain.lean:1-345` (with grep of the rest);
`DesignExistsOfChoices.lean:1-30`; `LogXLowerFamilyOfTheorems.lean:1-140`; `LinkMin.lean:723-735`; `LossesSmallShares.lean:464-476`;
`ExistsRefill.lean:255-320`; `IsResidueClassZero.lean:140-250`; SUT:20-32,370-440; `ValidForConstructedPointClassesEventuallyWorking.lean:150-215`;
`MemberTopFinalContextParameters.lean`; `ExistsClassSelOfRowL.lean`; `DataDIVDefs.lean:1-60`; `KernelPlaceMeanBound.lean`;
`IntegrableOfContinuousCircleMeasure.lean:1528-1541`; `DIVRecBridgeSel.lean:190-207`; `TopShape.lean:34-57`.
Not opened: `DivisionKernelConstantBounds` / `linkDIVt_of_rowsT`; `existsLayeredData…`/`layeredAutomorphicData…`; `kitS`/`hostWW`;
`famGLmin_of_realPlaceSecondLayer`; `OneMapIntoCC`; `DivData`/`htMap`; the call site of `exists_refill`.
