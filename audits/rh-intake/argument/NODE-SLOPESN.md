# NODE-SLOPESN: what pays for Ga (`SlopesN_at` / `SlopesNF`, the lattice N_u, and the map out of it)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations are as in NODE-SLOPE, plus:
- `TDN` = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- `DDD` = `Formalism/LocalRingCardinality/DataDIVDefs.lean`
- `PP` = `Formalism/LocalToGlobal/GlobalTheory/PlacesP.lean`
- `LQP` = `Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean`
- `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
- `AAG` = `Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean`
- `JS` = `Formalism/LocalToGlobal/GroupLattices/JointServices.lean`
- `IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
- `SRB` = `Formalism/SharpRestriction/GrowthBounds/AdmissibleIntegers/StatementsOfRemainingBound.lean`
- `AFN` = `Formalism/LocalToGlobal/GroupLattices/AdmissibleFamilyNoKernel.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`

## 0. Summary

1. **N_u is case (ii): a rescaled lattice.** The family carries a structure field `Fm.nprimeDef : NprimeDef`
   (`DDD:22-24`, used at `PP:723`). It says
   N_u = I_u · NuLat_u, with I_u = ∏_{w∈supp} 𝔭_w^{−⌊e_w·sg(u,w)⌋} (`DDD:17-20`),
   where sg(u,w) = Σ_{j≤m}(gain_j(w) + F_j(w) − E_j(u,w)) (`DP2:215-216`).
   NuLat_u is a free sublattice field of `SizeData₂` (`DP2` field `NuLat`). `NuDef` (`DDD`, after `InertK`) ties it to M_u,
   with local colength lenMN. So μ(N_u) = μ(NuLat_u) + Σ_w sz(w, sg) holds by construction. `NprimeMuR`
   (`GTI:69-70`) states this up to O(X''), and `HypLow` (`Formalism/SizeWindowBrackets/ClaimGaFree.lean:65-72`) records it
   as an exact identity: μN = μMu + Sg − BeSum(len, τ). Together with lenMN ≤ duS(τ + io), this gives `SlopesN_at`.
   **The lower bound μ(N_u) ≥ μ(M_u) + Ga + … is therefore definitional (scaling plus small colength). It is not a theorem about vanishing.**
2. **The content is in integrality: B_u(N_u) ⊆ (RR)^∨** (`OneMapIntoCC`, `DA:180`; clause (i) of `LinkDIV_at`, `GTI:78`).
   Since N_u = 𝔭^{−sg}·NuLat, this says that the Bessel-period pairing of every φ ∈ NuLat_u with every test vector F has
   w-adic valuation ≥ ⌊e_w·sg(u,w)⌋. That is exactly `adm2` (`LQP:206-210`). The chain is then:
   - integrality, injectivity ⇒ the slope inequality `joint_a_ramified_holds` (NODE-SLOPE): s ≤ μ(RR^∨) + log|W| + Φ;
   - DIV: μ(RR^∨) + h − Fo ≤ MAIN.
3. **On the live path, `adm2` is not trivialised.** It comes from `closed_family_admissible_twist_link_alt`
   (`TPS/ClosedFamilyAdmissibleTwistLink.lean:13-31`) → `admissible_family_of_inclusion`/`famU`/`admissible_level_two`
   (`AAG:214ff, 262-300, 315`). That route reduces it to:
   - a **column-valuation statement** `WJS.Conclusion1` (`WJS:97-101`): for x in the sublattice NP(u,w), col(x) ≡ 0 mod ϖ^{totS},
     where totS = Σ_j (gainS_j + F_j − E_j);
   - plus period integrality (`period_geTU`, `AAG:72-95`).
   
   `Conclusion1` is proved in `SRB` from `UAt`, a chain-valuation bound on the **family's own** chain `reW (Fm.Gy x i) LC`.
   It then crosses to columns through `CmpV` (`WJS:156-159`). Both `UAt`'s inputs (`SysTw`) and `CmpV` arrive **as hypotheses**
   (`SelectionServed.twU`, `TPS/GServT.lean:13-16`), a binder of `shape_closed_link_n_of_green`. No constructor exists in the tree:
   `twU :=` occurs only as pass-through (`GServT.lean:29`, `ServiceOfTiedSelection.lean:37`).
4. **zeroCh is used only on the LinkG branch.** There it discharges `unitBoundAtTwistedPlaces` and `ServiceLowerValuation` by
   `vKge_zero` (`AFN:211-218`). LinkG supplies to SlopesN only the colength clause
   (`LocLe … ⌊τ⌋ NuLat Mram ∧ lenMN ≤ duS(τ+io)`, `PP:723-725` via `hG`). That clause does not need the chain, so zeroCh is harmless there.
   It does **not** feed adm2/OneMapIntoCC.

## 1. Statement

`SlopesN_at L C` (`QLD:180-182`), for every word u:
- μ_max(N_u) ≤ μ_max(M_u) + Ga + Fo − Ee(u) + C·m·B0;
- μ(M_u) + Ga + Fo − Ee(u) − LoU(u) ≤ μ(N_u).

Here M_u = (fm u).lat 0, N_u = div.Nu u, and LoU = C·IOsum + C|TT|m(a/k + b′)·log T(u) + C·X″ + 1 (`QLD:176-178`).

`SlopesNF` (`QLD:252`) is the family version. It is supplied by `slopesNF_of` (`TDN:1544-1546`) ← `PlacesF` (`TDN:1541`) ←
`Places_at` (`TDN:~1514-1527`): ∃ sg′, de, μMu, … with `HypLow`, `HypLow2`, `HypHigh` (`ClaimGaFree.lean:65-97`) and size
bounds. `slopesN_at_of` (`TDN:1530-1539`) is linear arithmetic on `lower_bound_simplified`/`claimHigh_valid`.

`Places_at` is supplied by `placesF_of` (`PP:638-737`) → `places_at_of` (`PP:300-330`). Its hypotheses are:
- `Fm.nprimeDef` (N = I_u·NuLat);
- `Fm.nuDef` (NuLat ⊆ Mram locally, with colength lenMN);
- `NuCommens`;
- `hRank`;
- `adm26`;
- `hMu : NprimeMuR` (from `LinkMu`, an input in `GlobalTheoremInputs`, `GTI:158-160`);
- `hG1` (LinkG: LocLe at ⌊τ⌋ and lenMN ≤ duS·(τ+io));
- τ ∈ ℕ, io ≥ 0, τ = 0 at T, Σ sz(τ) ≤ b².

**The opposite inequality** (Ga upper bound). It is not in this node; it is assembled in `LoC` (NODE-SLOPE §2(a)) from:
- `OneMapIntoCC` + `htMap ≤ h` (LinkDIV (i), (vi));
- `Frame_at` = SlopeIneq (`QLD:188-194`): s − log|W| − (1−δ)^{-1}(4uF log(1+HH/uF) + (η+4√e)HH) ≤ μ(RR^∨);
- LinkDIV (vii): μ(RR^∨) + h(u) − Fo ≤ MAIN(u) + C|TT|a·La + C·m(B0+Nc)x^{Cabs ε} (`GTI:84-86`).

## 2. Argument (what is applied to what)

**Lower side (by construction).** By NprimeDef, N_u is NuLat_u scaled by the fractional ideal ∏𝔭_w^{−⌊e_w sg⌋}.
Scaling a rank-d hermitian O_LL-lattice by 𝔭^{−k} raises the normalised slope by 2·k·log N𝔭/[LL:ℚ]-type terms, i.e. by sz(w, sg).
NuLat_u ⊆ M_u has local colength lenMN(u,w) ≤ duS·(τ_w + io_w), which costs at most Σ 2 l_w·len/du = O(τ + io).
So μ(N_u) ≥ μ(M_u) + Σ_w sz(Σ_j gain_j − τ) + Fo − Ee − O(IO + …) = μ(M_u) + Ga + Fo − Ee − Lo. In this inequality nothing vanishes.
The −τ inside Ga is the colength price of NP ⊆ p^{⌈τ⌉}M (`IRZ:464-472`).

**Upper side (where content must be).** The map is B_u = `div.Bk u` : N_u → (RR)^∨. `BesselId`/`BuRational` (`GTI:69-71`,
NODE-SLOPE) identify it, up to a nonzero scalar and isometries, with the Bessel-period pairing besS. On the live path:
- **Integrality** (`OneMapIntoCC`) comes from `WordFacts` (`RB:126-133`) ← `DivisionPackage(Face).wordFacts` (`RB:608-614, 633`).
  That uses `val2` (`RB:598-606`):
  ∀ φ ∈ Nu_u (coordinate lattice), ∀ F: Pt(φ, F) = 0 ∨ ⌊e_w sg⌋ ≤ v_w(Pt(φ, F)).
  `val2` is `val2AllAtR` (`JointServices/ValIntNonneg.lean:73-91`) applied to the hypothesis **adm2**. It goes through `perToVal2` (`:31-71`),
  an honest span induction: if every generator's period has valuation ≥ s, so does every lattice element.
  The `shift` field (`RB:~425`) says NuC = shiftLat(Nu, sgRec), the coordinate form of NprimeDef.
- **adm2** (live) = `famU` (`AAG:262-300`) → `admissible_level_two`. It splits into three cases:
  - (a) w over T(u): `admissible_at_twist_places`, from `Conclusion5Sharp`/`TwistedColumnBoundAtT` (inputs `aP10`);
  - (b) w over g0, g1: `atG_coreU`, from `UsedTuplesBoundByConstant` (input `aAtG`);
  - (c) other w: `admissible_off_twist_places` (`AAG:171-196`). It applies `Conclusion1` (from `Serv`, i.e. `ServF`) to x = nuIn φ ∈ NP.
    This gives ColGe(x, totS) with sg ≤ totS (`gainLe_of_fills`). It then applies `period_geTU`: column valuation +
    `MemberChainIntegral` + `PeriodClassSumWeyl`/`TwistedPeriodAdmissible` (inputs `aPt0`, `aPtTw`, `aPer0`, `aPerTw`) ⇒ period valuation ≥ sg.
- **Conclusion1** (`SRB`, `baseChange_preserves_unitary_of`/`kernel_valuation_served`):
  - for served w it comes from `TupleLatticeValuation` = `first_in_local_models` (`SRB`, span induction on NP generators);
  - NP generators are yProd(VV′)(p^{Σ_{t0∉VV′}⌈Sv⌉}·F) (`IRZ:470-471`). For t0 ∉ VV′ the divisibility by p^{Sv} is **explicit in the
    generator**. For t0 ∈ VV′ it comes from `UAt` (`WJS:161-170`): chainK^m(yv_{t0}^m F) has valuation ≥ Σ_j (gU_j − Pr_j) + low;
  - `UAt` comes from `G.Joints.unit_bound_of_sum_over_primes` (`Formalism/SharpRestriction/GrowthBounds/JointsTw.lean:243-270`), using
    `FormalGroupSystem.Pf.stmt_proved` and the `SysTw` system from `twU`;
  - chain valuation is converted to column valuation by `CmpV` (also from `twU`).
- **Injectivity.** `nuIn_inj` is a D7 field (`RhoDetPrimeEqMuTildeMulChiPow.lean:292`). The slope inequality needs B_u to be
  near-isometric (InputSG, from LinkS). Note that LinkDIV (vi) asks htMap ≤ h only **when Bk u ≠ 0** (`GTI:82-83`).

## 3. (c) Trivial instantiations from `link_gl` down (what I saw)

| # | Object | file:line | Effect |
|---|---|---|---|
| 1 | `zeroCh (Fm.Gy x i)`, chain ≡ 0 | `AFN:166-171`, used `:206-218, 251` | `unitBoundAtTwistedPlaces`, `ServiceLowerValuation`, admG1 vacuous on the LinkG branch. Feeds the loss and colength clauses only |
| 2 | `vKge_zero` | `AFN:178-187` | proves divisibility because 0 ∈ submodule |
| 3 | `NprimeDef` as a family field `Fm.nprimeDef` | `DDD:22-24`; `PP:723`; `RB:690` | N_u is a rescaled copy by definition |
| 4 | LinkDIV (vi) guarded by `Bk u ≠ 0`; WordFacts likewise | `GTI:82`; `RB:129` | height bound vacuous if a map is zero (not shown to happen) |
| 5 | `TopShapeAlt True True` | `TPS/TopShape.lean:31` | V and NR slots trivial (known from NODE-ROOT) |
| 6 | `HH := x^{CH}·b` constant | NODE-SLOPE | not a trivialisation, but chosen rather than derived |
| 7 | sanity instances with `nuIn := fun _ => 0` | `Formalism/LocalRingCardinality/SpanPowerMembership/*.lean` (e.g. `ExampleClassGroupCardPos.lean:213`) | not on the live path (I infer from names; they are examples) |

On the adm2/ServF branch the chain is `reW (Fm.Gy x i) LC`, with LC existential from `twU`. It is **not** zeroCh.
If LC were zero, `CmpV` would force every column, and hence every period pairing, to vanish; then Bk = 0 and the frame hypotheses fail.
The tree does not decide this, because twU is an unconstructed input.

## 4. (d) Sanity: where must GRH-strength sit?

The weights are w ≈ b on thick places, a ≈ x·b. So (a/p^e − w)_+ ≈ b(x/p^e − 1)_+, and per (t, j)
ASK ≈ b·Σ_{p^e<x, p inert, e odd} 2 log p·(x/p^e − 1): a Riesz mean at x for (1−χ_d)/2-weighted prime powers.
MAIN per (t, j) is b·(x log x − (1+γ − L′/L(1,χ_d))x + …), the explicit-formula main term.
The final error is O(|TT|·m·b·x^{1/2+Cε}) against a main term of size |TT|·m·b·x log x. Per unit b this is
Riesz-sum − main = O(x^{1/2+ε}), i.e. GRH for χ_d (and the host).

I infer that the chain splits the strength as follows:
- (α) a **local divisibility** that is exact to O(b) per prime: v_w(period) ≥ Σ_j gain_j(w) ≈ ASK_p (adm2 ← Conclusion1 ← UAt/CmpV/SysTw);
- (β) a **mean-slope inequality** losing only O(b) + log|W| (rank-free; `joint_a_ramified_holds`, with InputSG from LinkS: δ ≤ e^{−x^{ez/7}}, η·x^{CH} ≤ 6);
- (γ) a **degree bound** DIV accurate to relative x^{−1/2}, with γ and L′/L(1,χ_d) **inserted by definition** through logΩ (`DP2:224`).

Together this is a product-formula inequality: Σ_{inert p} (log p)·v_p ≤ archimedean size, with √x accuracy. That is a Weil-explicit-formula positivity statement, which is equivalent in strength to GRH.
**No single clause I opened is visibly GRH-strength.** (α) is local at each p and (β) is proved. So the strength must be in:
- (γ), DivisionPackage `pkg` (`RB:643`, `BridgeRowsF.pkg`), i.e. that μ(RR^∨) + hExpl6 matches MAIN with exactly these constants;
- and/or the joint compatibility of the inputs twU (SysTw, CmpV), aP10, aAtG, aPer*, LinkS (InputSG), LinkMu, all **hypotheses** of
  `shape_closed_link_n_of_green` (`TPS/TopShape.lean:31-33`). They are taken from HypsAlt (NODE-THETA).

A system of local and global inputs that are all individually plausible-looking, yet jointly imply GRH, would be a
breakthrough. So I infer that at least one input is false, or that the inputs are jointly unsatisfiable by real objects. I could not identify which one.

## 5. Children (ranked)

| # | Name | file:line | Statement | Weight |
|---|---|---|---|---|
| 1 | `SelectionServed.twU` (SysTw + CmpV) | `TPS/GServT.lean:13-16`; `WJS:156-159` | the family's chain at each served w satisfies the formal-group system's admitted conditions, and chain valuation ≤ column valuation | **core, unconstructed input** |
| 2 | DivisionPackage `pkg` / `DIVinN` ⇒ WordFacts (vii) | `RB:643`; `RB:126-133` | μ(RR^∨) + h − Fo ≤ MAIN + errors | **core** (NODE-SLOPE child 1, still unopened) |
| 3 | `FormalGroupSystem.Pf.stmt_proved` + `unit_bound_of_sum_over_primes` | `JointsTw.lean:243-270` | chainK^m(yv^m F) gains Σ_j(gU − Pr) | core (local divisibility engine; not opened) |
| 4 | `adm2` inputs `aPt0`/`aPtTw`/`aPer0`/`aPerTw`/`aP10`/`aAtG` | `TPS/ClosedFamilyAdmissibleTwistLink.lean:14-24` | integrality of periods/columns at T, g_i, twisted tuples | core inputs |
| 5 | `joint_a_ramified_holds` + InputSG (LinkS) | NODE-SLOPE | mean-slope inequality with near-tight frame | core (proof unopened) |
| 6 | `perToVal2`, `val2AllAtR`, `first_in_local_models`, `period_geTU` | `ValIntNonneg.lean:31-91`; `SRB`; `AAG:72-95` | span induction and valuation bookkeeping | glue (read; honest) |
| 7 | `places_at_of`, `HypLow`, `slopesN_at_of` | `PP:300-330`; `ClaimGaFree.lean:65-97`; `TDN:1530-1546` | slope of scaled lattice | glue |

## 6. Oddities

1. N_u's slope gain is defined (NprimeDef), so `SlopesN_at` is accounting. It is the mirror of NODE-LOSS (Ga is ASK by definition).
   All vanishing content is shifted into adm2 → twU and then into hypotheses.
2. NP generators carry an explicit factor p^{Σ⌈Sv⌉} for t0 ∉ VV′ (`IRZ:471`). Part of the "divisibility" is therefore multiplication
   built into the generator. Its cost is meant to be paid by NP ⊆ p^{⌈τ⌉}M and lenMN ≤ duS(τ+io). I did not verify that Σ⌈Sv⌉ ≤ τ-type accounting holds.
3. Height clause conditional on Bk ≠ 0 (`GTI:82`, `RB:129`).
4. `twU`, `pkg`, `LinkS`, `LinkMu`, `LinkDIV` all appear only as hypotheses. `GlobalTheoremInputs` (`GTI:158-160`) is an
   antecedent of `LinkGLOBAL`/`LinkGLOBAL7` (`LossesSmallShares.lean:464-466`; `LinkMin.lean:695-725, 752-775`).

## 7. Coverage

Read:
- `QLD:170-262`; `TDN:1480-1546` (+ the start of the FullLattices section);
- `DDD:1-80`; `DP2:76-260`; `GTI:60-100, 158-164`; `DA:130-195`;
- `RhoDetPrimeEqMuTildeMulChiPow.lean:280-300, 355-366`;
- `PP:280-330, 600-760`; `RB:100-180, 300-520, 640-718`; `LQP:200-222`;
- `JS:30-170`; `ValIntNonneg.lean:1-91`; `ClassOfRecordOfChoice.lean:90-230`; `IndefiniteRealisationChoice.lean:170-200`;
- `LossesSmallShares.lean:36-60, 455-520`; `LinkMin.lean:660-800`; `LinkGl.lean`; `TPS/TopShape.lean`;
- `TPS/ClosedFamilyAdmissibleTwistLink.lean`; `AAG:1-380`; `WJS:15-275`; `IRZ:414-475`;
- `SRB:1-224`; `AdmissibleIntegers.lean`; `SumOverPrimesHypotheses.lean:150-228`; `GServT.lean`;
- `JointsTw.lean:243-272`; `AFN:160-255`; `ClaimGaFree.lean:65-106`.

Not opened:
- `kernel_valuation_served` body (`WJS:348`); `FormalGroupSystem` Stmt/admitted; `SysTw`;
- `DivisionPackage(Face/Kernel)` construction (`link_brest_alt`, `wire_sel_alt`);
- `lower_bound_simplified`; `NuServedDef`; `HypsAlt` suppliers of twU.
