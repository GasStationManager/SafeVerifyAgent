# NODE-WRITEUP: the slope chain as one proof, with a sign and normalisation audit

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations as in NODE-SLOPE, plus
`SPl` = `Formalism/HarderNarasimhan/StatementPl.lean`, `LS` = `Formalism/LatticeSlopes/Statement.lean`,
`HNS` = `Formalism/HarderNarasimhan/Statement.lean`, `QR` = `Formalism/HarderNarasimhan/QuotRealize.lean`,
`SMj` = `Formalism/HermitianLattices/StatementMaj.lean`, `CGF` = `Formalism/SizeWindowBrackets/ClaimGaFree.lean`,
`DDD` = `Formalism/LocalRingCardinality/DataDIVDefs.lean`, `SLB` = `Formalism/QuotientMetricDivisors/ScalarLiftLowerBoundFull.lean`,
`C28` = `Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`, `IS` = `Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean`.
Scope: the core chain only, from the lattices N_u, RR and maps B_u to ASK ≤ MAIN + Err. Hosts, Landau and the Selmer bound
are out of scope. Nothing compiled. "Read" means that I read the statement at the cited line in this pass.

## 1. Setting

**Field and lattices.** K = LL = `what₂.LL` is a totally complex number field, n = [K:ℚ]. A hermitian lattice is an `HLat`
(`DA:61-72`): a K-space V with basis b, frames X_v ∈ GL(ℂ) at each infinite place v, and an 𝒪_K-submodule L. The norm at v is
|x|_v = |X_v^{-1}·σ_v(x)| (`fcoord`, `SMj:29-31`). Realised in ℝ^{2·#places·dim} (`realize`, `SMj:78`), L is a ℤ-lattice.

**Slope.**
- `LS:23-25`: deg_ℤ(L) = −log covol(L) and slope = deg_ℤ/rk_ℤ.
- `SPl:76-77`: μ(L) := 2·slope − log 2 + log|disc K|/n. This is twice the normalised Arakelov slope. The offset makes μ(𝒪_K) = 0
  for the standard metric (check: covol 𝒪_K = 2^{−n/2}|D|^{1/2}).
- μ_max and μ_min are defined the same way from `HNS:29-33`: μ_max is the sup over sublattices, μ_min the inf over saturated quotients.
- `SizeMu` (`SPl:~95-107`) records the consequences: μ = −2 log size, and L ⊆ L′ of the same rank gives ht L′ ≤ ht L.
  So **a superlattice has smaller covolume and larger μ.**
- `bridge_hn_mu` (`DA:106`): μ = −lcv/rank, with lcv = (2/n)·log ht (`DA:88`).

**Dual.**
- dualLat L = {f ∈ Hom_K(V,K) : f(L) ⊆ 𝒪_K} (`QR:15-26`). This is the 𝒪_K-linear dual, not the trace dual.
- dualFrame X = (Xᵀ)^{-1} (`QR:28`). This is the correct dual metric for the bilinear pairing f(x) = φᵀx: if x has
  coordinates X^{-1}σx, then f has coordinates Xᵀσφ.
- RR^∨ := (dualL, dualB, dualX). Define μ(RR^∨) := `muDual` (`DA:97`).
- `bridge_dual_mu_holds` (`RankBoundMonotoneInDimension.lean:993`, proved; body not read) gives μ_min(RR^∨) = −μ_max(RR).
  The mean identity μ(RR^∨) = −μ(RR) is never used: every clause below uses `muDual` directly.

**Height of a map.** For φ : V → W,
htMap(φ) = (1/#places)·Σ_v log‖X′_v^{-1}[φ]_v X_v‖²_op (`SPl:55-62`).
- On a totally complex field this is twice the Bost height (1/n)·Σ_σ log‖φ‖_σ.
- So it matches the factor 2 in μ. `HtImage` (`SPl:109-121`) is the resulting inequality: ht(φA) ≤ ∏_v‖φ‖_v^{2 rk}·htQ.

**The data** (`DivData`, `DA:139-160`; `D7`):
- RR: the target hermitian lattice.
- For each word u ∈ W (one u0 fixed): a hermitian lattice N_u = `div.Nu u`, a K-linear map B_u = `div.Bk u` : N_u⊗K → (RR⊗K)^∨, and a real h(u).
- M_u = (fm u).lat 0 is the "unmodified" source lattice, with Mram = comap of M_u under nuIn (`DDD:12-13`).
  **Do not confuse M_u with the layer lattices M_j inside DIV** (`IS:315`). Those are target-side cusp-form lattices.
- NuLat_u is a sublattice of Mram (a `SizeData₂` field). `NuH u` is N_u with L replaced by NuLat_u: the same V, basis and metric (`DP2:236`).

**Rescaling.**
- N_u.L = I_u·NuLat_u, where I_u = ∏_{w∈supp} 𝔭_w^{−⌊e_w·sg(u,w)⌋} (`NprimeDef`, `DDD:15-24`).
- sg(u,w) = Σ_{j≤m}(gainD_j(w) + F_j(w) − E_j(u,w)) (`DP2:212-213`).
- gainD is the gain with the dropped primes set to 0 (`DP2:209`).

**Local weights.**
- sz(w,y) = 2·lw(w)·e_w·y, with lw = log N𝔭_w/n (`DP2:204`, `DA:39`).
- Σ_{w|p} 2·lw·e_w = 2 log p (`FactUnitNormalisation`, `DA:55`).
- From these: Ga = Σ_w sz(Σ_j gainD_j − τ), Fo = Σ_j Σ_w sz(F_j), and Ee(u) = Σ_j Σ_w sz(E_j(u,·)) (`DP2:215-220`).

**Constants.**
- logΩ = γ + log(π/v) − L′/L(1,χ_d) (`DP2:224`).
- MAIN(u) = Σ_t [m(ph(a_t) − a_t logΩ) − a_t log T(u)], with ph(y) = y log y − y (`DP2:228-230`).
- Main = Σ_j Σ_t a_t(log a_t − 1 − γ + L′/L − mean_ρ log w_{jρ}) (`MB:100-102`).

**Weighted means.**
- d_u = rk N_u.
- s = Σ_u d_u(μ(N_u) − h(u))/Σ d_u (`sFrame`, `DA:125-127`; `MB:87`).
- uF = max_u(μ_max N_u − h(u)) − s.

## 2. The chain

Fix u0 and write ΣA = Σ_t a_t. Every line holds for every word u ∈ W(u0) unless it is averaged.
The tags are: **def** = definition, **id** = identity, **thm** = proved inequality, **IN** = place where an input theorem or hypothesis enters.

**(1) Rescaling.**

  μ(N_u) = μ(NuLat_u) + Σ_w sz(w, sg(u,w)) + O(C·X″).

- Lean: `NprimeMuR`/`LinkMu` (`GTI:69-75`, IN, as an input of `GlobalTheoremInputs`). There is also an exact version,
  μ(shiftLat Nu sg) = μ(Nu) + 2Σ lw·shiftZ(sg) (`DivClausesR` clause 4, `C28:120-122`), on the DIV-package side.
- Node: SLOPESN.
- Type: def + id. Scaling by 𝔭^{−k} multiplies covol_ℤ by N𝔭^{−k·rk}, so μ rises by 2k·log N𝔭/n = 2k·lw.

**(2) Colength.**

  μ(NuLat_u) = μ(Mram_u) − Σ_w 2lw·len_w/d_u,  len_w ≤ dM(τ_w + io_w),  μ(Mram_u) = μ(M_u) − f·log(T−1)/(T−2).

- Lean: `HypLow`/`HypLow2` (`CGF:65-86`). Supplied by `places_at_of` (`PP:300`) from `NuDef`, `adm26` (IN), `hMu` and
  `hG1` = the LinkG colength clause (IN). That clause is proved via `LemmaVVolumeGeneral` (NODE-COLENGTH).
- Node: SLOPESN, COLENGTH.
- Type: id + thm + IN.
- (1) and (2) together give `ClaimLow2`/`SlopesN_at` (`QLD:180`), i.e. **QSB lower**:

  (1+2)  μ(N_u) ≥ μ(M_u) + Ga + Fo − Ee(u) − Lo5(u)   (`QSB:19-22`).

  The τ in Ga is the colength price: Sg subtracts τ, and BeSum adds back exactly du·τ.

**(3) Source floor.**

  μ(M_u) ≥ −cSlope·nT·a·La(1+m/k)   (`Slopes`, `MB:146-148`; IN via `slopesMF_of_count_fam`, unopened).

  Ee(u) ≤ m·ΣA·lg + cE·m·B0   (`EComp5`, `QSB:24-25` = LinkDIV (viii); IN).

**(4) Integrality** (the hypothesis of (5)).

  B_u(N_u) ⊆ RR^∨, i.e. ∀ φ ∈ NuLat_u, ∀ F ∈ RR: v_w(⟨F, B_u φ⟩) ≥ ⌊e_w·sg(u,w)⌋.

- Lean: `OneMapIntoCC` (`DA:180`; LinkDIV (i), `GTI:78`) ⇐ `val2` (`C28:108-109`) ⇐ `adm2` ⇐ `famU`/`Conclusion1` ⇐ `UAt`+`CmpV` (`twU`).
- Node: SLOPESN, TWU, ROWSU, LOCALDIV, KERNELLAW.
- Type: IN. This is the divisibility theorem.
- The ⇔ between "image in dualLat" and "pairing integral" is `bridge_ccb_dual` (`DA:114-121`).

**(5) Slope inequality (Bost + HN + frame).** For HH ≥ s − μ_min(RR^∨):

  s − log|W| − (1−δ)^{-1}[4·uF·log(1+HH/uF) + (η + 4√e)·HH] ≤ μ(RR^∨).

- Lean: `joint_a_ramified_holds` (`JD:254`), the proof of `JointARam` (`FTR:197-221`). Read: the conclusion is literally
  `≤ muDef b′ X′ cc` with cc = RR.dualL, b′ = dualB, X′ = dualX. `Frame_at` (`QLD:188-193`) restates it with
  η = 5σ + 3√de and e = 2e0. The consumer is `SlopeIneq` (`MB:151-157`).
- Hypotheses: (4); htMap(B_u) ≤ h(u) when B_u ≠ 0 (LinkDIV (vi), `GTI:82-83`); `InputSG` (LinkS) and δ (LinkIRR).
- Node: RANK, SLOPE, THEOREMS, SLEAVES, PAIRB, COUNT.
- Type: thm (proved), with its hypotheses IN.

**(6) HN spread.**

  s − μ_min(RR^∨) = s + μ_max(RR) ≤ x^{CH}b =: HH.

- Lean: LinkDIV (ii) (`GTI:79`, IN, producer unread) + `bridge_dual_mu_holds` (thm) ⇒ `HHBound` (`MB:158`).
- Type: IN + thm.

**(7) DIV.**

  μ(RR^∨) + h(u) − Fo ≤ MAIN(u) + cDiv·nT·a·La + cDiv·m(B0+Nc)x^{eDiv·ε}.

- Lean: LinkDIV (vii) (`GTI:84-86`) = `MB:118-121`.
- Node: DIV, HEIGHT, COVOL, HS, VOLUME, L6.
- It is assembled by `divIneqRecord` (`SLB:52-94`, pure real arithmetic) from four pieces:
  - (A) μ(RR^∨) ≤ meanLog κ + Σ_j pq_j Σ_ρ w_{jρ}·logΩ + 2FoOfR + Eb, with Σ_j lcv(M_j)/D ≤ Σ_j l3_j
    (`BoundsMu` thm; `L3`, `IS:315`, IN = `CovolumeBoundOfX` ⇐ `LowAt`).
  - (C) h(u) = hu − meanLog κ, hu = hP + Σ_j hK_j − mlam, with
    - hK_j ≤ Σ_ρ(phν − nν·logΩ),
    - hP ≤ −ΣA·log T,
    - mlam ≥ Σ fa − e6 (`L6`, IN),
    - and htMap(B_u) ≤ h(u) (`height_chain_atR`, thm).
  - nν = a_t[ρ∈TT] + k·w + δ.
  - Σ_j pq_j = mk, |pq_j − k| ≤ m.
  - Fo = 2·FoOfR (`foTie`).
- Type: thm (arithmetic) on IN.

**(8) Count.**

  log T(u) ≥ Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − cCount(La + m²La/k)   (`Count5`, `QSB:27-29`; IN, `countF_fam` unopened).

**(9) Chain, per u** (`s_lower5`, `LoC:50-65`, thm). Add (1+2), (3) and (7), then use (8) to replace −MAIN(u)'s +ΣA log T(u)
by its lower bound. **Fo cancels, and Ee's m·ΣA·lg cancels against Count's m·lg.** This gives

  μ(N_u) − h(u) ≥ Ga + μ(RR^∨) − K5 − Lo5(u),

  where K5 = SDiv − ΣA·Λ5 + m·ΣA·lg + EDiv + cE·m·B0 + cSlope(…) and SDiv = Σ_t m(ph(a_t) − a_t logΩ).

  Averaging with weights d_u gives

  s ≥ Ga + μ(RR^∨) − K5 − wmean(Lo5).

**(10) Close** (`Ga_bound5`, `LoC:115-171`). Combine (9) with (5) and (6). **μ(RR^∨) cancels.**

  Ga ≤ K5 + wmean(Lo5) + log|W| + Φ.

- Φ ≤ (1−δ̄)^{-1}(4 log(1+x^{CH})(K3 + wLo5 + b) + (η̄+4√ē)x^{CH}b).
- This bound on Φ comes from `u_function_le_mean` (`LoC:81`, which uses QSB upper, HComp and Count) and `phi_bound`.
- `key_identity5` (`LoC:105`, id) gives SDiv − ΣA·Λ5 + m·ΣA·lg = Main + ΣA·cCount(…). The log(π/v) cancels here.

**(11) Loss** (`LossBounds`, `QSB:34`; IN via `Loss_at`/`LinkG_at`, ⇐ `GainBoundAt`, NODE-PAIRING):

  ASK − Ga ≤ LoP,  IO ≤ LoP.

**(12) Conclusion** (`each_unit_bound_statement`, `LoC:175-197`):

  **ASK ≤ Ga + LoP ≤ Main + ErrX5at**, with ErrX5at as in `QSB:45-54`.

In one display:

```
ASK − LoP ≤ Ga                                                   (11)
Ga ≤ μN(u) − μM(u) − Fo + Ee(u) + Lo5(u)                         (1)(2)  def/id + colength
   ≤ [μN(u) − h(u)] − μ(RR^∨) + MAIN(u) + EDiv − μM(u) + Ee(u) + Lo5   (7) DIV: −Fo + h ≤ MAIN − μ(RR^∨) + EDiv
   ≤ [μN(u) − h(u)] − μ(RR^∨) + SDiv − ΣA·Λ5 + m·ΣA·lg + errs     (3)(8)
averaged over u:  Ga ≤ s − μ(RR^∨) + Main + errs                  key_identity5
                     ≤ log|W| + Φ + Main + errs                   (5)(6): s − μ(RR^∨) ≤ log|W| + Φ
```

## 3. Sign and direction audit

| # | point | needed | Lean | ok? |
|---|---|---|---|---|
| S1 | slope convention | superlattice ⇒ larger μ | deg = −log covol (`LS:23`); μ = 2·slope + const (`SPl:76`); `SizeMu` last clause | yes |
| S2 | rescaling raises μ by +sz | N_u ⊇ NuLat_u (exponent −⌊e·sg⌋) | `DDD:15-18`: power `-(⌊ur sg⌋)`; NprimeMuR has +Σsz | yes |
| S3 | colength lowers μ; only an **upper** bound on len is needed | len ≤ dM(τ+io) | `HypLow` (`CGF:68`) and BeSum with + len | yes |
| S4 | integrality is stronger for a bigger gain | v(pairing) ≥ ⌊e·sg⌋ on NuLat, i.e. 𝔭^{−sg}NuLat ↦ RR^∨ | `val2` "sg ≤ v_w(Pt)" (`C28:108-109`); `bridge_ccb_dual` | yes |
| S5 | h is an **upper** bound on log‖B‖² | htMap ≤ h, with the same frames (Nu.X → dualX) as μ | `GTI:82-83`; `LatGeom` `FTR:70`; `DivClausesR` clause 2 uses opNorm² with dualFrame XE (`C28:114-117`) | yes |
| S6 | factor 2: μ = 2·slope vs ‖·‖² in htMap | the same scaling on both sides of Bost | htMap = (1/#pl)Σ_v log‖·‖²_v = 2·h_Bost; `HtImage` ht ≤ ∏‖·‖^{2rk} | yes |
| S7 | factor 2: sz vs ASK | gain y at p ↦ 2y log p = Λ(p^e)(1−χ(p^e)) | `FactUnitNormalisation`; ASK weight 2 log p (NODE-ACCOUNT, `FPN:84`) | yes |
| S8 | Bost direction | sub of N with μ_min > μ_max(cc/cc_θ) + h maps into cc_θ | `theoremFSharp_of`/`slope_inequality_mean` (NODE-RANK; body not read by me) | stated correctly in RANK |
| S9 | the frame is on the **target** | Q = Σγ_i Ball_i Ball_i^* on ℂ^{κ⊔κ₁}, with κ = basis of RR^∨; columns are sources | `FTR:72-76` (rows Sum.inl k = Y′^{-1}[B_i]_v Y_i); `InputSG` on the Gram blocks Bf_i^*Bf_j (`FTR:30-35`) | yes |
| S10 | the frame is near-surjective, not near-injective | the sources' images fill RR^∨⊗ℂ, so a high-slope source forces a high mean slope of the target | `TFS:66-67` rank bound | yes |
| S11 | PAIRB vs RANK | B_u = P_u composed with coordinates, (B_u φ)(F) = ⟨sEE F, P_u φ⟩, so B_uᵀ = P_u^* (the Bessel period map RR → N_u^∨). The frame operator is Σγ P_uP_u^* on HH; the Gram kernel is P_u^*P_{u′} | `besS` (`TD16:1113`, via RANK); `BesselId` (`GTI:65-67`) | consistent: the "rows" are B_u and "P_u into HH" is the same matrix |
| S12 | dual metric | the dual frame is correct for the bilinear pairing | fcoord = X^{-1}σx (`SMj:31`); dualFrame = (Xᵀ)^{-1} (`QR:28`) | yes |
| S13 | HN spread uses μ_min(dual) = −μ_max | lower bound on μ_min(RR^∨) | LinkDIV (ii) upper-bounds μ_max(RR); `bridge_dual_mu_holds` | yes |
| S14 | (B) direction | upper bound on μ(RR^∨) ⇐ **lower** bound on μ(M_j) (covol upper bound) | `L3`: lcv/D ≤ l3; μ = −lcv/rank; `LowAt`: μ ≥ −mainT | yes |
| S15 | log T(u) | the chain needs a **lower** bound on log T (MAIN has −ΣA·log T) | Count5 clause 1 is used in `s_lower5` (h3) | yes |
| S16 | Fo, logΩ, m·lg | cancel with matching normalisation | Fo: `foTie` 2·FoOfR = L.Fo and sz = 2lw·e·F. logΩ: the same `logOm` in (B), (C) and MAIN. lg: key_identity5 | yes, syntactic |
| S17 | gain lower bound | only Ga ≥ ASK − LoP is needed | LossBounds; the upper direction is not needed (PAIRING shows it holds) | yes |

**Net reading.** The chain is: integral superlattice + slope inequality ⇒ (mean source slope − height) ≤ target slope + Φ,
and target slope + height ≤ MAIN + Fo. μ(RR^∨) enters both with coefficient +1 and cancels. **So the chain never uses the
size of μ(RR^∨), only the combined DIV statement.** Every inequality points in the direction the next line consumes.
I found no sign reversal.

## 4. Dependency table

| line | rests on | status in the audit |
|---|---|---|
| (1) | `NprimeDef` (family field); `LinkMu`/`NprimeMuR` (input); exact `shiftLat` identity (C28 clause 4) | statements read (SLOPESN, here); elementary |
| (2) | `NuDef`; LinkG colength ← `LemmaVVolumeGeneral`; κ an infimum; `admB2`/`Conclusion2`; `adm26` (μMram = μM − f log(T−1)/(T−2)) | colength proved (COLENGTH); admB2 partly (ADMB2); `RemainingCountingStatement` unread; adm26 statement only |
| (3) | `Slopes` ⇐ `slopesMF_of_count_fam`; `EComp5` ⇐ LinkDIV (viii), aAtG | statement only, unopened |
| (4) | `val2` ⇐ `adm2` ⇐ `famU`, `Conclusion1`, `UAt`, `CmpV`, `period_geTU`; inputs `twU` (`SysTw`), aP10, aAtG, aPer*; formal-group `stmt_proved` | traced (SLOPESN, TWU, ROWSU, LOCALDIV, KERNELLAW, PAIRING); higher-rank capped law untested (NUMTEST2: rank one is a lower bound) |
| (5) | `joint_a_ramified_holds`; `FrameLA1`, `slope_inequality_mean`, `layer_cake_formula`; InputSG ⇐ LinkS ⇐ ThmSOwn/`TheoremSSelected`; LinkIRR ⇐ `closed_linkIRR_of_join_count`; ChosenProviso, ChCode, BesselId, RamRank | top level read (RANK); sub-lemmas unread; Theorem S decisive estimates partly read (PAIRB, COUNT, SLEAVES); LinkIRR unread |
| (6) | LinkDIV (ii) producer; `bridge_dual_mu_holds` | producer unread; bridge proved, body not read |
| (7) | `BoundsMu`/`slope_bounds`; `Passage`; `CovolumeBoundOfX` ⇐ `LowAt` ⇐ `VolumeTheoremX` (`ThmB`, point heights), `FlatDegree` (Chowla–Selberg), `HSAt`; `height_chain_atR`, `BlockBound`, averaged Chowla–Selberg; `L6` ⇐ 7 Published premises; `weight_height_sum_le`; `divIneqRecord` | (A) statement only; (B) read to LowAt (COVOL, HS, VOLUME), ThmB unread; (C) proved (HEIGHT); L6 proved conditionally (L6); divIneqRecord statement read here, proof unread |
| (8) | `countF_fam` (prime T(u) in a short window) | unopened |
| (9)-(10) | `s_lower5`, `u_function_le_mean`, `key_identity5`, `phi_bound`, `Ga_bound5` | read (SLOPE, here) |
| (11) | `Loss_at`, `LinkG_at` ⇐ `GainBoundAt`, `StarAt`, `kinkHH`, `ask_add_Mn` | read (PAIRING, LOSS) |
| (12) | `each_unit_bound_statement` | read |

## 5. What does not fit

No sign or direction misfit was found. Below are discrepancies in paraphrase or meaning, and the items I could not confirm.

1. **"μ(N_u) = μ(NuLat) + gain" is an input, not a derivation, on the consumer path.** `places_at_of` takes `hMu : NprimeMuR`
   (from LinkMu, `GTI:73-75`, error C·X″) rather than deriving it from NprimeDef. The exact identity is proved only on the DIV-package
   side (`C28:120-122`). It is elementary, but it is listed as definitional in SLOPESN, FAMILY and SUMMARY row 4.
2. **The exponent is not "gain".** SUMMARY row 4 writes N_u = 𝔭^{−gain}·NuLat. The Lean exponent is ⌊e_w·Σ_j(gainD + F − E)⌋,
   with τ *not* subtracted (τ is paid in the colength) and dropped primes zeroed. Ga itself is net of τ.
3. **There are two M's.** M_u (source, `(fm u).lat 0`, used in QSB/Slopes) and M_j (target layers, `IS:315`, used in DIV (B), COVOL and LowAt)
   are different lattices on opposite sides of B_u. Nodes write "M" for both.
4. **μ(RR^∨) is not bounded on its own.** It cancels between (5) and (7). SLOPE §0 ("Ga ≤ target slope + h ≤ MAIN") and the brief's
   line "μ(RR^∨) + h − Fo ≤ MAIN" read naturally as two separate bounds. The chain uses only their sum.
5. **"Injectivity" is not a hypothesis.** SLOPESN §0.2 says "integrality, injectivity ⇒ slope inequality". JointARam has no
   injectivity hypothesis: B_u = 0 is allowed for single u (RANK). Only the joint near-surjectivity (frame) is used.
6. **"Period map" naming.** SLOPE and SLOPESN call P_u the period map. PAIRB shows it is a Poincaré series C_u → HH, so B_uᵀ = P_u^* is
   the period map. Both readings describe the same pairing ⟨sEE F, P_u φ⟩, so this is not a mathematical misfit. Not checked:
   how `BuRational` turns this sesquilinear pairing into a K-linear B_u with values in Dual(RR).
7. **Not confirmed: the factor between FlatDegAt and l3m.** COVOL reports FlatDegAt = (p−q)/2·logΩ + …, while l3m = (p−q)·w·logΩ.
   This is consistent with μ = 2·Arakelov slope, but I did not read the conversion (CXC). If the factor were wrong, C2 of NODE-ACCOUNT
   (relative x^{−4}) would fail by a factor 2.
8. **Not confirmed: `HypLow2`'s exact identity** μ(Mram) = μ(M) − f·log(T−1)/(T−2) (via `adm26`). It is an exact equality for a rank-du
   sublattice and looks like a model-specific statement. Unread.
9. **Not confirmed:** the bodies of `slope_inequality_mean` and `FrameLA1` (S8 and S10 rest on RANK's reading), `divIneqRecord`'s proof,
   and the LinkDIV (ii) producer.

## 6. Coverage

Read this pass:
- `SPl:1-125`; `HNS:15-40`; `LS:15-25`; `DA:36-44, 55-190`; `QR:12-32`; `SMj:17-85`;
- `FTR:28-101, 195-221`; `GTI:60-100`; `DDD:1-30`; `CGF:1-106`; `DP2:196-240`;
- `QSB:15-56`; `MB:76-165`; `LoC:45-197`; `SLB:50-95`; `IS:278-330`; `C28:105-124`;
- `QLD:188-194`; `PP:280-332`; `RankBoundMonotoneInDimension.lean:990-1000`.

Nodes read: SUMMARY, SLOPE, RANK, DIV, SLOPESN, ACCOUNT, PAIRING (§0-2). HEIGHT, COVOL, VOLUME, FAMILY, L6, NUMTEST2, COLENGTH and PAIRB: summaries only.
