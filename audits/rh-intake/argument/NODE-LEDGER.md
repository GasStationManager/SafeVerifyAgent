# NODE-LEDGER: the final inequality on the live path, line by line

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(inferred)* = my reading. [NODE] = taken from that node, not re-read. Nothing was compiled.

Abbreviations (new ones marked *):
- `MB` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`; `QSB` = `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`; `LoC` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`; `WMD` = `Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean`
- `SC` = `Formalism/SizeWindowBrackets/SChain.lean`; `EW` = `.../ErrorFormsWeakWindowsFalse.lean`; `GB` = `.../GrowthBoundGivesRiemannHypothesis.lean`; `FPN` = `.../FirstPrimeNeSecondPrime.lean`; *`PCh` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean`
- `QLD` = `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`; `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`; `LSS` = `.../GlobalSchurBounds/LossesSmallShares.lean`; `TG` = `.../GlobalSchurBounds/TieGlobal.lean`
- `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`; `DA` = `.../DataArith.lean`; `RV` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean`; *`HCl` = `Formalism/LocalRingCardinality/HostCls.lean`; *`DH` = `.../DataHost.lean`
- `CGT` = `Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`; `INP` = `.../Divisibility/Inputs.lean`; `DHB` = `.../Divisibility/DivisionHeightBoundStatement.lean`; `SO` = `Formalism/DivisorInequality/StatementObj.lean`
- `CG` = `Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean`; `CAH` = `.../PrimitiveCosets/CoreAtH.lean`; `SI` = `Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean`; `CT` = `.../LandauTheorems/ChTop.lean`; `CC` = `.../LandauTheorems/ChCore.lean`; *`CB` = `.../LandauTheorems/ChBalance.lean`
- `DW` = `Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean`; `TS` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean`; *`DNV` = `Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean`; *`PTF` = `Formalism/ThickAverageLoss/PartnersToFactorsAt.lean`

## 0. Verdict

1. **The ledger composes.** Fifteen displayed lines (§2), each a Lean statement, add up to Gm(x) ≤ x^{1/2+(eD+eL+7)ε}. Every combination step is a proved `linarith`/`linear_combination` (LoC:50-197, CT:37-72, CC:283-442, CG:16-74). No term has the wrong sign, none is missing, and every error term is ≤ U·x^{1/2+O(ε)}. **No ESCALATE.**
2. **The exponent is now explicit.** On the traced live path `topDesWin` is called with Cabs = 2, C0 = 3, **eD = 2, eL = 0** (TS:52; signature DW:11). So the final statement is **Gm(x) ≤ x^{1/2+9ε}**. This settles MAIN-ARGUMENT §1's open question: eD + eL + 7 = 9 > 0.
   - The 9 is made up as follows: 2 + 0 + 3 from the error envelope ErrX5at ≤ x^{(eDiv+eLoss+3)ε}·ErrText (PCh:613-616, EW:19); +3 from `GrowthSizeBound` (GB:119-122); +1 from SigA and the averaging constants (CG:63-74).
   - ε is fixed per family. `FamilyClassConnected` (DNV:13-15) gives, for every ε ∈ (0, ε₁), a separate family `FamP ε` satisfying `ChainTied` on its windows. The limit ε → 0 is taken only in the Landau step [LANDAU].
3. **Main-term cancellation.** The prime-side and archimedean-side main terms never meet as computed numbers.
   - The archimedean m·ph(a_t) − m·a_t·logΩ is turned into `Main` by an exact algebraic identity (`key_identity5`, LoC:105-107; WMD:170-218).
   - `Main` is identified with the prime side's explicit-formula main term `MAIN` by definition (CT:11-35).
   - Σ_p γ_p·a·log p never appears. The gain enters only as the abstract scalar Ga, bounded below by `LossBounds` and above by the slope chain.
   - Required precision: relative x^{−1/2+O(ε)} on the archimedean side (the DIV, Count5 and Bost errors). The p-adic side is required to x^{−1+O(ε)} (LoP with eL = 0).
4. **Signal primes are inert in ℚ(√−d) and split in ℚ(√−q).** `primeClass_eq_signal_iff'` (HCl:116-117) gives (−d/p) = −1 with psAt p = 1, and `psAt_prime` (HCl:178-179) gives psAt p = (−q/p). InertClass primes are inert in both (HCl:134-135). So NODE-SIGNAL is right and NODE-NUMTEST4's phrase describes inertClass.
5. **H5 is not in the Lean.** No statement bounds Ga − ASK by the budget (greps in §5). The only upper bound on Ga is `ga_le_at` (`.../Divisibility/HookProducts/CardLiftsEq.lean:70-72`): Ga ≤ 16·m·|TT|·a·log(X″+1). That is ≈ x^{1/2+ε/3+O(ε)} × budget, far too weak for H5.
6. **New confirmation of COREGM oddity 2.** `exists_data_completion` (PCh:306-309, statement SC:126-137) is proved. It says that from ASK ≤ Main + DIV-error + LoP alone one can build a record satisfying all 11 clauses of `SizeData₂`; the record takes Ga := ASK − LoP (PCh:192). So the ledger has content only through the ties to real lattices (TieLocal TG:63-82, and the Link* producers).

## 1. Statement (the live top, re-read)

- **`core_gm`** (CG:12-15): for every level Λ and every ε > 0, for all large x and every frame, host and TT, EAtH ∧ CoreAtH ⇒ Λ.Gm(x) ≤ x^{1/2+(eD+eL+7)ε}.
- **Where eD and eL come from.** `CoreAtH` (CAH:29-41) asks for C.eDiv ≤ eD and C.eLoss ≤ eL. It is produced from `ChainTied Fm eD eL …` (TG:97-114) by `tiedCore_of_chainTied` (`PrimitiveCosets/LevelGmLeOnFamilyScales.lean:13-26`).
  - `ChainTied` comes from `FamilyClassConnected` (DNV:13-15), which `topDesWin` proves with its own (eD, eL) (DW:25).
  - The live call is `topDesWin … 2 3 2 0` (TS:52), so eD = 2 and eL = 0.
  - The LinkGLOBAL supplier `linkGLOBAL7_pk` (LSS:468-511) returns `LinkGLOBAL7 Fm Cabs CH C0 Cabs 0` and calls `linkCore` with eL = 0. Its Data is `M.data` (QLD:464-504) and its Consts are `mkC … Cabs … eL CH` (LSS:291).
  - *(inferred)* The hop from `hgl.2` (TS:52) to `linkGLOBAL7_pk` goes through `global_link_of_part_statements_with_delta` (`.../GlobalLinkOfPartStatementsWithDelta.lean:10-24`, grep only). `windowInequality_of_artinInputs` was not opened.

## 2. Argument: the ledger

Fix x, the family member i0 and a unit u0 ∈ A0. Every quantity below is a field of `Dd = M.data` (QLD:464-504), tied to lattices by TieLocal (TG:63-82). Notation:
- ΣA = Σ_t a_t; nT = |TT|; δ = |T2|/n; ph(y) = y log y − y (MB:9);
- logΩ = γ + log(π/v) − LpL (MB:88; DP2:224), with LpL = Re L′/L(1, (·/d)) (DP2:65-71, 126-127);
- s = wmean_u(μN − h) (MB:92); uF = max_u(μmaxN − h) − s (MB:94-95).

**The slope side (per u0).**

```
(L0) s − log|W| − (1−δ_p)⁻¹[4uF·log(1+HH/uF) + (η+4√e)HH]  ≤  μCC                      SlopeIneq MB:151-156
       Bost; proved (`joint_a_ramified_holds` [SLOPE]); supplied as Frame_at QLD:188-193, FrameF QLD:258-260; HH = x^CH·b (QLD:498)
(L1) μCC + h(u) − Fo  ≤  Σ_t [m(ph(a_t) − a_t logΩ) − a_t log T(u)]
                         + cDiv·nT·a·La + cDiv·m(B0+Nc)·x^{eDiv·ε}                          DIV MB:118-121
       = LinkDIV_at (vii) GTI:82-84 with Cabs = eDiv = 2; producer divClausesR_of CGT:118, 210-245 (sub-ledger D1–D5)
(L2) μM(u) + Ga + Fo − Ee(u) − Lo5(u)  ≤  μN(u),
       Lo5 = cSl1·IO + cSl1·nT·m(a/k+b′)·log T + cSl1·X″ + 1                                  QSB:15-17, 22; SlopesN_at QLD:181-183
(L3) −cSlope·nT·a·La(1+m/k)  ≤  μM(u)                                                        Slopes MB:140
(L4) Ee(u)  ≤  m(ΣA·lg + cE·B0)                                                              EComp5 QSB:24-25 → LoC:32-35
(L5) Lam5 := Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − cCount(La + m²La/k)  ≤  log T(u)             Count5 QSB:27-30; LoC:17-19
```
Adding (L1)–(L5) for each word u (the two Fo's cancel), then taking the d_u-weighted mean, gives `s_lower5` (LoC:50-52):
```
(L6) Ga + μCC − K5v5 − wmean_u Lo5  ≤  s,
       K5v5 = cSlope·nT·a·La(1+m/k) + m(ΣA·lg + cE·B0) + SDiv − ΣA·Lam5 + EDiv              LoC:21-23
       SDiv = Σ_t m(ph(a_t) − a_t logΩ),  EDiv = cDiv·nT·a·La + cDiv·m(B0+Nc)x^{eDiv ε}       WMD:129-132
(L7) SDiv − ΣA·Lam5 + m·ΣA·lg  =  Main + ΣA·cCount(La + m²La/k)     [exact]                  key_identity5 LoC:105-107
       Main = Σ_j Σ_t a_t (log a_t − 1 − γ + LpL − mean_ρ log w_{jρ})                          MB:107-109
(L8) uF ≤ K3 + wmean Lo5   (QSB upper bound, Slopes upper, HComp, EComp5, Count5 third clause)   LoC:81-83; K3 WMD:138-139
```
(L0) + (L6) + (L7) + (L8), with HHBound (MB:158-159) and FParams (MB:161-163), give `Ga_bound5` (LoC:113-120):
```
(L9) Ga  ≤  Main + log|W| + K0v5 + wmean Lo5
            + (1−δ̄)⁻¹[4 log(1+x^cHH)(K3 + wmean Lo5 + b) + (η̄+4√ē)·x^cHH·b],
       K0v5 = ΣA·cCount(La+m²La/k) + EDiv + m·cE·B0 + cSlope·nT·a·La(1+m/k)                  LoC:25-27
```

**The gain side, and the closing of the chain.**

```
(L10) ASK − Ga ≤ LoP = cLoss·nT·m·b·x^{eLoss ε}  (eLoss ≤ eL = 0),   IO ≤ LoP              LossBounds QSB:34-35, MB:105
        from Loss_at QLD:203-210 (supplier LossesSmallShares LSS:298-299, Loss_at … C 0)
(L11) ASK(u0) ≤ Main(u0) + ErrX5at(u0)                                each_unit_bound_statement LoC:175-197
        ErrX5at = ΣA·cCount(La+m²La/k) + EDiv + m·cE·B0 + cSlope·nT·a·La(1+m/k) + log|W| + LoP + MLo5
                  + (1−δ̄)⁻¹[4 log(1+x^cHH)(UBar5 + b) + (η̄+4√ē)x^cHH·b]                      QSB:45-54 (MLo5 :37-39, UBar5 :41-43)
(L12) ErrX5at ≤ x^{(eDiv+eLoss+3)ε}·ErrText,  ErrText = nT·a(1+m²/k) + m(B0+Nc)                errX5at_le PCh:613-672; EW:16-19
(L13) gapA(u0) := Σ_t Σ_j [ASK(a_t,t,w_{u0,j}) − Re MAIN(a_t,w_{u0,j})]  =  ASK(u0) − Main(u0)
        ≤ x^{CErr·ε}·[nT·aE(1+m²/k) + m(2n·m·b·x^ε + |T2|·k·b·x^ε/(n·n·x^{−ε}))]             ch_top CT:37-72; bracket EW:133-135
        (Main = Σ_t Σ_j Re MAIN by ch_top_main_eq CT:11-35; BNBounds is an equality on the live path, LSS:250-262)
```

**The bridge to Gm.**

```
(L14) for each t, j:  ASK − MAIN = De  [exact]                                                  ch_balance CB:200-202
      Re Th(u0,t) ≤ Re De + 2f(3(x+1)(η+1) + (x+1)·b·θ)   (thick w → b; thin dropped by ThinScales) th_le CC:75-81
      Σ_{u0∈A0} Th = |A0|·b·(δ/2)·Σ_{ψ∈PsiA} ψ(e1 t)·G_ψ(a_t/b)                                 sum_Th CC:56-62
      ⇒ nT·m·b·(δ/2)·(GmA − SigA − 4x^{1/2+ε})  ≤  Err + 2·nT·m·b/x                             core CC:283-289; one_char → hY CC:426-440
(L15) GmA − SigA ≤ x^{1/2+(C+3)ε}  (C = eD+eL+3)                                                 GrowthSizeBound GB:119-122; CC:441
      Gm = GmA (gmA_eq), SigA ≤ 4o·x^{1/2+ε} (bdG), 1+4o ≤ x^ε  ⇒  Gm(x) ≤ x^{1/2+(eD+eL+7)ε} = x^{1/2+9ε}   CG:55-74
```

**DIV sub-ledger (what makes (L1)).** Producer `divClausesR_of` (CGT:184-245). Its clause 3 (CGT:118) reads μ_cols − meanLog κ + hu − 2·FoOfR ≤ rhs. It becomes (L1) through two ties: hu − meanLog κ = h (`hTie`) and L.Fo = 2·FoOfR (`foTie`) [DIV].
```
(D1) μ(RR_base^∨) ≤ meanLog κ + Σ_j lcv(M_j)/D + 2Σ_j Σ_{y∈Tw} lw·F + LG + Σ_j(E1_j + E2_j) + E3   BoundsMu SO:72-74 (via IndefSide.boundsMu, CGT:211)
(D2) Σ_j l3_j ≤ Σ_j Σ_ρ pq_j·w_{jρ}·logΩ + El3   (lcv/D ≤ l3_j [WHERECONG, IU:333-334])         L3main CGT:87
(D3) μ_cols − meanLog κ ≤ mu0 + [3de(mu0+hh+28la) + 28la],  bracket ≤ 1 + C0·m·lam0             passage CGT:216-239
(D4) mean_v log‖B_u‖_v² ≤ hu − meanLog κ;  hu = hA + Σ_j(hB_j − hX_j)                            CGT:114-117, 204-209; INP:188-198
       hA = −Σ_t a_t log T + Ch(…)La;  hB_j = Σ_ρ[Σ_i ph(ν_{jρi}) − (Σ_i ν_{jρi})·logΩ] + Ch·f·Nn²(La + m³L);  hX_j = Σ_ρ logH_{jρ} − Ch·f·nV²·Lp
(D5) μ + hu − 2Fo ≤ rhs = Σ_t[m(ph(a_t) − a_t logΩ) − a_t log T] + (50C0+10)·nT·a·La + 60ce·m·x^ε(B0+Nc)   divIneq DHB:131-134; INP:200-203
       uses El3 + LG + Σ(E1+E2) + E3 ≤ errB = ce·m·x^ε(B0+Nc) (CGT:89; INP:205-206) and the RecNums fields
       weight_height_sum_le (INP:90), weight_sum_eq (INP:92), |pq_j − k| ≤ m (INP:136), |logΩ| ≤ La (INP:138)
```
*(inferred; the body of `divIneqRecord` was not re-read)* The logΩ cancellation in (D5):
- +Σ_j Σ_ρ pq_j·w·logΩ from (D2) against −Σ_j Σ_ρ(a_t[ρ∈TT] + k·w + δ)·logΩ from hB leaves −m·Σ_t a_t·logΩ.
- The residual is Σ_j Σ_ρ (pq_j − k)·w·logΩ − Σ δ·logΩ. Given |pq_j − k| ≤ m and w ≤ 2b (INP:134), it is ≤ 2m²·f·b·La ≈ 2m·B0·(La/x^ε).
- So only the per-j bound is needed, not Σ_j pq_j = mk.
- Likewise the hook terms: Σ_i ph(ν) − logH ≤ ph(a_t)[ρ∈TT] + eE leaves m·Σ_t ph(a_t).

### 2a. Sizes (live parameter record)

The record is fixed by these lines:
- `Scale`: L = x^ε, b = e^L, a = xb, X′ = e^{x^{ε/3}}, b′ = a/X′, w″ = b′/(xn), X″ = a/w″ = xnX′, and 0 < ε < 1/52 (DP2:9-47);
- `RankVal` (RV:28-32), and f = 2n (HCl:153-154);
- a_t ∈ [a, a + a/(k·x^{13})] (DP2:80);
- B0 = f·m·b·x^ε = 2n·m·b·x^ε and Nc = |T2|·k·b·x^{2ε}/n² (DA:200-206, LSS:250-262);
- La ≤ 2x^ε (QLD:234); δ ≥ x^{−ε} (QLD:242); nT ≥ x^{−ε/8}·n/2 (LSS:281-289 via `ChosenTT`);
- (η̄+4√ē)·x^{CH} ≤ 6 (QLD:258-260); δ̄ = e^{−x^{ez/7}} (QLD:502).

Resulting sizes: n ∈ [x^{2+8ε}, 2x^{2+8ε}]; m ∈ [1, 2]·x^{1/2−ε/16}; k ∈ [1, 2]·x^{9/2+10ε}.

The signal unit is U = nT·m·b·δ/2 ∈ [x^{5/2+6.8ε}/4, 2x^{5/2+8ε}]·b (CC:289).

| term (line) | size | /U |
|---|---|---|
| ASK, Main (L11) | ≈ m·nT·a·x^{ε/3} | ≈ x^{1+4ε/3} |
| Fo, μN, h, Σ l3, Σ hB (L1, L2, D) | ≈ m·k·f·b·x^{O(ε)} [ACCOUNT] | ≈ x^{4.5+O(ε)} (cancel exactly or to relative x^{−4}) |
| ΣA·cCount·La(1+m²/k) (Count5) | ≤ 4cCount·nT·a·x^ε | ≤ 8cCount·x^{1/2+2.07ε} ("x/m") |
| cDiv·nT·a·La (DIV boundary) | ≤ 2cDiv·nT·a·x^ε | ≤ 4cDiv·x^{1/2+2.07ε} ("x/m") |
| cSlope·nT·a·La(1+m/k) (source floor) | same | same ("x/m") |
| cDiv·m·B0·x^{2ε} (DIV interior) | 2cDiv·n·m²·b·x^{3ε} | ≤ 16cDiv·x^{1/2+4.07ε} ("m") |
| cDiv·m·Nc·x^{2ε} | m·k·b·x^{4ε}·δ/n | ≤ 8cDiv·x^{1/2−1.9ε} ("k/n²") |
| m·cE·B0 (EComp5) | 2cE·n·m²·b·x^ε | ≤ 16cE·x^{1/2+2.07ε} ("m") |
| Bost 4log(1+x^{cHH})(UBar5+b) | (1+cHH)·x^ε × (the same three families) (PCh:650-651) | x^{1/2+O(ε)} |
| (η̄+4√ē)x^{cHH}b | ≤ 6b | ≤ 24x^{−5/2} |
| LoP (eL = 0) | cLoss·nT·m·b | ≤ 2cLoss·x^ε, i.e. x^{−1/2} of the budget |
| MLo5, log\|W\| ≤ (k−3)log 2, X″ | poly(x)·X′ or nT·m²·x^ε·a/k | o(1) |

**Total.** The Lean replaces this table by (L12)–(L13). The bracket divided by U is:
- 2aE(1+m²/k)/(m·b·δ) ≤ 8x^{1/2+2ε};
- 4nm·x^ε/(nT·δ) ≤ 8m·x^{2.125ε} ≤ 8x^{1/2+2.625ε} (using the window m ≤ x^{1/2+ε/2});
- 2k·x^{2ε}/(n·nT) ≤ 4x^{1/2+1.125ε}.

The sum is ≤ 20x^{1/2+2.625ε}. *(inferred: the body of `proposition_size_bound` was not read)* GrowthSizeBound absorbs 20x^{2.625ε} + o(1) into x^{3ε}. That needs x^{3ε/8} ≥ 26, and that is exactly the hypothesis `26 ≤ x^{3ε/8}` (GB:117, SC:77). Hence G ≤ x^{1/2+(C+3)ε} with C = CErr ≤ eD + eL + 3 = 5. **Total error = U·x^{1/2+9ε−ε} at most, and the final statement is x^{1/2+9ε}.**

### 2b. The main-term cancellation line

Combining (L9)+(L10) gives the line itself, (L11): ASK(u0) ≤ Main(u0) + ErrX5at(u0).
- **Archimedean side.** m·ph(a_t) − m·a_t·logΩ (from D4/D5) becomes Main through (L7). This is pure algebra (WMD:170-218): the log(π/v) inside logΩ cancels the log(v/π) of Count5, and the m·lg of EComp5 cancels that of Count5. What survives is a_t(log a_t − 1 − γ + LpL − mean log w) per (t, j).
- **Prime side.** ASK (FPN:84-87) is the count Σ_n Λ(n)(1−χ_{−d}(n))(a/n − w_partner)₊ + d-term. Its explicit-formula main term is MAIN = a(log a − 1 − γ + ell(chC) − mean_Φ log w) (FPN:89-91), and ASK − MAIN = De exactly (CB:200-202).
- **The tie.** Main = Σ Re MAIN holds by definition (CT:11-35, via IdentU SI:67-72). LpL = Re ell(chC) holds by `Char_at` (QLD:226) and HostAddCharCompatible (CAH:18-20).
- **The p-adic gain.** Σ_p γ_p·a·log p appears nowhere. The prime side's only link to the lattices is (L10), and Ga is an abstract sum of local gains: Ga = Σ_w sz(w, Σ_j gain_j − τ) (DP2:220), with sz(w, y) = 2·lw·e_w·y (DP2:205-206).
- **Required precision.** Main/U ≈ x^{1+4ε/3} against ErrX5at/U ≤ x^{1/2+O(ε)}, so the two sides must agree to relative **x^{−1/2+O(ε)}**.
  - Archimedean side: delivered by (L1) through LinkDIV_at (vii) / divClausesR_of; by (L5) through `Count_at` (QLD:167-171) and `countF_fam`; and by (L0) through FrameF.
  - p-adic side: required to relative x^{−1−ε/3+ε} by (L10), from `LossesSmallShares` (LSS:298-299), whose producer `hL7` is a premise of `linkGLOBAL7_pk` (LSS:472) and was not traced.
  - Inside DIV, the logΩ and Σph terms of size ≈ x^{4.5}·U must cancel to relative x^{−4} [ACCOUNT C2]. In the Lean this holds by definition (the same `logOm` symbol) together with the per-j bound |pq_j − k| ≤ m.

### 2c. One prime of each kind, p ≈ x

E0 coordinates (FPN:15-21, PTF:13-29):
- The Frobenius of p in ArithData is ((sgn(√−d), sgn(√−q)), h) (`recOf`, TG:24-32; the √−d sign is `.1.2`, ConjEMemHostFIff:31; the √−q sign is `.1.1` = psAt, ConjEMemHostFIff:68-69, DH:44).
- Φ = {g.1.1 = 0} (PTF:20). partner(t, g) = ((1,1), 0) + g + ((0,0), t) (FPN:19, PTF:24-26). Thick places are ((0,1), t+u0) with t ∈ T2 (PTF:27, 97).
- *(inferred)* `art` agrees with Frobenius on the field signs, as the file name `ArtinMapSecondEqJacobiSym` suggests; I did not open that file.

| prime | Frob_p | in ASK (FPN:76-87) | partner of i·Frob, i odd | coefficient per (t, j) | where else in the ledger |
|---|---|---|---|---|---|
| **signal** ((−d/p) = −1, (−q/p) = +1) | ((1,0), h) | yes, odd i | ((0,1), t+ih): thick iff t+ih−u0 ∈ T2 (then w ∈ [b, b+η+1]); otherwise w ≤ 2b′ (SI:46-47) | thick: 2 log p·(a_t/p − w)₊ = 2 log p·b·(a_t/b·p⁻¹ − 1)₊ + O(η log p): **the Riesz weight at n ≈ x**; i ≥ 3 gives 0. Non-thick: ≈ 2 log p·a_t/p | (L10) through Ga's places w ∣ p (TTw = all tops, DP2:168-169); in the bridge it is the g = e1(s+u0−t) = ((1,0), ·) term of De, which carries the ψ-shares (CC:16-22, 56-62) |
| **inertClass** ((−d/p) = (−q/p) = −1) | ((1,1), h) | yes, odd i | ((0,0), t+ih): a top or thin place, never thick, so w ≤ 2b′ | ≈ 2 log p·Σ_{i odd} a_t/p^i (uncapped, since a_t/p ≈ b ≫ b′ and a_t/p³ ≈ b/x² ≫ b′) | In De its Riesz length is a/w ≥ X′/2, killed by ThinScales in th_le (CC:75-81). On the slope side only through Ga ≥ ASK − LoP (the Hecke/colength or orbit route [SERVED]) |
| **split** ((−d/p) = 1) | ∈ Φ | no (IsInert, FPN:72-73) | — | 0 | Only through the constant ell(chC) = L′/L(1,χ_{−d}) in MAIN and through −G_chC, G_chpsC in De (ColourSum FPN:123-125; Gsig GB:33-34), bounded at y = x by ValuesAtX (GB:67-69). No local gain: gain = τ = io = 0 off signal/inertClass (DP2:110-111) |

So Λ(n)(1−χ(n))(a/n − w)₊ comes from the factor 2·log p on odd i·Frob ∉ Φ in ASK (FPN:86): for n = p^i, 1 − chC(i·Frob) equals 2 exactly when p is inert and i is odd. With w ≈ b at thick partners, the Riesz length is y = a_t/b ≈ x.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `each_unit_bound_statement` | LoC:175-197 | SizeData₂ ⇒ ASK ≤ Main + ErrX5at | the ledger's sum | glue (read) |
| `key_identity5`/`key_identity` | LoC:105-111; WMD:170-218 | (L7), exact | archimedean → PNT main term | glue (read) |
| `errX5at_le` (→ `core_ineq`) | PCh:613-672 | ErrX5at ≤ x^{CErr ε}·ErrText | exponent envelope | glue (`core_ineq` not read) |
| `proposition_size_bound` | GB:119-122 (statement) | GrowthSizeBound | 1/2 + (C+3)ε | glue (body not read) |
| `divClausesR_of`, `RecNums.divIneq` | CGT:184-245; DHB:131-191 | (D1)–(D5) ⇒ DIV | DIV | core inputs are hypotheses (L3 covolume, RowsU heights) [DIV] |
| `Loss_at` / `LossesSmallShares` | QLD:203-210; LSS:298-299 | ASK − Ga ≤ C·nT·m·b | (L10) | core, producer not traced |
| `LinkG_at` | GTI:122-136 | 0 ≤ gain ≤ 4·nT·a/p; Σ class sums − losses ≤ Σ gain − τ | lower bounds on gains | core (hypothesis) |
| `ch_balance`, `th_le`, `core`, `one_char` | CB:200; CC:75, 283, 202 | bridge | (L14) | standard/glue |
| `ga_le_at` | CardLiftsEq.lean:70-72 | Ga ≤ 16·m·nT·a·log(X″+1) | the only upper bound on Ga | glue; not H5 |
| `exists_data_completion` | PCh:306-309 | SizeData₂ satisfiable from ASK ≤ Main + err | shows the clause list is vacuous without ties | glue |

## 4. Oddities

1. **H5 (Ga − ASK ≤ budget) is not in the Lean**, as a hypothesis or as a theorem; greps in §5. If H5 fails, the hypotheses are jointly false for the real lattices, not contradictory in form: (L9) bounds Ga above by Main + Err, and every lower bound on Ga used is ASK − LoP.
2. **Satisfiability of the parameter inequalities.** I checked each against the record of §2a; all hold for x ≥ x₀(ε):
   - x·m ≤ k (2x^{3/2−ε/16} ≤ x^{9/2+10ε});
   - k ≤ n²x^{1/2−ε} (needs 2 ≤ x^{5ε});
   - x^{1/2−ε} ≤ m ≤ x^{1/2+ε/2};
   - X″ = xnX′ ≤ a and k·b′ ≤ a (need nX′ ≤ b and k ≤ X′);
   - Nn² ≤ b, m³Nn²L ≤ b, k·Nn ≤ b, Nn·w″ ≤ b, b′Nn ≤ a, m·k·b′ ≤ a (INP:142-158; Nn ≈ x^{399} [ACCOUNT], against b = e^{x^ε});
   - 6f(x+1)(η+1) ≤ b/x (etaSz free and positive, DP2:145, 164);
   - 2f(x+1)e^{−c6 x^{ε/8}} ≤ 1/x;
   - log|W| ≤ (k−3) log 2 (if |W| ≈ Γ² with log Γ = CGam·m⁵·f·x^ε (DP2:176): m⁵·f·x^ε ≈ 128x^{4.5+8.7ε} ≪ k log 2);
   - b^{m/2} ≤ T and log T ≤ cCount·m·L (DP2:252, QSB:31);
   - 26 ≤ x^{3ε/8}.

   No pair contradicts; the record itself assumes ε < 1/52 (DP2:14). Not checked: the frame bounds (FrameF, LinkS, LinkIRR), which are existential, and t_win ≤ x^{Ct} (DP2:171-172).
3. **The window used is wider than the record.** GrowthSizeBound is proved for m ≤ x^{1/2+ε/2} (GB:113). The record has m ≈ x^{1/2−ε/16}. The ε/2 slack costs about 0.56ε in the exponent and is part of the 3ε.
4. **The precision demanded of the gain side exceeds what the conclusion needs.** With eL = 0, LoP = cLoss·nT·m·b. So the m-fold gain must reproduce ASK (size ≈ m·nT·a·x^{ε/3}) to absolute O(nT·m·b), i.e. relative x^{−1−ε/3}. The archimedean side needs only x^{−1/2}. This is a hypothesis of `LossesSmallShares` (LSS:298-299) and is worth a reader. *(inferred)* It is consistent with the per-prime O(1) digit-sum loss times m·nT tops, only if the Σ over primes of those O(1) losses carries no log x.
5. The signs of the two L′/L agree: logΩ has −LpL (DP2:224), so −m·a·logΩ contributes +m·a·LpL. That matches MAIN's +a·ell(chC) (FPN:90). Both are the (·/d) quadratic character (DP2:65-71); for d ≡ 3 mod 4 that equals χ_{−d}.

## 5. Coverage

Read in this pass:
- MB:1-229; QSB:1-84; LoC:1-246; WMD:125-222; SC:1-252; GB:1-183; EW:1-165; FPN:1-142;
- PCh:190-311, 600-694 (and the theorem list); CG:1-74; CAH:1-51; SI:1-100; CT:1-76; CC:16-30, 56-62, 75-84, 202-212, 283-446; CB:196-206;
- DP2:1-274; RV:15-60; DA:195-211; QLD:150-270, 455-510; GTI:25-168; LSS:1-130, 225-310, 455-515; TG:20-127; `LevelGmLeOnFamilyScales.lean`:1-39;
- DW:1-35; TS:28-57; DNV:13-21; CGT:40-130, 184-250; INP:60-215; DHB:100-195; SO:17-80;
- HCl:1-252; DH:1-80; ConjEMemHostFIff:55-80 and the grep at :30-31; `GaloisToProductIsIso.lean`:25-50; RecH:1-27; PTF (grep: InPhi, cconj, topPl, thickPl, IsThickAt);
- CardLiftsEq.lean:60-80; LocalQuadraticParts.lean:700-720; ChainLatticeSizesModelEventually.lean:1140-1155.

Greps for H5 (all run over the whole tree):
- `\.Ga( u0)? ≤|Ga u0 - D\.ASK|L\.Ga - |Ga - .*ASK|\.Ga\) ≤`
- `Ga\b.*ASK|ASK.*\bGa\b`
- `Ga\b.*≤.*ASK`

The hits are only ASK − Ga ≤ … (QSB, QLD, LocalQuadraticParts, WindowSettingSatisfiable, PrimeClassLossHypothesesSatisfiable, OneLeThresholdMulPowers, DiscriminantSettingSatisfied), the absolute-value constant lemma in ChainLatticeSizesModelEventually, `ga_le_at`/`GaugeFormBoundOfUniformSize` (Ga ≤ poly·b), and `compl`.

Not opened:
- the bodies of `proposition_size_bound`, `core_ineq`, `divIneqRecord`, `joint_a_ramified_holds`, `gmA_eq`, `sigA_le`, `windowInequality_of_artinInputs`;
- IU:333-334 (cited from WHERECONG); `ArtinMapSecondEqJacobiSym.lean`;
- the producer `hL7` of `LossesSmallShares`; `global_link_of_part_statements_with_delta` (grep only).
