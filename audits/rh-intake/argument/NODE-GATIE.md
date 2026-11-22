# NODE-GATIE: how the gain Ga is tied to real lattices, on both sides, and what the LoP budget really pays

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(inferred)* = my reading. [NODE] = taken from that node, not re-read. Nothing was compiled or run.

Abbreviations:
- `QSB` = `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`; `MB` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`
- `QLD` = `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`; `LSS` = `.../GlobalSchurBounds/LossesSmallShares.lean`
- `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`; `IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
- `LMin` = `.../GlobalSchurBounds/LinkMin.lean`; `LXL` = `.../GlobalSchurBounds/LogXLowerFamilyOfTheorems.lean`; `LGl` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean`
- `TS` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean`
- `TDN` = `.../GlobalSchurBounds/TopDensityNGeSixteen.lean`; `CGF` = `Formalism/SizeWindowBrackets/ClaimGaFree.lean`
- `PP` = `Formalism/LocalToGlobal/GlobalTheory/PlacesP.lean`; `PMin` = `.../GlobalTheory/PlacesMin.lean`
- `DDD` = `Formalism/LocalRingCardinality/DataDIVDefs.lean`; `GTI` = `Formalism/SharpRestriction/GlobalTheoremInputs.lean`
- `RB` = `Formalism/LocalToGlobal/Divisibility/RecBridge.lean`; `CGT` = `.../Divisibility/ConstantGeTwentyEight.lean`; `SJF` = `Formalism/LocalToGlobal/GroupLattices/ServJointF.lean`
- `LQP` = `Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean`; `WDS` = `.../Divisibility/WeightDegreeSizes.lean`; `AGP` = `Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean`
- `WJS` = `Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`; `DE` = `Formalism/LocalRingCardinality/DataErr.lean`
- `LRS` = `Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean`

## 0. Verdict

**No ESCALATE.** The brief's premise has to be corrected first.
- "ASK − Ga ≤ LoP" is **not** where divisibility is used. It compares two explicit formulas.
- The divisibility of the real maps enters only on the other side, through the lattice N_u, and it enters at the same precision as the archimedean side.

1. **Ga is defined, not existential.**
   - The Lean defines Ga = Σ_{w∈supp} 2·lwP(w)·e_w·(Σ_j gainD_j(w) − τ(w)) (DP2:220), built from the record fields `gain`, `tau` (DP2:93, 96).
   - On the live path those fields are pinned by `ParametersFill` (IRZ:401-411):
     - L.gain j w = gainP(…, p, j) at every supp place over a signal or inertClass prime;
     - L.tau w = tauP;
     - L.io w = ioP.
   - `not_inert` (DP2:122-123) forces gain = τ = io = 0 at every other place.
   - So Ga is a definite real number, an explicit piecewise-linear function of the a_t/p^e and the fills [LOSS, PAIRING].
2. **Lower clause (LossBounds).** It is a formula identity up to LoP. It is not a divisibility statement.
   - Its producer is now traced on the live path. The live supplier is `linkGLOBAL7_items`, not `linkGLOBAL7_pk` as NODE-LEDGER said.
   - Chain: TS:35 `link_gl` → `hgl.2` (TS:55) → `FamGLmin.link8` (LXL:71) → `link7` (LXL:60) → `linkGLOBAL7_min` (LMin:723) → `linkGLOBAL7_items` (LMin:693).
   - There, `lossF_of_7 Fm (stLoss7 eps Fm cTT cBad lG) cW` (LMin:721), and `stLoss7 = losses_of_small_share_weight` (LRS:165, 86).
   - `global_link_of_part_statements_with_delta`, the hop NODE-LEDGER inferred, has **no caller** (grep in §5). `linkGLOBAL7_pk` is a twin and is off the live path. Both use the same `stLoss7`.
3. **Upper side: the tie to the real lattices.** It runs through one symbol, the per-place exponent
   sg(u, w) = Σ_j (gainD_j(w) + F_j(w) − E_{u,j}(w)) (DP2:215).
   - **Source lattice.** The Lean *defines* the source lattice of the DIV map by `NprimeDef`: N_u = (∏_w 𝔭_w^{−⌊e_w·sg(u,w)⌋})·NuLat_u (DDD:16-25).
   - **Slope of N_u.** Its slope is computed exactly by `mu_eq` (PP:129-169) as
     μ(N_u) = μ(Mram) + Σ_w 2·lwP·⌊e_w·sg⌋ − colength.
     So μ(N_u) ≈ μ(M_u) + Ga + Fo − Ee by construction. That is `SlopesN_at` (QLD:180-182), via `Places_at`/`slopesN_at_of` (TDN:1516-1539) and `places_at_of` (PP:297-439).
   - **Integrality of the DIV map.** N_u can be the source of the DIV map only if Bk_u(N_u) ⊆ cc (`OneMapIntoCC`, LinkDIV_at first clause, GTI:78).
     - That inclusion is `oneMap_of_coord` (RB:33) applied to the clause `val2` (CGT:105-106).
     - `val2` comes from `val2AllAtRF` (SJF:84-104), which consumes `LocalQuadraticParts.adm2` (LQP:206-210): for every φ ∈ NuLat_u and every F, the period perCol_u(j_N φ, F) has w-valuation ≥ ⌊e_w·sg(u,w)⌋. The `sg` here is literally `L.sg u w`.
   - **Where adm2 comes from.** On the live path it is `admissible_level_two` (AGP:214-237). Off the level and type primes it uses `admissible_off_twist_places … (gainLe_of_fills hF hcs) hS.2.1`, and hS.2.1 is `WJS.Conclusion1` (WJS:97-101, `Serv` :241-243).
   - **What Conclusion1 says.** For every x ∈ InNP, the **actual** m-fold column map (D.mem u).C.col of (D.fm u).lat 0, or its twisted version, lands in ϖ^{e·totS}·(lat m) at w (`ColGe`/`VGe`, WJS:19-35). Here totS = Σ_j (gainS + F − ES) + vDG (WJS:76-77).
   - **From Conclusion1 to adm2.** The step is `period_integral_off_levelPrime`'s `hle` (WDS:973-1010). It uses three facts:
     - gain ≤ gainS (`GainLe`, from ParametersFill);
     - E = Eval = ES (`EDef`, DE:171-172; `ES`, WJS:70-71);
     - therefore sg + vDG ≤ totS.
   - From there the chain goes into NODE-SIGNAL/ORBIT: `sum_over_primes_service` → `noOp_of`/`chain_ge` → `thmAJetA` at signal places, and UAt/`main_ind` at GIdx places.
4. **The same Ga on both sides.** No slack. The same record fields (gain, τ, F, E, supp) appear in:
   - Ga, Fo and Ee (DP2:218-222);
   - the exponent of N_u (DDD:16-20);
   - the divisibility the Lean proves (adm2/Conclusion1).

   Every one of these fields is pinned (ParametersFill; `EDef`; `FDef`). Making Ga larger would raise sg, and then adm2 (a proved theorem about actual maps) would be needed at the larger exponent.
5. **Accounting (§2c).** LoP = (3|K|+13)·|TT|·m·b (LRS:101, 145-161) pays only formula-against-formula differences.
   - The losses of the real divisibility relative to the gain formula are booked in E. Their per-lift total is bounded by adm11 (LQP:315-321) at C·B0 = C·f·m·b·x^ε per lift. This is the "m" term of the budget, relative precision ≈ x^{−1/2+O(ε)}, not x^{−1}.
   - Rounding to integer valuations happens **once per place**, on the whole exponent sg. It costs ≤ C·X″ (LinkMu, GTI:69-70), and X″ = x·n·e^{x^{ε/3}} ≪ b.
   - The errF loss at signal primes (γ_p·|tops|·b per prime per lift, `EatI`, DE:145-155) totals ≈ |TT|·m·b·log X″ ≈ |TT|·m·b·x^{ε/3}. That is larger than LoP but sits in Ee ≤ m(ΣA·lg + cE·B0), well inside m·B0.
   - SUMMARY §11's "log log X″" omitted the log p weight. The correct figure is log X″. It is still inside the budget.

## 1. Statement

**Lower clause.**
- `LossBounds` (QSB:34-35): ∀ u0, ASK(u0) − Ga(u0) ≤ LoP ∧ IO(u0) ≤ LoP, with LoP = cLoss·nT·m·b·x^{eLoss·ε} (MB:104).
- `Loss_at C eL` (QLD:203-210) has two clauses:
  - IOsum ≤ C·|TT|·m·b·x^{eL·ε};
  - for every arithmetic reading (Reads, HEq to arithOf host): Σ_{t∈TT} Σ_j ASK(AD, N, a_t, t, w_j) − L.Ga ≤ C·|TT|·m·b·x^{eL·ε}.
- `LossesSmallShares Fm` (LSS:298-299): ∃ C x0, ∀ x ≥ x0, ∀ i, ChW_at → Loss_at (Fm.L x i) C 0. `LossFS` (LSS:13-21) is the version for the chosen weight vectors.
- On the live path, LSS's `lossF_of_7` is fed by `losses_of_small_share_weight` (LRS:86-163) with C = 3|K|+13 (LRS:101).

**Ga and its companions** (DP2:205-222).
- sz(w, y) = 2·lwP(w)·e_w·y.
- gainD_j(w) = 0 if p ∈ drop, else gain_j(w).
- sg(u, w) = Σ_{j∈[1,m]} (gainD + F − E).
- Fo = Σ_j Σ_w sz(F); Ga = Σ_w sz(Σ_j gainD − τ); Ee(u) = Σ_j Σ_w sz(E).

**Upper clause** (`SlopesN_at`, QLD:180-182):
- μmax(N_u) ≤ μmax(M_u) + Ga + Fo − Ee + C·m·B0;
- μ(M_u) + Ga + Fo − Ee − LoU ≤ μ(N_u), with LoU = C·IOsum + C·|TT|·m·(a/k + b′)·log T + C·X″ + 1 (QLD:176-178).

**Answer to task 1.** Ga is *defined* from record fields. Those fields are pinned to explicit formulas, not to lattice indices.
- The clauses that tie it to real objects:
  - (i) `ParametersFill` pins gain, τ, io to the formulas, and pins the count's partner weights and the family weights wj to the same `fill` (IRZ:403-406);
  - (ii) `NprimeDef` defines N_u with exponent ⌊e·sg⌋ (DDD:22-25);
  - (iii) `NuDef`/`LinkG.1` give the colength of NuLat in Mram as ≤ duS·(τ + io) (DDD:48-55, GTI:122-126);
  - (iv) adm2/Conclusion1 prove that the actual period of the actual chain image is divisible to ⌊e·sg⌋;
  - (v) `EDef`, E = Eval (DE:159-172).
- (iv), combined with (ii) and DIV, is what forces Ga to be at most the true divisibility (up to E): the "upper bound applies to the same Ga".
- The lower clause is a theorem about the formula. It needs no lattice.

## 2. Argument

### 2a. Lower bound: producer chain (task 2, lower half)
| # | name | file:line | content |
|---|---|---|---|
| 1 | `shape_closed_link_n_of_green` | TS:35, 52-55 | `hgl := link_gl …`; `hgl.2` is the LinkGLOBAL argument of `topDesWin … 2 3 2 0` |
| 2 | `GlobalTheory.Top.link_gl` | LGl:14-31 | `hGLm.link8 2 3 …` |
| 3 | `FamGLmin.link8` → `linkGLOBAL_of_7w` | LXL:71-75, 56-58 | LinkGLOBAL from LinkGLOBAL7 and ChosenWall |
| 4 | `FamGLmin.link7` → `linkGLOBAL7_min` → `linkGLOBAL7_items` | LXL:60-65; LMin:723-736, 693-721 | `linkCore … hSN … (lossF_of_7 Fm (stLoss7 eps Fm cTT cBad lG) cW)` |
| 5 | `stLoss7` = `losses_of_small_share_weight` | LRS:165, 86-163 | `loss_setting_family`, `joint_discriminant_eventually`, `Ga_at`, `ASK_at`, `IO_at` |
| 6 | the per-prime local clause | [LOSS, SERVED] | `LinkG_at.2.2` (GTI:127-133) ← `GainBoundAll`/`StarAll` ← `gU_lower`/`ask_add_Mn` (identity max(0, A−w) + min(A, w) = A) |

The divisibility theorems are **not** in this chain. Their absence is correct, not a gap: Ga is the formula, and the formula is ≥ ASK − LoP by arithmetic.

### 2b. Upper bound: the consumer and producer chain (task 2, real half)
| # | name | file:line | content |
|---|---|---|---|
| U1 | `slopesNF_of` ← `placesF_min'` | LMin:714-715; TDN:1544-1546; PMin:23-131 | SlopesN from Places_at |
| U2 | `places_at_of`, `mu_eq`, `muMax_le` | PP:297-439, 129-169, 171-243 | μ(N_u) = μ(Mram) + Σ 2lwP⌊e·sg⌋ − Σ 2lwP·len·e/rank (exact). Floor loss Rd ≤ CMu·X″ (`NprimeMuR`, GTI:69-70; PP:425-439). Colength via hG1 = LinkG.1 |
| U3 | `ClaimGaFree.HypLow/HypLow2/HypHigh` | CGF:65-101 | the algebra turning U2 into SlopesN (IO/(1−de), de·Ta/(1−de) with Ta ≤ b², de ≤ 2f/T, T ≥ b³) |
| U4 | `NprimeDef` | DDD:16-25 | N_u := 𝔭^{−⌊e·sg⌋}·NuLat_u |
| U5 | `OneMapIntoCC` ∈ LinkDIV_at | GTI:78; DataArith.lean:180 | Bk_u(N_u) ⊆ cc |
| U6 | `wordFacts_of` / `DivisionPackageFace.wordFacts` → `linkDIV_L2R_face` → `divClausesR_of` | RB:128-152, 633-640; CGT:184-192 | the first clause via `P.cols.intoDual … I.val2` |
| U7 | `val2AllAtRF`, `perToVal2F` | SJF:84-104, 45-82 | val2 at exponent ⌊e·L.sg u w⌋ from adm2, by span induction over NuLat |
| U8 | `adm2` ← `admissible_level_two` (live: `famU`) | LQP:206-210; AGP:214-237, 262-300 | the period of j_N(φ) for φ ∈ NuLat has valuation ≥ ⌊e·sg⌋ |
| U9 | `admissible_off_twist_places` (twin of `period_integral_off_levelPrime`) | AGP:236 (statement :171, body not read); WDS:973-1010, `hle` at :989 | InNP split (VV = ∅ ⇒ Sram; else NP); `hle`: sg + vDG ≤ totS, using GainLe and EDef |
| U10 | `WJS.Conclusion1`, `Serv` | WJS:97-101, 241-243, 252-255 | ColGe of the actual column map at totS |
| U11 | its producers | [SIGNAL, ORBIT, CHAININD, JETA] | signal and VV = ∅ places: `sum_over_primes_service` → `noOp_of`/`chain_ge` → `split_bound_eleven_one` → `thmAJetA`. GIdx served places: `kernel_valuation_served` → UAt → `main_ind`/`LowTermBound` (`stmt_proved`, `LemmaVVolumeGeneral`) |

### 2c. Accounting (task 3)
Units: U = |TT|·m·b·δ/2. Budget = U·x^{1/2+O(ε)}. LoP = (3|K|+13)·|TT|·m·b (eL = 0). B0 = f·m·b·x^ε (DataArith.lean:200).

**What LoP pays** (formula against formula, per (top, lift), summed over p with weight 2 log p) [PAIRING, SERVED, LOSS]:

| source | how it is handled | size |
|---|---|---|
| caps | identical by ParametersFill (count cut-off = family weight = cap); identity ask + Mn = γ_p·A | 0 |
| floors | **none**: gainP and ASK are both real piecewise-linear in a/p^e (IRZ:247-258, 355-359) | 0 |
| shift a → a − 2cG, cap → fill + cG, dl | inside lo(p): C(cG+η)·log_p 2a per active e; poly(x) per prime; Σ_{p≤X″} ≈ X″·poly(x) | ≪ b |
| top offset b′/x (and η) | lo(p) term b′/x for p < X′: Σ_{p<X′} 2 log p·b′/x ≈ 2X′b′/x = 2a/x = 2b | **the O(b) per (top, lift) that LoP is sized for** |
| V-top surplus vs τ | exact pairing (kinkHH) plus Pr | O(b/n) [PAIRING] |
| dropped or non-served primes, p > X″, p = d, bad orbits | whole ask charged, gain 0 | ≤ x^{−1+O(ε)}·U each [SERVED] |
| small primes | none inert below x^{ez/5} [SERVED] | 0 |

**What the real divisibility is allowed to lose** (not LoP):

| source | where | size (my estimate) |
|---|---|---|
| integer rounding ⌊e·sg⌋, once per place | Rd ≤ CMu·X″ → LoU's C·X″ (PP:425-439) | ≤ 2θ(X″) ≈ 2X″ ≪ b |
| Legendre digit sums, de/dl, N(j−1)N(j)·log_p | EatI dl1, dl2 and N·N terms (DE:145-155) → E | per lift Σ_{p≤X″} poly(x)·log a ≈ X″·x^{≈800} ≪ b |
| v_p(DGam) | Eval head (DE:160-162) | Σ_p log p·v_p(DGam) = log DGam = poly(x) |
| γ_p·Wc loss (errF) | EatI γ_p·|topsBC|·(b+η+1+3Sc) → E | per lift ≈ 2|TT|·b·Σ_{p≤X″, inert} log p/p ≈ |TT|·b·log X″; over m lifts ≈ |TT|·m·b·x^{ε/3}, i.e. ≈ x^{ε/3}·LoP |
| c6·Σw/p | EatI → E | per lift ≈ c6·f·b·log X″ |
| kindA FOrb term | EatI `max 0 (Σ_{kindA} FOrb/nP)` → E | kindA positions are Bool-false (tops and thin), weights ≤ 2b′, so ≈ k·f·b′ ≪ b *(inferred: thick weights sit only at Bool-true places, PTF via LEDGER §2c)* |

- E is charged by adm11 (LQP:315-321): Σ_{w ∉ g-types} |sz(E)| ≤ C·B0 per lift. This is LinkDIV_at clause (GTI:82-83) → EComp5 (QSB:24-25).
- So the total admissible loss is ≈ m·C·B0 = 2C·n·m²·b·x^ε ≈ U·x^{1/2+O(ε)}. errF uses only x^{ε/3}/(m·x^ε) of that.

**Why the signal-prime count is exact.** The signal gain is g0 = Σ_{e odd}(al/p^e − capU)₊ − dl, with capU = fill(true, ·) + cG = the thick weight wj ∈ [b, b+η+1] (IRZ:132-135; NODE-SIGNAL).
- So the Riesz term b·(a_t/(b·p) − 1)₊ is reproduced symbol for symbol.
- The only difference is the poly(x) shifts cG and dl. Over π(X″) primes these total X″·poly ≪ b.
- Exactness comes from neither telescoping nor averaging. Two facts give it:
  - (1) the gain is defined by the same piecewise-linear expression as the count;
  - (2) the true divisibility is required only to that expression minus E, with E ≤ C·B0 per lift, plus one floor per place.

### 2d. Slack check (task 4)
1. **Could Ga exceed the true divisibility?** No.
   - Ga's gain and τ are the fields that enter sg, hence N_u.
   - adm2 must hold at the same ⌊e·sg⌋.
   - The only inequality in the step is gain ≤ gainS (`gainLe_of_fills`, WDS:931-934, via ParametersFill), and gainS equals gainP except at IsCs ⊂ drop (`isCs_drop`) and at Exc primes.
   - *(inferred)* At Exc primes gain = 0 by `gain_g`/`not_inert`; this was not checked for condN primes.
2. **Is the upper bound applied to a different quantity?** No.
   - SlopesN uses μ(D.div.Nu u), and Nu is fixed by NprimeDef.
   - DIV uses the same D.div.Nu (OneMapIntoCC, htMap). `dcPt` (SJF:41-42) identifies the DIV coordinate period Pt with D.what₂.perCol, the object of adm2.
3. **Colength.**
   - τ is subtracted in Ga. NuLat must have colength ≤ duS(τ + io) (LinkG.1, PP:300-303).
   - io and Ta enter LoU. IO ≤ LoP by Loss_at clause 1.

## 3. Children
| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `adm2` ← `admissible_level_two` ← `Serv`/`Conclusion1` | LQP:206; AGP:214; WJS:97, 241 | the actual chain image is divisible to Σ_j(gain + F − E) at every inert place | **the only tie of Ga to divisibility** | core (producers in SIGNAL/ORBIT/CHAININD) |
| `NprimeDef`, `mu_eq`, `places_at_of` | DDD:22; PP:129, 297 | N_u = 𝔭^{−⌊e·sg⌋}NuLat; exact slope formula | puts Ga into μ(N_u) | glue (read) |
| `val2AllAtRF`, `divClausesR_of` clause 1, `oneMap_of_coord` | SJF:84; CGT:189-192; RB:33 | adm2 ⇒ Bk_u(N_u) ⊆ cc | makes the upper bound bite | glue (read) |
| adm11 producer `secondComplement_family_of_inputs` / `complement_two_of_items` | WDS:690; `LocalToGlobal/ClassOfRecordOfChoice.lean:148` | Σ_{w not over g} \|sz(E_{u,j})\| ≤ C·B0 for E = Eval | pays errF, dl, dG and the kindA FOrb term | **core, body not read** |
| `NprimeMuR` producer `nprimeMuR_at` | GTI:69; `AdmissibleParameterJoins/SumLogPrimeFactorsLe.lean:694` (grep) | floor loss ≤ C·X″ | floors | glue, not read |
| `losses_of_small_share_weight` | LRS:86-163 | LossesSmallShares with C = 3\|K\|+13 | lower clause | glue (read; arithmetic per [LOSS]) |

## 4. Oddities
1. **Correction to NODE-LEDGER §1 and §2b.**
   - The live LinkGLOBAL supplier is `linkGLOBAL7_items` (LMin:693), reached through `link_gl`/`link8`/`link7`/`linkGLOBAL7_min`.
   - `global_link_of_part_statements_with_delta` is unreferenced, so `linkGLOBAL7_pk` is a twin off the live path.
   - The difference: `placesF_min'` (PMin:23) supplies SlopesN on the live path, not `placesF_of`.
   - `hL7` is traced: it is `stLoss7`.
2. **Correction to the brief and to LEDGER Oddity 4.** The "relative x^{−1}" precision is demanded of formula ASK against formula Ga, which hold by identity. The real divisibility is demanded only to E ≤ C·B0 per lift, i.e. relative ≈ x^{−1/2+O(ε)}. That is the same order as DIV.
3. **errF size.** It is ≈ |TT|·m·b·log X″ (log p weight included), not log log X″. It is booked in E, not LoP, and is inside m·B0 by a factor ≈ m·x^{2ε/3}.
4. **Unverified.**
   - The adm11 bound for E = Eval (above) is the clause that certifies all the divisibility losses at once. It deserves a reader.
   - The GIdx branch of Conclusion1 needs `Ties9` to tie the LatInst Y = Fm.Gy chain to the actual column map. NODE-LOSS saw `zeroCh (Fm.Gy …)` used for LinkG's `admG1`. `Serv` takes `Fm.Gy` itself (WJS:254), so that is not the same object. I did not reopen Ties9.
5. Floors: there is one ⌊·⌋ per place, on the total exponent over all m lifts and all tops. The per-prime floor loss is therefore not multiplied by |TT|·m.

## 5. Coverage
Read in this pass:
- PROTOCOL; NODE-LEDGER, LOSS, LIVEPATH, SERVED, ORBIT, SIGNAL, CHAININD, ACCOUNT, PAIRING (all); COREGM (grep); SUMMARY:200-280.
- QSB:1-84; MB:100-110; QLD:150-310; DP2:76-130, 195-240; IRZ:395-425.
- LSS:1-40, 280-312, 455-515; GlobalLinkOfPartStatementsWithDelta.lean (all); LGl (all); LXL:1-110; LMin:690-780; TS:28-57; LRS:86-165.
- TDN:1440-1546; CGF:1-105; PMin:1-131; PP:100-440.
- DDD:1-70; GTI:60-140; StatementPl.lean:30-80 (htMap is archimedean only); RB:20-160, 600-700; CGT:90-130, 184-250; SJF:1-140.
- LQP:206-216, 260-380; GandSy.lean, GandSaj.lean (all); WDS:900-1100; AGP:214-330; WJS:19-77, 97-102, 241-256; DE:120-200; DataArith.lean:196-212; Numbers.lean:165-185; LpLower.lean:14-19; ClassOfRecordOfChoice.lean:140-200.

Greps run:
- `global_link_of_part_statements_with_delta`: only its own file;
- `linkGLOBAL7_pk`, `stLoss7`, `OneMapIntoCC`, `val2 :=`, `LocalQuadraticParts.adm2`, `UnroundedValuationBound`, `slopesNF_of`, `placesF_min'`, `def NprimeDef|NuDef|NprimeMuR`, `def FOrb`, `def lpF`, `def Compl3`, `ComplementTwo`.

Not opened:
- `secondComplement_family_of_inputs` body; `nprimeMuR_at`; `admissible_off_twist_places` body (I read its twin `period_integral_off_levelPrime`);
- `ServF`'s supplier `hServ` upstream of TS; Ties9; `askIsF`, `Ga_at`, `ASK_at` bodies.
