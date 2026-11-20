# NODE-PAIRING: delivered divisibility against the prime count, per inert prime

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `IRZ` = `Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean`
- `PCC` = `Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/PartnerCountOfCentral.lean`
- `C1G` = `Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean`
- `FGS` = `Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean`
- `UQS` = `Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean`
- `SF` = `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SizeCount/Development.lean`

## 0. Verdict (short)

1. **ACCOUNT's open point (C6) is resolved in the favourable direction.** For the constructed family, Ga − ASK is
   bounded above by about nT·m·b/n plus terms that are negligible next to b. That is far below LoP ≈ nT·m·b and far
   below the budget. The V-top surplus (≈ 2a per V-top per lift, ACCOUNT's x^{1/2} × budget) is cancelled exactly by τ.
   The cancellation is not approximate at the b′ scale:
   - `kinkHH` (PCC:369) is an **injective pairing**. Each odd-position top y is sent to the pair (nearest preceding
     even-position top s, distance e = dMinus(y)), and every e = 1 top partner of a V-top is used.
   - The `off` that `tIf` drops (it uses b_y, not fill_y = b_y + off) is returned exactly by the first sum of `Pr`.
   - What is left of Σ_V Mn is the following:
     - thin-partner terms, ≤ w″ + η each;
     - partners at distance ≥ 3 that are not nearest, ≤ a/p³;
     - copies of kaJ.

   Under `SizeFacts` (η ≤ w″/x, k·Sc ≤ w″) these total O(a/(x·n)) = O(b/n) per V-top per lift after summing over p with
   weight 2 log p. The Lean proves only the lower direction, but the upper direction follows from the same definitions
   in a few lines (§3). So (P) + DIV + SlopeIneq do not force a one-sided bias. **No hidden contradiction.**
2. **Net delivered = ASK, per prime, both ways.** The divisibility theorem delivers γ_p·a at even-position tops and
   ASK-shaped excess at odd-position tops. The colength cost τ then removes the even-position surplus again. So the
   *net* gain at each served prime is the prime-count summand ± O(lo). Any excess the Hecke operators buy is spent on
   their colength.
3. **The cap is the same w by definition plus one structural lemma.** It is not an independent theta-side quantity.
   - The family's level-j weight at the Frobenius-translate position is pinned to the count's `fill` (`LatTied`, IRZ:440,450-451; `ParametersFill`, IRZ:403-405).
   - The divisibility cap is that weight's second row ν_{j,·,2} (FGS:36-38).
   - It is a cap because a product of minors has degree ≤ (number of minors at that position) in any single column
     direction (`HitsCapPos`, `UTS/StatementE.lean:15-21`).

## 1. Objects at one inert p, one lift j, one Frobenius orbit t0

**Frobenius orbit.** p is inert (`IsResidueClassZero`, so not signal). The places above p form ⟨hP⟩-orbits in HH = A.
The orbit of t0 is identified with positions i ∈ ℤ/n′, n′ = ord(hP), i ↦ t0 + i·hP (`phi`, PCC:39). Here n′ is even
(`even_addOrderOf_hP_of_pow_le`, used at PCC:712). The rep t0 is `X.bs` (an `Inst` field, IRZ:142-144).

**Tops, V-tops, TypeV, dMinus.**

| term | definition | file:line |
|---|---|---|
| top | s ∈ host.TT (a target place; weight a_s ≈ a) | IRZ:168-171 (`topsOn`) |
| IsV (V-top) | top at **even** position relative to the rep: bs(s) + i·hP = s with i even | IRZ:179-180 |
| TypeV | even position i ∈ Fin n′ (local form of IsV; `isV_phi` PCC:95) | UQS:54 |
| dMinus(y) | for an odd top y: least d ∈ (0, n′] with y − d a TypeV top; it is odd (`dMinus_odd` PCC:122) | IRZ:207-209 |
| partner(s, e) | (false, s + e·hP): the place reached by Frobenius^e (`partner_of_central` PCC:345) | IRZ:131-132 |
| fill(j, z) | b_z·[z top] + off_j(z); off ∈ [b′/x, b′/x+η] at tops, [w″, w″+η] at thin places | IRZ:146-148,154-155 |
| fillG | fill − kaJ, kaJ = (k + (2j−1)(t+1))/2 | IRZ:157-159 |

Window facts: a_s ∈ [a, a(1+…)], b_s ∈ [b′, 5b′/4] (`InWin` C1G:99-101; `SizeFacts` SF:28). Also η ≤ w″/x,
k·Sc ≤ w″ ≤ b′/x (SF:28-31), and kaJ ≤ Sc ≤ cG = 4Sc (`kaJ_le` C1G:71, `base` PCC:198).

**The formulas (the Lean says).** Write A_s = a_s, al_s = a_s − 2cG, W_{s,e} = fill(j, partner(s,e)),
capU_{s,e} = fillG(j, partner(s,e)) + cG, and Σ_e for the sum over odd e ≥ 1.

| symbol | formula | file:line |
|---|---|---|
| ask_s (`askP`) | Σ_e (A_s/p^e − W_{s,e})₊. This is the count summand: Λ(p^e)(1−χ(p^e)) = 2 log p for e odd, 0 for e even | IRZ:373-374 |
| askG | the same with fillG (≥ askP; askG ≤ askP + Nm·log_p 2a by `RequiresAll`) | IRZ:368-369; C1G:123-127 |
| Mn_s | Σ_e min(A_s/p^e, W_{s,e}); **ask_s + Mn_s = γ_p·A_s** (`ask_add_Mn`) | PCC:246-256 |
| gU | γ_p Σ_{tops} al_s − Σ_{odd tops} Σ_e min(al_s/p^e, capU_{s,e}) − dl | IRZ:254-258 |
| g0 | Σ_{tops} Σ_{e, ¬Excl} (al_s/p^e − capU_{s,e})₊ − dl. Excl(s,e) means s+e is another top reached for the first time | IRZ:235-251 |
| dl | K.dl1·n′·Nm²·log_p 2a + K.dl2·Nv·(log_p 2a)² | IRZ:241-243 |
| Pr (p ≥ p0) | Σ_{odd tops y}(fillG(y) − b_y) + Pr1·n′(w″+η+cG+Nm) = Σ_y(off_y − kaJ) + small | IRZ:262-265 |
| Pr (p < p0) | rG·(Nv(2b′+cG) + n′(w″+η+cG+Nm)) | IRZ:266-267 |
| tv (p ≥ p0) = `tIf` | **Σ_{odd tops y} min(b_y, A_{y−d}/p^d)**, d = dMinus(y); + κ1·Nv·N1(a/p² + La·a/(pk)) + κ2·Nv(…poly…) + 2n′cG | IRZ:217-225 |
| tv (p < p0) = `tIIf` | tII·rG·Nv(La·a/(pk) + a·p^{−L1} + c0num + kQp) + 2rG·n′·cG, c0num = 2b′+2cG | IRZ:197-200 |
| Dp | ⌈DI·40n′δ1·x^A·(N1⁵+k³)·log_p a⌉ (p ≥ p0); DII version for p < p0 | IRZ:188-195,269-270 |
| τ_p (`tauP`) | ep + Σ_{t0∈VV} m(⌈tv⌉ + Dp + 1) | IRZ:341-344 |
| gain_j (`gainP`) | Σ_{t0∈VV} max(gU − Pr, g0⁺) + Σ_{t0∉VV} g0⁺ (0 if hP = 0 or p > X″) | IRZ:355-358 |
| lo (p0 ≤ p < X′) | C(cG+η)log_p 2a + b′/x + η + C·w″·log x/δ1 + bo + C log x(La·a/(pk) + a/p²) | PCC:581-585 |
| lo (p < p0) | C(cG+η)log_p 2a + C·rG·b′·log x + C log x(La·a/(pk) + a·p^{−L1}) | PCC:575-578 |

**Formal-group side** (`stmt_proved`'s numbers, FGS:24-81). Here λ is the base weight: λ_{s,0} = a_s,
λ_{s,last} = −b_s at tops, and the other entries have |·| ≤ c (`IsBaseWeight`, UQS:59-63). The level-j weight is
ν_j(s, i) = λ_{s,i} + w_j(s), and w_j(s) = fillG(j, (false, t0+s·hP)) (`LatTied`, IRZ:450-451).
- cap(s′) = ν_j(s′, 2) if s′ is a top, ν_j(s′, 1) otherwise. So cap = fillG(partner) ± c ≤ capU (FGS:36-38).
- gB = γ_p Σ_{TT} al − Σ_{s∈TT odd position} Σ_{e} min(al_s/p^e, cap(s+e)) − de (FGS:57-61).
- gA = Σ_{TT} Σ_{e ∉ dSet(s)} (al_s/p^e − cap(s+e))₊ − de, where dSet(s) = distances to opposite-parity tops (FGS:63-70).
- alEven = Σ_{even tops} al. The Hecke-free branch gives only gB − alEven, and the even-position γ_p·al is supplied by
  the Hecke normalisation (NODE-LOCALDIV Step D; `Nprime` FGS:72 sums λ over even positions).

**What `LowTermBound` delivers** (FGS:708-716, instantiated by `UAt_of` with Gn = gU ≤ gB, G0n = g0 ≤ gA,
PRn = Pr ≥ Pr_FG via `SmallResidueCharComparison`, FGS:741-754). For every F in the span of
yProd(VV′)(p^{ΣSv}·M):

  v(chainK_m F) ≥ Σ_{j=1}^m [ Σ_{t0∈VV} max(gU_j − Pr_j, g0_j) + Σ_{t0∉VV} g0_j ] − Σ_j dG_j.

NP ⊆ p^{⌈τ⌉}M with colength ≤ d(τ+io) (NODE-TWU). So the **net delivered exponent per lattice rank is Σ_j gain_j − τ**.

## 2. The per-prime chain (p0 ≤ p < X′, served orbit t0, one lift j)

The chain is assembled from `gU_lower` (PCC:308-343), `kinkHH` (PCC:369-438) and `caseE_arith` (PCC:545-560).
Write V for the V-tops and O for the odd tops of the orbit.

```
gU + dl  ≥ Σ_{s} ask_s + Σ_{s∈V} Mn_s − Nv·3cG·log_p 2a          (gU_lower: identity on V, odd_top on O)
Σ_{s∈V} Mn_s ≥ Pr_first + Σ_{y∈O} min(b_y, A_{y−d}/p^d) − Nv(b′/x+η)      (kinkHH)
⇒ gU + dl − Pr − ⌈tv⌉ − Dp − 1 ≥ Σ ask − Nv·[3cG log + b′/x + η] − (Pr2 + κ-terms + Dp + 2)
                                ≥ Σ_s (ask_s − lo)                    (caseE_arith; lo absorbs the bracket)
```

That is `StarAt` (C1G:129-131). Summed over j and over orbits it is `GainBoundAt` (C1G:113-120):
Σ_j Σ_s(ask − lo) − m·fl ≤ Σ_j gain_j − τ.

**How the pairing works (kink, PCC:136-196).** The map y ↦ (xm(y), d(y)) = (y − dMinus(y), dMinus(y)) sends odd
tops into V × {odd e}. It is injective on each fibre, because y = xm(y) + d(y) (`posAdd_back`). So
Σ_{y∈O} min(W_y, A_{xm(y)}/p^{d(y)}) is a sub-sum of Σ_{s∈V} Σ_e min(A_s/p^e, W_{s+e}) = Σ_V Mn_s.

For p < p0 (`starAt_D`) the pairing is **not** used:
- Pr + tv ≈ (1+tII)·rG·Nv·2b′ is charged to lo's C·rG·b′·log x per top (`caseD_arith` PCC:497-543);
- the V-top surplus Σ_V Mn ≥ 0 is simply discarded.

## 3. The reverse inequality (C6): Ga − ASK from above

I infer this; it is not in the Lean, but it uses only the definitions above.
- capU ≥ fill, because kaJ ≤ Sc ≤ cG, and al ≤ a. So on odd tops γ_p·al_s − Σ_e min(al_s/p^e, capU) = Σ_e(al_s/p^e − capU)₊ ≤ ask_s.
- Likewise g0 ≤ Σ ask − dl. On V-tops, γ_p·al_s ≤ ask_s + Mn_s.

Hence gain_j − Σ ask ≤ Σ_{t0∈VV} (Σ_V Mn_s − Pr_j)₊. Since τ ≥ m·Σ_{t0} tv_pair, we get

  Σ_j gain_j − τ − Σ_j Σ ask ≤ Σ_{t0∈VV} Σ_j (Σ_V Mn_s − Pr_first − tv_pair)₊.

Split Σ_V Mn_s along the injection:

| piece | bound per V-top | why |
|---|---|---|
| paired (s, d(y)) minus its tv term minus (off_y − kaJ) | min(A, b+o) − min(A, b) − o + kaJ ≤ kaJ | `off` cancels exactly against Pr_first |
| e with s+e thin | ≤ (w″+η) per e with A/p^e ≥ w″, i.e. ≤ (w″+η)(1 + ½ log_p(2a/w″)) | off_thin |
| e ≥ 3, s+e an odd top not paired to s, or wrap-around e > n′ | Σ_{e≥3} A/p^e ≤ 2.1·a/p³ | non-nearest partners are at distance ≥ 3 |

The partner s+e of an even s at odd e is always at an odd position, so it is never another V-top.

Weighted by 2 log p and summed over p0 ≤ p < X′, per V-top per lift:
- thin: ≈ 2X′(w″+η)(1 + O(log(xn)/x^{ε/3})) ≈ 2a/(x·n) = 2b/n (X′·w″ = a/(xn));
- far partners: 2.1·a·Σ_{p≥p0} 2 log p/p³ ≈ a/p0² ≈ b·x^{−69};
- kaJ: 2X′·Sc ≪ b (X′ = e^{x^{ε/3}}, Sc poly(x)).

For p < p0: Mn_s ≤ 2.5b′(2 + ½ log_p X′), so Σ_{p<p0} 2 log p·Mn ≲ b′·x^{35+ε/3} ≪ b. For non-served p and
p ≥ X′: gain = Σ g0⁺ ≤ ask, so there is no excess.

**Total: Ga − ASK ≤ nT·m·O(b/n + b·x^{−69}) + negligible ≪ LoP ≈ nT·m·b ≪ budget.** With the proved
Ga ≥ ASK − LoP this gives |Ga − ASK| ≤ LoP. ACCOUNT's estimate "gain ≈ ASK + Σ_V Mn, Σ_V Mn ≈ 2a" is right
*before* τ. After τ the surplus is gone to O(w″) per (V-top, prime).

## 4. Worked numbers (toy orbit n′ = 4, tops at positions 0 (V) and 1 (odd), positions 2,3 thin)

The toy uses b_y = B = 1000, off_top o = 1, thin weight w″ = 1, A = 10⁶, and cG = kaJ = 0. The script is
`/tmp/claude-0/-home-user-SafeVerifyAgent/6f6a4549-468b-59ec-896e-73bdf5d26a96/scratchpad/pair.py` (exact rationals).

**Fills.** W(0) = W(1) = 1001 and W(2) = W(3) = 1. Partners: from 0, e = 1, 5, 9, … → pos 1 and e = 3, 7, … → pos 3.
From 1, e = 1, 5, … → pos 2 and e = 3, 7, … → pos 0.

| | p = 101 (only e = 1 beats B; A/p³ = 0.97 < w″) | p = 7 (e = 1, 3 beat B; thin up to e = 7) |
|---|---|---|
| γ_p·A | 9901.961 | 145833.333 |
| Legendre v_p(A!) − A/(p²−1) | 9899.961 (diff s_p(A)/(p−1) = 2.000) | 145830.667 (diff 16/6 = 2.667) |
| ask_0 (V) / Mn_0 | 8899.990 / 1001.971 | 144770.809 / 1062.524 |
| ask_1 (odd) / Mn_1 | 9899.990 / 1.971 | 144829.094 / 1004.240 |
| ASK_p = ask_0 + ask_1 | 18799.980 | 289599.903 |
| gU (= 2γA − Mn_1) | 19801.951 | 290662.427 |
| gU − ASK (= Mn_0, the V surplus) | 1001.971 (≈ 5% of ASK) | 1062.524 (0.37%) |
| tv_pair = min(B, A_0/p) | 1000 | 1000 |
| Pr_first = o − kaJ | 1 | 1 |
| **slack gU − Pr − tv − ASK** | **0.971** = thin e = 3 term | **61.52** = thin e = 3, 7 (1 + 1) + wrap e = 5 (A/7⁵ = 59.50) + 0.02 |
| Legendre-delivered at odd top: v_p(A!) − A/(p²−1) − #factors (≤ Mn_1) | 9897.990 vs ask_1 9899.990 | 144826.427 vs ask_1 144829.094 |

Readings:
- ask + Mn = γ_p·A holds to all digits (identity `ask_add_Mn`).
- **Odd tops:** delivered = ask − s_p(A)/(p−1). The digit-sum defect (2.0, 2.67) is what `de` (FGS:47, ≥ NN·lgp(al) + lgp(al)², here ≥ 15) and dl are there to cover, as NODE-LOCALDIV §4 found.
- **V-top:** the delivered divisibility is γ_p·A − de, so it **exceeds** ask_0 by Mn_0 ≈ B. τ's pairing term removes B exactly, and Pr_first removes o. The excess remains on the delivered side; relative to ASK it is 0.97/18800 ≈ 5·10⁻⁵ (p = 101) and 61.5/289600 ≈ 2·10⁻⁴ (p = 7).
- The p = 7 residue 59.5 comes from wrap-around (n′ = 4). In the Lean, n′ ≥ x^{ε/4} and such p < p0 go through `starAt_D`, where the slack is discarded anyway. For p ≥ p0, wrap terms are ≤ a/p^{n′+1}.

## 5. Where the cap w comes from (b)

The chain of identifications is as follows. Each step is either "the Lean says" or labelled as inferred.
1. The count's cut-off for (lift j, top s, prime power p^e) is fill(j, partner(s,e)). This is the family weight
   wj(j, τ) at the place Frob_p^e·s (`ParametersFill` clauses 1-2, IRZ:403-405; ACCOUNT: `partner = cconj + g + topPl t`).
2. The local datum's twist is w_j(s) = fillG = fill − kaJ (`LatTied`, IRZ:450-451; non-orbit positions IRZ:437-440).
   The base weight puts a_s in the first row and −b_s in the last (UQS:59-63).
3. The divisibility cap is cap(s+e) = ν_j(s+e, 2) = λ_{s+e,1} + w_j(s+e), the **second row of the level-j highest weight**
   at the partner position (FGS:28-38). For a top partner this is ≈ b + off − kaJ. For a thin partner it is
   λ_{·,0} + off − kaJ ≈ w″.
4. Why the second row is a cap: the jet operator is a product of column minors (one per column of the Young diagram).
   A Hasse derivative taken in one direction more than capN = #minors at that position kills it (`HitsCapPos`,
   `UTS/StatementE.lean:15-21`; `capN` :158). Each hh-factor X_{s}^{p^{e}}·X_{s+e}… uses one such derivative at the
   partner position, so #factors of size p^e ≤ min(al/p^e, cap). That capN equals ν(·,2) is NODE-LOCALDIV's reading; I did
   not re-derive it.
5. Why the partner is at odd distance e: the Gaussian hh = Σ u_s S_s^p S_{s+1} pairs position s with s+1 (Frobenius
   shifts position by one), and its monomials have degree p^{2l+1} (NODE-LOCALDIV Step C).

So **the link is a definition, not a theorem.** The family's unitary weights are *chosen* to equal the count's cut-offs:
thin places get determinant twist w″ = b′/(xn), tops get b_t + b′/x. The structural facts that make the chosen weight act
as a cap are (4) and (5).

## 6. Children

| # | name | file:line | statement | weight |
|---|---|---|---|---|
| 1 | `kink` / `kinkHH` | PCC:136-196, 369-438 | injective pairing of odd tops with (nearest preceding V-top, odd distance); tv_pair + Pr_first ≤ Σ_V Mn + Nv(b′/x+η) | glue (read; correct) |
| 2 | `gU_lower`, `ask_add_Mn`, `odd_top` | PCC:249-343 | max + min identity; gU ≥ Σask + Σ_V Mn − log terms | glue (read) |
| 3 | `caseD_arith`, `caseE_arith`, `NumStar` | PCC:440-560 | lo absorbs Pr2, κ-terms, Dp, ceilings; and for p < p0 the whole Pr + tv | glue (read; all-real linear arithmetic) |
| 4 | `LPprime` / `OrbitLatticeBounds` (colength of (T_r)^m M ≤ m·d·(tv + Dp) off κ-small set) | `CornerGLContinuity.lean:180-196` | the Hecke image's index per rank is ≈ Σ_pairs min(b_y, a_s/p^d) | **core, not opened**: it is what makes τ the *true* cost of the V-surplus |
| 5 | even-position γ_p via Hecke normalisation (`ea_BU`, `ea_BrScale`, `Nprime`, cl_r ≥ alEven) | FGS:72, 671-695; `MV/EaApplyDScale.lean:98` | T_r-images gain γ_p·al at V-tops | core (NODE-LOCALDIV) |
| 6 | `HitsCapPos` ↔ cap = ν(·,2) | `UTS/StatementE.lean:15,158` | caps equal second-row lengths | core-ish, statement read |
| 7 | `SmallResidueCharComparison` supplier (`NumCmp`) | FGS:731-757 | gU ≤ gB, g0 ≤ gA, Pr_FG ≤ Pr | glue, supplier not traced |

## 7. Oddities

1. **V / non-V depends on an arbitrary rep.** IsV is parity relative to `X.bs` (an `Inst` field). LatTied indexes local
   positions from the same rep (IRZ:441-446), so the formal side and the family side agree. Mathematically, "even" means
   one of the two conjugate embedding types (`lamAt` dualises odd positions, UQS:67-68).
2. **For p < p0 the costs are paid by lo, not by the surplus.** lo ≈ C·rG·b′·log x per top is O(b′) per top, which is
   negligible only because Σ_{p<p0} 2 log p·b′ ≈ x^{35}b′ ≪ b.
3. **The τ pairing is exact to the unit of `off`.** tIf uses b_y, and the missing off_y comes back through Pr_first =
   Σ(fillG − b). This is deliberate and it checks.
4. **Gain is net-zero over ASK.** The delivered divisibility at V-tops exceeds the count by ≈ Σ min(a/p, b′) ≈ 2a per
   V-top per lift (ACCOUNT's figure, confirmed). All of it is returned as colength. So the Hecke operators contribute
   nothing to the slope: the Hecke-free part is what yields ASK. This agrees with REVIEW-TWU §2.
5. `RelativePresentationLiterature` (FGS:702-706) is a numerical inequality Sv ≤ m·γ·Σal with "Literature" in its name.
   It is proved in `stmt_proved` (NODE-LOCALDIV). I did not examine it.
6. Nothing looks false. The only "too good" place is child 4. If (T_r)^m M had colength per rank larger than
   m(tv + Dp + 1) — for instance ≈ m·Σ_V Mn including the thin and far terms — the lattice bookkeeping would still close,
   because the extra is O(w″). But if the true index of T_r at weight (a, …, −b) were of order a/p rather than
   min(b, a/p^d) per pair, `LemmaVVolumeGeneral` would be false.

**Escalation E-PAIR-1.** Check this for one inert p ∈ (p0, X′) and one orbit of length n′ with alternating tops:
the integrally normalised T_r on weight-(a, 0, …, 0, −b) algebraic modular forms has index p^{≈ b·#odd tops} per rank,
up to Dp.

## 8. Coverage

Read:
- IRZ:1-485 (all);
- PCC:100-851 (kink, base, ask_add_Mn, odd_top, gU_lower, kinkHH, NumStar, orbit_facts, caseD/E_arith, lo_D/E, starAt_D/E, starAll_of);
- C1G:99-137;
- FGS:20-110, 700-757;
- UQS:50-68;
- `UTS/StatementE.lean` (grep: HitsCapPos, capN, dSet);
- SF:15-40;
- DataParams₂ etaSz lines (145-164 via grep).

Not opened:
- `LPprime`/`OrbitLatticeBounds` bodies; `tsum_pos_add_min`/`tsum_truncated_shift_le` bodies; the `NumCmp` supplier;
- `adm1` (orbit density, used for Nv ≥ n′δ1/(C31 log x));
- `Ga_at`'s place-to-prime rewrite (taken from NODE-LOSS);
- the proof that `SizesAt` holds on the live path (SF bounds used as stated).
