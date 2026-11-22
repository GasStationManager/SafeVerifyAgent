# NODE-SHARP: which actual loss carries the √x, and does the chain prove too much?

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own arithmetic or inference. [NODE] means taken from that node and not re-read. Nothing was compiled or executed.

Abbreviations, as in NODE-LEDGER, plus:
- `DA` = `Formalism/LocalRingCardinality/DataArith.lean`; `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`; `DE` = `Formalism/LocalRingCardinality/DataErr.lean`
- `RV` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/PairRowIffQdRows.lean`; `SLN` = `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SecondLabelsNonempty.lean`
- `SC` = `Formalism/SizeWindowBrackets/SChain.lean`; `GB` = `.../GrowthBoundGivesRiemannHypothesis.lean`; `EW` = `.../ErrorFormsWeakWindowsFalse.lean`; `QSB` = `.../QuotientSlopeBoundsWith.lean`; `MB` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`
- `WDS` = `Formalism/SharpRestriction/Divisibility/WeightDegreeSizes.lean`; `QLD` = `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`; `ZON` = `Formalism/LocalToGlobal/Divisibility/ZscOfNum.lean`
- `EFS` = `Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean`; `FDS` = `Development/AutomorphicSpectrum/Statements/GeometryStatements/FlatDegree.lean`

Notation *(mine)*: W := Σ_ρ w_{jρ} is the weight mass of one lift. Thick places carry w ∈ [b, b+η+1], and every other place carries w ≤ 2b′ [ACCOUNT, from DP2:151-155]. So W ≈ |T2|·b = δ·n·b, and m·W ≈ 2U·(n/|TT|) ≤ 4x^{ε/8}·U. **Test used throughout.** A per-lift loss of size W·x^{O(ε)} totals U·x^{O(ε)}, which is harmless. A per-lift loss of size m·W·x^{O(ε)} totals m·U·x^{O(ε)}, which is barrier-sized.

## 0. Verdict

**No ESCALATE.** The chain does not prove too much. The reason is not the term the exposition named.

1. **The barrier-carrying term is the T_u-adic part of Ee, the divisibility loss at the type prime.** It is a *defined*, nonnegative quantity whose size is pinned from below, not an allowance:
   - At p = T_u every lift has E_{u,j}(w) = EatT (DE:159-161), so sg(u, w) = −m·EatT (`sg_atT`, WDS:887-901).
   - EatT = 2·Σ_τ Wtau + f·Nm + |tops|(t+1)(m+1)/4 at the seen places (DE:103-107).
   - log T_u is forced to be ≍ m·x^ε. From below it is bounded by `TuGe`, b^{m/2} ≤ T (DP2:252), and by Count5's lower clause log T ≥ Σ_j mean_ρ log(wv/π) + m·lg − … (QSB:27-30), with lg = log(g₀g₁) ≥ 0 (QLD:165). From above it is bounded by Count5, log T ≤ cCount·m·L (QSB:30).
   - *(mine)* So Ee_T ≈ m·EatT·log T_u ≳ m·(2δnb)·(m/2)·x^ε. Hence **Ee_T/U ≥ 2m·x^ε ≥ 2x^{1/2+15ε/16}** across the whole RankVal window, and it is ≤ 192·cCount·m·x^{2.125ε}.
   - It grows like m², because every lift is T-nonintegral by ≈ the full weight and log T must hold m copies of the Riesz-length normalisation. So enlarging m cannot prove G = o(√x).
2. **REVIEW2 is right that eE is not the carrier.** Σ_{j,ρ} eE ≈ m·W·x^ε ≈ (δ/2)·B₀, so eE/U ≲ 4x^{9ε/8}.
   - The logΩ signature residual is negligible: Σ_j(2j−1−m) = 0, and w_{jρ} varies in j by ≤ η+1 (poly) at thick places and by ≤ 2b′ elsewhere.
   - The 424·B₀ divisibility losses away from T are B₀-sized **in total**, not per lift.
3. **A second, sign-unsettled carrier is the covolume's q-part.**
   - `flatDegVal` has an exact term q·(log d − lrd E) (EFS:751-752; FDS:19-20).
   - The non-flat Hilbert–Samuel part is ∝ q_j·W.
   - Both total ≈ m·U·x^{O(ε)}, and the Lean puts both into l3u = B₀·log log x (ZON:65).
4. **The maximal admissible m.** In the Lean, m is fixed at ≈ x^{1/2−ε/16} (RV:30) and is ≤ x^{1/2+ε/2} (GB:113). Re-dimensioned under the non-vanishing constraints (SLN:35-39) together with k ≤ n²x^{1/2−ε}, the largest m is ≈ x^{11/20} *(mine)*. There the chain's own bracket gives G ≲ x^{0.55+O(ε)}, which is weaker, and Ee_T ≳ x^{0.55}·U. Consistent.
5. **The core inequality, stated cleanly (§2.4).** It is a one-sided bound, at the single point y ≈ x per (t, j), on the Riesz-smoothed Chebotarev error in the abelian field E for a nonnegative class function. It is implied by GRH for the Dirichlet characters of conductor dividing d·q·2^{s+2}, and no known result contradicts it.
   - An unconditional "adversarial thick-set" test reaches only x^{1/2}·polylog·x^{ε/16}, which is inside the budget.
6. **New rigidity requirement on T*.** Truth forces ΣA·(log T_u − Lam5) ≲ x^{1/2+O(ε)}·U, i.e. log T* − Lam5 ≲ x^{O(ε)}. The Lean bounds log T only by cCount·m·L above (§4.2).

## 1. Statement (what is being tested)

The chain is ASK − LoP ≤ Ga ≤ Main + ErrX5at (QSB:45-54), together with the exact bridge ASK − MAIN = De. Write each link as A_i ≤ B_i + e_i, where e_i is its budget. The links telescope, so **Σ_i r_i = ASK − Main exactly, with r_i := A_i − B_i the actual consumption.**
- *(mine)* In every window, G_m − SigA is of size ≥ c·x^{1/2} on a set of x of positive logarithmic density: under GRH it is almost periodic in log x with nonzero mean square, and without GRH it is larger by Landau.
- So some r_i ≥ c′·U·x^{1/2} must hold at those x.
- Negative r_i (Hadamard defect in Bost, the defect h − log‖B_u‖_true, unused divisibility, Count5 slack) cannot carry it.
- It must come from a loss that is genuinely ≥ U·x^{1/2}.

## 2. Argument

### 2.1 Definitions (Lean)

- **Scale** (DP2:9-45):
  - L = x^ε (:27), b = e^L (:29), a = x·b (:31);
  - X′ = e^{x^{ε/3}} (:33), b′ = a/X′ (:35), w″ = b′/(xn) (:37), X″ = a/w″ (:39);
  - δ₁ = x^{−ε/8} (:45), and ε < 1/52 (:14).
- **RankVal** (RV:28-32):
  - x^{2+8ε} ≤ n ≤ 2x^{2+8ε};
  - √(xδ₁) ≤ m ≤ 2√(xδ₁);
  - x^{9/2+10ε} ≤ k ≤ 2x^{9/2+10ε};
  - f = 2n [LEDGER, HCl:153].
- **Budgets** (DA:198-210):
  - B₀ = `sizeBudget` = f·m·b·x^ε (:200);
  - Nc = `budgetNc` = |T2|·k·b·x^ε/(n·n·x^{−ε}) = |T2|·k·b·x^{2ε}/n² (:204-210).
- **Windows**:
  - `RestSize` (SC:53-58): aE ≤ 2xb, |TT| ≥ x^{−ε/8}n/2, δ = |T2|/n ≥ x^{−ε}, m ≥ x^{1/2−ε}, k ≤ n²x^{1/2−ε};
  - `SizeWindows` (GB:109-117): adds m ≤ x^{1/2+ε/2}, x·m ≤ k, 26 ≤ x^{3ε/8};
  - `ErrWindows0` (EW:28-39): adds La, L ≤ 2x^ε, k·b′ ≤ a, log|W| ≤ (k−3)log 2.
- **Theorem S** (`RankNums`, SLN:34-43):
  - x^{1/4} ≤ m, m⁴ ≤ f, f ≤ k;
  - x^{ε/2}·m⁵·f·x^ε ≤ k ≤ x⁵;
  - lrd ≤ x^{ε/2}.
- **Signal unit**: U = |TT|·m·b·(δ/2) (GB:119-122).
- **ErrText** = |TT|·a(1 + m²/k) + m(B₀ + Nc) (EW:16-17). The envelope is x^{(eD+eL+3)ε} (EW:19).

*(mine)* With these, B₀/U = 2f·x^ε/(|TT|·δ) ≤ 8x^{2.125ε}, and |TT|·a·La/U ≤ 4x^{1+2ε}/m.

### 2.2 Ledger terms: budget, budget/U, family

All ratios are *(mine)*, at m ≈ x^{1/2−ε/16}, with constants from the record kept symbolic.

| term (line) | budget (Lean) | budget/U | family | fixed by |
|---|---|---|---|---|
| Count5, ΣA·cCount(La + m²La/k) (L5) | QSB:28-29, 46 | ≤ 4cCount·x^{1/2+2.06ε}; the m²/k part is x^{−3.5} of that | x/m | aE ≤ 2xb (SC:54), m ≥ x^{1/2−ε} (SC:57) |
| DIV boundary, cDiv·\|TT\|·a·La (L1) | MB:118-121; QSB:47 | ≤ 4cDiv·x^{1/2+2.06ε} | x/m | the same, plus b′·Nn ≤ a and m·k·b′ ≤ a [HEIGHT] |
| source floor, cSlope·\|TT\|·a·La(1+m/k) (L3) | MB:139-141; QSB:49 | ≤ 4cSlope·x^{1/2+2.06ε} | x/m | the same |
| DIV interior, cDiv·m·B₀·x^{2ε} (L1, D1–D5) | MB:121; QSB:47 | ≤ 8cDiv·x^{1/2+4.06ε} | m | B₀ (DA:200), m ≤ x^{1/2+ε/2} (GB:113) |
| DIV non-vanishing, cDiv·m·Nc·x^{2ε} | QSB:47 | ≤ 8cDiv·x^{1/2−1.875ε} | k/n² | k ≤ n²x^{1/2−ε} (SC:58), Nc (DA:204-210) |
| EComp5, m·cE·B₀ (L4) | QSB:24-25, 48 | ≤ 8cE·x^{1/2+2.06ε} | m | the same as for m |
| Bost HN term, 4·log(1+x^{cHH})·(UBar5 + b) (L0/L8) | QSB:41-43, 53 | ≈ 4cHH·log x × (the x/m and m rows, via cSlope·\|TT\|aLa(2+m/k) and cSl1·m·B₀) | x/m and m | HHBound (MB:158-159) |
| (η̄+4√ē)·x^{cHH}·b | QSB:54; ≤ 6b [ACCOUNT, QLD:258-260] | ≤ 24/(\|TT\|mδ) ≈ x^{−5/2} | negligible | FrameF |
| log\|W\| | ≤ (k−3)log 2 (EW:39) | ≈ x^{4.5}/(x^{2.5}b) → 0 | negligible | b = e^{x^ε} |
| LoP = cLoss·\|TT\|·m·b (eL = 0) | MB:105; QSB:34-35 | 2cLoss/δ ≤ 2cLoss·x^ε | one per (top, lift) | Loss_at [GATIE] |
| MLo5 | QSB:37-39 | m²·x·L/(kδ) and m·x·L/(X′δ): → 0 | negligible | k ≥ xm, X′ |

DIV sub-ledger (D1–D5). Its total budget is (50C₀+10)·|TT|·a·La + 60·ce·m·x^ε(B₀+Nc) [DIVKEY, SLF:84-87].

| component | Lean allowance | allowance/U | family |
|---|---|---|---|
| covolume error l3u | B₀·log log x per layer (ZON:65) | ≈ 8C·m·x^{2.1ε}·log log x | m |
| E1 (theta-image index) | CE·x^ε(B₀+Nc) per layer [WHERECONG, INDEXBUDGET] | m-sized | m |
| E2 (congruence modules) | Nc-sized allowance [NONVAN, WHERECONG] | k/n² | k/n² |
| E3 = Σ lw·2/ℓ² | [MAIN §5.2] | ≪ 1 | negligible |
| eE (Fock–hook defect) | 15C₀·m(B₀+Nc)·x^ε [DIVKEY, AbE:86-98] | m-sized | m |
| pq/logΩ residual | 6m(B₀+Nc)·x^ε [DIVKEY, AbE:137-152] | m-sized | m |
| δ, top part | C₀·\|TT\|·k·b′·La, with m·k·b′ ≤ a | x/m | x/m |
| eP (last map), Lpass | C₀·\|TT\|·a·La + 9C₀·m(B₀+Nc)x^ε; (1+C₀)·m(B₀+Nc)x^ε | x/m and m | x/m and m |

**Answer to task 1** *(mine)*.
- **budget/U ≈ m·x^{O(ε)}**: every B₀-proportional entry. These are cDiv·m·B₀·x^{2ε} (with l3u, E1, eE, eK, the pq residual, the δ rest, eP's m-part and Lpass inside it), m·cE·B₀, and cSl1·m·B₀ inside UBar5.
- **≈ x/m**: Count5, the DIV boundary terms (hA, the δ top part, logc/logxi), the source floor, and UBar5's cSlope·|TT|·a·La.
- **≈ k/n²**: m·Nc (E2).
- Everything else is ≤ x^ε, i.e. x^{−1/2} of the budget or less.

### 2.3 Actual sizes against budgets (task 2)

All estimates in this subsection are *(mine)* unless a node or line is given.

**(i) One-off terms.**
- *Source floor and HN spread.* The natural size of μ(M_u) (weight-a forms) is |TT|·a·x^{O(ε)}, so the budget is plausibly used.
- The spread across words is genuine: |log T_u − log T_u′| ≤ cCount·log k (QSB:31). That moves ΣA·log T by |TT|·a·log k, which is x/m-sized.
- *Count5.* T ∈ [T*, (1 + 1/(fk))·T*] (DP2:186-190). log T* = logXu − 2·logΓ/(fk) with 2·logΓ/(fk) ≤ 2 [DIVKEY]. So even the O(1)-per-unit-weight discrepancy gives ΣA·O(1), which is x/(mδ), the x/m family.
- *DIV top δ.* The k·b′ allowance is unused slack (YDH:527-531) [STEPE]. So that one-off is not consumed.

**(ii) Per-lift terms.**
- **eE.** It is ≈ w·log w per (j, ρ) off tops and ≈ w·log a at tops, where w ≈ b′ [STEPE]. Σ_{j,ρ} eE ≈ m·W·x^ε ≈ (δ/2)·B₀, so eE/U ≲ 4x^{9ε/8}. **This is the "B₀ in total" REVIEW2 found, and it is confirmed.**
- **Signature residual R = Σ_j(2j−1−m)·Σ_ρ w_{jρ}·logΩ.** It is signed, and it cancels:
  - Σ_j(2j−1−m) = 0;
  - the j-dependence of w_{jρ} is ≤ η+1 = poly(x) at thick ρ and ≤ 2b′ elsewhere, and the s_j trend gives (t+1)(m³−m)/6 per ρ [DIVKEY];
  - so |R| ≲ m²·f·(η + 1 + 2b′)·La, and R/U → 0 (b′/b = x/X′).
  - The Lean takes it in absolute value (AbE:137-152) [DIVKEY]. It does not carry the barrier.
- **Divisibility losses away from T (adm11).** The question was whether the per-lift budget is used at size f·b·L. It is not.
  - Per lift, c6·Σ_{kindBC} w/p summed with log p over p ≤ X″ is ≈ 12·W·log X″ ≈ 12·W·x^{ε/3}.
  - errF is ≈ |TT|·b·x^{ε/3}; kindA ≈ k·f·b′; deLoss and EatX are ≪ b [ADM11 table].
  - Over m lifts: ≈ 48·x^{ε/3+ε/8}·U + 2x^{4ε/3}·U = U·x^{O(ε)}.
  - The budget is 848·m·B₀ ≈ 6800·m·x^{2.1ε}·U. **The ratio budget/actual is ≈ m·x^{O(ε)}.** So yes: this is B₀-sized in total, not per lift.
  - The g-prime part: DegreeCountBound's errG·log g ≈ 2W·(CYL+1)·x^ε per lift [ADM11 inputs 3–4], which totals U·x^{O(ε)}.
- **The T_u-adic loss, Ee_T.** This is the exception.
  - Ee(u) = Σ_j Σ_{w∈supp} sz(w, E_{u,j}(w)), with sz(w, y) = 2·lwP·e_w·y (DP2:204-205, 218).
  - At resChar w = T_u the value is EatT for every j (DE:159-161; `sg_atT` WDS:887-901).
  - EatT ≠ 0 only at seen places, where `SeenDef` requires all τ-conjugates of π_T to have positive valuation (DE:62-64). T = π·π̄ with π ∈ K (DP2:190). *(mine)* Since Tau ≅ Psi restricts to one embedding of K, these are the places over one prime of K above T. They carry Σ lwP·e_w ≈ ½·log T.
  - Hence Ee_T ≈ m·EatT·log T_u.
  - EatT ≥ 2·Σ_τ Wtau (DE:103-107). Wtau is the largest |HC weight − i(t+1)/2| over levels i ≤ m and non-top rows (DE:98-101). *(inferred)* At a thick τ it is ≥ b − poly(x), because the level-i HC weight contains e_i(τ) = w_{iτ} [STEPE NUM:224]. So EatT ≳ 2δnb, and EatT ≤ 12·f·b [ADM11].
  - log T_u ≥ (m/2)·x^ε (DP2:252), and log T_u ≤ cCount·m·L (QSB:30).
  - Therefore **2m·x^ε ≤ Ee_T/U ≤ 192·cCount·m·x^{2.125ε}**, i.e. ≥ 2x^{1/2+15ε/16} at m ≥ √(x^{1−ε/8}).
  - Per lift it is ≥ (δ/2)·B₀: the per-lift budget is genuinely used up to the factor δ ≥ x^{−ε}.
- **Covolume q-part.** `flatDegVal` = (p−q)/2·logOm + q·(log d − lrd E) (EFS:751-752). The proved Prop is N.deg = (p−q)/2·Re logOm + q·(2·log√d − log rd E) (FDS:19-20).
  - l3m keeps only Σ_ρ(p_j − q_j)·w·logΩ (ZON:63-64), so the q-term lies inside l3u.
  - *(mine)* If lcv is 2w times the flat degree, as the normalisation of l3m suggests, then the q-term totals Σ_j 2q_j·W·(log d − lrd E) ≈ m²·W·½·log d. That gives /U ≈ 2m·x^{ε/8}·log d, which is barrier-sized.
  - On the hosts of HOSTSEL, log d − lrd E ≈ ½(log d − log q) − O(log n) > 0 [MAIN §0 step 2; inferred from rd multiplicativity].
  - The non-flat Hilbert–Samuel part has natural size ‖u′‖·x^{O(ε)} with ‖u′‖ ∝ q_j·W. The live bound is only one-sided at its own order of magnitude [VOLUME §1, oddity 2].
  - **The sign of both is not settled by the record.** This is a candidate, not a proof.
- **E1, E2.**
  - E1's discriminant piece is ≲ (allocation)/PPv. Its tight piece is J0 (≤ 32·x^ε·f·m·b·L), whose actual size is unknown [E1LOOSE].
  - In E2, Ш ≤ √b [WHERECONG]. The Selmer and v_ℓ(h_E) parts are unquantified, and log h_E ≈ n·x^{O(ε)} ≪ b *(mine)*.
  - Neither is shown to be m-sized in truth.

**(iii) Frame/Bost terms.**
- log|W| ≤ (k−3)·log 2 ≈ x^{4.5} against U ≈ x^{2.5+O(ε)}·b: negligible, because b is exponential.
- (η+4√e)·HH ≤ 6b: x^{−5/2}·U.
- The uF·log(HH/uF) term is the x/m-family spread above, times cHH·log x.
- Its m-part, cSl1·m·B₀, is an allowance for μmax(N_u) (QSB:21). Its actual size includes the u-dependence of Ee_T, m·EatT·Δlog T ≤ 24·cCount·m·f·b·log k. That is B₀·log k/x^ε, so U·x^{O(ε)}.

### 2.4 Maximal m, and the core inequality (tasks 3–4)

**Constraints on m (read).**
- RankVal: m ∈ [1, 2]·√(x^{1−ε/8}) (RV:30). In the Lean, m is not free.
- m ≥ x^{1/2−ε} (SC:57; GB:112); m ≤ x^{1/2+ε/2} (GB:113; EW:32); x·m ≤ k ≤ n²·x^{1/2−ε} (GB:114; SC:58).
- x^{1/4} ≤ m, m⁴ ≤ f, x^{3ε/2}·m⁵·f ≤ k ≤ x⁵ (SLN:35-39).

**Re-dimensioned maximum** *(mine)*. Keep f = 2n and drop RankVal and the m-window.
- k ≤ n²x^{1/2−ε} together with k ≥ x^{3ε/2}·m⁵·f forces f ≳ m⁵·x^{−1/2+5ε/2}.
- Then k ≥ m¹⁰·x^{−1/2+O(ε)}, and k ≤ x⁵ gives **m ≤ x^{11/20−O(ε)}**.
- At that m the bracket gives G ≲ x^{O(ε)}(x/m + m + k/n²) ≈ x^{0.55}, a weaker conclusion, and Ee_T ≳ 2m·x^ε·U ≈ x^{0.55}·U.
- If instead every per-lift actual loss were m-independent (Ee_T absent), the actual consumption at m = x^{11/20} would be ≈ x^{0.45+O(ε)}·U. That contradicts the Ω-result, and a link would have to be false. **Ee_T is what prevents this.**

**The core inequality as a statement about zeros** *(mine, from LEDGER §2c and the explicit formula)*. Fix u0 and set c_p := 2·log p·min(x/p, 1).
- ASK(u0) counts inert p^i with weight 2·log p·(a_t/p^i − w_{j,partner})₊.
- The partner is thick iff t + h_p − u0 ∈ T2. So ASK − MAIN = De is, exactly, Σ over characters χ of Gal(E/ℚ) ≅ E0 × A of r̂_{u0}(χ)·(Riesz error of L(s, χ) at y ∈ {a/b ≈ x, a/w at tops and thin places, ≈ X′ or X″}).
- Here r_{u0}(h) = #{t ∈ TT : t + h − u0 ∈ T2} is a **nonnegative** class weight on the signal class.
- E is abelian, so every L(s, χ) is a Dirichlet L-function of conductor dividing d·q·2^{s+2}.
- Each error is −Σ_ρ y^ρ/(ρ(ρ−1)) + O(log cond).
- **The core asserts that this weighted zero sum is ≤ U·x^{1/2+O(ε)} at every x ≥ x₀ of the window.**
- After averaging over u0 ∈ A0, only ⟨ψ⟩ survives, with the positive (3 + 1_{A0}) coefficients. Per u0, the coefficients on ξ ∉ ⟨ψ⟩ have both signs.
- A real zero of L(s, χ_{−d}) enters with the favourable sign, through (1 − χ_{−d}).
- **GRH ⇒ core.** Σ_ξ |r̂(ξ)|/r̂(1) ≤ (|TT|·|T2|/n²)^{−1/2} ≤ √2·x^{9ε/16} by Cauchy–Schwarz and Parseval. So the error is ≤ x^{1/2+(9/16+2/5)ε+o(1)}·(mean r).
- **No known result contradicts it.** The conductors are exp(x^{Θ(ε)}) ≫ x, so unconditional zero-free and density results say nothing at y = x. The Ω-results are ≪ x^{1/2+9ε}.
- **Unconditional adversarial check.** Choose T2 to correlate with the actual primes. The arrangement-dependent part is Σ_p c_p·(r(h_p)/mean − 1). Its spread over arrangements is ≈ (Σ c_p²)^{1/2} ≈ (x·log x)^{1/2}. The best density-δ arrangement then reaches only x^{1/2}·(log x·log(1/δ))^{1/2}·x^{ε/16}, inside the budget.
  - The weight min(x/p, 1), not x/p, is what kills the small-prime bias: the cap removes the Mertens-type L′/L(1, ξ) main term from the arrangement-sensitive part.
  - So the core is not falsifiable this way. It shows the √x scale is intrinsic to the counting problem.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `EatT`, `Wtau` | DE:98-107 | the T-adic loss of word u at place w | carrier of the m-family | core definition (read) |
| `Eval`, `EDef` | DE:159-172 | E = EatT at T, for every j | pins Ee_T | glue (read) |
| `sg_atT` | WDS:887-901 | sg = −m·EatT at T | the m-fold recurrence | glue (read) |
| `SeenDef`, `AdmT`, `TuGe` | DE:62-64; DP2:186-190, 252 | seen places; T = ππ̄ near T*; b^{m/2} ≤ T | log T ≍ m·x^ε | core (read) |
| `Count5` | QSB:27-32 | log T bracketed by Lam5 and cCount·m·L | lower and upper bounds on log T | core hypothesis (read) |
| `flatDegVal`, `Fl.FlatDegree` | EFS:751-754; FDS:12-21 | flat degree with an exact q-term | second candidate | core-ish (read) |
| `RankVal`, `RankNums`, `SizeWindows`, `RestSize` | RV:28-32; SLN:34-43; GB:109-117; SC:53-58 | the constraints on m | maximal m | glue (read) |
| `EatI`, `sum_eatI` | DE:147-157; [ADM11] OLS:447-497 | the non-T losses | B₀-sized in total | read DE; OLS via node |

## 4. Oddities

1. **The exposition's "why 1/2" needs correcting** (MAIN §6.4, WHYHALF §0.4).
   - The per-lift loss that genuinely grows with m is the type-prime loss m·EatT·log T_u, which totals ≍ m²·W·x^ε.
   - It is not eE, not the signature residual, and not the adm11 losses at p ≤ X″.
   - The covolume q-part is a second, sign-unsettled candidate.
   - Stepanov's ℓ² overhead corresponds to "each of the m lifts is T-nonintegral by the full weight, and log T must hold m copies".
2. **Rigidity requirement on T*** *(mine)*. Σ r_i = ASK − Main ≥ −U·x^{1/2+O(ε)}, and the positive r's total ≲ m·U·x^{O(ε)}. So the Count5 slack ΣA·(log T_u − Lam5) must be ≲ x^{1/2+O(ε)}·U, i.e. log T* − Lam5 ≲ x^{O(ε)}·δ, out of ≈ m·x^ε.
   - The Lean has only log T ≤ cCount·m·L above (QSB:30).
   - If log T* exceeded Lam5 by x^c, the chain would assert ASK ≤ Main − x^{1/2+c}·U, which is false.
   - Computing logXu = (1/(fk))·log(D*/d*_u) against Lam5 is a finite, decisive check. This sharpens REVIEW2 A3.3.
3. **Design question for the author.** Suppose a variant used one prime T_j per lift, with lift j T-nonintegral only at T_j and log T_j ≈ x^ε. Then the T-loss would be m-independent per lift. Re-dimensioned to m = x^{11/20}, the chain would then prove G ≲ x^{0.45}, which is false. So something must make every lift carry the T-denominators (sg = −m·EatT). Which fact forces that?
4. **The seen-place reading is inferred.** If `seenP` failed at every place over T, EatT would vanish and Ee_T with it. The m-family would then have no identified genuine carrier besides the covolume q-part, and the "proves too much" question would reopen at m ≈ x^{11/20}.
5. The Wtau ≥ b lower bound at thick places is inferred from the weight formulas [STEPE]. The upper bound EatT ≤ 12fb is from ADM11 and was not re-read.

## 5. Coverage

Read in this pass:
- PROTOCOL; MAIN-ARGUMENT §0, §5, §6; REVIEW2 A3, A5 and its opinion paragraph;
- NODE-LEDGER, ADM11, DIVKEY, STEPE, WHYHALF and ACCOUNT in full; GATIE §0–1; INDEXBUDGET §0; E1LOOSE §0; WHERECONG §0; NONVAN §0; VOLUME §0–1, §4, oddities; COVOL §0–1; HEIGHT §0, §2(c)–4 (all as nodes).
- Lean: DA:195-212; RV:15-40; DP2:9-47, 180-190, 200-226, 248-254; SC:45-62; GB:105-125; EW:14-50, 125-140; QSB:12-56; MB:100-125, 138-165; SLN:28-45; EFS:740-756; FDS:8-22; ZON:58-70; DE:50-84, 85-172; WDS:880-902; QLD:160-166.
- Greps: `lg` definitions; `seenP`; `sg_atT`; `Tau`.

Not opened:
- the producers of Count5/`Conclusion5` and of T* (logXu, logΓ);
- AdmissibleOffTypeFamilyBound (EatT ≤ 12fb);
- the HC weight definitions behind Wtau;
- `lcv` against flat degree (the factor and sign of the q-term);
- Vvar (QSB:42);
- the J0 piece of E1.
