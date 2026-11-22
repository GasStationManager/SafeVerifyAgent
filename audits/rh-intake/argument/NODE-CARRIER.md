# NODE-CARRIER: which error-side term carries the √x barrier, and is the picture self-consistent?

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own computation or inference. [NODE] means taken from that node and not re-read. Nothing was compiled or executed.

Abbreviations: as in SHARP/FDEG/LEDGER (`DE`, `WDS`, `PFZ`, `DK`, `Par`, `TStep`, `EFS`, `FDS`, `ZON`). New ones:
- `ILB` = `Formalism/LocalToGlobal/HermitianForms/IsLocBasis.lean`; `DSW` = `.../HermitianForms/DetShiftShW.lean`; `DCo` = `Formalism/LocalRingCardinality/DataCoeff.lean`
- `FSt` = `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/FormsStable.lean`; `KIT` = `.../GlobalTwisting/KerIsTerm.lean`; `BFN` = `.../GlobalTwisting/BelowFiniteNonempty.lean`
- `GI/` = `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`; `UKS` = `GI/ExtInOfValIn.lean`; `SBS` = `GI/SharpBoundStabilityLatticeColumnChain.lean`; `FPL` = `GI/FivePointLawsTrueChains.lean`; `KLP` = `GI/TrueChainKernelsBoundLevelPrimePlaces.lean`; `TCR` = `GI/TrueColumnsRowSharpBounds.lean`
- `DDD` = `Formalism/LocalRingCardinality/DataDIVDefs.lean`

Units as in SHARP *(mine)*:
- U = |TT|·m·b·δ/2, which lies in [x^{5/2+6.8ε}/4, 2x^{5/2+8ε}]·b;
- W = Σ_ρ w_{jρ} ≈ δ·n·b is the weight mass of one lift;
- B₀ = f·m·b·x^ε, with B₀/U ≤ 8x^{2.125ε}.

"m-family" means total ≈ m·U·x^{O(ε)}. "x/m-family" means ≈ (x/m)·U·x^{O(ε)}.

## 0. Verdict

**Consistent. No ESCALATE.** I constructed a consistent scenario (§2.4). No inequality of the chain is forced false, and no true slack is forced above U·x^{1/2+O(ε)}.

1. **The barrier in the Lean's own chain is a class-(b) cost, so (II) cannot fail for the chain as built.**
   - The T-adic loss Ee_T = m·EatT·log T is not a bound on anything. It is the scaling exponent in the *definition* of N_u:
     - EatT is a `def` given by a formula (DE:103-107);
     - E is pinned to it by `EDef` (DE:159-172), a field of `ErrDefs` (DE:207-215), and by `ETDef` (PFZ:319-322);
     - N_u = Iu·NuLat with Iu = ∏𝔭_w^{−⌊e_w·sg⌋} (DDD:17-25), where sg = −m·EatT at T (`sg_atT`, WDS:887-901).
   - So the "true value" of this term is its booked value, ≥ 2m·x^ε·U [SHARP]. That is ≥ U·√x at every m in the window.
   - The chain's bound therefore always exceeds c·U·√x. Truth cannot contradict it.
2. **The T-cost is not forced. The Lean asserts no lower bound on any T-loss.**
   - EatT ≥ 2·Σ Wtau holds by definition. The divisibility inputs are upper bounds on denominators. KerP (KIT:110-113) is proved via `kerP` (KLP:17-59) from `PTerm` (BFN:83-89).
   - Constraint (I) does not force it either. The waste it creates is at most m·EatT·log T ≤ C·m·B₀ (`WeightBudgetBound`, PFZ:324-328), and that is ≤ U·x^{1/2+O(ε)} at the Lean's m.
   - A smaller EatT would need a stronger theorem, which the tree does not contain.
   - **By contrast, the g-prime loss m·ΣA·lg *is* forced in truth** *(mine)*. It is booked at ≈ x^{1+O(ε)}·U and offset by Count5's m·lg. Constraint (I) therefore forces the true g-adic denominators to match it to within U·x^{1/2+O(ε)}, i.e. to relative precision x^{−1/2} (§2.2).
3. **The mathematics FDEG left open (§2.3, mine).**
   - Sign convention. `ValTied.lat` (TStep:115-121) defines integrality in coordinates of a basis B of the **dual** of the class lattice, with an explicit factor ∏_τ det(B⁻¹z)^{s_i(τ)} (`fnOf`, ILB:40-47). de is the determinant in **self-dual-lattice** coordinates (TStep:97-100).
   - So de^s multiplies the integral polynomial by the *scalar* ∏_τ τ(det C_ℓB_ℓ)^{s_τ}. The convention is the same at levels i and i+1, so sharp's det^{+sSharp} and divDe's det^{−sDiv} move the valuation in opposite directions.
   - With one ϖ-defect at every level, the net is (t+1)/2 per τ per lift. This is the same exponent as KerUK and as the *proved gain* T^{f(t+1)/2} at unseen places (KerBar, KIT:105-108).
   - `unf` is an abstract field (DK:39). Its T-content enters only through KerP (an upper bound) and KerBar (a gain).
   - **True det-part loss ≈ f·(t+1)/2·log T per lift, i.e. poly(x)·m·x^ε.**
   - Two contributions remain undetermined, each ≤ W·log T: a seen-place scalar inside unf, and the top-coordinate drop (sharp only on extremal vectors).
4. **An honest class-(a) carrier exists: the covolume q-part, which is positive on the live hosts** *(mine)*.
   - flatDegVal = (p−q)/2·logΩ + q·(log d − lrd E) (EFS:751-755). This is an exact proved degree (FDS:12-21). l3m keeps only the (p−q) part (ZON:63-64), so the q-part sits inside l3u = B₀·log log x (ZON:66).
   - On the live hosts, log d ≍ Y^{ε/5}·log²Y ≫ log q ≍ Y^{ε/5} ≫ log n [HOSTSEL, HOSTS]. The conductor–discriminant formula then gives log d − lrd E ≈ ½·log d − ½·log q − O(log n) > 0.
   - The total is ≈ Σ_j 2q_j·W·(log d − lrd E) ≈ m²·W·½·log d, i.e. **≈ m·(n/|TT|)·log d·U = m·U·x^{O(ε)}**.
   - It is a true, positive covolume feature: the arithmetic degree of the flat determinant line on U(k+j−1, m−j) in its q_j = m−j negative directions. Summed over the descending layers it is triangular, Σ_j(m−j) ≈ m²/2.
   - It alone prevents a T-sharpened variant from proving too much.
   - Caveats: the factor 2w in lcv ↔ flat degree is inferred from l3m's normalisation, and a cancelling q·log d term in the Rallis scalar is not excluded, since L6 is a lower bound only.
5. **Prediction from (I).** The Hadamard defect h_bound − log‖B_u‖_true is a slack in Bost, so it must be ≤ U·x^{1/2+O(ε)}. Against h ≈ x^{4.5}·U, that is relative precision x^{−4}. This is plausible if the heavy components chain highest-weight vectors to highest-weight vectors *(mine)*. It is a falsifiable prediction of the Lean's correctness, not an inconsistency.

## 1. Statement (what was read)

**The T-cost is definitional.**
- `Wtau` (DE:98-101) is the max over i ≤ m and non-top rows a of |λ_i(τ)_a − ⌊i(t+1)/2⌋|.
- `EatT` (DE:103-107) = [seen w]·(2ΣWtau + f·Nm + |tops|(t+1)(m+1)/4).
- `Eval` (DE:159-169) gives EatT at resChar w = T_u. `EDef` (DE:171-172) gives L.E = Eval. `ErrDefs.edef` (DE:214).
- `ETpi`, `ET_eq`, `Conclusion5Sharp`, `ETDef` and `WeightBudgetBound` (PFZ:304-328):
  - Conclusion5Sharp: c·colT maps Nlam into S at every valuation n ≥ e_w·m·ET;
  - WeightBudgetBound: ETpi·log T ≤ C·B₀.
- `Iu` and `NprimeDef` (DDD:17-25): N_u = (∏𝔭^{−⌊e·sg⌋})·NuLat.

**Integrality at a level-T point.**
- `ValTied.lat` (TStep:115-121): x is integral iff, for every place w, every class c and every local basis B of `dualSet(clsCrd c)`, emb x c z = fnOf(shiftOf(lamT u i))(B⁻¹)(P)(z) with P ∈ IntSpan.
- `fnOf` (ILB:40-45) = ∏_τ det(M_τ y_τ)^{s_τ}·P(M y).
- `shiftOf` = detShift (ILB:47), where detShift = the last coordinate of the weight (DCo:21).
- `lamT` = shW(λ_i, ⌊i(t+1)/2⌋) (TStep:61-62; DSW:9-14).
- `ValTied.de` (TStep:97-100): de_i(z, τ) = τ(det C)·det(z_τ), where C*C = gram and C maps the self-dual L0 onto O^N.
- `StepLevel` (ILB:58-80): Lb ⊂ Lb^#, T·Lb^# ⊆ Lb, [Lb^# : Lb] = T^{2f}. It is carried at every level by `ClsTied` (TStep:70-89).

**The step.**
- `ColumnChain.unf` is an abstract field (DK:39).
- `sharp` multiplies by ∏de_i^{sSharp}, `divDe` divides by ∏de_{i+1}^{sDiv}, and Kmap = ρ·divDe∘unf∘sharp (DK:57-65).
- sSharp_i = e_i − N(i+1)/2 and sDiv_i = e_i − N(i)/2 (DK:41-47; Par:71-73), with N(j) = k + j(t+1) (Par:36). `FactSDivSharp`: sDiv − sSharp = (t+1)/2 (DK:223-225).

**What the Lean asserts about unf at T.** `KerPt` and `KerLaws` (FSt:202-238) have the following content.
- **UKLaw**: Σ over U-neighbours = T^{(t+1)/2}·(…).
- **IntBar**: at unseen w, K(y) = T^{f(t+1)/2}·(integral). This is a *gain*.
- **IntP**: at seen w, T^{fN(i)+ΣsDiv}·K(y) is integral.

Where these come from:
- They are produced in `sharpBound_stability_latticeColumnChain` (SBS:17-57) from `KerUK/KerBar/KerP` (KIT:101-113). Those come from `laws_true_fam` (FPL:46-62).
- KerP is `kerP` (KLP:17-59), from `PTerm` (BFN:83-89; exponent fN(i) − Σ detShift(λ_{i+1}), which equals fN(i) + ΣsDiv by KLP:44-56). PTerm is supplied by `pTerm_std` under `JetMoments` and `InducedSimpleLowestAlcove`.
- `AlcoveAt` (BFN:95-96) requires 2(λ_a − λ_b + N) < T.

**What ukSharp books.** `ukSharp` (UKS:155-198) books e = Σ_{v∉VVT} λ_{i+1}(τ_v)₀ + fN(i) + ΣsDiv ≤ 2ΣWt + fN(m).
- `WtBounds` (FSt:307-311) gives 0 ≤ sDiv ≤ Wt and detShift(λ_{i+1}) = −sDiv.
- It is consumed by TCR:17-50, which yields ColGeTw at −m·EatT.

**The covolume.**
- `deg_eq_toFrame` (EFS:712-714): deg s = deg(frame part) + q·(log d − lrd E).
- `flatDegVal` and `FlatDegree` (EFS:751-755).
- `Fl.FlatDegree` (FDS:12-21) states N.deg = (p−q)/2·Re logΩ + q·(2·log√d − log rd E).
- ZON:63-66: l3m_j = Σ_ρ((k+j−1) − (m−j))·w·logΩ, and l3u = B₀·log log x.

## 2. Argument

### 2.1 Classification of every error-side term (task 1)

Sizes and ratios are taken from SHARP/LEDGER/ADM11/STEPE/INDEXBUDGET/WHERECONG/NONVAN, except where marked *(mine)*.

| term | class | booked (/U) | true size (/U) | true ≈ booked? |
|---|---|---|---|---|
| Count5 slack ΣA·(log T − Lam5) | (a) | 8cCount·x^{1/2+2.07ε} (x/m) | ΣA·O(L) [FDEG §2.1], x/m | yes |
| source floor L3 | (a) | x/m | (a/k)·log T + nT·a·log k [TFLOOR] | yes |
| DIV boundary, HN spread | (a) | x/m | x/m [SHARP] | plausibly |
| **Ee_T = m·EatT·log T** | **(b)**, definitional | m-family, ≥ 2m·x^ε | = booked (it *is* the lattice) | by definition |
| Ee_g main part m·ΣA·lg | (b), offset by Count5's m·lg | ≈ x^{1+O(ε)} | **forced** to within U·x^{1/2+O(ε)} (§2.2) | forced |
| Ee off T and g (adm11) | (a) | 848·m·B₀ | U·x^{O(ε)} [ADM11] | no, factor m |
| eE (Fock–hook) | (a) | m-family | (δ/2)·B₀ total [SHARP] | no, factor m |
| pq/logΩ residual | (a) | m-family | ≈ 0, since Σ_j(2j−1−m) = 0 | no |
| δ (top k·b′) | (a) | x/m | slack [STEPE] | no |
| covolume l3u: q-part | (a), exact formula | m-family | **≈ m·(n/\|TT\|)·log d, positive** *(mine)* | **yes** |
| covolume l3u: non-flat HS part | (a) | m-family | ∝ q_j·W, sign unknown [VOLUME] | unknown |
| E1 (test-lattice index) | (a) | m-family | unknown; J0 piece open [E1LOOSE] | unknown |
| E2 (congruence modules) | (a) | k/n² + f·m·b·L² per layer | Ш ≤ √b; rest unknown. Heuristically Σ_ρ w·log w per layer, i.e. U·x^{O(ε)} total *(mine, speculative)* | unknown |
| floors ⌊e·sg⌋ | (b) | ≤ C·X″ (SLP) [ADM11] | = booked | negligible |
| T window, the T* formula, the windows m, k, n | (b), choices | — | — | — |
| Hadamard defect h − log‖B_u‖ | slack in Bost | — | must be ≤ U·x^{1/2+O(ε)} | prediction |
| frame (η + 4√e)·HH, log\|W\|, MLo5 | (a) | negligible | negligible | — |

**Is EatT a free field? No.**
- EatT is a `def` (DE:103). E = Eval is a record clause (DE:171-172), not a free choice.
- A smaller EatT would leave adm2 at T unproved. Its T-branch needs ColGe at −m·EatT (`admissible_at_twist_places` [ADM11]; TCR:36-50).
- That ColGe rests on KerP with exponent fN(i) + ΣsDiv, which is the exponent `PTerm` proves.
- The hypothesis `WeightBudgetBound` (PFZ:324-328) caps the cost, ETpi·log T ≤ C·B₀. It does not floor it.

### 2.2 Forced and unforced losses (task 2) *(mine)*

**The test.** For the m·EatT cost to be forced, truth would have to rule out a larger N_u.
- Let N_u′ ⊇ N_u be the largest lattice with B_u(N_u′) ⊆ cc. Bost's slack is then ≥ μ(N_u′) − μ(N_u).
- By (I), every slack is ≤ U·x^{1/2+O(ε)}.

**At T: not forced.**
- μ(N_u′) − μ(N_u) ≤ m·EatT·log T·(…) ≤ C·m·B₀ ≈ 8C·m·x^{2.1ε}·U. At m ≈ x^{1/2−ε/16} this is ≤ U·x^{1/2+O(ε)}.
- So (I) is met whatever the true T-denominators are, and **no lower bound on the T-loss follows from truth either.**
- I saw no statement in the tree that bounds a T-loss from below. The only "≥" is the definitional EatT ≥ 2ΣWtau.

**At g ∈ {g₀, g₁}: forced.**
- The booked g-loss is m·ΣA·log(g₀g₁) ≈ (2x·lg/δ)·U ≈ x^{1+O(ε)}·U.
- It is cancelled by the +m·lg inside Count5's lower bound on log T (LEDGER L4, L5, L7).
- Suppose the true g-adic denominators were smaller by D. Then N_u could be enlarged by D at g with nothing else changing, and the chain would give ASK ≤ Main + Err − D.
- Truth therefore forces **D ≤ U·x^{1/2+O(ε)}**: the column chain is non-integral at g by the booked ΣA·log g per lift, to relative precision x^{−1/2}.
- This is plausible. At g the adm2 content is a homogeneity statement: vNN = Σ_τ nuAbs·v(π̄_g) (DE:88-89). Homogeneity is exact.

**The inequalities that would be false if a true quantity were small are on the gain side, not the loss side.** These are Ga ≥ ASK − LoP (L10), and adm2's positive-exponent divisibility at inert and signal places [ADM11 §2c]. They are lower bounds on gains.

### 2.3 The T-adic step: sign of the det twist, and what unf does (task 3) *(mine, on the Lean definitions of §1)*

Write δ_ℓ := det(C_ℓB_ℓ) and a_ℓ := v_w(τ(δ_ℓ)), where B_ℓ is a basis of the dual of the level-ℓ class lattice and C_ℓ⁻¹ is a basis of the self-dual L0.

1. **Integral functions.** Integral level-ℓ functions have the form det(B_ℓ⁻¹z)^{s_ℓ}·P(B_ℓ⁻¹z) with P integral (TStep:115-121; ILB:40-47).
2. **A det twist is a scalar.** Since de_ℓ(z) = δ_ℓ·det(B_ℓ⁻¹z) (TStep:97-100), de_ℓ^s maps integral functions to integral functions times the **scalar** ∏_τ τ(δ_ℓ)^{s_τ}. The valuation moves by Σ_τ s_τ·a_ℓ(τ) on **every** monomial.
3. **Same convention at both levels.** Both B's are dual-lattice bases and both C's are self-dual-lattice bases. So the step contributes Σ_τ [sSharp_i·a_i − sDiv_i·a_{i+1}].
4. **The net.** Each level carries one T-defect, Lb = N ⊕ O·πe_last [TDIV, FDEG §2.2] (`StepLevel` at every level, TStep:70-89). So a_i = a_{i+1} = a ∈ {0, −1}, and the net is −a·Σ_τ(sDiv − sSharp) = |a|·|Tau|·(t+1)/2 (DK:223-225).
   - One twist raises the valuation and the other lowers it, by sSharp ≈ sDiv ≈ w each. They cancel down to (t+1)/2.
   - Over the whole chain this telescopes to m·|Tau|·(t+1)/2.
5. **Cross-check.**
   - The same exponent is what the Lean *proves* as a **gain** at unseen places (IntBar/KerBar: K = T^{f(t+1)/2}·integral, FSt:220-222, KIT:105-108).
   - It is also the U-commutation factor (FSt:216-218).
   - The lowest-alcove hypothesis (BFN:95-96) makes the reductions simple. That makes equivariant lattice comparisons scalar, which supports the reading that the det part is a pure scalar.
6. **unf.**
   - It is an abstract linear map (DK:39). Its T-content is visible only through KerP (an upper bound, fN(i) + ΣsDiv at seen w) and KerBar.
   - At seen places it may carry a further scalar, e.g. a π̄-power from evaluating at level-datum points as in TDIV. By the product formula such a scalar would carry an equal archimedean gain, which the per-lift Fock bound does not book.
   - Whether that scalar exists cannot be decided from the Lean.
7. **The top-coordinate drop.** This is the Σ_{v∉VVT} λ_{i+1}(τ_v)₀ in `ukSharp` (UKS:171-178). It costs λ₀ ≈ w only on vectors with extremal last-row degree.

**Rank N versus Sym^a.** The det part is identical in both, because a det twist is scalar on every monomial.

**Conclusion.** The true T-loss per lift is f·(t+1)/2·log T (det part), plus an undetermined seen-place scalar in unf, plus the drop on the actual vectors. In the model the total is poly(x)·m·x^ε. The booked per-lift loss is ≈ EatT·log T ≈ B₀. **The booking is ≤ the truth + B₀ in all cases, and is consistent with the truth being a factor b/poly smaller.**

### 2.4 Joint constraints and a consistent scenario (task 4) *(mine)*

**Two constraints on any scenario.**
- **(II).** At true values, ASK − Main ≤ Σ(class-(b) costs as defined) + Σ(class-(a) terms at their true sizes).
- **(I).** Every slack is ≤ U·x^{1/2+O(ε)}.

**The scenario.** It satisfies (I), (II) and the Ω-results at every admissible m, including SHARP's re-dimensioned m ≈ x^{11/20}.

| term | assigned true size /U | why admissible |
|---|---|---|
| x/m family (Count5, floor, boundary) | (x/m)·x^{O(ε)} | as booked |
| Ee_T | det model: poly·m·x^ε/U → 0 as a *true denominator*. The chain still *pays* ≥ 2m·x^ε | the lattice is defined smaller. The Bost slack is ≤ 8C·m·x^{2.1ε} ≤ x^{1/2+O(ε)} at the Lean's m, so (I) holds |
| Ee_g | = booked, to within U·x^{1/2+O(ε)} | forced (§2.2); homogeneity |
| eE, adm11, pq residual | x^{O(ε)}, x^{O(ε)}, ≈ 0 | [SHARP, ADM11] |
| **covolume q-part** | **≈ m·(n/\|TT\|)·log d ∈ [m·x^{2ε/15}, 2m·x^{ε/8+ε/5}]·polylog** | exact positive degree. It is ≤ C·l3u per layer, since per layer 2q_j·W·½·log d ≤ f·m·b·log d ≤ B₀ |
| non-flat HS part, E1, E2 | ≤ their budgets; say U·x^{O(ε)} | not determined |
| Hadamard defect | ≤ U·x^{1/2+O(ε)} | highest-weight alignment of the heavy component |

**Check of (II).**
- At x with G ≥ c·√x, the chain bound is at least the class-(b) cost m·EatT·log T ≥ 2m·x^ε·U ≥ c·U·√x.
- In a hypothetical T-sharpened variant at m ≈ x^{0.55}, the covolume q-part supplies ≈ x^{0.55+O(ε)}·U ≥ c·U·√x.
- So that variant would prove only G ≲ x^{0.55+O(ε)}, not G = o(√x).

**Check of (I).** Every slack listed is ≤ U·x^{1/2+O(ε)} at the Lean's m ≈ x^{1/2−ε/16} (RV:30).

**What each "m-family" candidate is, in truth.**
- **(i) Covolume q-part.** A genuine class-(a) term of true size ≈ budget. Its meaning: on U(k+j−1, m−j) with CM type pulled back from K (`IsTypeFn` [VOLUME §4]), the flat section's period at the q_j conjugate embeddings is z₋ rather than z₊. Each negative direction therefore costs (log d − lrd E) per unit weight relative to the p-directions (EFS:712-714). Descending from the definite top layer (q = 0) adds one negative direction per layer, which gives Σ_j q_j = m(m−1)/2. This is the arithmetic counterpart of Stepanov's ℓ² overhead.
- **(ii) E1.** Not settled. The discriminant budget has a power of x to spare; J0 is open [E1LOOSE].
- **(iii) E2.** Not settled. Ш is idle (≤ √b).
- **(iv) Hadamard defect.** Slack on the height side.
  - It is forced small by (I), to relative x^{−4}.
  - It is not constrained by (II), because slack only raises the bound.
  - Joint consistency needs the composite to be near-isometric on the heavy highest-weight line. That is consistent with Bost's mean form [TFLOOR §2.3].

**When a contradiction would appear.** Only if, simultaneously:
- (A) the true T-loss is poly per lift;
- (B) the q-part is cancelled elsewhere, or log d − lrd E ≤ 0;
- (C) E1, E2 and the HS part are truly o(m);
- (D) someone proved (A).

Then a sharpened chain at m = x^{0.55} would give G ≲ x^{0.45}, which is false. So **at least one of (A)–(C) must fail in truth**. The Lean proves none of them false and assumes none of them true. This is a constraint on the mathematics, not a falsity in the tree.

### 2.5 Verdict (task 5)

**Consistent.**
- In the Lean, the barrier is carried by the definitional T-cost m·EatT·log T. That cost is a choice of the lattice, it is permitted by (I), and it cannot be undercut without a stronger theorem than KerP.
- In truth, the barrier is honestly carried by the covolume q-part Σ_j 2(m−j)·W·(log d − lrd E) ≈ m·U·x^{O(ε)}. It is positive because log d ≫ log q ≫ log n on the live hosts.
- If the q-part were cancelled, one of E1, E2, the HS part or the unf seen-place scalar would have to be ≳ B₀·x^{−1/20} per lift.

No inequality is shown false. **No ESCALATE.**

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `EatT`, `Eval`, `EDef`, `ErrDefs` | DE:98-107, 159-172, 207-215 | T-loss by formula; E pinned | class (b) | definition (read) |
| `Iu`, `NprimeDef` | DDD:17-25 | N_u = ∏𝔭^{−⌊e·sg⌋}·NuLat | the lattice is defined | definition (read) |
| `ValTied.lat`, `.de`; `fnOf`, `shiftOf`; `detShift` | TStep:97-121; ILB:40-47; DCo:21 | dual-basis integrality with det^s; de in self-dual coordinates | sign convention | definition (read) |
| `sharp`, `divDe`, `Kmap`, `unf`; `sExp`, `sExp'` | DK:39-65, 223-225; Par:36, 71-73 | step = det^{sSharp}∘unf∘det^{−sDiv}; unf abstract | mechanism | definition (read) |
| `KerPt`: UKLaw, IntBar, IntP; `KerLaws` | FSt:202-238 | T^{(t+1)/2} commutation; gain T^{f(t+1)/2} unseen; cost T^{fN+ΣsDiv} seen | the T-content of unf | core (read) |
| `KerUK`, `KerBar`, `KerP` → `kerP` → `PTerm` | KIT:101-113; KLP:17-59; BFN:83-96; FPL:46-62; SBS:41-57 | the proved T-adic kernel bounds | upper bound only | core; `pTerm_std` body not read |
| `ukSharp`, `WtBounds`, `UKSharp` | UKS:155-198; FSt:307-316 | per-step booking ≤ 2ΣWt + fN(m) | booking | glue (read) |
| `Conclusion5Sharp`, `ETpi`, `ETDef`, `WeightBudgetBound` | PFZ:304-328 | denominator ≤ m·ET; cap ETpi·log T ≤ C·B₀ | cap, not floor | core (read) |
| `sg_atT` | WDS:887-901 | sg = −m·EatT | glue | read |
| `flatDegVal`, `deg_eq_toFrame`, `Fl.FlatDegree` | EFS:712-714, 751-755; FDS:12-21 | exact q·(log d − lrd E) term | honest carrier | core (read) |
| l3m, l3u | ZON:63-66 | the q-part sits in l3u | booking | read |

## 4. Oddities

1. **Booking asymmetry at T.**
   - KerP charges sDiv (≈ w) and credits nothing for sharp's sSharp. Yet at the conjugate (unseen) places the tree proves a *gain* T^{f(t+1)/2} (KerBar).
   - In the det model, the seen-place truth should also be ≈ (t+1)/2 per τ.
   - This is safe for validity. It means the Lean's "carrier" Ee_T is an artefact of the proof's bookkeeping.
2. **The g-prime loss is the one booked loss that truth forces to precision x^{−1/2}** (§2.2). A reviewer checking DegreeCountBound/UsedTuplesBoundByConstant [ADM11 oddity 4] should know that this sharpness is *required*, not merely sufficient.
3. **The sign of log d − lrd E rests on my inference.**
   - It uses the conductor–discriminant formula with inertia of order 2 at d and at q, and the host sizes from HOSTSEL/HOSTS.
   - The structure Gal(E/ℚ) ≅ {±1}² × A was not re-read.
   - The factor 2w (lcv ↔ flat degree) is inferred from l3m's normalisation.
4. **No lower bound on any loss was seen** in the files read. The only lower-bound content used in the chain is on gains: (L10) and adm2's positive exponents.
5. **The Hadamard sharpness to relative x^{−4} is a consequence of the theorem plus Ω.** It is not proved, and it is worth a numerical spot-check on a toy chain.

## 5. Coverage

**Read in full:**
- PROTOCOL; NODE-SHARP, FDEG, TFLOOR, TDIV, TU, LEDGER, DIVKEY, STEPE, ADM11, COVOL, HS, VOLUME, INDEXBUDGET, WHERECONG, NONVAN.
- MAIN-ARGUMENT, HOSTSEL and HOSTS by grep for the sizes of d and q.

**Lean, read:**
- DE:1-218; TStep:1-131; ILB:1-153; DSW:1-47; DCo:21-23, 52-56 (grep); DK:1-247; Par:15-84;
- FSt:150-329; UKS:150-198; GI/LevelChainSharpColumnValuationOfPointKernelLiftL.lean:1-93; SBS:1-59; GI/IntPOfKerP.lean:1-37; KIT:1-130;
- TCR:1-52; FPL:1-64; GI/FivePointLawsTrueChainsStatement.lean; KLP:1-61; GI/KernelJetsLevelPlaceIntegralMomentsStatement.lean; BFN:40-110;
- PFZ:285-330; WDS:885-902; DDD:10-30; EFS:700-756; FDS:1-25; ZON:55-95.

**Greps run:** `def fnOf|shiftOf|shW|atInf|dualSet|IsLocBasis`; `detShift|natW|delSq|extremal`; `KerLaws|KerTie|ValTie|LevTie`; `sharpBound_stability_latticeColumnChain`; `def KerP|KerBar`; `def PTerm|pTerm_std`; `EatT` (all files).

**Not opened:**
- `pTerm_std`, `jetMoments` and `weylModule_simple_closedLowestAlcove` bodies;
- `trueChainKernels_bound_conjugatePrimePlaces`; the `Unf`-record producers;
- `exists_coordinates_valueLattices_eq_weylLattices` (the valB ↔ ValTied link);
- the L6 Rallis-scalar factors (a possible cancelling q·log d term); the host field structure (Gal(E/ℚ)) behind lrd E.
