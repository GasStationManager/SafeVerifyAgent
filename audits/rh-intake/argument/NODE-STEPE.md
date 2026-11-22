# NODE-STEPE: the size bound on the DIV remainders (`stepE_num`), its three inputs, and the Chowla–Selberg constant

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own algebra, Stirling estimates or inference. [NODE] means taken from that node and not re-read. Nothing from the tree was compiled or executed. The only thing I ran was a 15-line Python check of my own model formulas (§2.3), which used none of the tree's code.

Abbreviations:
- `NL` = `Formalism/LocalToGlobal/Divisibility/NumbersLink.lean`; `NUM` = `.../Divisibility/Numbers.lean`; `NLem` = `.../Divisibility/NumbersLemmas.lean`; `ZON` = `.../Divisibility/ZscOfNum.lean`
- `TDR` = `Formalism/QuotientMetricDivisors/TheoremDivIneqRows.lean`; `TDRS` = `Formalism/QuotientMetricDivisors/TheoremDivIneqRowsShift.lean`; `FW` = `Formalism/QuotientMetricDivisors/FinalW.lean`
- `YDH` = `Formalism/QuotientMetricDivisors/HermitianTwistDivisors/YoungDiagramHook.lean`; `YDT` = `.../HermitianTwistDivisors/YoungDiagramTopExact.lean`
- `SS` = `Formalism/LogFactorialIndices/StatementSize.lean`
- `PWN` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/PaddedWittNormSquare.lean`; `NFL` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFockLSqLe.lean`; `CM` = `Formalism/LocalToGlobal/Divisibility/CoefMod.lean`
- `MLP` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogPeriodChowlaSelberg.lean`; `MLC` = `Development/AbelianVarietyTheory/Proofs/FoundationProofs/MeanLogPeriodConjugatesEqChowlaSelberg.lean`; `DZE` = `Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/DedekindZetaEqSumRealEisenstein.lean`; `MPL` = `Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/MeanPeriodLogarithms.lean`; `IDT` = `Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/IsDiscriminantTwelfthRootOfIdealLattice.lean`; `PER` = `Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/PeriodRelations/Period.lean`; `LCN` = `.../PeriodRelations/LeadingConstantNeZero.lean`
- `KHC` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/KernelHalfChainNumbersAnyLevelPrime.lean`; `HOST` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean`; `TCG` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolG.lean`; `IPF` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/InnerProductFormula.lean`

## 0. Verdict

1. **`stepE_num` is proved, fully elementarily, and read to the bottom.** No hypothesis about real objects enters it. It uses three inputs:
   - the explicit formulas for the weights (ν from Harish-Chandra parameters, a⁺ from the Rallis side), which make the rows of ν and of a⁺ **interlace**;
   - the classical inequality **hook product ≥ ∏ (row length)!** (`young_diagram_hook`, YDH:386-422);
   - **ph(n) ≤ log n!** together with the mean-value bound ph(y) − ph(y′) ≤ (y − y′)·log y.

   The bound it proves is true. My model Stirling computation (§2.3) agrees with it, and the bound is tight up to a factor of about 2 in the remainder. **No ESCALATE from task 1.**
2. **Size and booking of eE** *(mine)*. eE_{jρ} is genuinely ≈ w·log a at a top and ≈ w·log w elsewhere, so it is not small. Summed over (j, ρ) it is ≈ m·f·b·La, which falls in the **per-lift ("m") family** of the 1/2 balance (booked as 15C₀·m(B₀+Nc)xe by AbE [DIVKEY]). It is **not** a C·a·La-per-top term. δ is likewise a per-lift term.
   - The k·b′ allowance for tops in the δ bound is unused slack in the proof (§2.2).
   - So the m-independent C₀|TT|a·La that DIVKEY/HEIGHT attribute partly to "the top part of δ" is, for δ, pure slack.
3. **The Chowla–Selberg constant matches the classical one exactly** (§4, my derivation from the Kronecker limit formula). The in-tree identity is:
   - mean over classes of log(4π·y·|η(τ)|⁴) = γ + log(2π/√d) − L′/L(1, χ_{−d});
   - equivalently, mean over conjugates of log(area(Λ^ρ)/π) = γ + log(2π/√d) − L′/L(1, χ), for lattices with g₂³ − 27g₃² = 1.

   It is **proved in-tree** from the first Kronecker limit formula and the class number formula (DZE:83-154, 222-243; MLC:141-195). This is the classical elliptic Chowla–Selberg formula, not Colmez's averaged formula.

   The record's logΩ = γ + log(2π/rd_E) − L′/L(1) differs from it by −log(rd_E/√d). That difference is accounted for exactly, by measuring the period against an 𝒪_E-ideal (brN, the norm of AA0·𝔇_{E/K}; MLP:17-56, 58-82).

   The sign and the coefficient of L′/L(1, χ_{−d}) are right. **No ESCALATE from task 3.**
4. **Consistency of normalisations across (a), (b) and (c) is only partly enforced, and I found no explicit comparison lemma.**
   - logΩ is one shared symbol (`Nd.logOm`, `N.logOm`) in (a) and (c), and it is tied to the true period through proved Chowla–Selberg on the (a) side (KHC:316-320 → MLP:84).
   - The norms are three different ones:
     - (a) is the Fischer–Fock norm on VV_λ, divided by the Fock norm of the extremal vector (NFL:71-77; CM:160-176);
     - (b) is the Fock norm of the Weil-representation vector δ (IPF:147-149);
     - (c) is "Petersson × (2πx)^{−|wt|/2}, probability measure" [COVOL], compared to the realised norm through `covering_meas_of_prints` (TCG:47; not opened).
   - They meet only through the frames that the composition lemmas share by type (`height_chain_atR`, `SpecDet`) [HEIGHT; DETSIG]. I did not find a single lemma stating that the definite frame XT_j of the Rallis scalar is the pairK-normalised Fock frame of the jet bound.
   - This is **NEEDS-DETAIL, not ESCALATE**. No computation shows a mismatch. A mismatch c^{|wt|} would sit inside L6's Published-premised proof or inside the covolume hypotheses, not in the proved parts (§3.4).

## 1. Statement

`stepE_num` (NL:388-394): for every lift j ∈ {1..m} and place ρ,

  eE_{jρ} ≤ C₀·(w_{jρ} + S + N² + m(t+1)η)·La,   |δ_{jρ}| ≤ C₀·(w_{jρ} + k(N + S) + m(t+1)η + [ρ∈TT]·k·b′),

where (NL:32-39):
- eE_{jρ} = Σ_i ph(ν_{jρi}) − logHook_{jρ} − [ρ∈TT]·ph(a_ρ);
- δ_{jρ} = Σ_i ν_{jρi} − [ρ∈TT]·a_ρ − k·w_{jρ}.

The objects, unfolded:
- **ph(u) = u log u − u** (SS:7). For an integer n, ph(n) = log n! − ½log(2πn) + O(1/n) *(mine, Stirling)*.
- **logHook_{jρ} = log hookProd(apDiag_{jρ})** (NUM:245).
  - hookProd(μ) = ∏_{cells (i,c)} (μ_i − c + μ′_c − i − 1) in 0-indexed form, i.e. the product of hook lengths (SS:35-36).
  - apDiag is the Young diagram whose rows are ⌊a⁺_{j,ρ,i}⌋, i < k − 1 + j (NUM:239-243).
  - So logHook = log H(a⁺) = log(|a⁺|!/f^{a⁺}). By the Frobenius identity, H = ∏ℓ_i!/∏_{i<l}(ℓ_i − ℓ_l) with ℓ_i = a⁺_i + p − 1 − i. That is NODE-L6's logHook(n, a) formula, the Rallis main term.
- **The Fock weights** (NUM:224-225): ν_{jρi} = srcPar_{ρ,i} + e_j(ρ) − (N_{j−1} + N_j − 1 − 2i)/2, for i < N_{j−1}.
  - srcPar is u_i (with the inner entries replaced by v_{i−1} − ½ − Del·δ_i) for i < k (NUM:211-222). For i ≥ k it is a block of −e_j + (t-shifts), i.e. the small block "blk".
  - At a top, u₀ = a_t + (k−1)/2 (NUM:247-248). So ν_{·,0} = a_t + w′ with w′ = w − s_j, s_j = (k + (2j−1)(t+1))/2 (NL:41).
- **The hook weights** (NUM:182-184): a⁺_{jρi} = sigPar_{ρ,i} + e_j − (nV − 1 − 2i)/2 − (p_j − q_j)/2, with sigPar = (v_1..v_{k−1}, −b_1, …) (NUM:178-180).
- **Interlacing** (`NumFacts.inter`, NL:75-76): u_{i+1} < v_i < u_i. This is the Gelfand–Tsetlin branching between the k-row source weight and the (k−1)-row hook weight.
- **w** = e_j(ρ) (NUM:160-163). The size facts are s_j ≤ w ≤ 2b (`sw`, `w2b`, NL:47, 68-69).

## 2. Argument

### 2.1 The chain of the proof
`stepE_num` (NL:395-537) instantiates `rowsStepEOrigin` (FW:29 = `young_diagram_step_origin`, YDT:254-295; statement TDRS:129-166). Its hypotheses are discharged by:
- `nu_eq_originRow` and `aPlus_eq_originBig` (NLem:217-230), which are `ring` identities;
- the interlacing field `inter`;
- `hookLower_of rowsHook` (NLem:537-541), i.e. logFactRows(apRows) ≤ logHook.

`young_diagram_step_origin` performs three steps.
1. It shifts w to w′ = w − s_j (YDT:273-282).
2. It converts the origin formulas into the "rows" shape (`young_diagram_origin_off/top`, YDT:212-252). Interlacing of real parameters becomes integer interlacing ar_i ≤ ν_i + T, ν_{i+1} + T ≤ ar_i, with T = (j−1)t (YDT:185-208).
3. It calls `young_diagram_step_shift` (YDT:10-61) → `young_diagram_step` (YDH:492-548). That theorem *defines* eE and δ as the remainders and bounds them through `young_diagram_factorial` and `young_diagram_period`.

**The mathematics of `young_diagram_factorial` (YDH:250-331), top case** *(the Lean's steps, in words)*. The rows are:
- ν = {a + w′, r₀, w′ + c_1, …, w′ + c_n} ∪ blk, with n = k − 2, r₀ ≤ w′, 0 ≤ c ≤ S and Σblk ≤ m(t+1)η;
- a⁺ = {r_0..r_n} ∪ sm, with |r_i − (w′ + c′_i)| ≤ sh = (j−1)t and c, c′ interlacing.

The steps:
1. logHook ≥ Σ_i log(r_i!) ≥ Σ_i ph(r_i). This uses `young_diagram_hook` (H(μ) ≥ ∏μ_i!, since every hook in row i is at least the arm + 1) and ph(n) ≤ log n! (YDH:142-162).
2. Pair ν-row w′ + c_i with a⁺-row r_{i+1}. By ph(y) − ph(y′) ≤ (y − y′)·log y (YDH:30-46, 85-107), each pair costs ≤ (c_i − c′_{i+1} + sh)·La. The telescoping sum Σ(c_i − c′_{i+1}) ≤ S comes from interlacing (YDH:212-217).
3. The unpaired terms are ph(a + w′) + ph(r₀) − ph(r_0) + phRows(blk). They are ≤ ph(a) + (2w′ + Bl)La + 1 (YDH:231-248), because:
   - ph(a + w′) − ph(a) ≤ w′·log(a + w′);
   - ph(r₀) ≤ w′·La;
   - −ph(r) ≤ 1;
   - phRows(blk) ≤ Bl·La.

   Result: Σph(ν) − logHook ≤ ph(a) + (2w′ + S + n·sh + Bl)·La + 1 (TDR:39-41).
4. In the off-top case (YDH:256-294) ν has one more w-sized row than a⁺. That row's ph(w′ + c_last) ≤ (w + S)La is the remainder.
5. Finally, `arith_fact_top/off` (YDH:432-460) absorb n·sh ≤ N², Sc ≤ C₀S, etc. into the stated C₀(w + S + N² + Bl)·La.

**`young_diagram_period` (YDH:350-375)** shows Σν = a + k·w′ + δ₀ with −w ≤ δ₀ ≤ nS + Bl at tops, and 0 ≤ δ₀ ≤ (n+1)S + Bl off tops. Then δ = δ₀ − k·s_j (YDT:20), and |k·s_j| ≤ k·N.

### 2.2 What this means
- eE is the **branching defect**. The Fock (jet) weight has k rows, of which one carries a_t at a top. The Rallis hook weight has k − 1 big rows. Their row-by-row factorials cancel to within the interlacing slack, which leaves one unmatched w-sized row: a + w′ at a top, or w′ + c elsewhere.
- **The top a_t row is not in the hook product**, which confirms DIVKEY's inference. Its ph(a_t) survives exactly. Its overlap with the k·w block costs only w·log a.
- **Unused slack.** In `young_diagram_step` the top δ bound is obtained from arith_per with X = k·b′ ≥ 0 merely added (YDH:527-531). The true top deviation is ≤ w + nS + Bl + kN. So the "[ρ∈TT]·k·b′" term in `sδ`, which AbE turns into C₀|TT|a·La via m·k·b′ ≤ a, is slack and not an actual deviation. This is harmless, since it only enlarges an upper bound.

### 2.3 The model computation *(mine)*
Take one top, j = 1 (so sh = 0), c = c′ = 0, blk = sm = ∅, r₀ = w (take s = 0 for simplicity). Then ν = (a + w, w^{k−1}) and a⁺ = (w^{k−1}), a rectangle with R = k − 1 rows.

- **Hook product of a rectangle.** H(w^R) = ∏_{i=0}^{R−1} (w+i)!/i!.
- **Top.**
  D_top = ph(a+w) + R·ph(w) − Σ_{i<R}[log(w+i)! − log i!].
  - Stirling: log(w+i)! = ph(w) + i·log w + i²/(2w) + ½log(2πw) + O(i³/w² + 1/w), and Σ_{i<R} log i! = (R²/2)log R − ¾R² + O(R log R).
  - So D_top = ph(a+w) − (R²/2)·log(w/R) − ¾R² − (R/2)log(2πw) + O(R log R + R³/w).
  - Also ph(a+w) − ph(a) = a·log(1 + w/a) + w·log(a+w) − w ∈ [w log a, w log(a+w)].
  - Hence **D_top − ph(a) = w·log a − (R²/2)log(w/R) + O(R² + R log w)**. For a ≫ w ≫ R² (the live regime: w ~ b = e^{x^ε}, k ~ x^{4.5}) this is ≈ w·log a.
- **Off a top.** D_off = k·ph(w) − log H(w^R) = ph(w) − (R²/2)log(w/R) + … ≈ w·log w.
- **Against the Lean's bound.** The Lean allows ph(a) + (2w + Sc + n·sh + Bl)·La + 1 at a top, and (w + 2Sc + …)·La off it, with La = log(a·rd) ≥ log(a+w). So D_top − ph(a) ≈ w log a ≤ 2w·La and D_off ≈ w log w ≤ w·La. **The bound holds, with a factor ≤ 2 to spare in the remainder.**
- **Numerical check** of these closed forms with lgamma (my script, my formulas only). For (a, w, k) = (10⁶, 10³, 10), (10⁸, 10⁴, 30), (10⁵, 10⁴, 50):

  | (a, w, k) | D_top − ph(a) | w log a | Lean bound 2w·La + 1 | D_off | w log w |
  |---|---|---|---|---|---|
  | (10⁶, 10³, 10) | 13 564 | 13 816 | 27 632 | 5 656 | 6 908 |
  | (10⁸, 10⁴, 30) | 181 119 | 184 207 | 368 415 | 79 015 | 92 103 |
  | (10⁵, 10⁴, 50) | 107 425 | 115 129 | 230 260 | 73 915 | 92 103 |
- **Sizes in the live parameters.** Per (j, ρ), eE ≈ w·La ≤ 2b·La. Summed over the m lifts and |Pl| ≈ f places: Σ eE ≲ 2C₀·m·f·b·La. This is the per-lift ("m") family, ≈ m·B₀-sized in the ledger's booking [DIVKEY: AbE:86-98, 15C₀·m(B₀+Nc)xe].
  - It is **not** C·a·La per top. The a-dependence at a top is only w·log a, not a·something.
  - In the 1/2 balance it feeds the "m" term, which balances x/m at m ≈ √x.
  - Unlike the pq residual (DIVKEY §2.5), it cannot be removed by averaging over j. It is a genuine positive loss ≈ w log w per (j, ρ), because the k-row Fock weight carries one w-sized row more than the hook weight.

## 3. The three per-lift inputs (task 2)

### 3.1 (a) The Fock jet term, +Σ_i ph(ν) − |ν|·logΩ
- **Theorem.** `BlockBound` (PWN:36-49), proved as `blockBound` (NFL:262) [HEIGHT; I read the statement and NFL:60-89].
  - Hypotheses: G is entire on (ℂ^{a×b})^ι with |G(z)| ≤ S·exp(Σ_τ r_τ²|z_τ|²/2), and the coordinate constant satisfies |cD_τ·r_τ|² = 1/Ω_τ.
  - Conclusion: the jet operator jetOp(jetC cD G): VV_λ → VV_λ′ has squared operator norm ≤ S²·∏_τ Ω_τ^{−|ν_τ|}·e·(2|ν_τ|+2)^{2ab}·exp(Σ_i ph(ν_{τi})) (PWN:32-34).
- **Norms.**
  - normSq = Re fockL(v, v)/∏_τ eN(λ_τ) (NFL:71-77). fockL is the Fischer form, ⟨z^m, z^m⟩ = m! (CM:21-22, 31).
  - eN(λ) is the Fischer norm of the extremal (highest-weight) vector. So VV_λ carries the Fischer norm normalised so that the highest-weight vector has norm 1 (pairK = gramTw/extNorm · fockL, CM:160-176).
  - These are definite-side norms with no (2π·x)^{wt} factor [HEIGHT].
- **Where logΩ enters** *(mine, from the hypothesis)*.
  - Cauchy on a polydisc of radius² = ν_i/r² gives |coefficient_ν| ≤ S·∏(e r²/ν_i)^{ν_i/2}.
  - Hence |D^νG(0)|² ≤ S²·∏ν_i!·(2πν_i)^{1/2}·r^{2ν_i}.
  - The jet is taken in the algebraic coordinate, z = cD·(analytic coordinate), so it picks up |cD|^{2|ν|}, and |cD r|² = 1/Ω turns r^{2|ν|}|cD|^{2|ν|} into Ω^{−|ν|}.
  - Ω_τ = exp(logOmAt(ρ, τ)) is the area/π-type metric of the ρ-conjugate CM period lattice, measured against an algebraic generator s of the 𝒪_E-ideal line: logMet = log(π|ρs|²/area) (IDT:156-157). Its mean is meanLogOm (IDT:160-166).
- **Status.** Proved [HEIGHT]. Used on the live path through `kerSide_of_meansS` with logOmτ := logOmAt and mean = N.logOm (KHC:315-320, read). The `tOm` rewrite (KHC:232, 319) identifies N.logOm with the host value `logOmVal D` (from `numDatum_numbers_eq_host_of_compatible`; not opened).

### 3.2 (b) The hook term, −logHook
- **Theorem.** `IndefData.L6`: log λ_{j,p,v} ≥ Σ_ρ logHook_{jρ} − C·f·nV²·Lp, at every infinite place v and every Hecke part p [L6; HEIGHT]. On the live record l6m j := Σ_ρ Nd.logHook(j, ρ) (ZON:67, read). This is the same `logHook` definition (NUM:245) that `stepE_num` uses.
- **The archimedean formula** [L6, not re-read]. λ is the Rallis θθ* eigenvalue:

  λ = ∏ dim K-type · vol · ∏_ρ hook(p, a⁺)·hook(q, a⁻) · ‖f‖²/d^S · ∏_ρ ∫|⟨v, π_ρ(g)v⟩|² · |L^S((1+t)/2)|.

  The hook factor is the Fock norm of the Weil-representation vector δ (`DeltaNorm`, IPF:147-149, read). The remaining factors are the formal degree (Harish-Chandra) and the convergent Euler product.
- **Sign.** In the height chain, −log λ_j appears (h_u = hP + Σ hK − mlam, with Σ fa − e6 ≤ mlam; DIVKEY (s3), (s5)). A lower bound on λ therefore lowers the upper bound on the height. −logHook helps, and the direction used is the one supplied. In `stepE_num` only logFactRows(a⁺) ≤ logHook is needed, which is the right direction (TDRS:148).
- **Status.** Premise. It is proved from seven `Published.*` theorems, with suppliers in-tree [L6]. I did not re-read it.

### 3.3 (c) The covolume term, +pq_j·w·logΩ
- **Theorem.** D2: lcv(M_j)/D ≤ (p_j − q_j)·Σ_ρ w_{jρ}·logΩ + C·B₀·log log x.
  - It comes from the effective arithmetic Hilbert–Samuel bound and `FlatDegree`. FlatDegree says the flat section on U(p, q) has degree (p−q)/2·logΩ + q(log d − log rd_E). It is computed from `chowla_selberg_period` (the CM elliptic curve over ℚ(√−d) with period γ + log(2π/√d) − L′/L(1, χ)) [COVOL; VOLUME; HS].
  - On the live record l3m j = Σ_ρ ((k+j−1) − (m−j))·w·Nd.logOm (ZON:64-65, read). This is the same symbol as in (a).
- **Status.** The live supplier `topCovolG_alt_alt` (TCG:39-58, read as a skeleton) is a theorem conditional on seven hypothesis bundles: VolumeEstimateHypotheses, HypothesesX, PublishedHodgeBundleTheorems, HypothesesH, Published.GrothendieckDeformation, HSCore.Quoted and DeepStR. The bodies are not opened here.

### 3.4 Consistency of normalisations
What the Lean shares:
- **One logΩ symbol.** (a) and (c) both use `Nd.logOm`/`N.logOm` (ZON:64-65; KHC:316-320).
- **(a) is tied to the true period** by the proved MLP/MLC chain (§4).
- **(c) is tied to its own Chowla–Selberg instance** (`chowla_selberg_period`) [COVOL]. The (2π/rd_E) form appears on both sides [COVOL §; MPL:19-25].
- **Frames are shared by type.** The height chain bounds log‖B_u‖²_v with the same frame objects XT_j, XW_j, XE that the det identity (SpecDet) uses on the covolume side [HEIGHT §1(b); DETSIG]. Any mismatch there would make a proved lemma false.

What I did **not** find:
- a lemma identifying the definite frame XT_j (the Rallis side, b) with the pairK-normalised Fischer norm of (a);
- a lemma identifying XW_j with the Petersson × (2πx)^{−|wt|/2} norm used for lcv in (c).

The (c) comparison runs through `covering_meas_of_prints` / `coreLe_of_gram_meas_liftRational` (TCG:47, 58), which bounds the realised norm against c·Petersson with |log c| ≤ C·unitE [COVOL child 11]. I did not open it.

*(mine)* Why this matters:
- A discrepancy c^{|wt|} between the norm of (a) and that of (b) would change hK − hX by |ν|·log c per (j, ρ). Since |ν| ≈ a_t + k·w, that shifts the coefficient of a_t (and of k·w) like a wrong logΩ.
- It would have to sit inside L6's Published-premised proof or inside the covolume hypothesis bundles. The proved parts (BlockBound, stepE_num, MLC) cannot hide it.

Greps run:
- `extNorm` over the tree (users in `Formalism/LocalToGlobal/Columns/*`, `SiegelLatticeTheory/*`, `PeriodIntegrals/UnitaryGroupMassFormula/*`; none in the L6 files);
- `def DeltaNorm` (IPF:147);
- `def pairK|def fockL|def extNorm|def gramTw` (CM).

## 4. Chowla–Selberg: in-tree statement and classical check (task 3)

### 4.1 What the tree proves (read)
- **`LFunction_one_and_mean_log_eta`** (DZE:117-154). For K imaginary quadratic of discriminant −d, d > 4, with χ the Kronecker character:
  - L(1, χ) = πh/√d;
  - (1/h)Σ_classes log(y_c·|η(τ_c)|⁴) = γ − log(2√d) − L′/L(1, χ).

  The proof uses ζ_K(s) = ((2/√d)^s/2)·Σ_c E(τ_c, s) (DZE:83-115, so w = 2), `tendsto_realEisenstein_sub_pole`, i.e. Kronecker's first limit formula E = π/(s−1) + 2π(γ − log 2) − π log y − 2π log|η|² + o(1), and `compare_expansions` (DZE:14-60) against ζ(s)L(s, χ). It is proved.
- **`chowla_selberg_eta`** (DZE:222-243): (1/h)Σ log(4π·y·|η|⁴) = γ + log(2π/√d) − L′/L(1, χ).
- **`mean_log_area`** (MLC:141-195). For lattices L_s, the conjugates of L₀ ∝ σ(I), normalised by g₂³ − 27g₃² = 1:

  mean_s log(area(L_s)/π) = γ + log(2π/√d) − L′/L(1, χ).

  The proof: by `sum_log_norm_unit` (MLC:126-137), the discriminant of a model over N is a unit, so its log norms sum to 0. Homotheties then reduce to `chowla_selberg_eta`.
- **`meanPeriodAt`** (MLP:58-82). meanLogOm = logOmVal = γ + log(2π/rd_E) − L′/L(1), via:
  - `br_meanLogOm_eq` (PER:39-44): meanLogOm = −(2/[E:ℚ])·log brN + mean log(area/π);
  - `two_log_brN` (MLP:17-56): (2/[E:ℚ])·log brN = log rd_E − log √d, where brN = N(AA0·𝔇_{E/K}) (LCN:14-17) and |disc E| = N(𝔇_{E/K})·d^{[E:K]};
  - `logOmVal_eq` (MPL:19-25): π/v = 2π/rd_E, with v = rd/2 and rd = |disc E|^{1/[E:ℚ]} (HOST:71).

  The record's logOm (NUM:68) has the same formula, γ + log(π/v) − Re L′/L(1, (·/d)).
- **Which form.** This is the **classical (elliptic, class-averaged) Chowla–Selberg formula for K = ℚ(√−d)**, proved in-tree. It is not Colmez's or Obus's averaged formula for abelian CM fields. The CM field E enters only through its 𝒪_E-ideal rescaling (brN).
- **The character.** For D7, d % 4 = 3 (`discriminant_mod_four`, LCN:19-21), so (·/d) = χ_{−d}, the character of K. This partly closes DIVKEY's open point, for the D7 host.

### 4.2 Classical check by hand *(mine)*
Let K = ℚ(√−d), d ≡ 3 (mod 4) prime, d > 3 (so w_K = 2), with class number h. For a class A, with reduced form (a, b, c), set τ_A = (−b + √−d)/(2a) and y_A = √d/(2a).
1. ζ_A(s) = ½·Σ′ Q(m,n)^{−s} = ½·(2/√d)^s·E(τ_A, s), where E(τ, s) = Σ′ y^s/|m + nτ|^{2s}, because a·y_A = √d/2.
2. Kronecker: E(τ, s) = π/(s−1) + 2π(γ − log 2 − log(√y|η(τ)|²)) + O(s−1).
3. ζ_K = ζ·L: the residue gives L(1) = πh/√d (= 2πh/(w√d)). Comparing constant terms after dividing by L(1):

   γ + L′/L(1) = log(2/√d) + (2/h)·Σ_A(γ − log 2 − log(√y_A|η_A|²)).

   Hence (1/h)·Σ_A log(y_A|η_A|⁴) = γ − log(2√d) − L′/L(1, χ_{−d}). **This equals DZE:121-123.**
4. **Period.** For Λ = ω(ℤ + ℤτ), Δ(Λ) = g₂³ − 27g₃² = ω^{−12}(2π)^{12}η(τ)^{24} and area = |ω|²y. With |Δ| = 1 (unit discriminant, averaged), area^{1/2} = 2π|η|²√y. So

   mean log area = 2 log 2π + γ − log(2√d) − L′/L(1), i.e. **mean log(area/π) = γ + log(2π/√d) − L′/L(1, χ_{−d})**.

   This equals MLC:147-148 and agrees in sign and constant.
5. **Faltings height cross-check.** From the functional equation of Λ(s) = (d/π)^{s/2}Γ((s+1)/2)L(s, χ), using ψ(½) = −γ − 2 log 2 and ψ(1) = −γ:

   L′/L(0) = −log(d/π) + γ + log 2 − L′/L(1).

   Substituting, −½·mean log(2·area) = −½·L′/L(0, χ) − ¼·log d − ½·log(2π). This is the formula quoted in the brief (h_Fal = −½(L′/L(0) + ½log d) − ½log 2π, normalisation h = −½log(i∫ω∧ω̄)). With Deligne's normalisation (area/π) it is −½L′/L(0) − ¼log d.
6. **The record's constant.** logΩ = γ + log(π/v) − L′/L(1) with v = rd_E/2. For E = K (rd = √d) we get v = √d/2 = covol(𝒪_K ⊂ ℂ), which is exactly item 4. For larger E the −log(rd_E/√d) is the brN rescaling of §4.1, which is proved.

**Verdict on task 3: the constant matches.** The term γ − L′/L(1, χ_{−d}) carries the right sign, the log(2π/√d) is right, and the rd_E correction is proved. So DIVKEY oddity 5's worry (a wrong sign of L′/L hidden by the shared symbol) does not materialise on the (a) side.

## 5. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `young_diagram_step` | YDH:492-548 | defines eE, δ as remainders; bounds them | core of `stepE_num` | glue (proved, read) |
| `young_diagram_factorial` | YDH:250-331 (stmt TDR:34-41) | Σph(ν) − fa ≤ [top]ph(a) + (2w + S + n·sh + Bl)La + 1 under interlacing | branching/Stirling | standard (elementary; proved, read) |
| `young_diagram_hook` | YDH:386-422 (stmt TDR:52-54) | H(μ) ≥ ∏ μ_i! | hook vs factorial | standard (proved, read) |
| `young_diagram_period` | YDH:350-375 | Σν = a + k·w′ + δ₀ with δ₀ ∈ [−w, nS + Bl] | δ bound | glue (read) |
| `young_diagram_step_origin`/`_shift`, `origin_*` | YDT:10-295 | origin shift w′ = w − s_j; real → integer interlacing | glue | glue (read) |
| `nu_eq_originRow`, `aPlus_eq_originBig`, `hookLower_of` | NLem:217-230, 537-541 | ring identities; logFactRows(a⁺) ≤ logHook | glue | glue (read) |
| `BlockBound`/`blockBound` | PWN:36-49; NFL:262 | Fock–Cauchy jet bound | input (a) | standard; proved [HEIGHT] |
| L6 (`IndefData.L6`) | [L6]; ZON:67 | log λ ≥ Σ logHook − C f nV² Lp | input (b) | core premise (Published) |
| `topCovolG_alt_alt` | TCG:39-58 | covolume bound from 7 hypothesis bundles | input (c) | core; hypotheses not opened |
| `LFunction_one_and_mean_log_eta`, `chowla_selberg_eta` | DZE:117-154, 222-243 | Kronecker limit ⇒ Chowla–Selberg | logΩ | standard; proved (read) |
| `mean_log_area`, `meanPeriodAt`, `two_log_brN` | MLC:141-195; MLP:17-82 | mean log(area/π), then the rd_E rescaling | logΩ tie | standard; proved (read) |
| `covering_meas_of_prints`, `coreLe_of_gram_meas_liftRational` | TCG:47, 58 | realised norm vs Petersson | normalisation of (c) | not opened |

## 6. Oddities
1. **The k·b′ top allowance in `sδ` is slack** (YDH:527-531). The ledger's one-off C₀|TT|a·La therefore over-books δ. This is harmless.
2. **eE is a genuine loss of ≈ w·log w per (j, ρ)**, not an error term. It is booked in the per-lift family. Any refinement of the balance would have to keep a per-lift loss of size ≈ f·b·La per level unless the Fock weight and the hook weight had the same number of w-sized rows.
3. **The origin shift.** δ contains −k·s_j with s_j ≈ (k + (2j−1)(t+1))/2. So Σ_j Σ_ρ δ·logΩ has a systematic part ≈ f·k·m(k + mt)·La. That is ≪ m·f·b·La (b exponential), so it is negligible.
4. **No lemma states that the three norms coincide** (§3.4). This is the one place where a wrong normalisation could hide, inside L6's Published-premised proof or the covolume hypotheses.
5. **The Chowla–Selberg used is the elliptic one for K.** E's period enters only through an 𝒪_E-ideal rescaling. This fits the setup, since the Hodge type is pulled back from K [VOLUME].

## 7. Coverage
Read in this pass:
- PROTOCOL; MAIN-ARGUMENT §0, §5; NODE-DIVKEY, NODE-HEIGHT and NODE-L6 in full; NODE-COVOL, VOLUME, HS, DETSIG, LEDGER and ARCH by grep for normalisation/Chowla–Selberg lines.
- NL:1-90, 290-549; NUM:1-275; NLem:210-232, 510-541; ZON:55-100.
- TDR:1-90; TDRS:100-200; FW:1-38; YDT:1-297 (all); YDH:13-112, 140-550; SS:1-47.
- PWN:1-60; CM:20-69, 140-176; NFL:60-89.
- MLP:1-87 (all); MLC:120-251; DZE:1-262; MPL:1-34; IDT:10-30, 140-185; PER:30-70; LCN:10-25.
- HOST:71, 166-168; KHC:232, 300-333; TCG:1-60; IPF:147-149.

Not opened:
- `blockBound`'s proof body (NFL:151-300);
- L6's proof and its Published premises;
- `covering_meas_of_prints` and the TCG hypothesis bundles;
- `chowla_selberg_period`/FlatDegree [COVOL];
- `tendsto_realEisenstein_sub_pole`'s body;
- `numDatum_numbers_eq_host_of_compatible`;
- AbE's booking of eE (taken from DIVKEY).
