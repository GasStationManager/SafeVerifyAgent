# NODE-DIVKEY: the DIV line, the key identity, the signature question, and m = 1

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(mine)* = my own algebra or inference. [NODE] = taken from that node, not re-read. Nothing was compiled or executed.

Abbreviations (as in NODE-LEDGER, plus new ones marked *):
- `MB` = `Formalism/RankGapBounds/MeanBoundSecondForm.lean`; `WMD` = `Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean`; `LoC` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`; `QSB` = `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`
- `DP2` = `Formalism/LocalRingCardinality/DataParams₂.lean`; `QLD` = `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`; `CAH` = `Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean`; `CT` = `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean`; `FPN` = `Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean`; `GB` = `Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean`
- `INP` = `Formalism/LocalToGlobal/Divisibility/Inputs.lean`; `DHB` = `.../Divisibility/DivisionHeightBoundStatement.lean`; `CGT` = `.../Divisibility/ConstantGeTwentyEight.lean`; `ZON` = `.../Divisibility/ZscOfNum.lean`
- *`NL` = `Formalism/LocalToGlobal/Divisibility/NumbersLink.lean`
- *`SLF` = `Formalism/QuotientMetricDivisors/ScalarLiftLowerBoundFull.lean`; *`GBR` = `Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean`; *`SK` = `Formalism/QuotientMetricDivisors/StatementK.lean`; *`TDI` = `.../HermitianTwistDivisors/TheoremDivIneq.lean`; *`DAs` = `.../HermitianTwistDivisors/DivAssembly.lean`; *`AbE` = `.../HermitianTwistDivisors/AbsorbE.lean`; *`SRE` = `Formalism/QuotientMetricDivisors/SixthReductionExplicit.lean`
- *`JL` = `Formalism/SharpRestriction/GlobalSchurBounds/JointsL.lean`; *`STL` = `Formalism/SharpRestriction/GlobalSchurBounds/StandardLattice.lean`; *`DK` = `Formalism/LocalRingCardinality/DataKernels.lean`; *`GAL` = `Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/GapAtLeast.lean`
- *`CI` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean`; *`LWM` = `Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean`; *`WIA` = `Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean`

## 0. Verdict

1. **The key identity holds exactly, as claimed.** I redid it by hand from the definitions (§2.2). Every log(π/v), every m·lg and the Count5 error term cancel term by term. No error is hidden in it. The c(La + m²La/k) term is Count5's slack carried through unchanged; the identity itself produces no error. **No ESCALATE.**
2. **The signs agree on both sides.** Both use +L′/L(1, χ) with the same χ, and the coefficients of 1 and γ match.
   - Main contains +LpL, which comes from −a·logΩ, since logΩ = γ + log(π/v) − LpL (DP2:224).
   - MAIN contains +ell(chC) (FPN:89-91). Here ell(ψ) is the constant that GPsi *adds* to the twisted Riesz sum (FPN:67-69). So ell(ψ) = L′/L(1, ψ), and `Char_at` says exactly this (QLD:220-228).
   - The explicit formula for Σ_n Λ(n)(1 − χ(n))(y/n − 1)₊ has main term y log y − (1+γ)y + y·L′/L(1, χ) (§2.3). Its χ is chC on both sides. LpL is *defined* as Re L′/L(1, (·/d)) (DP2:65-71) and is tied to Re ell(chC) by `Char_at` (QLD:226).
3. **Disagreement 1 is settled for LEDGER.** On the live path, Σ_j(p_j − q_j) = mk is never used.
   - The DIV record has only the hypothesis ∀j, |pq_j − k| ≤ m (SLF:71; SK:41; INP:136).
   - The single place pq enters the proof is a pointwise triangle inequality (DAs:14-24), summed crudely (AbE:137-152).
   - The live pq_j is (k + j − 1) − (m − j) with j ∈ {1..m} (NL:574), so the hypothesis reads |2j − 1 − m| ≤ m.
4. **Disagreement 2 (m = 1).** *(mine)* Setting m = 1 formally in the ledger's sizes gives G(x) ≤ x^{1+O(ε)}. That is Chebyshev/Mertens quality: no better than the trivial bound G = O(x). It is neither x^{1−o(1)} nor x·x^{−c}. The tree never instantiates m = 1. Its windows require m ≥ x^{1/2−ε} (GB:111) and m ≥ 2 (NL:599 `two_le_m`).
5. **The four unread bodies have now been read.**
   - `divIneqRecord` and its chain down to `divisor_inequality_assembly` and `error_absorption` are pure real-number algebra (§2.1).
   - `core_ineq` (CI:13-46, statement and opening only) is a size envelope.
   - `proposition_size_bound` (LWM:507-583) is the division by U.
   - `windowInequality_of_artinInputs` (WIA:17-26) is quantifier glue around `core_gm`.

## 1. Statement

### (a) DIV as the Lean states it
`DivIneqRecord` (SLF:52-87) is a statement about real numbers only. The live call (DHB:131-191, `RecNums.divIneq`) obtains it from `divIneqRecord` (SRE:9). That is `divisor_inequality_explicit` (GBR:91) = `divIneqRecord_of divisor_inequality` (GBR:63-87), and `divisor_inequality : TheoremDivIneq` (TDI:12-25, statement SK:11-57). In mathematical language:

Let J be the lifts (|J| = m) and Pl the places (|Pl| ≤ f), with tops TT ⊂ Pl. Suppose
- (s1) μ_C ≤ μ₀ + Lpass  [base-to-column passage, D3];
- (s2) μ₀ ≤ Σ_j Σ_ρ pq_j·w_{jρ}·logΩ + 2Fo + Eb  [covolume D1 + layer covolume D2];
- (s3) h_u = hP + Σ_j hK_j − mlam  [height chain];
- (s4) hK_j ≤ Σ_ρ (phν_{jρ} − nν_{jρ}·logΩ) + eK_j  [Fock/Cauchy jet bound];
- (s5) Σ_j Σ_ρ fa_{jρ} − e6 ≤ mlam  [L6: Rallis scalar ≥ hook product];
- (s6) hP ≤ −Σ_{t∈TT} a_t log T + eP  [last map];
- (s7) phν_{jρ} − fa_{jρ} ≤ [ρ∈TT]·ph(a_ρ) + eE_{jρ}  [`weight_height_sum_le`];
- (s8) nν_{jρ} = [ρ∈TT]·a_ρ + k·w_{jρ} + δ_{jρ}  [`weight_sum_eq`];
- size conditions, among them |pq_j − k| ≤ m, |logΩ| ≤ La, 0 ≤ w ≤ 2b, m·k·b′ ≤ a, b′N ≤ a (SLF:65-83).

Then μ_C + h_u − 2Fo ≤ Σ_t [m(ph(a_t) − a_t logΩ) − a_t log T] + (50C₀+10)·|TT|·a·La + 60·ce·m·(x^ε B₀ + (log x)² Nc) (SLF:84-87).

On the live record (DHB:144-149) the slots are:
- phν = Σ_i ph(ν_{jρi}) and nν = Σ_i ν_{jρi};
- fa = logH (log of the hook product, NL:548);
- mlam = Σ_j hX_j;
- e6 = m·Ch·f·nV²·Lp.

RecNums.rhs (INP:200-203) is the same bound with x^ε(B₀+Nc).

### (b) The key identity
`key_identity5` (LoC:105-111):

  SDiv − ΣA·Lam5 + m·ΣA·lg = Main + ΣA·cCount·(La + m²La/k),

with these definitions:
- SDiv = Σ_t m(ph(a_t) − a_t logΩ) (WMD:129);
- Lam5 = Σ_j (1/f)Σ_ρ log(w_{jρ}v/π) + m·lg − cCount(La + m²La/k) (LoC:17-19);
- Main = Σ_j Σ_t a_t(log a_t − 1 − γ + LpL − (1/f)Σ_ρ log w_{jρ}) (MB:107-109);
- ph(y) = y log y − y (MB:9);
- logΩ = γ + log(π/v) − LpL (MB:88).

Its Lean proof is `linear_combination` from WMD's `key_identity` (WMD:170-216). That version uses an `abelian₂` which has L in place of La and an extra −2·logGam/(fk) (WMD:125-127). The two identities differ by the same quantity on both sides.

## 2. Argument

### 2.1 DIV as a paper proof (the body of `divisor_inequality`)
The proof is `divisor_inequality_assembly` (DAs:11-42) followed by `error_absorption` (AbE:26-203). In words:

**Step 1, pointwise (DAs:14-24).** Fix a lift j and a place ρ. Add the four inputs that are indexed by (j, ρ):
- +pq_j·w·logΩ, the covolume of layer j at ρ, from (s2);
- +phν − nν·logΩ, the Fock norm of the j-th jet step at ρ, from (s4);
- −fa, the hook part of the Rallis scalar, from (s5).

Then substitute nν = a_ρ[ρ∈TT] + k·w + δ from (s8), and bound phν − fa by (s7). This gives

  pq_j·w·logΩ + phν − fa − nν·logΩ  ≤  [ρ∈TT](ph(a_ρ) − a_ρ·logΩ) + eE + |pq_j − k|·|w|·|logΩ| + |δ|·|logΩ|.

- **logΩ**: the covolume contributes +pq_j·w and the jet degree contributes −(k·w + a[TT] + δ). The k·w parts cancel. That leaves −a_t·logΩ at each top, once per lift, plus the residual (pq_j − k)·w − δ.
- **ph**: the Fock bound puts the full Σ_i ph(ν_i) ≈ log ∏ν_i! in the height. The hook product of the Rallis scalar λ_j enters through −log λ_j ≤ −Σ logHook + e6 (L6). Together they leave ph(a_t) at tops and eE elsewhere (s7). So each lift contributes exactly one ph(a_t) − a_t·logΩ per top.

**Step 2, sum over (j, ρ) and assemble (DAs:25-42).**
- Summing step 1 over j and ρ gives m·Σ_t(ph(a_t) − a_t logΩ), because |J| = m.
- (s6) supplies −Σ_t a_t log T.
- (s1) and (s3) supply μ_C and h_u.
- The 2Fo of (s2) is the −2Fo on the left.

**Step 3, absorb the errors (AbE).** Every remainder is bounded by C₀·|TT|·a·La or by C·m(B₀+Nc)x^ε:
- the pq residual: Σ|pq − k||w||logΩ| ≤ m·f·m·2b·3L ≤ 6·m·(B₀ + Nc)·xe (AbE:137-152);
- the δ term: the top part k·b′ uses m·k·b′ ≤ a, which gives C₀|TT|a·La; the rest is m·B₀-sized (AbE:158-197);
- eE and eK: 15C₀ and 5C₀ times m(B₀+Nc)xe (AbE:86-98, 124-136);
- eP: C₀|TT|a·La + 9C₀·m(B₀+Nc)xe, using b′N ≤ a (AbE:104-122);
- Lpass ≤ (1+C₀)·m(B₀+Nc)xe, using m·lam₀ ≤ b (AbE:80-83).

**On the live path, two of these inputs are definitions.**
- δ is *defined* as the remainder Σ_iν − a[TT] − k·w (NL:38-39), so `weight_sum_eq` is proved by `ring` (NL:579).
- eE is *defined* as Σ_i ph(ν_i) − logHook − [TT]ph(a) (NL:35-36), so `weight_height_sum_le` is proved by `linarith` (NL:578).
- The content therefore lies in the bounds `sE`/`sδ` (INP:198-201), proved by `stepE_num` (NL:388-394; body not read). They say:
  - Σ_i ph(ν_i) − log hookProd − [TT]ph(a_t) ≤ C₀(w + S + N² + m(t+1)η)·La;
  - |δ| ≤ C₀(w + k(N + S) + m(t+1)η + [TT]·k·b′).

**Upstream (D1–D4), as the Lean feeds them in.**
- **D1 + D2 (CGT:222-243).** `boundsMu` gives μ(RR_base) ≤ meanLog κ + Σ_j l3_j + 2ΣF + LG + Σ(E1+E2) + E3. With L3main, Σ_j l3_j ≤ Σ_jΣ_ρ pq_j·w·logΩ + El3 (CGT:87), this yields (s2) for μ₀ = μ(RR_base) − meanLog κ. Here l3m_j = Σ_ρ((k+j−1) − (m−j))·w_{jρ}·logΩ (ZON:63-64).
- **D3.** The passage (CGT:232-239) gives (s1).
- **D4.** The height side is [HEIGHT].
  - Cauchy estimates in Fock space give the jet-step operator norm ≤ ∏ν!·Ω^{−|ν|}: hB_j = Σ_ρ[Σ_i ph(ν) − (Σ_iν)logΩ] + err (INP:192-193).
  - The averaged Chowla–Selberg identity replaces mean_ρ log Ω_ρ by logΩ [HEIGHT].
- **How logΩ enters with coefficient a_t per lift** *(mine, from s4 and s8)*. The jet degree |ν| at a top includes the order-a_t derivative at every lift. So Ω^{−|ν|} carries Ω^{−a_t} once per lift. Over m lifts this gives −m·a_t·logΩ.

### 2.2 The key identity by hand *(mine)*
Write P = log π and V = log v. From the definitions:
- SDiv = Σ_t m[a_t log a_t − a_t − a_t(γ + P − V − LpL)] = m·Σ_t a_t(log a_t − 1 − γ + LpL) − m(P − V)·ΣA.
- ΣA·Lam5 = ΣA·Σ_j μ_j + m(V − P)·ΣA + m·ΣA·lg − ΣA·c(La + m²La/k), where μ_j = (1/f)Σ_ρ log w_{jρ}.

Hence

  SDiv − ΣA·Lam5 + m·ΣA·lg = m·Σ_t a_t(log a_t − 1 − γ + LpL) − ΣA·Σ_j μ_j + ΣA·c(La + m²La/k)
    [the terms −m(P−V)ΣA and −m(V−P)ΣA cancel; the m·ΣA·lg terms cancel].

Main = Σ_j Σ_t a_t(log a_t − 1 − γ + LpL) − Σ_j μ_j·Σ_t a_t = m·Σ_t a_t(…) − ΣA·Σ_j μ_j.

So the identity is **exact**. The constant log(π/v) and the precise normalisation of Ω (log 2π/√d against log π/v) play no role, because they cancel against Count5's log(v/π). Only γ and the L′/L(1) constant survive.

### 2.3 Sign of L′/L on the two sides *(mine, using read definitions)*
- Gfun(y) = Σ_{n≤y} Λ(n)(y/n − 1) − y log y + (1+γ)y (DP2:61-63).
- GPsi(ψ, y) = Σ_{n≤y} Λ(n)·primVal ψ(n)·(y/n − 1) + y·ell(ψ) (FPN:67-69).

Subtracting, for χ = chC:

  Σ_{n≤y} Λ(n)(1 − χ(n))(y/n − 1) = y log y − (1+γ)y + y·ell(χ) + [G_z(y) − G_χ(y)].

ell(χ) = L′/L(1, χ) is the right normalisation, because Σ_{n≤y} Λχ(n)/n → −L′/L(1, χ). `Char_at`'s first clause (QLD:222-225) states this for the primitive χ with χ(n) = primVal chC(n). At a thick partner, with y = a/w, the main term times w is

  w[y log y − (1+γ)y + y·L′/L] = a(log a − 1 − γ + L′/L − log w),

which is MAIN (FPN:89-91), and Main per (t, j) when w is constant in ρ. The coefficients match: −1 (from ph), −γ (from +γ in logΩ, taken with −a), and +L′/L (from −LpL in logΩ, taken with −a).

**Which character.**
- LpL = Re L′/L(1, (·/d)) with d prime (`chiK` = quadraticChar(ZMod d), DP2:65-71).
- The host constructions carry d ≡ 3 mod 4 (`hd4`, `.../InertJacobiLevels/HostFam.lean:95`; `.../LevelLetterCocycles/EmbeddingTypeJumps.lean:30`, a `Conclusion1` Prop). Under that congruence, (·/d) = χ_{−d}, the character of K = ℚ(√−d).
- I did not trace that the live host carries d ≡ 3 mod 4. That chC is the √−d coordinate is LEDGER's reading, not re-checked.
- Chowla–Selberg in the form mean log area = γ + log(2π/√d) − L′/L(1, χ_{−d}) [HEIGHT, MLC] has the sign I recall from the Kronecker limit formula. I checked this from memory through L′/L(0) = −log(d/π) + γ + log 2 − L′/L(1) and h_Fal = −½(L′/L(0) + ½ log d), not from the source.

### 2.4 Why m²La/k appears, and its size
- It enters through Count5: log T(u) ≥ Σ_j mean_ρ log(w_{jρ}v/π) + m·lg − cCount(La + m²La/k) (QSB:27-30). Its supplier is `Count_at` (QLD:166-169), proved by `countF_of` (JL:144-159).
- The lower bound comes from lowB (STL:524-527), with sc.L in place of La. lowB is the lower half of `Conclusion5` (STL:529-531), a hypothesis delivered by `PartFiveFamilyBounds`. Its producer was not opened.
- What `countF_of`'s body adds (JL:60-124):
  - T is a prime in [T*, (1 + 1/(fk))T*], so log T ≥ log T* (JL:70-83);
  - log T* = logXu − 2·log Γ/(fk) (JL:66-69; DK:157-159);
  - 2 log Γ/(fk) ≤ 2 (JL:116-119), absorbed by raising the constant to C + 2.
- logXu = (1/(fk))·log(D*/d*_u) (GAL:88, 95-99), a normalised log ratio of a volume/dimension quantity. *(inferred)* So m²La/k is the error of a dimension-type product over the m×m block of the lifts: f·m² factors of size ≤ La, divided by fk. I have not verified this.
- **Size.** m²/k ≈ x^{1−ε/8}/x^{4.5+10ε} ≈ x^{−3.5}, so ΣA·c·m²La/k is a factor x^{−3.5} below ΣA·c·La. The term is negligible. The operative Count5 precision is ΣA·cCount·La ≈ |TT|·a·x^ε, the "x/m" family [LEDGER §2a].

### 2.5 Disagreement 1: is Σ_j(p_j − q_j) = mk used?
**No.** The Lean says:
- the hypotheses are only ∀j, |pq_j − k| ≤ m (SLF:71, SK:41, INP:136);
- the only use of pq in the DIV proof is `hA` in DAs:20-22, i.e. (pq_j − k)·w·logΩ ≤ |pq_j − k||w||logΩ|;
- summed in AbE:137-152 this is ≤ 6·m·(f·m·b·L).

Other pq hits are size bounds:
- `main_le_RN` (`.../Divisibility/EigenvalueSumLeClosedOf.lean:1669-1670`) uses only |pq| ≤ k + m;
- L3main and `l3main_ofNum` (ZON:79-86) only carry the term.

Greps run: `\bpq\b` in INP, CGT, ZON; `pq :?=|\.pq\b` over `Formalism/LocalToGlobal` and AnchorBoundStatement; `∑ j, R.pq j\b|∑ j, pq j\b|sum_pq|pq_sum|Finset.sum_range_id` over `Formalism/LocalToGlobal`, `Formalism/QuotientMetricDivisors` and `.../DivisorProofs`. None gives a Σ_j pq_j identity.

**The signature's role in the coefficient of logΩ** *(mine)*.
- (p_j − q_j)·w is the logΩ coefficient of the flat-section covolume of layer j [COVOL]. It must cancel the k·w part of the jet degree to relative x^{−4}, since k·w·logΩ ≈ k·f·b·La per lift.
- The signature (k+j−1, m−j) gives p_j − q_j − k = 2j − 1 − m ∈ [−(m−1), m−1].
- The leftover R = Σ_j(2j − 1 − m)·Σ_ρ w_{jρ}·logΩ is booked at its crude size ≤ 2m²·f·b·La, which is the "m" family.
- If w_{jρ} did not depend on j, Σ_j(2j − 1 − m) = 0 would make R vanish exactly. The Lean does not exploit this.
- From the lower bound w_{jρ} ≥ (k + (2j−1)(t+1))/2 (NL:68-69): Σ_j(2j−1−m)(2j−1) = (m³ − m)/3. So the j-trend of the lower bound alone contributes (t+1)(m³−m)/6 per ρ, which is far below m·B₀.
- R is therefore of size m·B₀ only if w_{jρ} varies in j by amounts ≈ b. I did not determine this. w is the HC entry e_j (DP2:76-77).

### 2.6 Disagreement 2: the m = 1 sanity check *(mine, from LEDGER §2a sizes)*
The bracket divided by U (LEDGER §2a; MAIN-ARGUMENT §6.1) has three terms:
- 2aE(1+m²/k)/(m·b·δ) ≤ 4x^{1+ε}/m;
- 4nm·x^ε/(nT·δ) ≲ 8m·x^{2.125ε};
- 2k·x^{2ε}/(n·nT).

At m = 1:
- the first term is ≈ 4x^{1+ε}, from the one-off terms: source floor, DIV boundary, Count5, HN spread;
- the second is x^{O(ε)};
- the third is tiny for any k ≤ n²x^{1/2}.

`proposition_size_bound`'s steps are δ(G − 4X) ≤ 22PY, then δ ≥ x^{−ε} (LWM:556-574). Run on these sizes, they give G(x) ≲ x^{1+O(ε)}.

Compare the trivial bound. Σ_{n≤x} Λ(n)(x/n − 1) = x·Σ_{n≤x}Λ(n)/n − ψ(x) = x log x + O(x) (Mertens), so G = O(x) unconditionally. The m = 1 ledger is therefore *weaker* than or equal to Chebyshev/Mertens, not x·x^{−c}. Equivalently, Main/U ≈ x^{1+4ε/3} and Err/U ≈ x^{1+O(ε)}: the main-term identity is then swamped by its own boundary errors.

This matches the Stepanov analogy at ℓ = 1, where ℓN ≤ ℓq + O(q) + O(ℓ²) gives N ≲ q. It also matches WHYHALF §0.3 ("a single lift gives only the trivial bound"). The general balance x^{O(ε)}(x/m + m + k/n²) is minimised at m ≈ √x.

### 2.7 The remaining unread bodies
- **`core_ineq`** (CI:13-46; I read the statement and the first ~35 lines of the proof). Under 1 ≤ y, L, La ≤ 2y, sA ≤ 2nT·a, M·b ≤ a, k·b′ ≤ a, Xpp ≤ a, log|W| ≤ a, lk ≤ g·y, lH ≤ h·y and 200(1+K)²hg ≤ y, the ErrX5at-shaped sum is ≤ yD·yL·y³·(nT·a(1 + M²/k) + M(B₀+Nc)). It is a size envelope: glue.
- **`proposition_size_bound`** (LWM:507-583).
  - Err ≤ 10·x^{Cε}·x^{1/2+13ε/8}·(nT·m·b), via SZ.T1–T4 (not read).
  - Dividing by Q = nT·m·b gives δ(G − 4x^{1/2+ε}) ≤ 22·x^{Cε}·x^{1/2+13ε/8}.
  - δ ≥ x^{−ε} gives G ≤ 26·x^{1/2+(C+21/8)ε}.
  - 26 ≤ x^{3ε/8} gives G ≤ x^{1/2+(C+3)ε}.
  - So the 3ε splits as 13/8 (bracket) + 1 (division by δ) + 3/8 (the constant 26). This confirms LEDGER's 2.625ε + 3ε/8.
- **`windowInequality_of_artinInputs`** (WIA:17-26). Family-level `Tied` ⇒ `CoreAtH` at some member (hypothesis `h`). Then `core_gm` gives the bound at every x ≥ max(x₁, x₀, x_E). Glue.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `divisor_inequality_assembly` | DAs:11-42 | pointwise (j,ρ) cancellation and summation, as in §2.1 steps 1–2 | logΩ and ph cancellation | glue (read) |
| `error_absorption` | AbE:26-203 | every remainder ≤ C₀\|TT\|a·La or C·m(B₀+Nc)x^ε | DIV error | glue (read) |
| `divIneqRecord_of` | GBR:63-87 | constant change 50C₀+10 → 60ce | glue | glue (read) |
| `RecNums.divIneq` | DHB:131-191 | live instantiation | glue | glue (read) |
| `stepE_num` | NL:388-394 | bounds on eE (hook vs Fock) and δ (weight sum) | the Stirling/hook content of s7 and s8 | core; body not read |
| L6 (`IndefData.L6`) | [HEIGHT] | log λ_j ≥ Σ logHook − C f nV² Lp | Rallis hook products | core premise [HEIGHT] |
| `key_identity5`/`key_identity` | LoC:105-111; WMD:170-216 | (L7), exact | arch. → PNT main term | glue (read; re-derived by hand) |
| `Char_at` | QLD:220-228 | ell ψ = L′/L(1, χ_ψ); LpL = Re ell chC | ties the two L′/L | core hypothesis (field) |
| `countF_of` → `Conclusion5`/`lowB` | JL:144-159, 60-124; STL:524-531 | log T ≥ lowB | Count5 | lowB's producer not read |
| `proposition_size_bound` | LWM:507-583 | GrowthSizeBound | 1/2 + (C+3)ε | glue (read); SZ.T1–T4 not read |
| `core_ineq` | CI:13-46 | envelope | ErrX5at ≤ x^{(eD+eL+3)ε}·ErrText | glue (statement read) |
| `windowInequality_of_artinInputs` | WIA:17-26 | family ⇒ windows | glue | glue (read) |

## 4. Oddities

1. **Two DIV inputs are definitions on the live record.** `weight_sum_eq` and `weight_height_sum_le` are tautologies there: δ and eE are defined as the remainders (NL:35-39, 578-579). Their content moves into `sE`/`sδ` from `stepE_num`. LEDGER and HEIGHT list them as "numeric facts", which is true but undersells this. The real claim is that Σ_i ph(ν_{jρi}) − log hookProd(apDiag) − [TT]ph(a_t) ≤ C₀·w·La. *(inferred)* The hook product at a top therefore omits the a_t row. `stepE_num`'s body was not read.
2. **The logΩ residual's place in the "m" family is a booking choice.** The bound |pq_j − k| ≤ m is used where Σ_j(pq_j − k) = 0 is available. R = Σ_j(2j−1−m)Σ_ρ w_{jρ}·logΩ is m·B₀-sized only if w varies in j by about b (§2.5). So this item is not by itself evidence that the per-lift loss *must* grow with m (WHYHALF §0.4/§0.5). The other "m" items (covolume q-error, E1, E2, EComp5) stand on their own.
3. **The DIV record's errors are larger than its inputs by constant factors only.** The constants are 50C₀+10 and 60ce. No x-power slack was found.
4. **Count5's m²La/k term is negligible** (x^{−3.5} relative). Its origin is in a hypothesis (`Conclusion5`/lowB) that I did not trace.
5. **The Chowla–Selberg normalisation constant does not matter** for the identity, since log(π/v) cancels. Only the coefficient −1 on L′/L and +1 on γ do. If the in-tree average had the wrong sign of L′/L, the identity would still close, because logΩ is one shared symbol. Main would then disagree with MAIN by 2a·L′/L per (t, j), and `Char_at` would not repair that. The sign therefore rests on MLC/MLP [HEIGHT], which I did not re-read.
6. None else seen in the bodies read.

## 5. Coverage

Read in this pass:
- PROTOCOL.md; MAIN-ARGUMENT.md §0, §5, §6; NODE-LEDGER.md in full; NODE-HEIGHT.md in full; NODE-COVOL, DETSIG, ACCOUNT, WHYHALF, RANK, SLOPE (first ~60 lines each, which covers their verdicts and statements).
- SLF:1-470; GBR:1-227; SRE:9-13; SK:1-60; TDI:1-28; DAs:1-45; AbE:1-205.
- DHB:125-195; INP:82-96, 166-206; CGT:80-92, 205-250; ZON:55-110.
- NL:25-104, 388-400, 541-600, 640-672.
- LoC:1-125; WMD:120-223; MB:1-12, 76-125; QSB:1-56; DP2:55-80, 120-130, 176-190, 215-260.
- CT:1-40; FPN:60-130; QLD:160-180, 220-232; CAH:14-24.
- JL:60-159, 1140-1175; STL:524-532; DK:145-165; GAL:88-101.
- CI:1-80; LWM:507-600; GB:100-125; WIA:1-36.
- `.../InertJacobiLevels/HostFam.lean`:85-97; `.../EmbeddingTypeJumps.lean`:26-32; `.../EigenvalueSumLeClosedOf.lean`:1664-1672.

Not opened:
- `stepE_num`'s body; SZ.T1–T4; `core_ineq` past line 80;
- the producer of `Conclusion5` (`dropping_proposition_holds` etc.); `DstarP`/`duStarP`;
- MLC/MLP (Chowla–Selberg) and `boundsMu`'s proof;
- whether the live host's d satisfies d ≡ 3 mod 4 (only construction sites were grepped).
