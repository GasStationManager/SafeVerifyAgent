# NODE-QPART: the q-part of the layer covolume, and the covolume chain behind L3

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" means I read the cited line in this pass. *(mine)* marks my own computation or inference. [NODE] means taken from that node and not re-read. Nothing was compiled or executed.

Abbreviations:
- `EFS` = `Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFlatSecRankZero.lean`
- `FDS` = `Development/AutomorphicSpectrum/Statements/GeometryStatements/FlatDegree.lean`
- `FDH` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/FlatDegreeHolds.lean`
- `HMS` = `Development/AutomorphicSpectrum/Proofs/AdelicProofs/HermitianMetricLogNormFormulaStatement.lean`
- `ICM` = `Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsConstMul.lean`
- `KCF` = `Development/AutomorphicSpectrum/Proofs/GeometryProofs/KroneckerCharacterFrameBound{,Statement}.lean`
- `CXC` = `Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean`
- `FBA` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatBoundOfAnchor.lean`
- `FTS` = `Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlatLineThetaRootTwistTwistingSectionStatement.lean`
- `HBW/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/`; `FSC` = `HBW/FlatAtOfSplitCovering.lean`
- `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`; `FVS` = `TPS/FlatValStatement.lean`
- `ZON` = `Formalism/LocalToGlobal/Divisibility/ZscOfNum.lean`; `DAs` = `Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DivAssembly.lean`
- `HRaw` = `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean`; `DH` = `Formalism/LocalRingCardinality/DataHost.lean`
- `OMS` = `Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OneMeasureSizes.lean`; `IPM` = `Development/AbelianVarietyTheory/Definitions/Foundations/IsProbabilityMeasureMuPart.lean`

## 0. Verdict

**No ESCALATE.** The q-term appears in the Lean with coefficient 2q_j per unit of anchor weight and with a positive sign, so it increases the covolume bound. My reconstruction of the flat degree from the Lean's local hypotheses gives the Lean's formula exactly. No Published input on this chain is stronger than the literature, because none of the precision-carrying steps is a Published input. Three points refine CARRIER §4 and MAIN-ARGUMENT §9.8.

1. **Where the q-term sits.** It is not in the covolume statement used by DIV. That statement is lcv(M_j)/D ≤ l3m_j + C·l3u, with l3m_j = Σ_ρ(p_j − q_j)·w_{jρ}·logΩ and l3u = B₀·log log x (ZON:63-66). The q-term enters only inside the proof of `FlatAt` for layers j < m. In the honest lower bound for μ(Gs(−c₀)), its contribution is
   - −2q_j·Σ_τ anc_τ·(log d − lrd E), which is exact (from flatDegVal), plus
   - −2q_j·lrd E·Σ_τ|anc_τ|, a loss stated in the twist lemma.

   The factor 2 comes from slope_sq. Both terms are then thrown into (11·CA + 83)·unitE by |c₁ + (p−q)/2·logΩ| ≤ 3qL and AnchorAt.2 (FBA:76-102). So in the covolume upper bound the q-part is **+2q_j·W_j·(log d − lrd E)**, plus a booked +2q_j·W_j·lrd E when the anchor weights are ≥ 0. The factor "2w" that CARRIER inferred is confirmed.
2. **Mathematical meaning** *(mine, checked against HMS)*.
   - At the archimedean places the q conjugate directions are measured by their own Hodge Gram matrix Δ, with the inverse sign (ICM:59-63). Their period |z₋| equals |z₊|, so they contribute −(q/2)·(same period) and no q·log d.
   - The whole q·(log d − lrd E) is an integral-structure defect at the finite places. Per conjugate direction it is the different of E/ℚ, minus v(d) (EFS:183-184, 219-223; ICM:80-82). That is what one expects when the q directions are made integral through the polarisation, i.e. trace duality plus √−d.
   - The 2π/√d-type Legendre factor that the brief predicted does not appear in flatDegVal. Whether a per-direction log(2π·x) is hidden in the transport from Hodge-Gram norms to `homN` (whose lieFacZ is blind to the sign of the direction, IPM:664-665) is the one point I could not settle (§4.1).
3. **Size on live hosts** *(mine, from Lean fields)*. Using rd_ge, rd_le and QS ≤ n² (HRaw; DH:48):
   - ½log d − ½log q − 2log n + log 2 ≤ log d − lrd E ≤ ½log d − (e+1−2^{−e})·log 2.
   - Since log d ≍ Y^{ε/5}log²Y ≫ log q ≍ Y^{ε/5} ≫ log n, this gives **log d − lrd E = ½·log d·(1 − O(1/log²Y)) > 0**.
   - lrd E ≈ log d is excluded by rd_le.
4. **Truth: is a term of size ≈ m per unit U forced?** **Not established, and I lower CARRIER's claim.**
   - On the Rallis side, no compensating q·W·log d term appears among the factors of the exact λ formula [L6]. The dropped q-side hook is ≥ 0 and is a gain.
   - But the q-term is exact only relative to μ(uM). The Lean controls μ(uM) only by UAt, μ(uM) ≥ −C·unitE (CXC:138). Its natural size, f·m·b·L [VOLUME], exceeds the per-layer q-term by about x^{4ε/5}/log²x *(mine)*.
   - So the true lcv(M_j) is not determined to the precision needed to isolate the q-term. The q-term is a correctly signed term that the method books. That it is a true lower bound on the covolume would need an upper bound on μ(uM), which the tree does not use.
   - Uncertainty: moderate. The Rallis suppliers and the Hodge→homN transport were not opened.
5. **B (the covolume chain).**
   - `covolume_measure_eq_one` does not say "the measure is 1". It supplies `OneMeasure` = ExactRatio + RatioBound + IndexBound (OMS:92-96). Its volume bound is a Tamagawa/Prasad-type upper bound, log μ(𝓕) ≤ f·r²·log(r+3) + 119·f·r²·L (`HBW/CovolumeRatioIdentity.lean:11`).
   - Arithmetic Hilbert–Samuel is **not** invoked in its literature form. `ArithHilbertSamuel` (q9) is faithful Gillet–Soulé/Zhang/Moriwaki and is unused for HSAt [HS].
   - The precision comes from three in-tree pieces: the effective Chow-form `SlopeBound` [HS, VOLUME]; the in-tree uniform `VolumeTheoremX`, a mean-slope lower bound only, with error ≥ the logΩ main term [VOLUME]; and the exact `FlatDegree` (Chowla–Selberg). The non-compactness and log-singular-metric issues are moved into the unread RootOrigin/GoodOrigin link [VOLUME oddity 4].
   - The "descent to W_m" is not an induction. Each layer j < m uses one deep cover of the same layer, and only the top layer (q = 0) uses LowDef [HS; VOLUME §5].
   - **The fockScale/lieFacZ oddity is resolved.** ξ₀ = −1/(N(𝔠_K)·√−d) ∈ ℚ·√−d (DH:149), so |τ(ξ₀)| = 1/(N(𝔠_K)·√d) at every τ. The per-place fockScale and the global x = xiR coincide on every record.

## 1. Statement

### 1.1 The covolume statement that DIV uses
- `L3` [COVOL] states lcv(XW_j, M_j)/D ≤ l3m_j + C·l3u.
  - l3m_j = Σ_ρ((k+j−1) − (m−j))·w_{jρ}·logΩ (ZON:63-64);
  - l3u = B₀·log log x (ZON:66);
  - `l3main_ofNum` gives Σ_j l3_j ≤ Σ_jΣ_ρ pq_j·w·logΩ + m·C·l3u (ZON:86-95).
- logΩ = γ + log(π/v) − L′/L(1, χ_d) (`DataParams₂.lean:224`), with v = rd_E/2 (DH:143). So **logΩ = γ + log(2π/rd_E) − L′/L(1, χ_d)**, which is CM.logOm.
- The chain to it is `topCovolG_alt_alt` (TPS/TopCovolG.lean:39-61): gram, meas, anchor, deepEx, deepGood, flatDeg (`flatDeg_of_scholzeWeinstein_of_prints`), HS package, then `liftLowBound_of_cover_estimates`, then `covolX_of_truncation_badSet_lambda_lowBound`. As mathematics: lcv/D ≤ −μ(latGood) ≤ … ≤ −muCore + C·unitE (RecAt, CoreAt, LowAt; CXC:57-59, 92-96).

### 1.2 The flat degree (exact)
- `flatDegVal` (EFS:751-752) = (p−q)/2·logΩ + q·(log d − lrd E). `FlatDegree logΩ` (EFS:754) says that every flat section s on every component has deg s = flatDegVal.
- `FlatSec` = ConstSec of weight `flatWt τ` (parallel weight −1 at τ; EFS:153, 157), with valuation defect `flDefect_vw` = q·(ord_𝔩(conjDifferent) − v_𝔩(d)) (EFS:183-184).
- `deg_eq_toFrame` (EFS:711-715): deg s = deg(the defect-0 frame) + q·(log d − lrd E). The q-term is exactly the defect sum (`sum_flDefect_vw`, EFS:219-223; `sum_ord` = lrd E, EFS:124).
- The frame version (KCF statement): for norms with `HasInfNorm`/`HasFinNorm`, N.deg = (p−q)/2·Re CM.logOm, **with no q-term**. `HasNorms` (ICM:80-82) shifts N.fin by q·(logIdeal(𝔇_E) − log|d|). `HasInfNorm` (ICM:59-63) gives log|φ(v, w)| + (log det Γ − log det Δ)/2. Here Γ and Δ are the Hodge Gram matrices of the p frame vectors at τ and of the q frame vectors at τ̄.
- `Fl.FlatDegree` (FDS:12-19): N.deg = (p−q)/2·Re CM.logOm + q·(2·log√d − log rd E). It is proved in FDH:60-118 from:
  - `chowla_selberg_period` for both roots ±√−d, with the same x = γ + log(2π/√d) − L′/L for both (FDH:68-69);
  - `frame_function_cm_value`: r·z₊^p = ρ·z₋^q;
  - `hermitian_metric_log_norm_formula` (HMS:8);
  - `flatDegree_logOm_re`: Re CM.logOm = x − lrd E + log√d (FDH:41-58).

### 1.3 How FlatAt consumes it
- `FlatAt C` (CXC:135-136): μ(Gs(−c₀)) ≥ μ(uM) − mainT − C·unitE. It is proved by `flat_at_of_split_covering` (FSC:28-90), and the root route is `flat_alt_alt` (TPS/FlatBoundOfAnchor.lean:34-43).
- The twist lemma `flatLine_thetaRoot_twist_twistingSection` (FTS:14) states, with anchor weights w and scalar shift m₀ = n/2:
  deg(u + w) ≥ deg(u) + rank·[Σ_τ w_τ·c₁(τ) − q·lrd E·Σ|w_τ| − m₀·fr·(½log 2π + lrd E) − logSum(bad)].
  Here c₁(τ) = −(mean flat degree) = −flatDegVal (EFS:742-748, 754, 758-760).
- `FlatVal` (FVS:11): |c₁ + (p−q)/2·logΩ| ≤ 3·q·L. *(mine)* Its exact value is q·|log d − lrd E|.
- `twice_twist_ge` (FBA:76-102): from hc1 and AnchorAt (CXC:98-102: |mainT − Σ(p−q)·anc·logΩ| ≤ CA·unitE and Σ|anc|·q·L ≤ CA·unitE), it follows that −mainT − (11·CA + 83)·unitE ≤ 2·[…] (the bracket of the twist lemma).

## 2. Argument

### 2.1 The exact covolume formula, item A(1) *(mine, from §1)*
Write W_j = Σ_τ anc_τ ≥ 0 and suppress the m₀ and bad-prime losses. Composing RingAt, Maps, FlatAt and UAt for j < m gives

  lcv(M_j)/D ≤ Σ_τ(p_j − q_j)·anc_τ·logΩ  [= mainT up to CA·unitE]
       + **2q_j·W_j·(log d − lrd E)**  [exact flat degree; coefficient 2 from slope_sq; positive]
       + 2q_j·lrd E·W_j  [twist-lemma loss]
       + 2m₀·fr·(½log 2π + lrd E) + 2·logSum + 2b + C·unitE (from −μ(uM)).

- The first q-term plus the loss together give 2q_j·W_j·log d.
- The Lean discards all of this into (11·CA + 83)·unitE via 3qL and AnchorAt.2.
- For j = m we have q = 0, so no q-term (LowDef).

### 2.2 Derivation of the flat degree by hand, item A(2) *(mine)*
I took the hypotheses of HMS:8 at face value, with deg = −(mean of all log-norms) (EFS:516) and logIdeal summing to −lrd E (EFS:124).
1. **Archimedean mean.** It is mean log|ρ| + ½·mean log|a| − (p−q)/2·(x − ½log d). The p directions carry +(p/2)(log n + ½log d) and the q directions carry −(q/2)(log n′ + ½log d). Both have mean −log n = x.
2. **Finite sum.** Using the t-relation and the product formula for ρ, a and r (with r² = −d), it is −Σ_∞log|ρ| − ½Σ_∞log|a| + (p+q)/2·(lrd E − log d).
3. **Total.** deg = (p−q)/2·(x − ½log d) + (p+q)/2·(log d − lrd E).
4. **Comparison.** Substituting logΩ = x − lrd E + ½log d gives (p−q)/2·logΩ + q·(log d − lrd E). **This equals the Lean's HMS conclusion term by term.** The coefficients of log d, lrd E and x are (p+3q)/4, −(p+q)/2 and (p−q)/2 on both sides.

**Reading.**
- In the symmetric form, every one of the p+q directions carries ½(log d − lrd E), and only the period part is weighted by p − q.
- The "q-part" is therefore what is left over once the main term is written with DIV's logΩ. That logΩ is fixed by the key identity's cancellation against Count5 (v = rd_E/2) [DIVKEY].
- So relative to DIV the q-part is a genuine residual, not a choice of convention.
- The brief's model has the conjugate period carrying Ω⁻¹·(2π/√d-type). The Lean instead uses Ω⁻¹ exactly at ∞, puts the d- and different-factors at the finite places, and has no 2π. By the product formula the d placement is equivalent. The 2π is the open point (§4.1).

### 2.3 Sign and size on the live hosts, item A(3) *(mine)*
**Host data from the Lean.**
- Gal(E/ℚ) ≅ G₀ × A with G₀ = {±1}².
- Inertia at d is ⊆ {1, iod} (`art_d`).
- E/K is unramified above d: primes dividing 𝔇_{E/K} contain QS·q (`diffSupport`).
- rd_ge: 2^{e+1−2^{−e}}·√d ≤ rd. rd_le: rd ≤ (QS/2)·√(qd). Both are HRaw fields (read). QS ≤ n² (DH:48).

**Consequences.**
- The bounds of §0.3 follow.
- Conductor–discriminant gives the same picture: the characters nontrivial on iod have d-conductor d, so the d-part of lrd E is exactly ½·log d.
- So log d − lrd E ≈ ½·log d > 0, and it is ≤ 2L by `lrd_le` (FBA:113-123).

**Size.**
- Per layer, the q-term ≈ q_j·W_j·log d ≤ 2·(q_j/m)·(log d/L)·unitE.
- That is a fraction ≤ x^{−4ε/5}·log²x of its own allowance.
- Summed over the layers it is ≈ (m²/2)·W·log d, i.e. ≈ m·(n/|TT|)·log d·U in CARRIER's units [CARRIER].

### 2.4 Cancellation and truth, item A(4)
**DIV assembly** (DAs:11-42, read). The covolume enters as +pq_j·w·logΩ in (s2), whose error Eb contains m·C·l3u. The Rallis scalar enters as −fa through (s5). The q-part lives only in Eb, and AbsorbE bounds it by C·m(B₀ + Nc)x^ε [DIVKEY].

**The Rallis side** [L6]. The exact formula is l = ∏dimK · dim · vol · ∏hook(p)·hook(q) · ‖f‖²/d^S · ∏∫|⟨v, πv⟩|² · |L^S|.
- The weight-dependent factors are the hooks and the Harish-Chandra degree (∏|λ_a − λ_b|, polynomial).
- No factor is linear in weight × log d. The ξ₀ ∝ d^{−1/2} dependence is absorbed by fockScale-normalised creation operators, with fock(δ, δ) = hook exactly, and by lieFacZ on both sides of ExactRatio [NORMS].
- The dropped hook(q, a⁻) ≥ 0 is a gain, of size Σ q·a⁻·log a⁻ (weights, not d).
- *(mine)* **No cancellation of the q-term on the Rallis side.**

**Truth.** The q-term is an exact difference μ(Gs) − μ(uM) relative to DIV's logΩ. But μ(uM) is known only up to ±unitE, which is far larger. So whether the true lcv(M_j) − l3m_j is ≥ c·q_j·W·log d is undecided.
- CARRIER's statement "in truth the barrier is honestly carried by the q-part" should read: "the q-part is the method's correctly-signed booked carrier; it would be a true carrier if μ(uM) ≤ o(q·W·log d) per layer, which nothing in the tree asserts."

### 2.5 The covolume chain, item B
- **`covolume_measure_eq_one`** (`HBW/NormalizedCovolumeEqOne.lean:19-25`) assembles the following, each taking hP:
  - `level_subgroup_index_bounded`;
  - 1 ≤ dimK;
  - μ(𝓕) ∉ {0, ∞};
  - `covolume_ratio_eq_index` (ExactRatio: ipAt = μ(𝓕)·∏dimK·probSq; it uses `cusp_forms_rapid_decay`);
  - the dimK bound;
  - `tamagawa_pairs_compatible` = `tamagawa_number_upper_bound` (`HBW/PlugPairs.lean:12`);
  - `log_measure_ratio_bounded` (`HBW/LogMeasureRatioBounded.lean:16-37`: log ratio ≤ 122·f·r²·L).
- MeasAt also needs a **lower** bound on log ratAt. That comes from the separate `exists_neg_unitE_le_log_ratAt` (TPS/CoveringMeasureReductionBound.lean:18-27), whose body I did not open.
- *(mine)* ExactRatio is the unfolding "L² over 𝓕 = μ(𝓕) × probability L²" with Schur's ∏dimK. The content is in the two volume bounds, which are standard-shaped (Prasad/Tamagawa).
- **FlatDegreeSt → homN.** EFS's FlatSec degree is lineDeg of cInf, where cInf is the constant value of `homN` = lieFacZ·ptN (EFS:454-456, 514; IPM:680-681). FDS/KCF are stated for Hodge-Gram norms (ICM:59-63). The transport (`degree_frames`, `KroneckerCharacterPeriodFormula.lean:104`; `exists_constSec`) was located but not read. Its premises PublishedHodgeBundleTheorems.q4/q2 are ignored [COVOL].
- **Arithmetic HS.**
  - The literature form (q9, `ArithHilbertSamuel`) is per variety, asymptotic and for C^∞ line bundles, and it is faithful [HS].
  - It is not on the HSAt path. HSAt is an effective finite-level Chow-form inequality (`SlopeBound`, in-tree, proved) [HS, VOLUME].
  - Uniformity over the growing family comes from `VolumeTheoremX` (in-tree; one-sided; error ≥ the main term) [VOLUME].
  - No Published input claims a full arithmetic HS for vector-weight cusp forms on non-compact U(p,q). So nothing here is stronger than the literature *as a Published premise*. The strength sits in in-tree theorems, which this node did not verify.

## 3. Children

| name | file:line | statement | role | weight |
|---|---|---|---|---|
| `flatDegVal`, `FlatDegree`, `deg_eq_toFrame`, `flDefect_vw`, `sum_flDefect_vw` | EFS:183-184, 219-223, 711-715, 751-754 | deg(flat) = (p−q)/2·logΩ + q(log d − lrd E); the q-part is the finite defect | exact q-term | core (read) |
| `Fl.flatDegree` ← `hermitian_metric_log_norm_formula`, `chowla_selberg_period`, `frame_function_cm_value` | FDH:60-118; HMS:8 | Chowla–Selberg ⇒ the flat degree | source of logΩ and of the q-term | core; HMS statement checked by hand (§2.2); suppliers not opened |
| `HasNorms`, `HasInfNorm`, `HasFinNorm`; `kronecker_character_frame_bound` | ICM:59-82; KCF | q directions with inverse Hodge Gram; frame degree has no q-term | convention | definition (read) |
| `flatLine_thetaRoot_twist_twistingSection` | FTS:14 | twist lower bound with the loss q·lrd·Σ\|w\| | consumer | core (statement read; premise AbelianDeRham) |
| `FlatVal` (`abs_flat_c1_add_logOm_le…`) | FVS:11 | \|c₁ + (p−q)/2·logΩ\| ≤ 3qL | discards the sign | glue |
| `twice_twist_ge`, `lrd_le`, `flat_at_of_split_covering` | FBA:76-123; FSC:28-90 | q-part ≤ (11CA+83)·unitE | booking | glue (read) |
| `AnchorAt` | CXC:98-102 | Σ\|anc\|·q·L ≤ CA·unitE | q-part allowance | glue (read) |
| `covolume_measure_eq_one` → `OneMeasure` | `HBW/NormalizedCovolumeEqOne.lean:19-25`; OMS:14-96 | ExactRatio + volume bounds | metric normalisation | core-ish; suppliers not opened |
| `CovolumeRatioIdentity` | `HBW/CovolumeRatioIdentity.lean:11` | log μ(𝓕) ≤ f·r²·log(r+3) + 119·f·r²·L | Tamagawa-type bound | standard-shaped |
| `degree_frames`, `exists_constSec` | `KroneckerCharacterPeriodFormula.lean:104` | Hodge-Gram degree → homN degree | where a q·log(2πx) could hide | **definition to unfold; not read** |

## 4. Oddities

1. **The lieFacZ sign question.**
   - homN multiplies by exp(−(Σ_{τ,i}G_{τ,i}/2)·log(2πx)), with no sign distinction between the p and q coordinates (IPM:664-665).
   - The Hodge-Gram norm in HasInfNorm treats the q directions with the opposite sign (ICM:63).
   - flatDegVal has no log 2π or log x term. So the transport must either cancel lieFacZ(flatWt) exactly or absorb it. If it did not, a q-dependent term of size ≈ q·|log(2πx)| ≈ q·(½log d + log N𝔠_K) per unit weight would be at stake: the same order as the q-part.
   - Not checked. This is the one place where the q-coefficient could be wrong.
2. **The name `covolume_measure_eq_one` oversells.** No measure is set to 1. The probability measure muQ1 is a definition, and the content is ExactRatio plus the volume bounds.
3. **FlatVal keeps only |·|.** The q-part's known positive sign is thrown away. This is harmless for validity.
4. **The twist lemma charges q·lrd E·Σ|w|** on top of the exact q·(log d − lrd E). Whether this second loss is real (non-integrality of the twist at the different) or only booked is not determined.
5. **ξ₀ ∈ ℚ·√−d** (DH:149, with `sqd_sq`), so NORMS oddity 2 is closed.

## 5. Coverage

**Read (audit files):** PROTOCOL; NODE-CARRIER, NORMS, COVOL, HS, VOLUME and L6 in full; DIVKEY:1-120; MAIN-ARGUMENT §9.8 and the §5 table row; HOSTS:28-60, 130-145; ARCH by grep.

**Lean read:**
- EFS:700-760 plus grep lines; FDS (all); FDH (all); HMS (all); `FrameFunctionCmValueStatement.lean`; `ChowlaSelbergPeriodStatement.lean`; ICM:59-84;
- KCF statement and `KroneckerCharacterFrameBound.lean:20-27`; CXC:15-175; FBA:1-140; FSC:20-92; `TPS/FlatBoundOfAnchor.lean` (all); FVS; FTS:14;
- ZON:55-100; DAs:11-42; `DataParams₂.lean:60-72, 218-230`; DH:125-160 plus grep 48, 54; HRaw:12-45, 142-178;
- `CuspidalL2Subspace.lean:25-40`; `LocalNewformFunction.lean:135-141`; IPM:660-682;
- `HBW/NormalizedCovolumeEqOne.lean` (all); OMS:14-120; `MeasAtOf.lean:15-50`; `TPS/CoveringMeasureReductionBound.lean:14-40`; `HBW/LogMeasureRatioBounded.lean` (all); `HBW/PlugPairs.lean`; `HBW/CovolumeRatioIdentity.lean:11`; `HBW/ToKnownTheoremsOf.lean:1-60`;
- `TPS/TopCovolG.lean:39-61`; `SchurLatticeConjugates.lean:39-41`; `AdjoinCycZeta.lean:130-145`.

**Greps run:** `def lrd`; `def rd\b`; `def rdE`; `host.v`; `sqd`; `def fockScale`; `def HasNorms`; `degree_frames`; `covolume_measure_eq_one`; `PublishedHodgeBundleTheorems`; `twice_twist_ge`; `flatLine_thetaRoot_twist_twistingSection`; `abs_flat_c1_add_logOm…`; `exZ`.

**Not opened:**
- `degree_frames` and `exists_constSec` bodies (the Hodge→homN transport);
- `deg_eq_of_local_two_curves` (the HMS proof); `frame_function_cm_number_field`/`_height`;
- the twist-lemma proof; `exists_neg_unitE_le_log_ratAt`; `covolume_ratio_eq_index` and `tamagawa_number_upper_bound` bodies;
- AbsorbE (cited via DIVKEY); the Rallis suppliers [L6].
