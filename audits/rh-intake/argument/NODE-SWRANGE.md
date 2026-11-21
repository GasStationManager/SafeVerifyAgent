# NODE-SWRANGE: the Siegel–Weil range behind the Rallis inner product formula (HeckeForm / HeckeFormNS, AForm)

Paths are relative to `.../scratchpad/art/lean/src`. `DAV/` = `Development/AbelianVarietyTheory/`, `DLP/` = `DAV/Proofs/DecoratedLatticeProofs/`, `TPS/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/`, `LTD/` = `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/`. Abbreviations from NODE-MULTEQ / NODE-DETSIG (HFN, PRM, SEN, …) are reused. New ones:
- `ISZ` = `DAV/Definitions/LatticeFrames/IntegrandSZero.lean` (Pair, SiegelWeilAll, GlobalForm, EulerRight, HeckeForm)
- `SWC` = `DAV/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitaryConvergent.lean`; `SWS` = `DAV/PublishedTheorems/SiegelWeil₂/SiegelWeilUnitarySchrodinger.lean`
- `WSF` = `DAV/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean`
- `DMF` = `DAV/PublishedTheorems/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean` (DoublingMethod)
- `UDG` = `DAV/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean` (UnramifiedDoublingGL)
- `SWI` = `DLP/SiegelWeilFockDoubledPairOfWeilAndIchino.lean`; `HOD` = `DLP/HeckeFormOfDoubling.lean`; `HIE2` = `DLP/HeckeInnerProductFormulaOfDoublingEuler.lean`
- `SVL` = `DAV/BlockTheory/TwistedDiscreteSeries/SphericalVolumeLift.lean`; `TLC` = `DLP/ThetaLiftChainStepExactInnerProduct.lean`
- `ECL` = `TPS/EveryCharacterOfLiteratureOfVWin.lean` (root filling of the Published leaves)

Tags: **[proved, read]**, **[proved, stmt]**, **[hyp]**, **[not found]** as in PROTOCOL/DETSIG. Nothing compiled.

## 0. Verdicts

| Q | Answer |
|---|---|
| Q1 | All four leaves are **statements whose shape matches the literature**, and none is visibly stronger. (a) `WeilSiegelFormulaUnitary`: Weil's convergence of the theta integral over U(B) when B is anisotropic or rank A + witt B < rank B (with a continuous-seminorm bound). The Siegel–Weil identity is claimed only when 2·rank A < rank B, where the Siegel Eisenstein series on U(A⊕A⁻) converges absolutely. This is Weil 1965. (b) `SiegelWeilUnitaryConvergent`: for rank A < rank B ≤ 2·rank A and rank A + witt B < rank B, the Eisenstein series of the Siegel–Weil section continues holomorphically to s₀ = (rank B − rank A)/2, and its value there is the normalised theta integral, with constant 1, for Fock (K-finite) vectors. This is Siegel–Weil in Weil's convergent range for unitary groups: the unitary analogue of Kudla–Rallis 1988 (Crelle 387), due to Ichino (Math. Z. 2007). It is also contained in the later regularised work (Gan–Qiu–Takeda 2014, Yamana). (c) `DoublingMethod`: Langlands continuation of Siegel Eisenstein series with local uniform moderate growth; at most a simple pole at (b − n)/2 for b > n; the Piatetski-Shapiro–Rallis basic identity for Re s > n/2; continuation of the global zeta integral. (d) `UnramifiedDoublingGL`: Z(s) = L(s+½, α)L(s+½, α⁻¹)·∏_{i=1}^n(1 − q^{−(2s+i)}) at split places (Piatetski-Shapiro–Rallis; Li 1992). I checked n = 1 by hand. **Status:** each is a `def … : Prop` in namespace `GlobalTheory.Published`, so in-tree it is a statement. On the live route each is supplied by an **in-tree theorem** with a closed proof term; the root argument `O` is ignored (ECL:481-482, 529-530, 541-542, 371-372, 511-512). `SiegelWeilUnitaryConvergent` itself is **derived in-tree** from the stronger-looking Schrödinger-model leaf `SiegelWeilUnitarySchrodinger`, which has the same range (`sw_doubled_of_std`, `DLP/SiegelWeilDoubledSpaceOfStandardUnitary.lean:33-56`). I did not read the proofs of these closed theorems. |
| Q2 | Precise Lean inequality: `SiegelWeilAll` / `SiegelWeilFock` require 1 ≤ rank A < rank B and (witt B = 0 ∨ rank A + witt B < rank B) (ISZ:89-98; `SiegelWeilFock.lean:16-29`). With rank B = rank A + t (`HidaSetting`, SVL:75-77) this is exactly HeckeForm's `wittIndex B = 0 ∨ wittIndex B < t` (ISZ:168). **Row step j → j+1** (A = Y_j, B = Y_{j+1}, TLC:106-111): rank A = r + jt, rank B = r + (j+1)t, witt B ≤ ⌊(m−j−1)/2⌋ < t (proved, `ThetaChainStageWittIndexLtAndPlacesTwoSplit.lean:15-30`). So every row step is **inside Weil's convergent range**. Only j = 0 is in the absolutely convergent range 2·rank A < rank B (r < t). Steps 1 ≤ j ≤ m−1 have rank A < rank B ≤ 2·rank A and fall in the `SiegelWeilUnitaryConvergent` branch. **Layer lift** U(W_j) → U(V_j) (AForm): rank A = r, rank B = r + t, witt V_j = 0, and rank W_j < t is proved (`LiftPairPositiveDefiniteWittIndexZeroCartanStatement.lean:13`). It is anisotropic and absolutely convergent (Weil 1965). **No step is in the stable range** (witt B ≥ rank A fails everywhere), and none is needed. |
| Q3 | Case (b) of the brief, with a correction: the roles do make the right inequality hold. MULTEQ's "2·rank A < rank B" is the condition for **absolute convergence of the Eisenstein series** on the quasi-split doubled group U(A⊕A⁻) ≅ U(n,n), n = rank A. Siegel–Weil only needs **convergence of the theta integral over U(B)**, i.e. Weil's condition rank B − witt B > rank A. `siegelWeilAll_of_hypotheses` (SWI:49-84, **read**) case-splits. If rank B ≤ 2·rank A it applies `SiegelWeilUnitaryConvergent` (SWI:58-63). Otherwise it applies `WeilSiegelFormulaUnitary`'s absolutely convergent identity and identifies the coset sum with `EisValueAt` via `eisValueAt_flat` (SWI:64-84). No regularised statement is assumed, and there is no gap. |
| Q4 | **Justified in every range where it is used. Not ESCALATE.** ΘΘ* and θθ* are computed from Siegel–Weil in Weil's convergent range. The basic identity for Re s > n/2 is followed by an Euler product for Re s > n+1, then by analytic continuation to s₀ = t/2 (HIE2:19-64, read). The value l of L^S at s = t/2 (i.e. at (1+t)/2) is a hypothesis `HolValueAt … l` passed in by the caller. Residual items for an expert are in §4: confirm the Ichino 2007 citation for the full Weil range, and note that the leaves are in-tree closed theorems whose (large) proofs were not read. |

## 1. Statement

### 1.1 The four leaves (as the Lean says)
- **`WeilSiegelFormulaUnitary`** (WSF:56-69, read). For every rank-≥1 A, every B and Haar m on U(B), assume witt B = 0 or rank A + witt B < rank B. Then:
  - (i) for each basis ε there is a continuous seminorm ν with ∫_{[U(B)]} Σ_ξ |φ(h⁻¹ξ)| ≤ ν(φ) (`absThetaInt`, WSF:30-31);
  - (ii) for every Weil datum ω on (U(A⊕A⁻), U(B)) and theta function f, h ↦ θ(g,h;f) is integrable on [U(B)];
  - (iii) **if 2·rank A < rank B**, the Siegel–Weil section g ↦ ∫_{Lagrangian} ω(g)f is left P(F)-invariant, its coset sum over P(F)\G(F) converges, and it equals the averaged theta integral ⨍_{[U(B)]} θ(g,h;f) dh.
- **`SiegelWeilUnitaryConvergent`** (SWC:18-32, read). Assume rank A < rank B ≤ 2·rank A and rank A + wittIdx B < rank B. For every Weil datum, majorant a with Iwasawa decomposition, Cartan data, covolume-one measure, Haar ν and Fock vector f, the theta integral converges and `EisValueAt A (flat …(swSec f)(s₀)) s₀ (thetaMean ω ν f)` holds with s₀ = `sZero A B` = (rank B − rank A)/2 (`SphericalZero.lean:38`, grep line). Unfolded:
  - `EisValueAt` (`DAV/Definitions/Foundations/EisValueAtIffEisPoleLE.lean:46`): the flat family converges for Re s > rank A/2 (`IsEisFamily`, :34);
  - and for every g, `HolValueAt (s ↦ E(g,s)) s₀ (thetaMean g)`;
  - `HolValueAt` (`DAV/Definitions/Foundations/EventuallyEqOfIsPreconnected.lean:228`, with `IsExtAt` :218 and `IsMerExt` :214) means: a meromorphic extension from a right half-plane, analytic at s₀, with that value;
  - `thetaMean` (`DAV/PublishedTheorems/TwistedTraceFormula/SiegelWeilAnisotropicUnitary.lean:19-21`) = ⨍_{[U(B)]} θ.
  So: **E(g, s₀, Φ_f) = I(g, f)** with constant 1, which is right for m > n.
- **`SiegelWeilUnitarySchrodinger`** (SWS:107-122, read). This is the live source of the previous leaf. It states the same theorem for U(n,n) × U(V) in the Schrödinger model: n < rank V ≤ 2n, n + wittIdx V < rank V, χ|_{𝔸_F^×} = η^{rank V} (`ResEta D χ V.rank`), Fock Φ, s₀ = (rank V − n)/2 (SWS:90). The conclusion is HolValueAt of the coset sum at s₀, equal to the averaged theta integral. `sw_doubled_of_std` (`DLP/SiegelWeilDoubledSpaceOfStandardUnitary.lean:33-56`, read) transports it to the doubled-space form. The range hypotheses are passed **unchanged** (`hAB hB2 hW`, line 55).
- **`DoublingMethod`** (DMF:36-46, read). For V of rank n ≥ 1, majorant a with Iwasawa, Hecke μ with `ResEta D μ b`, and φ in the degenerate principal series:
  - (i) the flat Eisenstein family continues meromorphically, and near every s₀ some (s−s₀)^k E is holomorphic, jointly continuous and of uniform moderate growth (`EisRegularAt`, DMF:17-22);
  - (ii) if n < b, there is at most a simple pole at (b − n)/2;
  - (iii) for cusp forms f₁, f₂ and Re s > n/2, the basic identity holds: ∫∫ E(ι(g₁,g₂)) f₁ f̄₂ μ⁻¹ = Z(s, φ, ⟨π(g)f₁, f₂⟩) (`BasicIdentity`, DMF:26-28), and Z continues.
  On the root variant this leaf is replaced by `DoublingMethodLocalZetaIntegrals` = `ResidueKilled.DM` (`LTD/DiscreteSpectrumResidualClassification.lean:6`, grep line). That is the same statement with (ii) replaced by `True` (`Development/WeilBound/RepresentationTheoryGL/EisensteinResidues/AnisotropicGlobalForms/DmOfHyp.lean:13-22`, read). (iii) is proved in-tree from CuspRapidDecay + SiegelEisensteinContinuation (`dm_of_two`, same file :24-34, read).
- **`UnramifiedDoublingGL`** (UDG:314-324, read). k is a p-adic field, K = GL_n(𝒪) has volume 1, π has Satake α, and ω is a zonal spherical function. Then ∃ s₀ such that for Re s > s₀,
  ∫_{GL_n(k)} f_s(diag(g,1))ω(g) dg = ∏(1−α_i q^{−s−½})⁻¹ ∏(1−α_i⁻¹q^{−s−½})⁻¹ ∏_{i=1}^n(1 − q^{−(2s+i)}).
  Here f_s = |a/d|-character to the power s + n/2 for the parabolic stabilising the diagonal, and ι = block diagonal (UDG:19-28, 304-306).
  - *(inferred)* For n = 1 the integral is Σ_{k≥0}α^kq^{−k(s+½)} + Σ_{k≥1}α^{−k}q^{−k(s+½)} = (1−q^{−2s−1})/((1−αq^{−s−½})(1−α⁻¹q^{−s−½})), as claimed.

### 1.2 HeckeForm / HeckeFormNS (the Rallis formula consumed downstream)
`HeckeForm D` (ISZ:165-180, read) has these hypotheses:
- `Pair` (ISZ:60-72), whose `HidaSetting` (SVL:75-77) gives 1 ≤ rank A, 1 ≤ t, **rank B = rank A + t**;
- witt B = 0 ∨ witt B < t;
- Fock Φ₁, Φ₂ unramified off S_f;
- cusp forms u₁ (with Satake family `par` off S_f) and u₂ (spherical off S_f);
- ∃ s₁ < t/2 such that the doubling integrand at s₁ is integrable over the off-S_f open set.

Its conclusion: the lifts converge, and for every l with HolValueAt(L^S(s+½, par⊗χ_B⁻¹), t/2, l),

  ⟨θ(Φ₁,u₁), θ(Φ₂,u₂)⟩_{U(B)} = vol·(l / d^S(t/2))·∫_{open, off S} ⟨ω(g)Φ₁,Φ₂⟩⟨g·u₁,u₂⟩ dg.

`up` integrates over U(A) and produces a function on U(B) (ISZ:27-28): the lift goes **from the smaller space A up to B**. `HeckeFormNS` (HFN:202-218, read) is HeckeForm with two extra hypotheses (2 ≤ t, and a split auxiliary place). `heckeFormNS_of_heckeForm` (HFN:220-223) just drops them.

## 2. Argument

### 2.1 The chain HeckeFormNS ⇐ Published leaves (all read at top level)
1. `Hypotheses3.q8` (`DAV/Definitions/LatticeFrames/LatticeFramesOfHyps.lean:28-30`) = `heckeFormNS_of_heckeForm (heckeForm_of_doubling₂ q13 q2 q7 sw q9 q10 D)`. The root-side twin is `PublishedThetaConditionTheorems.q8` (`LTD/Hypotheses3.lean:7-24`). It uses `heckeForm_of_doubling'` (`LTD/HeckeFormOfDoubling.lean:16-25`), which is identical except for the DoublingMethod variant.
2. `heckeForm_of_doubling₂` (HOD:47-56) combines:
   - **GlobalForm** from `global_form_of_siegel_weil` (p1..p5);
   - **EulerRight** from the unramified computations: split places via `UnramifiedDoublingGL` (p6); inert places via the proved `unramifiedDoublingIntegral_inert_place`; parameter bounds via the proved `sphericalParameterBound_*`;
   - then `heckeInnerProductFormula_of_doublingEuler`.
3. **GlobalForm** (ISZ:100-112) says: the doubling zeta integral ∫ integrand(s) converges for Re s > rank A/2, has a holomorphic value z at s₀, and ⟨θu₁, θu₂⟩ = vol·z. It is proved by `globalForm_of_siegelWeil` (`DLP/GlobalFormOfSiegelWeil.lean:28-34`): `SiegelWeilFock` (from SWI) is fed into `global_form_frame_lattice` (stmt) and then transferred to any self-dual lattice (stmt).
4. **The range split** (`siegelWeilAll_of_hypotheses`, SWI:49-84, read in full):
   - The hypothesis is witt B = 0 ∨ rank A + witt B < rank B (SWI:56-57).
   - **Case rank B ≤ 2·rank A** (SWI:58-63): witt B = 0 implies rank A + 0 < rank B, since rank A < rank B. So Weil's inequality holds, and `SiegelWeilUnitaryConvergent` is applied verbatim.
   - **Case 2·rank A < rank B** (SWI:64-84):
     - WSF(ii) gives convergence of the theta integral;
     - WSF(iii) gives coset-sum convergence and coset sum = theta mean;
     - Re s₀ = (rank B − rank A)/2 > rank A/2 (SWI:72-77);
     - `eisValueAt_flat` turns the convergent coset sum into `EisValueAt` (SWI:78-84).
5. **From s₀ to the L-value** (`heckeForm_of_global_euler`, HIE2:19-64, read):
   - s₀ = t/2 by rank B = rank A + t (HIE2:25-28).
   - EulerRight gives ∫ integrand(s) = L^S(s+½)/d^S(s)·∫_{off S} integrand(s) for Re s > rank A + 1 (HIE2:44-52).
   - The off-S integral is holomorphic on Re s > s₁ (`flatFamilyZeta_convergence_holomorphy`, HIE2:36-38, 53-58). d^S is analytic and non-vanishing (HIE2:43).
   - `holomorphicContinuationValue_eq_div_mul` (stmt) gives z = (l/d^S(t/2))·∫_{off S} integrand(t/2), by uniqueness of continuation (HIE2:60-64).
   - This is the standard route (Kudla–Rallis, Li).

### 2.2 Applications on the live route and their ranges
Definitions (PRM:12-17, 32, 40, read): r = k + m − 1, rankY j = r + jt, with r + 5 ≤ t, 3m < t, t odd, m ≥ 2.

| use | Lean site | U(A) (integrated, doubled) | U(B) (theta integral) | witt B | Weil: rank B − witt B > rank A | absolute: 2·rank A < rank B | stable: witt B ≥ rank A | branch used |
|---|---|---|---|---|---|---|---|---|
| row step 0 → 1 | TLC:100-118, 141-144 | Y_0, rank r | Y_1, r + t | ≤ ⌊(m−1)/2⌋ < t | yes | **yes** (r < t) | no | WSF (Weil 1965) |
| row step j → j+1, 1 ≤ j ≤ m−1 | same | Y_j, r + jt | Y_{j+1}, r + (j+1)t | ≤ ⌊(m−j−1)/2⌋ < t (0 at j+1 ≥ m−1) | yes: margin t − witt ≥ t − m/2 > 0 | **no**: 2(r+jt) ≥ r+(j+1)t ⟺ r + (j−1)t ≥ 0 | no | SWC (Weil-range Siegel–Weil) |
| layer lift W_j → V_j (AForm, also ConjScalarAt per MULTEQ) | `DLP/ThetaInnerProductFormulaDefiniteOfRallisConverge.lean:48, 64-66` | W_j, rank r | V_j definite, r + t | 0 | yes (anisotropic) | yes (rank W_j < t, proved) | no | `Convergent` (SVL:82-91) ← `rallisInnerProduct_convergent_of_weilSiegelFormula` (WSF + SiegelEisensteinContinuation + CuspRapidDecay) |

- **Row steps.** In TLC:142-144, `hHF` (HeckeFormNS) is applied with A = s.V, B = s'.V, `hrk : s'.V.rank = s.V.rank + D.R.t` (TLC:111) and `Or.inr hwitt`. Here `hwitt : wittIndex s'.V < t` comes from `wittIndex_lt_and_two_split` at level k+1 (TLC:100). That lemma's proof (read) bounds the Witt index by the negative index of sigYD(j) at one embedding and closes by `three_m_lt_t`.
- **Layers.** AForm's inner-product formula uses only `WeilSiegelFormulaUnitary` and `SiegelEisensteinContinuation` (`DLP/TwistedThetaLiftInnerProductFormulaOfHyp.lean:29-31`). Its `Convergent` requires A.rank < t, i.e. the absolute range (SVL:86). That is discharged by `hrank` from the lift-pair lemma.
- With the sizes of earlier nodes (k ≈ x^{9/2}, t ≈ x^{398.5}, m ≈ x^{1/2}), for j ≥ 1 the ratio rank B / rank A = (r+(j+1)t)/(r+jt) ∈ (1, 2]. The Weil margin is ≈ t, which is huge.

### 2.3 Where the leaves are filled
- The live HeckeForm chain needs `SiegelWeilUnitaryConvergent`. In `hypotheses3_of_siegelWeil` (`DAV/Proofs/TwistedOperators/Hypotheses3OfSiegelWeil.lean:11-19`, read) it is produced from `SiegelWeilUnitarySchrodinger` by `siegelWeil_doubledSpace_of_standardUnitary` (= `sw_doubled_of_std`). This is called from `hypH_of_rowRatW` (DII:17-20).
- The root record `published_results_eigen` (ECL:666ff, read 640-760) fills:
  - `weilSiegelFormulaUnitary` (ECL:676) with `Sw47.weilUnitary`, a closed theorem (`Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/FockAnisoFree.lean:12-13`);
  - `siegelWeilUnitaryConvergent` (ECL:677) with `Sw47.convergent` = `sw_doubled_of_std SiegelWeilCoefficients.field` (same file :10);
  - `siegelWeilUnitarySchrodinger` (ECL:716) with `SiegelWeilCoefficients.field` (`Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/SiegelEisensteinHalfPlane/IntegralUnitCoefficients/CoefND.lean:24-25`). That is built from `lit` (:19-22), `coefND` (:13-17) and `wtc`, the last being a theorem (`…/GlobalGaussLaws/Wtc.lean:6`, grep line);
  - `unramifiedDoublingGL` (ECL:679) with `UnramDoublingProof.unramifiedDoublingGL` (ECL:529-530);
  - `doublingMethod` (ECL:678) with `doubling_method O` = `dm_of_two cusp_rapid_decay siegel_eisenstein_continuation trivial` (ECL:371-372);
  - `siegelEisensteinContinuation` (ECL:717) with a closed theorem (ECL:369-370).
- So these are **[proved, stmt]**: in-tree closed theorems, not hypotheses. Their proof bodies (Siegel–Weil in Weil's range, Langlands continuation, the unramified GL computation) were not read.

## 3. Children

| # | Name | file:line | Statement (math) | Status | Weight |
|---|---|---|---|---|---|
| 1 | `siegelWeilAll_of_hypotheses` | SWI:49-84 | Siegel–Weil for the doubled pair in the whole Weil range, split at rank B = 2·rank A | proved, read | **core** (settles Q3) |
| 2 | `SiegelWeilUnitaryConvergent` ← `sw_doubled_of_std` ← `SiegelWeilUnitarySchrodinger` | SWC:18; `DLP/SiegelWeilDoubledSpaceOfStandardUnitary.lean:33`; SWS:107 | unitary Siegel–Weil, n < m ≤ 2n, m − r > n, constant 1 | Published def; supplied by in-tree theorem (`CoefND.lean:24`), proof not read | **standard** (Ichino 2007; unitary analogue of Kudla–Rallis 1988) |
| 3 | `WeilSiegelFormulaUnitary` | WSF:56 | Weil convergence; identity when 2n < m | Published def; in-tree theorem `FockAnisoFree.lean:12`, proof not read | standard (Weil 1965) |
| 4 | `DoublingMethod` / `DoublingMethodLocalZetaIntegrals` | DMF:36; `DmOfHyp.lean:13` | Eisenstein continuation and regularity; basic identity | the pole clause is dropped on the root variant; rest proved from SiegelEisensteinContinuation | standard (Langlands; Piatetski-Shapiro–Rallis) |
| 5 | `UnramifiedDoublingGL` | UDG:314 | unramified GL_n doubling integral | Published def; in-tree theorem (ECL:529-530; `DLP/IsCommensuratedKO.lean:125`, grep line) | standard (PSR, Li 1992) |
| 6 | `heckeForm_of_global_euler` | HIE2:19 | continuation from Re s > n+1 to s₀ = t/2 | proved, read | core glue |
| 7 | `wittIndex_lt_and_two_split` | `DLP/ThetaChainStageWittIndexLtAndPlacesTwoSplit.lean:15` | witt(Y_j) < t | proved, read | glue (the range check for row steps) |
| 8 | `global_form_frame_lattice`, `holomorphicContinuationValue_eq_div_mul`, `flatFamilyZeta_convergence_holomorphy` | `DLP/GlobalFormFrameLatticeStatement.lean:18`; HIE2:60; HIE2:36 | basic identity plus SW gives ⟨θ,θ⟩ = vol·Z(s₀); identity theorem; holomorphy of the flat zeta integral | proved, stmt | glue |

## 4. Oddities

1. **Citation to confirm (ten-minute check).** `SiegelWeilUnitaryConvergent` / `SiegelWeilUnitarySchrodinger` assert Siegel–Weil for every (n, m, r) with n < m ≤ 2n and m − r > n, constant 1. I attribute this to Ichino, "On the Siegel–Weil formula for unitary groups", Math. Z. 255 (2007), which extends Weil to the whole convergent range, as Kudla–Rallis 1988 did for (Sp, O). If an expert knows that paper's range to be narrower, the fallback is the regularised Siegel–Weil of Ichino 2004 / Gan–Qiu–Takeda 2014 / Yamana, which also covers this range (constant 1 for m > n). Either way I see no statement stronger than the literature.
2. **The Published leaves are not assumptions on the live route.** They are closed in-tree theorems (ECL:481-482, 511-512, 529-530, 541-542). The mathematical trust therefore rests on unread in-tree proofs of Siegel–Weil and Langlands continuation, which are major theorems, rather than on a citation. If those proofs compile without `sorry`/axioms the point is moot; this node did not check that.
3. **`SiegelEisensteinSimplePole` is `True` at the root.** The root record's field is typed `UnusedSlot72` (`TPS/BernsteinUnitaryProductIrreducible.lean:74`, grep line) = `True` (`LTD/DiscreteSpectrumResidualClassification.lean:7`, grep line), and it is filled by `trivial` (ECL:505-506). `S0.HypothesesUE` carries a genuine `SiegelEisensteinSimplePole` field (`DAV/Definitions/Divisors/HypothesisBundleConversions.lean:117`). I found no conversion from the root record to `HypothesesUE`: greps for `toUE`, `SiegelEisensteinSimplePole :=`, `: GlobalTheory.Published.SiegelEisensteinSimplePole` hit only structure fields. So the `member_bundles_large_ue` / `hypH_of_rowRatW` producer cited by MULTEQ may not be the root's live producer. The root-side Rallis chain (`LTD/Hypotheses3.lean:7-24`) uses `DoublingMethodLocalZetaIntegrals`, which drops the pole clause. **Not a range problem**: both producers use the same `siegelWeil_fockDoubledPair_of_weil_and_ichino` split (`LTD/GlobalFormOfSiegelWeil.lean:16-22`). A root-tracing node should settle which producer is live.
4. The pole clause of `DoublingMethod` (order ≤ 1 at (b−n)/2, b > n) is consistent with Kudla–Sweet / Tan on poles of Siegel Eisenstein series in Re s > 0. I did not unfold `ResEta`. It is not used on the root variant.
5. Two inputs to HeckeForm come from the caller and were not traced here:
   - HolValueAt of L^S(s+½, par⊗χ⁻¹) at t/2, i.e. the value l at (1+t)/2. For j ≥ 1 the level-j parameter contains segments, so (1+t)/2 is not in the trivial convergence region of the full level-j L-function. Its finiteness and non-vanishing are the `LFull`/`IsHval` business of NODE-MULTEQ.
   - the existence of s₁ < t/2 with integrability off S. It is discharged by `LevInt`/`QPeel` (TLC:133-139), which were not read.

## 5. Coverage

**Read:**
- ISZ:1-192; SWC:1-38; WSF:1-90; DMF:1-60; UDG:1-40, 300-330; SWS:90-126; `SiegelEisensteinSimplePoleOfDoublingMethod.lean:1-23`; `SiegelEisensteinContinuationOfDoublingMethod.lean:10-30`; `EisValueAtIffEisPoleLE.lean:10-60`; `EventuallyEqOfIsPreconnected.lean:195-232`; `SiegelWeilAnisotropicUnitary.lean:15-30`;
- HOD:1-58; `DLP/GlobalFormOfSiegelWeil{,Statement}.lean` (all); `DLP/SiegelWeilFockDoubledPairOfWeilAndIchino{,Statement}.lean` (45-86; Statement all); `SiegelWeilFock.lean:10-33`; `DLP/HeckeInnerProductFormulaOfDoublingEuler{,Statement}.lean` (all); HFN:200-224; `LatticeFramesOfHyps.lean:1-42`; `Hypotheses2.lean:1-24`;
- SVL:75-100; TLC:1-173; `ThetaChainStageWittIndexLtAndPlacesTwoSplit.lean:15-31`; PRM (grep lines 12-17, 32, 40);
- `DLP/ThetaInnerProductEqConstMulLValue.lean:40-57`; `DLP/TwistedThetaLiftInnerProductFormulaOfHyp.lean:29-33`; `DLP/RallisInnerProductConvergentOfWeilSiegelFormulaStatement.lean:21-22`; `DLP/ThetaInnerProductFormulaDefiniteOfRallisConvergeStatement.lean:14-15`; grep lines 41-66 of the proof file; `LiftPairPositiveDefiniteWittIndexZeroCartanStatement.lean:13` (fragment);
- ECL:369-373, 475-560, 640-760; `FockAnisoFree.lean` (all); `CoefND.lean:1-29`; `DmOfHyp.lean:1-36`; `LTD/HeckeFormOfDoubling.lean` (all); `LTD/GlobalFormOfSiegelWeil.lean:14-24`; `LTD/Hypotheses3.lean` (all);
- DII (all); `Hypotheses3OfSiegelWeil.lean` (all); `SiegelWeilDoublingAssemblyStatement.lean` (all); `DLP/SiegelWeilDoubledSpaceOfStandardUnitary.lean:33-60`; `LinkedBundleConstructionExists.lean:20-60`; `HypothesisBundleConversions.lean` (grep lines 56-135).

**Greps run:** `heckeForm_of_doubling₂|SiegelWeilUnitaryConvergent\b`; `def GlobalForm|HeckeForm|EulerRight|HeckeFormNS|global_form_of_siegel_weil|heckeInnerProductFormula_of_doublingEuler`; `SiegelWeilAll`; `siegelWeil_fockDoubledPair_of_weil_and_ichino|global_form_frame_lattice`; `def SiegelWeilFock`; `def EisValueAt|thetaMean|sZero|flat|wittIdx|wittIndex`; `def HolValueAt|Continues|IsRightDomain`; producers of `Published.(SiegelWeilUnitaryConvergent|WeilSiegelFormulaUnitary|DoublingMethod|UnramifiedDoublingGL)`; `SiegelWeilCoefficients.field|sw_doubled_of_std`; `wtc|genA_hf|top7`; `DoublingMethodLocalZetaIntegrals`; `def SiegelEisensteinSimplePole|UnusedSlot72|SiegelEisensteinContinuation|SiegelWeilUnitarySchrodinger`; `siegelEisensteinSimplePole\s*:`; `toUE|SiegelEisensteinSimplePole :=`; `structure UnitaryGroupThirdPlaceHypotheses|HypothesesUE`; `HeckeFormNS`; `wittIndex_lt_and_two_split`; `rallisInnerProduct_convergent_of_weilSiegelFormula|thetaInnerProductFormulaDefinite_of_rallisConvergent|liftPair_positiveDefinite_wittIndexZero_cartan`; `T.heckeForm_of_doubling\b`.

**Not opened:** proof bodies of `CoefND`/`top7`/`lit` (Siegel–Weil), `Sw47.weilUnitary`, `UnramDoublingProof.unramifiedDoublingGL`, `siegelEisensteinContinuation`; `global_form_frame_lattice`, `holomorphicContinuationValue_eq_div_mul`, `flatFamilyZeta_convergence_holomorphy`, `LevInt`, `QPeel`; `innerProductFormulaC_of_convergent` beyond grep lines; `ResEta`; which producer of the Rallis chain the root actually reaches.
