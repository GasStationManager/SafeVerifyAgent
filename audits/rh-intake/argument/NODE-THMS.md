# NODE-THMS: Theorem S (near-orthogonality) and the counting theorem: what they assert, how strong they are, a hand model

Paths are relative to `.../scratchpad/art/lean/src`. "The Lean says" = I read the cited line in this pass. *(mine)* = my own computation or inference. [NODE] = taken from that node, not re-read. Nothing from the tree was compiled or run. My scripts are in `/tmp/claude-0/-home-user-SafeVerifyAgent/6f6a4549-468b-59ec-896e-73bdf5d26a96/scratchpad/thms/` (`sl2_gram.py`, `inspect.py`, `hecke_pairs.py`). They were run with `python3 -I` and numpy only.

Abbreviations:
- `LSF` = `Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/LinkSFinalP.lean`
- `TSO` = `…/FlagStabilizerTensors/ThmSOwn.lean`
- `PB` = `Formalism/HermitianCurvature/StatementPB.lean`
- `RC` = `Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsConc.lean`; `RO` = `…/CokernelGLCounts/RowsOther.lean`
- `TD16` = `Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`
- `UAC` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean`
- `SWL/` = `Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/`; `ST/` = `Development/AbelianVarietyTheory/Statements/CuspFrameWeights/`
- `LP` = `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/LayerProd.lean`
- `CPM` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/ConjPowOfMulEqOne.lean`
- `CT` = `…/FlagStabilizerTensors/CountT.lean`; `STR` = `…/FlagStabilizerTensors/SpectralTiesReal.lean`; `DSE` = `Formalism/SharpRestriction/CuspSpanNormBounds/DstarEq.lean`; `BCE` = `Formalism/SharpRestriction/CuspSpanNormBounds/BridgeCountE.lean`

## 0. Verdict

**No ESCALATE.** Theorem S is *not* the statement the brief feared, namely "the Gram matrix of a spanning family is within 1 + b⁻⁶ of diagonal". Nor does it rest on "weight × displacement ≥ log(#cosets)".

1. **What Theorem S asserts.**
   - Fix a pair of distinct words u ≠ u′. The block P_u*P_u′ between two Poincaré-series blocks, of dimensions d_u, d_u′ ≍ D*/Γ², has squared Hilbert–Schmidt norm at most (1 + b⁻⁶)·d_u·d_u′/D*. This is the value for *randomly placed* subspaces (§1).
   - So the bound is not "≈ 0". It is an exact-constant upper bound at the random level, imposed on **every** pair. Two weaker statements follow from it and do not imply it:
     - the *average* over pairs, which is forced by linear algebra once the count and the diagonal clause hold (§2.4);
     - in combination with the count, that the Poincaré system is a near-tight frame.
   - In words: no pair of words correlates more than random by more than b⁻⁶.
2. **The mechanism is not archimedean decay.** The weight enters Theorem S only qualitatively: through absolute convergence (`WuDecay`) and through the large-gap hypotheses of Theorem B and multiplicity one.
   - The main term d_u d_u′/D* comes from the **generic open double cosets**, not from the identity, which contributes 0 for u ≠ u′. It is bounded above by an exact mass identity times a Bessel/Plancherel inequality ∫HS²(orbital integral) ≤ 1/d_π (`EnergyAbs`).
   - The other orbits are small for p-adic reasons: level savings (2/g)^{(s−1)kf}, Siegel mass ratios, rarity of non-saturated lattices q^{−(k−2r−5)}, and a Gauss sum on a hermitian quadric.
   - The constant b⁻⁶ is the **level's** Gelfand–Graev loss ∏_v(1 + 3/g_v) ≤ e^{6b⁻⁷} plus local-density corrections δ ≤ b⁻⁷ (§2.2).
   - The inequality the brief asked for, "weight × minimal displacement ≥ log(count)", does exist. It belongs to the **counting theorem** (far terms, §3.3), and its injectivity-radius input is `NearUnip`. That proof is elementary and I read it in full (§3.2).
3. **SL₂(ℤ) model** *(mine, §2.5)*.
   - The brief's edge effect is real for Fourier-index Poincaré series: P_1,…,P_D are *not* nearly orthogonal at the top of the range. At k = 600 (D = 50), the smallest eigenvalue of the Gram of P_1..P_50 is 0.002.
   - But the Lean does not live in that regime. Its "index" T_u is far beyond its weight [TFLOOR, COUNT], which is the random-correlation regime. There the model reproduces the Lean's three clauses in shape:
     - blocks of size b have ‖K_uu − 1‖² ≈ b²/D;
     - cross-blocks have mean ‖K_uu′‖²/(b²/D) = 0.97–0.99;
     - the maximum excess over 1 falls roughly like 1/b (3.4, 1.6, 0.9, 0.4 for b = 3, 6, 12, 24).
   - Hecke-related blocks (I, pI) show no excess.
   - Tightness of the frame improves with overfill: the relative HS deviation is 0.20, 0.12, 0.054 and 0.016 at overfill 3, 6, 12 and 24.
   - So an exact-constant per-pair bound is plausible only when the blocks are huge (d_u ≫ b¹²). The Lean has d_u ≍ D*/Γ², which is astronomically larger.
4. **Counting theorem** (§3).
   - The assembly is read. Its precision follows from the stated leaf bounds by elementary algebra. I re-derived the far-term and deep-term exponent margins from the Lean's formulas.
   - The dominant error is the **thin/cusp region**, whose relative volume is e^{−nf log n/4}. That is a rank effect (a Siegel mean value), not a weight effect.
   - There are no elliptic terms at all, because the level at g₀ makes the lattice neat.
   - The brief's "∏ root pairings⁻¹" form does not occur. Non-unipotent terms decay like e^{−hε²/16} = e^{−50(Cg+4)n³f log(b·rd)}.
5. **`rowsTiePT'_of` is glue** (read, `CT:41-43`). The tie is the record field `AutTie.D_eq : B.D = Dall` of the selection's `STies` (`STR:251`; `DSE:20`). It holds by construction for every selected record. Non-vacuity, i.e. that such records exist, is upstream: the selection σ is an argument of `at_choice_alt`.

## 1. Statement (Theorem S on the live path)

**The Lean.** `TheoremSSelected` (`TSO:669-674`): for every family member (x, i) under the standing hypotheses, and all words u ≠ u′,
```
‖((s.2 x hx h0 i).Y.tO u u').K0‖ ^ 2 ≤ (1 + ((Fm.L x i).sc.b ^ 6)⁻¹) * ((D.duS u) * (D.duS u') / D.what₂.Dstar)
```
It is produced by `offDiagonalK0_of_rows` (`LSF:58-112`) from `TheoremSDistinctWords` (`LSF:30-35`) and `TheoremSAtData` (`LSF:18-28`). The latter has hypotheses SizesAt, Hyp0, Stand, KTwoHypotheses, GapHyp, LocTied, TFrameAt, RowBig(epsL), RowNotScalar(epsL). The closed form `TheoremSClosedConclusion` also gives `hsSq u u' ≤ (1 + b⁻⁶)·d_u d_u′/D*` (`LSF:37-49`).

**Unfolded.**
- **Group and space.** G = U(V) for a hermitian space of signature (k + r, r + 1) at each of the f real places of F. HH is the π∞-isotypic, level-χ part of L²(G(F)\G(𝔸)), with dim HH = Dall [PAIRB §0; SLEAVES].
- **Sources.** C_u = ψ_N-equivariant, level-χ functions on the Bessel group R_u = U(W_u) ⋉ N, where W_u is definite of rank k. Its dimension is d_u = `duC` = finrank C_u, tied to `duS u` by `ConcTie` (`RC:30, 57`).
- **The maps.** P_u : C_u → HH is the Poincaré series T ↦ Σ_{δ∈R_u(F)\G(F)} Ph_T(δx) [PAIRB §0, `PIH:144-216`].
- **D\*** = `DstC` = formal degree × vol(fund) × e(1) (`RC:32`), tied to `D.what₂.Dstar` (`RC:57`).
- **The operator.** `Terms.K` = Σ_t op(t) is the double-unfolded kernel of (c_u c_u′)^{−1/2}·P_u*P_u′ : C_u′ → C_u, written as a sum over terms t (pairs of lattices and double-coset classes). It has values in HS(C_u′, C_u), so ‖·‖ is the Hilbert–Schmidt norm (`TermOp.lean:265`; `PB:57`).
- **K0** = (identity part) + (generic part) + (non-generic part) (`PB:61`). Here K = K0 + (degenerate part) (`PB:121-123`). For u ≠ u′:
  - the degenerate terms are 0 (`KppOffC` → `KppTermZero`, `RC:91-96`; `RO:17`);
  - the identity part is 0 (`IdZero`, `PB:111`; proved [COUNTS]).

  So K0 = K. **Every surviving term is a non-identity orbit.**
- **The diagonal clause** (`DiagC`, `RC:126-132`; `DiagRow`, `RO:50`; `KppDiag`, `RO:21-22`):
  - ‖K0(u,u) − 1‖² ≤ Γ_P·d_u²/D*, with Γ_P = e^{C_B m⁵ f log b} (`gamB`, `RC:51`), under `max CB C4 + 1 ≤ CGam`;
  - ‖K_deg(u,u)‖² ≤ d_u·e^{−kf log k}.

  With d_u ≍ D*/Γ² (Γ = e^{CGam m⁵ f x^ε}, ChProviso [NONVAN]) this is e0·d_u with e0 ≈ C0·Γ_P/Γ². This is the frame's ‖K_uu − 1‖²_HS ≤ e0·d_u (`MatK_at`, `TD16:807-819`, read).
- **Parameter ranges** [PAIRB §2(d)]:
  - k ≈ x^{9/2+10ε}, m = 2r + 2 ≤ 2x^{1/2−ε/16}, f ≤ 4x^{2+8ε};
  - log b = x^ε, level g ≥ (kb)⁸;
  - SizeNumbers, including k ≥ 8·Cn·m⁵·f·log b.
  - Index sizes: log T_u ≲ c·m·L [TFLOOR], weights |λ| ≤ b² [COUNT]. *(mine)* So T_u ≫ |λ|^{m/2}.

## 2. Argument for Theorem S, as mathematics

### 2.1 The double unfolding
- ⟨P_u T, P_u′ T′⟩ unfolds into a sum over R_u(F)\G(F)/R_u′(F), refined by lattice classes. Each term is scl·vol(K₂)·χ₂(·)·OO_t, where OO_t = ∫ rk1(W_u(x), W_u′(γ⁻¹x)) dμ∞ is an *integral* of Bessel vectors over G∞ [PAIRB §2(b); SLEAVES].
- ‖K0‖² is expanded through the Gauss-sum matrix GG on level indices. `NormSqBound` and `GGBound` give ‖K0‖² ≤ Pg·Γ1·Σ_i‖vecPart_i‖² (`PB:76-80, 98-99, 153-157`).
- Expanding gives a sum over **same-row pairs** (t, t′). `RowOrth` kills cross-row pairs (`PB:82-84`). The pairs split into:
  - corank ≥ 2 pairs (`big`);
  - generic corank-1 scalar pairs (`sc`);
  - generic non-scalar pairs (`nsc`);
  - non-generic corank-1 pairs (`one ngSet`) (`PB:65-73, 101-115`).
- *(mine)* So Theorem S is a **second-moment (fourth-power) relative trace formula**. Its geometric side is a sum over pairs of orbits.

### 2.2 Main term and the source of b⁻⁶
- **RowMain** (`PB:113`): Γ1·Σ_sc Re⟨vec t, vec t′⟩ ≤ (1+δ)e1·dd.
  - It follows from `NormBound`, an exact volume/mass identity Γ1·AA·(c0c0′)⁻¹·(vol factors)·(1/deg) = d_u d_u′/D*, times IntOO ≤ 1/deg [PAIRB §2(1)].
  - IntOO ≤ 1/deg is `EnergyAbs`: Schur orthogonality ∫|⟨b, σa⟩|² = ‖a‖²‖b‖²/d with Følner truncation and Fatou. Only the ≤ direction is used [COUNTS §3].
  - *(mine)* So the constant 1 is a **Bessel inequality for the relative Plancherel measure of the open cells**. The formal degree in D* cancels the 1/d_π. The main term is an upper bound, which is all an upper bound on ‖K0‖² needs.
- **Final constant** [PAIRB §2(d)].
  - Pg ≤ e^{6b⁻⁷} because f/g ≤ b⁻⁷: this is the Gelfand–Graev/mirabolic ratio ∏(1 − q^{−i})^{−1} ≤ 1 + 3/q.
  - δ ≤ b⁻⁷, and e1 ≤ exp(12f·2^{−(k−2r−2)}).
  - The loop and NG terms are each ≤ b⁻¹⁴.
  - (√(Pg(A+2ε)) + √(2Pg·ε))² ≤ 1 + b⁻⁶.
  - **b⁻⁶ is a level and local-density quantity**, not exp(−weight × displacement).

### 2.3 Why the off-diagonal orbits are small
These are all non-archimedean savings [PAIRB §2; COUNTS §3; THMB]:
- **Corank s ≥ 2:** the level gives (2/g)^{(s−1)kf} ≤ e^{−4kf log k}. The degenerate s = 2 class also carries the Siegel mass ratio (C/k)^{kf} ≈ Γ(k)^{−f}.
- **Generic non-scalar:** a level saving √((Cg^{−(2r+1)}k^{−r})^{kf}).
- **Non-generic corank 1:** a local saving q^{−(k−2r−5)}. It comes from first-type lattice counting and a second-type Gauss sum on the hermitian quadric. It is paid against a global height sum e^{Cn m⁵ f log b} from Theorem B (archimedean singular orbital integrals bounded by big-cell mass). This closes because k ≥ 8Cn·m⁵·f·log b.
- **"Count of double cosets"** is replaced by **masses of lattice classes** (Σ1/|Aut|), normalised by Siegel–Weil (`swxs_of_siegelWeil`) [SLEAVES].

**Not located.** I looked for a Theorem-S-side inequality "weight × min displacement ≥ log #cosets + 6x^ε", and for an injectivity-radius statement on the Theorem S chain. Greps run over `FlagStabilizerTensors/`, `ClosedLocalOrbits/` and `Formalism/HermitianCurvature/`:
- `DecGap`, `decHS`, `systole`, `displacement`, `NearUnip`: 0 hits.
- `injectiv`: hits in 5 files (`RealObjInhab`, `GGMirabolicInhab`, `LoopTerm`, `TermDef`, `LoopTieOfInhab`). I did not open them; the names suggest linear-algebra injectivity.

The weight's only roles on this chain:
- `WuDecay` (`HaarTransversals/WuDecay.lean:27-34`, read): W_u is reproduced by a compactly supported α, and ∫|W_u|·ν^{N1} < ∞ with N1 = 4n²√(2q). Polynomially weighted integrability gives absolute convergence of the Poincaré series (`FoldOK`, :36-46). It is supplied by `WuDecayOfGap` (`WuDecayAll.lean:25-27`, read), i.e. from the gap.
- The gap hypotheses of Theorem B and of multiplicity one [THMB].

### 2.4 Strength: per pair, not average and not entrywise *(mine)*
Put Q = Σ_u P̂_uP̂_u* and Σd = Σ_u d_u.
- Linear algebra alone gives Σ_{u≠u′}‖K_uu′‖² = tr Q² − Σ_u‖K_uu‖² ≥ (Σd)²/Dall − Σ_u‖K_uu‖².
- With Dall ≤ (1+η1)D* (count), ‖K_uu‖² ≈ d_u (diagonal clause) and Σd ≥ x^{CH}D* (overfill), the **average** of ‖K_uu′‖²/(d_u d_u′/D*) over pairs is ≥ 1 − η1 − x^{−CH} − O(√e0).
- Theorem S says every term is ≤ 1 + b⁻⁶. So the per-pair values are pinned near 1 for almost all pairs (weighted by d_u d_u′). Equivalently, Q is near-scalar in HS: a near-tight frame, with the eigenvalues of Q/c having mean-square deviation ≲ b⁻⁶ + η1 + x^{−CH}.
- This is the content: "max over pairs ≤ (1+b⁻⁶)·average". It is a uniform-equidistribution statement for the pairwise overlaps tr(Π_uΠ_u′).
- It **cannot hold if any block is under-correlated**, for example a block nearly orthogonal to everything, as small-index Poincaré series are in SL₂ (§2.5). Such a deficit must then be paid by an excess elsewhere. So Theorem S plus the count jointly exclude Bessel-decay-range blocks.
- In the Lean such blocks would have T_u small relative to the weight, and they do not occur (T_u ≫ |λ|^{m/2}).

### 2.5 The SL₂(ℤ) model *(mine; scripts above)*
Setting. ⟨P_m, P_n⟩ ∝ Δ(m,n) = δ_{mn} + 2π i^{−k} Σ_c S(m,n;c)/c · J_{k−1}(4π√(mn)/c). The correlations are r = Δ/√(Δ_mm Δ_nn). J_n is computed by the periodic trapezoid rule, checked against J_0(1) and J_5(10) to 10⁻⁹. Validation: the computed Gram of P_1..P_M has rank exactly D = dim S_k (25 at k = 300, 50 at k = 600).

| test (k = 600, D = 50, M = 300, unless stated) | result |
|---|---|
| near-orthogonality range | first m with \|r(m,n)\| > 10⁻³ for some n < m is m = 47 (4πm/k = 0.98); at k = 300 it is m = 23 (0.96). The condition is on √(mn), not on max(m,n): P_1, P_2, P_3 stay orthogonal to every P_n, n ≤ 150, at k = 300 |
| Gram of P_1..P_D | P_1..P_48: max\|r\| = 0.20, min eig 0.79. P_1..P_50: max\|r\| = 0.47, min eig 0.002. **The spanning family is not nearly orthogonal at the edge**, confirming the brief |
| single pairs m ≠ n ∈ [151, 300] | mean D\|r\|² = 0.98, median 0.44, max 15.5; 31% exceed 1. A per-pair bound at d = 1 is false, with χ²-type fluctuations; the top pairs (299, 193), (230, 255) are not arithmetically related |
| blocks of b consecutive indices, cross-pairs | ‖K_uu′‖²/(b²/D): mean 0.98 / 0.99 / 0.97 / 0.97, max 4.39 / 2.57 / 1.87 / 1.39 for b = 3 / 6 / 12 / 24. The excess decays roughly like 1/b |
| blocks, diagonal | ‖K_uu − 1‖²/b = 0.04 / 0.09 / 0.24 / 0.47 ≈ b/D, i.e. ‖K_uu − 1‖² ≈ b²/D: the Lean's `DiagRow` shape with constant ≈ 1 instead of Γ_P |
| Hecke-related blocks (I, pI), p∤I, \|I\| ≈ 12, 24 | p = 2: mean 1.03 / 1.00 (max 2.27 / 1.38); p = 3: mean 0.80 / 0.79. Generic: 0.99–1.00 (max 3.18 / 1.71). No arithmetic excess |
| frame tightness vs overfill (k = 300) | ‖Q − cI‖²/(c²D) = 0.20, 0.12, 0.054, 0.016 at M/D = 3, 6, 12, 24. Under-correlated (isolated) small-index vectors give eigenvalue 1 until M is large enough that 4π√(M) > k |

**Translation.**
- "Index small relative to weight" (Bessel decay) has **no counterpart** that Theorem S uses. The Lean's blocks are in the regime index ≫ weight, where SL₂ correlations are at random level.
- The Lean's diagonal clause is the model's ‖K_uu − 1‖² ≈ d²/D, made small by d_u ≈ D*/Γ² ≪ D*. It is not made small by decay.
- Spanning comes from overfill, as in the model.
- The model's per-pair excess decays like 1/b. *(mine)* For random subspaces the relative standard deviation is ≈ √2/√(d_u d_u′), so a b⁻⁶ uniform bound needs d_u ≫ b¹² up to logarithmic factors. In the Lean, d_u ≈ D*/Γ², with D* = (formal degree ≈ b^{O(n²f)}) × (volume). This is enormous, so no contradiction appears.
- **What remains an expert question** is whether the Lean's deterministic bounds (non-main pairs ≤ e^{−kf log k/3}·dd) can really be uniform over *all* pairs of words. That would mean no arithmetic coincidence between Bessel data puts a non-generic orbit at main-term size. `IdZero` is proved; the degenerate, NG and corank classifications rest on unread suppliers.

### 2.6 Cusps on the Theorem S side
- No pointwise kernel is used. Both sides are L² inner products of two explicit vectors of HH, so continuous spectrum and truncation do not arise [PAIRB §2(b)].
- Absolute summability of the term sum is `AbsConvT`, supplied by `AbsConvC_outright := AbsConvC_holds OOLintSumC_holds` (`ClosedVolumeStatements/FullExistsTiedHolds.lean:32`; definition `FlagStabilizerTensors/PoincareConstantEq.lean:130-135`, read). It is threaded by `absConvTied_holds` (`FlagStabilizerTensors/LinkSFinal.lean:97-99`; `RC:257-262`). The input `FoldOK` comes from `WuDecay`.
- The parabolic/unipotent (degenerate, G = 0) orbits are exactly 0 off the diagonal (`KppTermZero`; supplier `KppOffC_holds`, unread). On the diagonal they are ≤ d_u e^{−kf log k}.
- The phrase "unipotent, thin and deep parts small because of the rank, via Siegel–Weil volumes" belongs to the counting theorem, not to Theorem S.

## 3. The counting theorem

### 3.1 Statement (read, `SWL/LatticeCountingTheorem.lean:10-16`)
For every Cg there is n₀ such that for every `RowsAut` B and every (d, p, q, b) with `CountHyp`, eHom is finite-dimensional and

|D − mainTerm| ≤ exp(−(1/16)·n·f·log n)·mainTerm,

where mainTerm = ∏_v d_v · vol(fund) · Re e(1).

`CountHyp` (`LP:108-115`) consists of:
- DS data at every real place, signature (p, q) everywhere, q² ≤ n, n ≥ n₀;
- log rd ≤ eⁿ, log f ≤ √n;
- 2 ≤ b, log log b ≤ nf log n/16, |λ| ≤ b², g ≤ b^{Cg};
- g₀ > 4n prime and split;
- noncompact gaps ≥ 8·10¹⁴(Cg+4)n¹⁹f⁵log(b·rd) [COUNT §1].

On the live path, n = D.R.r ≈ k and f = D.R.f.

### 3.2 Assembly (read, `UAC:37-49`) and the injectivity radius
DecGap ← compression formula; PtBound ← DecGap; AbsoluteVolume, FlagMeasureBound, NonzeroFlagBound ← VolumeStep; then near, far, rare and deep; then `discreteSeries_counting_of_finite_and_bounds`.

`NearUnip` (statement `ST/ConvolutionSmoothL2.lean:136-143`; proof `near_unipotent`, `CPM:93-140`, read):
- **Statement.** Let ε = c/(n⁸f²) with c ≤ 10⁻⁵, 4n < g₀, and (g₀) radical in O_E. If γ ∈ G(F), φ_e(x⁻¹γx) ≠ 0 and dHS((x⁻¹γx)_v) ≤ ε at every v, then γ is unipotent, finitely and at every v.
- **Proof** (as mathematics):
  1. dHS ≤ ε with nε ≤ 1/4 gives |σ(tr γ^j) − n| ≤ 3n at every embedding, for j ≤ n (`near_arch`).
  2. e is supported on elements unipotent mod g₀, so tr γ^j − n ∈ g₀·O_E (`trace_pow_cong`, using radicality).
  3. An algebraic integer divisible by g₀ > 4n with all conjugates ≤ 3n is 0 (`ringOfIntegers_eq_zero_of_natCast_dvd_of_norm_embedding_le`).
  4. So tr γ^j = n for all j ≤ n, and γ is unipotent by Newton's identities.
- **Comments.**
  - This is a Minkowski–Serre-type neatness lemma. *(mine)* I also checked it independently via Kronecker plus Dimitrov's Schinzel–Zassenhaus bound together with g₀ unramified, which gives E ∩ ℚ(ζ_{g₀}) = ℚ.
  - The **minimal displacement** of a non-unipotent γ in the support is > ε = 10⁻⁶/(n⁸f²) at some place, uniformly in x.
  - It depends only on n and f. The level enters only through g₀ (no torsion, hence no elliptic terms). The discriminant does not enter at all.
  - ε is far smaller than necessary: nε ≲ 1 would do.

### 3.3 The error terms, with the Lean's formulas
- **Far** (`FarBound`, `ST/CuspFrame.lean:27-37`, read): Σ_far|φ_e| ≤ d·e(1)·latFactor(x)·2f·3^f·e^{−hε²/16}, with latFactor = (3√n/τ₁(x)²)^{2n²f} (`SWL/FarTermsLatticeBound.lean:15-16`). This is the brief's inequality: **weight × displacement² ≥ log(lattice count)**.
  *(mine)* hε²/16 ≥ 50(Cg+4)·n³f·log(b·rd). On the moderate region τ₁ ≥ τ* = X^{−11q} with X = nf·rd·g·b and q ≤ √n, log latFactor ≤ 2n²f(log 3√n + 22q log X) ≤ 44n^{5/2}f((Cg+1)log b + log rd + log nf) + O(n²f log n). n³ beats n^{5/2}, so far ≤ e^{−n²f}·mainTerm holds with room. The bound is Gaussian-regime decay (DecGap's min(t², t/√(2q)), with ε ≤ 1/√(2q)). That is why ε² and hence n¹⁹ = n¹⁶·n³ appear.
- **Near** (`SWL/NearNonzeroTerms.lean:12-26`, read):
  - nearAbs = 0 at x where all near γ are 1, i.e. least ≥ 1/2;
  - on τ* ≤ least < 1/2 the integral is ≤ e^{−nf log n/4}·mainTerm.
  - *(mine)* The standard picture: the unipotent count at depth τ, ≈ τ^{−2ρ}, cancels the Siegel-set density τ^{2ρ}, leaving (log 1/τ*)^{rank}·κ(j). The hypothesis log log b ≤ nf log n/16 is exactly what makes (log X)^a·κ(j) ≤ e^{a·nf log n(1/16 − 1/2)}. Body unread.
- **Rare** (`SWL/RareFlags.lean:10-14`): Prob(least < 1/2) ≤ e^{−nf log n/4}.
  - *(mine)* Heuristic: for a random unimodular lattice of real rank 2nf, the expected number of vectors of length < 1/2 is about vol B_{2nf}(1/2) = e^{−nf log(nf)+O(nf)}, so 1/4 has slack.
- **Deep** (`DeepBound`, `SWL/DeepSetBound.lean:15-19`; pointwise `DeepKernelBound`, `SWL/DeepKernelBound.lean:12-31`, read): kern(x,x) ≤ (2·radRh·√f·stepBe)^{16qN}·(6 stepBe)^N·e^f·(17√n/least²)^{2N}·D·∏c_v/μ_f(K_g), with N = n²f and radRh ∝ (2·least)^{1/q}.
  - *(mine)* The dependence on least is least^{16N−4N} = least^{12N}, which **decays** into the cusp. This is cusp-form decay by iterated mean-value/derivative bounds: J = 16qN derivatives, each costing stepBe ≈ √n b² (infinitesimal character), against an N-orbit of radius ∝ least^{1/q}.
  - At least ≤ τ* = X^{−11q} the bound is ≤ X^{−49qN}·e^f·D·∏c_v/μ_f(K_g). Times vol ≤ X^{N} [`AbsoluteVolume`] and the level volume ≲ X^{2N}, this leaves ≤ D·X^{−46qN} ≪ D·e^{−n²f}. I did not read the c_v gauge constants.
- **Combination.**
  - Upper bound: D ≤ mainTerm(1 + 2e^{−nf log n/4} + e^{−n²f}) + D·e^{−n²f}.
  - Lower bound: by kern ≥ φ_e(1) − near − far on the moderate region.
  - Together: relative error ≤ 3e^{−nf log n/4}/(1 − e^{−n²f}) ≤ e^{−nf log n/16} for n ≥ n₀. The precision follows from the leaves *(mine; the Lean's `abs_sub_le_exp_neg_sixteenth_mul` per [COUNT], not re-read)*.

### 3.4 Is the exponent of the natural form?
- The brief's heuristic is a relative error ≈ (elliptic orbital integral)/(formal degree) ≈ ∏ ⟨λ,α⟩⁻¹, i.e. polynomial in the weight. That presupposes elliptic terms, and there are none here: γ is non-unipotent ⇒ displacement > ε at some place ⇒ Gaussian decay of the test function itself.
- The test function is the matrix coefficient, which decays like (cosh t)^{−weight}: exponentially in weight × t². Its orbital integrals are never used.
- The **natural form of the Lean's dominant error is the cusp-volume term e^{−Θ(nf log n)}**. It is the relative measure of the region with a short isotropic flag, from the Siegel mean value via VolumeStep ← Siegel–Weil. This is natural and plausible.
- The literature (Savin; Clozel; de George–Wallach; Shin–Templier; Finis–Lapid–Müller) fixes the group and lets the level grow. None is uniform in rank n. The uniformity here comes from the lattice-volume leaves, which I did not read.

### 3.5 `rowsTiePT'_of` (read)
- `rowsTiePT'_of T hI hq := ⟨(rowsTieP_of T).1, ⟨(rowsTieP_of T).2, hI⟩, hq⟩` (`CT:41-43`). `rowsTieP_of` (`TSO:1103-1115`, read in part) takes `T.autTie` and level-subgroup facts.
- `AutTie` (`DSE:10-23`, read) records:
  - n = D.R.r, f = D.R.f, rd = rdE;
  - ε = epsS, λ = lamS;
  - σ is DS of lowest K-type;
  - g = g₀g₁;
  - **B.D = Dall** and **Dstar = B.I.Dstar(∏fdeg)**.
- It is a field of the selection record `STies` (`STR:245-256`, read), whose `X.B` is the very RowsAut of the Hida setting where the P_u live. Theorem S's D* (`DstC X = Dstar`, `RC:57`) is the same number.
- So the count speaks about *this* HH **by construction**. The count is applied for every tied B (`CountRowsClass`, `BCE:63-71`, read).
- **Open, upstream:** existence of such records. The selection σ is an argument of `at_choice_alt` (`TPS/AtChoice.lean:16-24`, read). If no tied record existed, the conclusion would be vacuous for that family. [NONVAN; JOIN §1c] say the frame forces Dall > 0.

## 4. Children and status table

| leaf | file:line | content | status | literature |
|---|---|---|---|---|
| `offDiagonalK0_of_rows` | LSF:58-112 | Theorem S assembled per family | proved, read | — |
| `t_PairBound` + numerics | GOB:525 [PAIRB] | abstract row bounds ⇒ ‖K0‖² ≤ (1+b⁻⁶)dd | proved, read [PAIRB] | — |
| `Terms`, K0, row classes | PB:15-140 | term system, pair classes | definitions, read | — |
| RowMain / `NormBound` / `EnergyAbs` | PN:20 [PAIRB]; EnergyAbs.lean:58 [COUNTS] | main term ≤ dd by mass identity × Bessel inequality | proved; EnergyAbs proof read [COUNTS]; mass identities (`jacobian_natural_measure_constant`, `local_ratio_product`, `column_identity`) unread | Schur orthogonality / formal degree: standard |
| LoopRowS (RowBig, RowNotScalar) | `ThmSOwn.lean:1015` [SLEAVES]; `RC:105-110` (def, read) | corank ≥ 2 and non-scalar ≤ e^{−kf log k/3}dd | statement only here; glue read [PAIRB]; Ξ(s) and degenerate counts unread | Siegel mass formula (Published leaves import it [THMB §9.7]); GHY |
| RowNG (`rowNGP_of_siegelWeil`) | `RC:112-117` (def, read) | NG ≤ 2^{−(k−2r−5)}e^{C4m⁵f log b}dd | proved via `RowNGJoint`; first type read; second-type Gauss sum leaf `FibU.shares` unread [THMB] | Weil-type hermitian Gauss sums (shape); tested [THMB §7] |
| Theorem B rotated | ThmBFinal.lean:7 [THMB] | singular orbital integrals ≤ big-cell mass | proved; Fourier-decay/germ leaves unread | none found |
| GGBound | GGM:13-140 [PAIRB] | Gelfand–Graev ⪯ (1+3/q)γ(1) | proved, read [PAIRB] | Gelfand–Graev; Gelfand–Kazhdan mirabolic |
| IdZero | `IdCellOffCHoldsOfVol.lean:660` [COUNTS] | identity orbit 0 for u ≠ u′ | proved [COUNTS] | — |
| KppTermZero, KppDiag, DiagC suppliers | `RC:91-100, 126-132` (defs, read) | degenerate part 0 / ≤ d_u e^{−kf log k}; diagonal ≤ Γ_P d_u²/D* | statements only (`KppOffC_holds`, `kernel_diagonal_positive`, `diagonal_positive_final` unread) | — |
| AbsConv / FoldOK / WuDecay / KExpansion | `PoincareConstantEq.lean:117-135`; `WuDecay.lean:27-46`; `LinkSFinal.lean:92-99` (read) | convergence and the unfolding identity | proved by named theorems; bodies (`OOLintSumC_holds`, `KExpansionC_holds`, WuDecayOfGap supplier) unread | Godement-type convergence; standard shape |
| carrierP / uniqGap | [NONVAN] | — | unread | — |
| `countingTheorem_of_volumeStep` | UAC:37-49 | assembly | proved, read | limit multiplicity (Savin, Clozel), in a new rank-uniform regime |
| DecGap ← formulaGap ← germ_jet_zero | [FORMULAGAP; GERMJET] | Gaussian decay of lowest-K-type coefficients | proved, read [nodes] | holomorphic case classical; general compression formula not found in the literature |
| `near_unipotent` | CPM:93-140 | near ⇒ unipotent | **proved, read** | Minkowski/Serre neatness lemma |
| NearModerate | SWL/NearNonzeroTerms.lean:22-26 | near ≤ e^{−nf log n/4}M | statement read; body unread | unipotent-term computation (shape) |
| FarBound, FarModerate | ST/CuspFrame.lean:27-37; SWL/FarTermSum.lean:20-24 | far ≤ e^{−n²f}M | statements read; bodies unread; exponent margin checked *(mine)* | — |
| DeepKernelBound, DeepBound | SWL/DeepKernelBound.lean:12-31; SWL/DeepSetBound.lean:15-19 | cusp-form decay; deep ≤ De^{−n²f} | statements read; bodies unread; margin checked *(mine)* | cusp-form decay (shape) |
| FlagRare, NonzeroFlagBound, FlagMeasureBound, AbsoluteVolume ← VolumeStep ← SW | SWL/RareFlags.lean:10-14 (read); SKI [COUNT] | thin-region measure e^{−nf log n/4} | statements only; SW is an in-tree theorem [THEOREMS] | Siegel mean value; Prasad/GHY volumes |
| CuspFrame / projector | ST/CuspFrame.lean:39-44 (read) | R(φ_e) is a projection onto cusp forms | statement only | Wallach; Schur |
| `rowsTiePT'_of` | CT:41-43 | tie count ↔ HH | **read: glue**; content = `AutTie` record field | — |

## 5. Oddities

1. **Misnomer.** "Near-orthogonality" means "at most random correlation". The off-diagonal blocks are *not* small: summed, they must equal the random value (§2.4).
2. **b⁻⁶ is a level constant.** It comes from Pg = ∏(1 + 3/g_v) with g ≥ (kb)⁸ and from δ ≤ b⁻⁷, not from archimedean decay. MAIN-ARGUMENT §7's "savings from … Gelfand–Graev" is right. The brief's "b⁻⁶ ≈ e^{−6x^ε} from weight × displacement" is not how it arises.
3. **NearUnip's ε = 10⁻⁶/(n⁸f²) is much smaller than the proof needs** (nε ≤ 1/4). This is harmless, but it is the source of n¹⁶ inside the gap hypothesis n¹⁹f⁵.
4. **Theorem S plus the count exclude under-correlated blocks** (§2.4). If any word's block were nearly orthogonal to all others (the SL₂ small-index phenomenon), the per-pair upper bound and the count could not both hold. In the Lean, T_u ≫ weight rules this out. The live parameter ties were not re-traced here.
5. **The deep pointwise bound has 16q·n²f derivative steps.** Each costs √n·b². This is consistent with cusp decay only because least^{12n²f} beats (b²)^{16qn²f}·… when least ≤ X^{−11q}, which my count above confirms.
6. Nothing read is false as literally stated.

## 6. Coverage

Read in this pass:
- PROTOCOL; MAIN-ARGUMENT §0, §5.3, §7; NODE-NONVAN (all), PAIRB (all), COUNTS (all), COUNT (all), SLEAVES (all), THMB (all); TFLOOR, RANK, FORMULAGAP, GERMJET, HIGHERRANK, SWRANGE, ADMB2: first 45 lines each.
- Lean:
  - LSF:1-112; TSO:640-700, 795-815, 1103-1115; PB:15-140;
  - RC:20-140, 257-282; RO:17-57; TD16:807-820;
  - `HaarTransversals/WuDecay.lean:1-60`; `WuDecayAll.lean:15-45`; `PoincareConstantEq.lean:100-145`; `LinkSFinal.lean:90-105`;
  - `DoubleCosetSingleUnfolding.lean:435-447`; `FullExistsTiedHolds.lean:32` (grep line);
  - UAC:1-51; `SWL/LatticeCountingTheorem.lean:1-20`; SWL/{NearNonzeroTerms, FarTermSum, RareFlags, DeepSetBound, DeepKernelBound}.lean (bodies minus imports);
  - ST/CuspFrame.lean:10-46; ST/ConvolutionSmoothL2.lean:125-146; `SWL/FarTermsLatticeBound.lean:15-19`; LP:99-110;
  - CPM:1-20 (imports), 60-140;
  - CT:1-75; BCE:40-75; DSE:8-24; STR:245-256; `PlaceDegreeData.lean:380-390`;
  - `TPS/AtChoice.lean:1-32`.

Greps:
- `DecGap|decHS|injectiv|systole|displacement|NearUnip` over the Theorem S directories (§2.3);
- `theorem rowsTiePT'_of`, `def RowsTieP|AutTie|PLevT'`, `structure STies`, `AbsConvTied`, `AbsConvC_outright`, `def OOLintSumC`, `theorem near_unipotent`, `def MatK_at`, `def TheoremSSelected|SelOK|ddC|hsSq`, `K0` in TermOp/PB.

Not opened:
- bodies of `nearModerate`, `farBound_of_ptBound`, `farTermsModerateRegion_of_flagBound`, `deepPointKernelBound_of_pointwiseBound`, `deepRegion_kernelDiagonal_bound`, the flag/volume bounds, `discreteSeries_counting_of_finite_and_bounds`, `abs_sub_le_exp_neg_sixteenth_mul`;
- `KppOffC_holds`, `kernel_diagonal_positive`, `diagonal_positive_final`, `OOLintSumC_holds`, `KExpansionC_holds`;
- the NormBound mass identities; the RowNG/LoopRowS sub-leaves beyond [PAIRB/COUNTS/THMB]; the selection σ's supplier;
- the five `injectiv` grep hits.
