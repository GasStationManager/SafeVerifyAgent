# NODE-FORMULAGAP — the lowest-K-type "compression formula" and `DecGap`

Source root: `…/scratchpad/art/lean/src`. Abbreviations: `EFC` = `Development/AbelianVarietyTheory/Statements/CuspFrameWeights/EigenfunctionFiniteCoefficients.lean`;
`FM/` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`; `PPU` = `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/PosPartUnitaryMul.lean`;
`DSK` = `Development/AbelianVarietyTheory/Statements/CuspFrameWeights/DiscreteSpectrumKFiniteDecomposition.lean`.

## 0. Verdict

- **The formula is true in every case I could test by hand.**
  - U(1,1) holomorphic: it gives exactly (cosh t)^{−m}.
  - U(2,1) holomorphic: it gives exactly the classical K_ℂ-component formula (cosh t)^{−(λ₁−λ₃+1)}.
  - U(2,1) non-holomorphic ("middle") discrete series: it gives F(0) = 1 and F ≤ 1. Its second derivative at 0 agrees exactly with the value forced by Schmid's vanishing. Its exponential rate is compatible with the Trombi–Varadarajan integrability threshold.
- **The proof strategy is correct and recognisable.** Both sides are bi-τ-equivariant, real-analytic solutions of Schmid's first-order system and agree at 1. Uniqueness comes from jets, then analyticity. I checked by hand both inputs of the step "the candidate solves Schmid's system".
- **The one deep, unread piece** is the jet-uniqueness lemma `germ_jet_zero` (FM/HighestWeightGapBound.lean:391, 486 lines, body not opened).
- **`DecGap` follows from the formula** by an elementary argument, which I read and checked.
- **Integrability:** the large-gap hypothesis implies the Trombi–Varadarajan/Hecht–Schmid condition by a wide margin. In the Lean, integrability is in fact derived from `DecGap` itself.
- **Literature:** the formula is **not** the Knapp–Wallach Szegő kernel (that uses a real parabolic of G). It is a Borel-of-G_ℂ / Flensted-Jensen-type closed formula. I do not know it as a published theorem.

## 1. Statement

### Setting (Lean says)
- **Group.** G = U(J_ε) ⊂ GL_n(ℂ) with J_ε = diag(±1); ε : Fin n → Bool marks the + coordinates.
- **K.** K = G ∩ U(n) = U(p) × U(q), embedded **interleaved** in the coordinates.
- **𝔭.** `inP` gives the hermitian X with X_ab ≠ 0 only when ε a ≠ ε b.
- **Harish-Chandra parameter.** `IsHCParam`: λ is strictly decreasing and λ − (n−1)/2 ∈ ℤ. The positive system is always the standard one, e_a − e_b for a < b. The chamber, i.e. which discrete series, is therefore encoded by ε: (ε, decreasing λ) ↔ discrete series of U(p,q).
- **Lowest K-type.** `lowK` = λ + ρ_n − ρ_c (UpqRep.lean:231), where ρ_n and ρ_c are computed from ε (StatementA.lean:34-40). This is the Blattner parameter.
- **`IsDS`** (`RelevantZeroGramTerms.lean:72-76`): σ is irreducible, unitary and square-integrable, has the K-type Λ, and Λ minimises the Vogan norm ‖μ + 2ρ_c‖² among its K-types.
  - The infinitesimal character is not part of `IsDS`. Vogan's/Schmid's theorem makes this characterisation unambiguous.

### Live path
- λ = `lamS` = (v_1 > … > v_{k−1} ≥ 0, −b_1, …, −b_m) and ε = `epsS` = (T^{k−1}, T, F, T, F, …, T, F), with m even (`RelevantZeroGramTerms.lean:165-170`).
- The signature is (k−1+m/2, m/2).
- Holomorphic means ε is T…TF…F, or the reverse, in coordinate order. So the live discrete series is **non-holomorphic** as soon as m ≥ 4. It is holomorphic only when m = 2.

### Φ_λ (Lean, `PPU:17-26`)
- μ = λ + ρ_std with ρ_std(a) = (n−1)/2 − a (`StatementDS.lean:23`).
- s_i = μ_i − μ_{i+1} = λ_i − λ_{i+1} + 1 for i < n, and s_n = λ_n − (n−1)/2.
- Φ_λ(z) = ∏_i Δ_i(z)^{−s_i}, where Δ_i is the i-th leading principal minor.
- Equivalently (`PhiPos`, `DSK:68-71`): if Q = b b^* with b lower triangular, then Φ_λ(Q) = ∏|b_ll|^{−2μ_l}.
- In representation-theoretic terms: Φ_λ is the left-N̄_ℂ-, right-N_ℂ-invariant power function of weight −μ on GL_n(ℂ). That is, Φ_λ = 1/⟨e_μ, F_μ(z) e_μ⟩ for the finite-dimensional representation F_μ of highest weight λ+ρ.
- Φ_λ depends on λ only, not on ε.

### `FormulaGap` (`EFC:50-56`, quoted)
```
⟪v, σ (exp X) u⟫ = (finrank (lowKSub ε lam σ)) *
   ∫ k' : KG ε, Phi lam ((toMK k')⁻¹ * exp X * toMK k') * (⟪v, σ k' w⟫ * ⟪σ k' w, u⟫) ∂muK
```
- Quantifiers: X ∈ 𝔭; u, v in the lowest K-type τ; w a unit highest-weight vector of τ (`IsHighestUnit`).
- Hypotheses: `GapAtLeast ε λ h` (|λ_a − λ_b| ≥ h whenever ε a ≠ ε b) and h ≥ 120·n·q^{3/2}, with q = `rkR` = min(p,q).
- In words: the τ-spherical function at P = e^X is the τ-compression dim τ·∫_K Φ_λ(k⁻¹Pk) τ(k)P_w τ(k)⁻¹ dk of a holomorphic power function on GL_n(ℂ), restricted to G.
- For general g the Lean uses polar decomposition, Ψ(g) = τ(gP⁻¹)·ps(P) (`PPU:45-59`).

### `DecGap` (`EFC:58-62`)
Under the same hypotheses, for all g ∈ G and u, v in τ:
- |⟨v,σ(g)u⟩| ≤ exp(−(h/8)·min(t², t/√(2q)))·‖u‖‖v‖, where t = dHS(g) = ‖½ log eig(g*g)‖₂ (`LayerProd.lean:18`, `PPU:104`).
- The same holds with the operator-norm distance and decE (`LayerProd.lean:24`).

### How `DecGap` follows (read: `FM/LowestKTypeDecayGapOfCompressionFormulaGap.lean:11-32`, `FM/ProdLeadMinorDecay.lean:94-177`)
1. Polar decomposition and unitarity reduce to g = e^X.
2. Cauchy–Schwarz plus Schur orthogonality (dim τ·∫|⟨v,τ(k)w⟩|² = ‖v‖²) give |coef| ≤ sup_k Φ_λ(k⁻¹e^Xk)·‖u‖‖v‖.
3. `prod_leadMinor_decay` bounds the supremum. Put Y = k⁻¹Xk ∈ 𝔭.
   - Each log Δ_l(e^Y) ≥ ¼·min(1, 1/R)·Σ_{a ≥ l > b}|Y_ab|². This is the convexity of log-sum-exp, applied to a centred "variance" whose range is bounded by R = √(2q)·‖Y‖.
   - Each entry Y_ab with ε a ≠ ε b crosses the cuts b ≤ i < a. Along those cuts Σ s_i ≥ λ_b − λ_a + (#cuts) ≥ h.
   - Summing gives Σ s_i log Δ_i ≥ (h/8)·min(hs, √hs/√(2q)).
   - Only the s_i ≥ 0 are used, so small compact-pair gaps do no harm. Δ_n = det = 1.
- This is elementary and, as I read it, correct. The bound has **no constant** because Φ_λ(1) = 1 and Φ_λ ≤ 1 on K-conjugates of e^𝔭. Every principal minor of a positive Q ∈ U(p,q) is ≥ 1: Jacobi plus Q⁻¹ = JQJ give det Q_S = det Q_{S^c}, and Fischer's inequality then gives det Q_S ≥ 1.

## 2. Argument for `formulaGap` (`FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean:22-99`, read)

The proof sets F(g) = (σ(g) restricted and projected to τ) − Ψ(g) (`diffOp`) and shows F ≡ 0.

1. **Candidate side.**
   - `psiPolar` (`DSK:105`): Ψ is bi-τ-equivariant and Ψ(1) = id.
   - `PsEquiv`: ps is K_ℂ-equivariant. Its proof goes through a K_ℂ Iwasawa change of variables (`IwasawaInt`).
   - `psiAnalytic`: Ψ is real-analytic.
   - `eab_integral_eq_zero` (`FM/HighestWeightEventuallyZero.lean:223-264`, read): **near 1 the candidate satisfies Schmid's system.** The system is Σ_ab E_ab F(G_ab) = 0 for every G in `Vminus`, the isotypic part of 𝔭⊗τ of highest weights Λ − β with β positive noncompact (`StatementU.lean:99-101`). The proof has two inputs:
     - (i) `exists_deriv_Phi_conj`: the right log-derivative of z ↦ Φ_λ(z̄) along k⁻¹Xk involves only the upper-triangular and diagonal entries. For X ∈ 𝔲(p,q), X̄ = −J Xᵀ J, which turns right N_ℂ-invariance into the vanishing of the lower components.
     - (ii) `vminus_K`: ⟨(σ⊗Ad)(k)(w ⊗ E_cd), G⟩ = 0 for c < d.
     - *Check of (ii) (mine):* w ⊗ E_cd has weight Λ + (positive root). A K-type of highest weight Λ − β would contain that weight only if −(β + γ) were a non-negative sum of compact positive roots, which is impossible. K-equivariance of the isotypic projection then gives the claim. Both inputs are correct.
2. **σ side.** `mul_vminus_eq_zero` (`FM/HighestWeightDerivativeSumZero.lean:80`): σ's lowest K-type satisfies the same system. This is Schmid's theorem, obtained here from Vogan-norm minimality of Λ in `IsDS`.
3. **Uniqueness.** `germ_jet_zero` (`HighestWeightGapBound.lean:391`). Its hypotheses: F is bi-equivariant with values in τ, smooth, and satisfies the system near 1; F(1) = 0; the noncompact gap exceeds 2n. Its conclusion: every iterated derivative Eword(w)F(1) vanishes.
   - *I infer:* this is the statement that τ occurs once in U(𝔤)⊗_{U(𝔨)}τ / (Schmid relations), i.e. the Schmid / Enright–Varadarajan–Wallach module has τ-multiplicity one when λ is far from the walls.
   - It is nontrivial at order 2, because Λ + (e₁−e₂) + (e₂−e₃) − (e₁−e₃) = Λ already in U(2,1).
4. **Analyticity.** `lowK_analytic` (Harish-Chandra: K-finite vectors are analytic) plus `vanish_of_zero_jet` give F(e^X) = 0.

The proof uses only gap > 2n (`exists_gap`); the stated 120·n·q^{3/2} is stronger than needed.

## 3. Hand checks

### (a) U(1,1), ε = (T,F), P = a_t
- k⁻¹a_tk has Δ₁ = cosh t and det = 1, so the formula gives (cosh t)^{−(λ₁−λ₂+1)} = (cosh t)^{−m}, since the weight is m = λ₁−λ₂+1. This is exact.
- In the bound, dHS(a_t) = √2·t, so the bound reads exp(−(h/8)·min(2t², t)) with h = m−1.
- It holds: log cosh t ≥ t²/4 for t ≤ ½, and log cosh t ≥ t/8 for t ≥ ½.

### (b) U(2,1) holomorphic, ε = (T,T,F), a_t in coordinates (1,3)
- With x = |k₁₁|² (uniform on [0,1]): Δ₁ = 1 + x(c−1) and Δ₂ = c, where c = cosh t.
- Λ = (λ₁, λ₂+1, λ₃−1) and N = dim τ − 1 = λ₁−λ₂−1 = s₁−2.
- F = c^{−s₂}·(N+1)∫x^N(1+x(c−1))^{−(N+2)}dx. The integral is exact: the integrand is d/dx[x^{N+1}(1+xC)^{−N−1}].
- Result: F = (cosh t)^{−(λ₁−λ₃+1)}, which equals ⟨w, τ(κ(a_t))w⟩ with κ(a_t) = diag(c⁻¹, 1, c). Exact agreement with the classical formula.

### (c) U(2,1) middle discrete series, ε = (T,F,T)
- Here ρ_n = ρ_c, so Λ = λ. τ = (λ₁, λ₃) on U(2) × λ₂, with N = λ₁−λ₃.
- Write p = λ₁−λ₂ and q = λ₂−λ₃ (not the signature), and C = c−1.
- The formula predicts F(t) = (N+1)∫₀¹ x^N (1+xC)^{−(p+1)} (1+(1−x)C)^{−(q+1)} dx, an Appell-type integral.
- F(0) = 1 and F ≤ 1.
- **Second order.** The formula gives F''(0) = −(pN + 2N + 2)/(N+2).
  - Independent computation: Schmid vanishing puts σ(E₂₁)w and σ(E₂₃)w in τ_{Λ+e₂−e₃}, and σ(E₁₂)w and σ(E₃₂)w in τ_{Λ+e₁−e₂}. Clebsch–Gordan gives ratios 1/(N+1). The relations σ(E₁₂)^* = −σ(E₂₁) and [E₁₂, E₂₁] acting by λ₁−λ₂ (similarly for E₂₃) then give ‖σ(Y)w‖² = [p(N²+2N+2) + 2q(N+1)]/(N(N+2)).
  - This equals the prediction identically, using p + q = N.
- **Large t.** The rate is e^{−(p+2)t} for w and e^{−(q+2)t} for the lowest-weight vector. The leading exponent is therefore min(p,q) + ρ(H), with ρ(H) = 2.
  - So L¹ holds iff min(p,q) > 2. This is exactly the Trombi–Varadarajan condition |⟨λ,β^∨⟩| > ½Σ|⟨α,β^∨⟩| = 2 for β = e₁−e₂, e₂−e₃. Consistent.
- **Not done:** an exact check of the full function. That would need SU(2,1) hypergeometric τ-spherical functions or the radial ODE.

## 4. Literature (I infer)

- **Holomorphic case:** the formula reduces to the classical τ(κ(g)) K_ℂ-component formula (checked in 3(b)).
- **Knapp–Wallach (1976) Szegő kernels:** these are τ-compressions over K/M of e^{(ν−ρ)H(g)} for a **real** minimal parabolic of G, paired with the Langlands/Schmid embedding into principal series. The Lean integrates over all of K the restriction to G of a power function for the **complex** Borel of GL_n(ℂ). There is no real parabolic and no ν.
  - So the Lean's formula is neither that theorem nor an immediate consequence of it. It is an exact closed formula for the τ-spherical function, which is stronger in explicitness.
- **Closest analogues:**
  - Flensted-Jensen's discrete-series functions: averages of the reciprocal of a highest-weight coefficient of a finite-dimensional representation of the complexification. U(p)×U(q) = K ∩ U(p,q) is the relevant K∩H for GL_n(ℂ)/U(p,q).
  - The Schmid–Wong open-orbit (G/T ⊂ G_ℂ/B_ℂ) picture.
  - I could not place the exact statement.
- **Uniqueness:** the input matches Wallach's / Enright–Varadarajan's algebraic construction and Yamashita's work on Schmid's system.

## 5. Children

| name | file:line | statement | weight |
|---|---|---|---|
| `germ_jet_zero` | FM/HighestWeightGapBound.lean:391 | bi-τ-equivariant solution of Schmid's system with F(1)=0 has zero jet (gap > 2n) | **core**; recognisable (τ-multiplicity one of the Schmid module); body unread |
| `eab_integral_eq_zero` | FM/HighestWeightEventuallyZero.lean:223 | the candidate satisfies Schmid's system near 1 | core; top level read; both inputs checked by hand |
| `exists_deriv_Phi_conj`, `vminus_K` | FM/ExistsDerivPhiConj.lean:81; (VminusK) | log-derivative of Φ̄ is upper-triangular; Vminus ⊥ w⊗𝔫-type | core but elementary; statements read |
| `mul_vminus_eq_zero` | FM/HighestWeightDerivativeSumZero.lean:80 | Schmid: lowest K-type killed by D | standard (Schmid 1975/76) |
| `psiPolar`, `PsEquiv`, `PsBasic`, `psiAnalytic` | DSK:105, 91, 81, 116 | equivariance, K_ℂ-equivariance, holomorphy of ps, analyticity of Ψ | glue/standard; bodies not read |
| `lowK_analytic` | FM/LowestKTypeAnalytic.lean:278 | K-finite vectors analytic along lines | standard (Harish-Chandra) |
| `phiPos` | FM/PhiPositiveDefiniteCholeskyFormula.lean:95 | Φ on positive matrices via Cholesky | glue |
| `prod_leadMinor_decay` | FM/ProdLeadMinorDecay.lean:150 | sup_k Φ ≤ decHS | core for DecGap; read; correct |
| `isKTypeOf_lowKSub`, `exists_gap` | FM/LowestKTypeMultiplicityOneLargeGaps.lean:129; FM/EventuallyUJ.lean:86 | glue | glue |

## 6. Oddities

1. `FormulaGap` assumes h ≥ 120·n·q^{3/2}, but the proof uses only gap > 2n.
2. `IsDS` carries no infinitesimal character. This is harmless: the minimal K-type determines the discrete series, and `PsiEigen`/`PhiEigen` (DSK) supply the eigen-property on the candidate side.
3. The formula is evaluated with w a highest-weight vector. For the middle discrete series the coefficient ⟨w,σ(a_t)w⟩ decays faster than the leading exponent of the representation (rate p+2 against min(p,q)+2). The bound in `DecGap` is a sup over k, so this does not matter.
4. **Integrability (d).** The Trombi–Varadarajan threshold for U(n) is |⟨λ,β^∨⟩| > n−1, far below h ≥ 120n.
   - The Lean does not invoke TV. `dsData_gap_integrable` (`Proofs/TwistedOperators/DiscreteSeriesTestDataLargeGapsIntegrable.lean:103-157`, statement and lines 144-157 read) gets integrability from `decGap_of_formulaGap` plus `HBig 40` with h = 100·r⁴.
   - So integrability is stated, and proved from the decay.
5. Nothing read is false as literally stated.

## 7. Coverage

**Read:**
- EFC (all).
- PPU:1-120.
- LayerProd.lean:1-30.
- FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean (all).
- FM/LowestKTypeDecayGapOfCompressionFormulaGap.lean (all).
- FM/ProdLeadMinorDecay.lean:90-179.
- FM/HighestWeightEventuallyZero.lean:1-60, 205-266.
- DSK:60-125.
- RelevantZeroGramTerms.lean:60-100, 150-175.
- StatementA.lean:25-40; StatementU.lean:95-115; StatementDS.lean:23.
- The Phi/Psi statement stubs.
- Theorem statement lines of `germ_jet_zero`, `mul_vminus_eq_zero`, `lowK_analytic`, `kType_iff`, `exists_deriv_Phi_conj`, `isKTypeOf_lowKSub`, `vanish_of_zero_jet`.
- DiscreteSeriesTestDataLargeGapsIntegrable.lean:103-157.

**Not opened:**
- Bodies of `germ_jet_zero` (HighestWeightGapBound.lean), `mul_vminus_eq_zero`, `vminus_K`, `exists_deriv_Phi_conj`, `psiAnalytic`, `PsEquiv`/`IwasawaInt`, `tauExists`, `lowK_analytic`, `DecGapOfFormula.dec_exp`.
