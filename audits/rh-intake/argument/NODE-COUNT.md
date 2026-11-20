# NODE-COUNT: `CountingTheorem` (exponentially precise limit multiplicity for U(p,q)^f)

Paths are relative to `.../scratchpad/art/lean/src`. Abbreviations:
- `FM/` = `Development/AbelianVarietyTheory/Proofs/FlagMeasures/`
- `ST/` = `Development/AbelianVarietyTheory/Statements/CuspFrameWeights/`
- `SWL/` = `Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/`
- `LP` = `Development/AbelianVarietyTheory/Definitions/SemilocalFrames/LayerProd.lean`
- `GA` = `Formalism/SharpRestriction/CuspSpanNormBounds/GlobAut.lean`
- `SHF` = `Formalism/SharpRestriction/CuspSpanNormBounds/StandingHypothesesHoldFamily.lean`
- `SND` = `Formalism/SharpRestriction/CuspSpanNormBounds/StandingNumericalData.lean`
- `SKI` = `ST/SameKindIsometric.lean`

## 0. Answers to the brief

- **(a) The quotient is non-compact.** The theorem covers every hermitian space. For the family it is
  applied to signature (k−1+m/2, m/2) at every real place, with n = r = k+m−1.
  - The Lean: `AutInst` (`GA:32-72`) allows any nondegenerate hermitian J over a CM extension E/F, with a
    J-self-dual O_E-lattice L. The signature vector is ε_v (`GA:54-59`).
  - `CountHyp` asks only for the same signature (p,q) at every real place (`LP:86`), with q² ≤ n. q = 0 is
    allowed.
  - The family's sign vector `epsS` (`RelevantZeroGramTerms.lean:169-170`) has k−1 entries `true`, then m
    entries alternating true/false. So q = m/2 ≥ 1, and the count uses n = D.R.r (`SHF:556-571`,
    `AdmissibleBoundsFromSource.lean:68-78`).
  - *I infer:* n ≥ 3 and the form is indefinite at every real place. Local hermitian forms of dimension ≥ 3
    are isotropic, so by Landherr's Hasse principle the space is isotropic and G(F)\G(𝔸) is not compact.
  - The proof is written for this case:
    - cusp forms (`IsCuspFn`, `GA:161-163`);
    - a reduction-theory height `least` (smallest Harder–Narasimhan "size" of the lattice at x,
      `LP:52`) with flag types (`LP:56-69`);
    - a separate deep-cusp argument.
  - The definite case q = 0 is handled separately as an exact equality D = D*
    (`definiteUnitaryGroup_count_eq_mainTerm`, `FM/DiscreteSeriesCountingOfFiniteAndBounds.lean:57-60`).
- **(b) The pre-trace formula is not integrated over conjugacy classes.** Nothing like Arthur's truncation is
  used. The proof:
  1. shows R(φ_e) is an orthogonal projection of rank exactly Dcount, onto continuous cusp forms;
  2. writes its kernel pointwise as Σ_i |F_i(x)|² = Σ_γ φ_e(x⁻¹γx);
  3. bounds the diagonal pointwise, region by region.
  The near terms are unipotent, by a Kronecker plus Minkowski argument. The thin part comes from the Siegel
  mean-value theorem via a volume recursion. The deep cusp is bounded by sup-norms of the cusp forms, not by
  counting lattice points.
- **(c) The gap is met, with a large margin. The "equal middle coordinates" worry does not apply.**
  - `GapAtLeast` constrains only pairs of **opposite** sign (noncompact roots):
    ∀ a b, ε a ≠ ε b → h ≤ |λ_a − λ_b| (`Formalism/FormalDegreeBessel/StatementDS.lean:16-17`).
  - The family's parameter (`lamS`, `RelevantZeroGramTerms.lean:165-167`) is λ = (v_1 > … > v_{k−1} ≥ 0,
    −b_1, −b_2, …, −b_m). The v-block is entirely `true`, so it is a compact block and its spacing does not
    matter.
  - The opposite-sign pairs are (v, −b_{even}) and (−b_odd, −b_even). `gapAtLeast_of` (`SHF:354-389`) reduces
    the gap to the steps b_{j+1} − b_j ≥ G with v, b_1 ≥ 0.
  - The steps are the family's `nodes_gap`: h0 ≤ b_{j+1} − b_j ≤ h0+1 with h0 = etaSz/m
    (`Formalism/LocalRingCardinality/DataParams.lean:42, 226-229`).
  - Discharge: `SizeNodes` (`Formalism/SharpRestriction/ElevenLe.lean:92-95`) requires
    x^θ·r¹⁹f⁵L ≤ etaSz/m. The explicit choice sets etaSz/m = ⌈x^{ch}⌉ with ch ≥ 1300 + cD
    (`.../GlobalInterpolation/ExplicitChoiceSizeNodes.lean:11-62`). The lemma also has r ≤ x⁵ and f ≤ x³, so the
    need is ≈ x^{110+θ+ε} against ≈ x^{1300}.
  - The chain to `CountTheoremHypotheses` p9: `node_gaps_large` (`SHF:1307-1320`) → field 21 of
    `StandingHypotheses` (`SND:141`) → `count_parameters_of_hyp` (`SHF:478-484`).
  - The size bound |λ| ≤ b² comes from b_j ≤ b² (`SND:134`) and `lamS_abs_le`.
  - The nodes are spaced x^{1300}, while b_j ∈ [b_1, 2b_1] (`SND:135`) and b = e^{x^ε}. These are compatible.
- **(d)** The theorem is precise and its architecture is recognisable. It is proved in-tree **conditional on
  `SiegelWeilUnitaryConvergent`**, a Prop input (`FM/CountConstantsOfSiegelWeil.lean:11-24`,
  `FM/VolumeStepOfSiegelWeil.lean:12-17`). It is applicable to the family. What is new is the explicit,
  rank-uniform precision and the decay lemma `DecGap`, which rests on a lowest-K-type "compression formula" I do
  not recognise from the literature for non-holomorphic discrete series.

## 1. Statement

`CountingTheorem` (`SWL/LatticeCountingTheorem.lean:10-16`):
```
∀ Cg, ∃ n₀, ∀ (B : RowsAut) d p q b, CountHyp B Cg n₀ d p q b →
  FiniteDimensional ℂ (eHom …) ∧ |B.D − mainTerm B d| ≤ exp(−(1/16)·n·f·log n) · mainTerm B d
```

### Data
`RowsAut` (`GA:227-255`) bundles the following.
- **Group and domain.** G = U(J), a fundamental domain `fund` for G(F) in G(𝔸) = ∏_v U(ε_v) × G(𝔸_f), and Haar
  measure μ_f.
- **Archimedean representation.** Unitary representations σ_v with unit vectors w_v. Their Hilbert tensor product
  is σs (`GA:167-172`).
- **Right regular action.** R on L²(fund) (`GA:125-127`).
- **Level idempotent.** e with operator Re, where Re = ∫ e(g) R(1,g) dg (`GA:137`). The idempotent `IsAdmIdem`
  (`GA:213-216`) is:
  - locally constant, e∗e = e, Hermitian, of positive type;
  - supported in K = Stab(L̂);
  - bi-K(g)-invariant;
  - supported on elements x with (x−1)ⁿ ∈ g₀·End(L̂), i.e. unipotent mod g₀.

### The two quantities
- D = dim_ℂ Re∘Hom_{G∞}(π∞, L²(G(F)\G(𝔸))) (`GA:174-201`).
- mainTerm = (∏_v d_v)·vol(fund)·Re e(1) (`LP:95`, `GA:205-206`).

### `CountHyp B Cg n₀ d p q b` (`LP:108-115`)
- For every v, λ_v is a Harish-Chandra parameter: strictly decreasing, with λ − (n−1)/2 ∈ ℤ (`StatementDS.lean:11-12`).
- σ_v is the discrete series with that parameter, w_v is a unit vector in its lowest K-type, and d_v is its
  formal degree (`IsDSData`, `LP:82-84`).
- The signature is (p,q) at every real place; n ≥ n₀; q² ≤ n.
- log rd ≤ eⁿ and log f ≤ √n, where rd = |disc E|^{1/2f} and f = [F:ℚ] (`GA:218-220`).
- 2 ≤ b and log b ≤ exp(nf log n/16).
- |λ_{v,a}| ≤ b².
- 1 ≤ g ≤ b^{Cg}.
- g₀ is prime, g₀ > 4n, and g₀ splits completely in E (#primes over g₀ = [E:ℚ]).
- GapGe: |λ_{v,a} − λ_{v,b}| ≥ 8·10¹⁴(Cg+4)·n¹⁹·f⁵·log(b·rd) for every noncompact pair (ε a ≠ ε b).

### In words
For a unitary group of a unimodular hermitian O_E-lattice with signature (p,q) at all real places, q² ≤ n, and
a discrete series π∞ whose noncompact-root gaps are ≥ C·n¹⁹f⁵log(b·rd):
the multiplicity of π∞ in L²(G(F)\G(𝔸)), weighted by the e-fixed part of the finite component, equals
d(π∞)·vol·e(1) to within relative error e^{−nf log n/16}. This holds uniformly in n, f, rd, b and the level.

Note: E/F unramified is **not** among the hypotheses of `CountHyp` itself.

## 2. Argument

The assembly is `countingTheorem_of_volumeStep` (`FM/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean:37-49`)
and `countingTheorem_of_finite_of_bounds` (`FM/DiscreteSeriesCountingOfFiniteAndBounds.lean:34-142`).

### (i) Projector and trace
- `AbstractGroupProjectorExists` and `LocalProjectorRealPlace` (`.../PlaceDegreeData.lean:297-353`) state the
  following. For an integrable square-integrable σ with formal degree d and unit vector w, set
  φ = d·⟨w, σ(g)w⟩‾. Then for **every** unitary π, π(φ) is the orthogonal projection onto {io(w) : io ∈ Hom_G(σ,π)}.
- *I infer* this is the right theorem. Schur orthogonality gives φ∗φ = φ. A vector in the range has coefficient
  equal to σ's, so it generates a copy of σ. No spectral decomposition of L² is needed, so the continuous spectrum
  causes no trouble.
- For U(p,q), integrability is supplied for h ≥ 120·n·q^{3/2}.
- In the Lean, `globalProj_holds` gives T = R(φ_e). `kernelB'` (`.../DiscreteSeriesCountingOfFiniteAndBounds.lean:80`)
  gives an orthonormal family F_1..F_D of continuous cusp forms with:
  - kern(x,x) = Σ_γ φ_e(x⁻¹γx) = Σ_i |F_i(x)|²;
  - ∫_fund kern = D.
- `CuspFrame` (`ST/CuspFrame.lean:39-44`) gives cuspidality. This is Wallach's theorem for integrable discrete
  series in substance.

### (ii) Split of the domain at τ* = X^{−11q}, X = n·f·rd·g·b (`LP:102-106`)
- **Moderate part (least ≥ τ*).** kern(x,x) − φ_e(1) = near + far. Here φ_e(1) = d·e(1) is the identity term
  (`PtBound`, `ST/CuspFrame.lean:23`).
- **Deep part (least < τ*).** Two bounds:
  - ∫_deep kern ≤ D·e^{−n²f} (`DeepBound`, `SWL/DeepSetBound.lean:15-19`). This comes from a pointwise bound
    ‖Σ|F_i(x)|²‖ ≤ (…)·D at deep points (`deepPoint_bound_cuspidalIsometricIntertwinerFamily`). That bound is
    cusp-form decay, combined with measure_fund·(…) ≤ e^{−n²f}. *I infer:* this answers the brief's worry. The
    bound is "D × sup of the normalised kernel", not a lattice count, and D is then absorbed on the left.
  - The identity term on the deep part is bounded by d·e(1)·μ(least < 1/2) ≤ e^{−nf log n/4}·mainTerm
    (`FlagRare`, `SWL/RareFlags.lean:10-14`).
- **Totals.**
  - near ≤ e^{−nf log n/4}·mainTerm (`NearModerate`, `SWL/NearNonzeroTerms.lean:26-29`);
  - far ≤ e^{−n²f}·mainTerm (`FarModerate`, `SWL/FarTermSum.lean:24-28`).
  - Elementary algebra then gives the 1/16 (`abs_sub_le_exp_neg_sixteenth_mul`).

### (iii) DecGap (`ST/EigenfunctionFiniteCoefficients.lean:58-62`)
- Statement. Let σ be a discrete series of U(p,q) with HC parameter λ and noncompact gap h ≥ 120·n·min(p,q)^{3/2}.
  For u, v in the lowest K-type:

  |⟨v, σ(g)u⟩| ≤ exp(−(h/8)·min(t², t/√(2q)))·‖u‖‖v‖,

  where t = dHS(g) = ‖½ log eig(g*g)‖₂ is the Cartan distance (`LP:18-19`, `.../PointwiseKernelBound.lean:12`).
  There is a companion bound in the operator-norm distance, decE (`LP:24`).
- There is no constant in front: the bound is tight at g = 1.
- Sanity check (mine): U(1,1), holomorphic discrete series of weight k, so h = k−1. The exact coefficient is
  (cosh s)^{−k}, and the bound is exp(−((k−1)/8)·min(2s², s)). The bound holds in both regimes.
- Proof. `decGap_of_formulaGap` (`FM/LowestKTypeDecayGapOfCompressionFormulaGap.lean`) combines the Cartan
  decomposition with the **compression formula** `FormulaGap` (`ST/EigenfunctionFiniteCoefficients.lean:50-56`):

  ⟨v, σ(exp X)u⟩ = dim τ · ∫_K Φ_λ(k⁻¹ exp X k) ⟨v,σ(k)w⟩⟨σ(k)w,u⟩ dk

  for X ∈ 𝔭, where w is the highest-weight vector of the lowest K-type and Φ_λ is an explicit power function on
  positive-definite matrices (`phiPos`, a Cholesky formula).
- `formulaGap` (`FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean:22-99`) proves it. It shows that the
  difference operator has vanishing jet at 1, using:
  - Schmid's operator (`mul_vminus_eq_zero`, `eab_integral_eq_zero`);
  - lowest-K-type multiplicity one under the gap;
  - analyticity of K-finite coefficients.
- For holomorphic discrete series this is the classical K_ℂ-component formula. For general discrete series I
  know no published analogue, but it is not visibly wrong. The bodies of `germ_jet_zero`, `psiPolar` and
  `phiPos` were not opened.

### (iv) Near terms
- `NearUnip` (`ST/ConvolutionSmoothL2.lean:136-143`) states the following. Take ε = c/(n⁸f²) with c ≤ 10⁻⁵, and
  γ ∈ G(F) with φ_e(x⁻¹γx) ≠ 0 and dHS((x⁻¹γx)_v) ≤ ε at all v. Then γ is unipotent, both archimedeanly and
  finitely.
- *I infer* the mechanism:
  - eigenvalues of γ are algebraic integers of degree ≤ 2fn with all conjugates within 1+O(√(nε)) of the unit
    circle, so Kronecker / Dobrowolski makes them roots of unity;
  - (x−1)ⁿ ≡ 0 mod g₀, with g₀ > 4n split in E, so no nontrivial g₀-power root of unity has degree ≤ n over E;
  - hence all eigenvalues are 1.
- This explains both n⁸f² and the hypothesis "g₀ splits completely". Note that unipotence, not just
  "torsion-free", is what is concluded.
- The bound: nearAbs = 0 when least ≥ 1/2. On the type-j region with τ* ≤ least < 1/2, the integral is
  ≤ mainTerm·2κ(j)·(2fq·11q·log X)^a (`FM/NearTermsModeratePointsOneTypeBoundStatement.lean:11`).
  - The log X factor is ∫dτ/τ from τ* to 1/2. *I infer* the γ-count and the Siegel-domain density cancel.
  - κ(j) ≤ exp(−½(Σj)·n f log n) (`ConstantBound`, `SKI:104-110`).

### (v) Far terms
- `FarBound` (`ST/CuspFrame.lean:27-37`): the sum is ≤ mainTerm·latFactor(x)·2f·3^f·e^{−hε²/16}, given
  hε ≥ 64n² and ε ≤ 1/√(2q).
- With ε = 10⁻⁶/(n⁸f²): hε²/16 = 50(Cg+4)·n³f·log(b·rd). *I infer* this is where n¹⁹ comes from, since
  n¹⁹ = n^{16}·n³ with n^{16} from ε². It beats the lattice-point factor.

### (vi) Thin part
- `VolumeStep` (`SKI:32-43`): for n ≥ 3, the space splits as I ⊥ ⟨x⟩ with x*Jx = ±1, and
  gaugeVol(I)/volU(n)^f = gaugeVol(I')/volU(n−1)^f · massRatioRightSide(E,n).
- It follows from `SiegelWeilUnitaryConvergent` via a one-vector Siegel mean (`FM/VolumeStepOfSiegelWeil.lean:12-17`).
- From it come:
  - `FlagMeasureBound` (`SKI:95-102`): rel. measure of type-j set ≤ κ(j)·∫dens;
  - `NonzeroFlagBound` (`SKI:112-117`): rel. measure of {stepLt(1/2) ≠ 0} ≤ e^{−nf log n/3};
  - `AbsoluteVolume` (`SKI:125-130`).
- Heuristic (mine). This is the hermitian Siegel mean-value theorem. The expected number of nonzero vectors of
  size < 1/2 in a random unimodular lattice of real dimension 2fn is about vol(ball of radius 1/2) ≈
  (πe/(8fn))^{fn}, which is e^{−fn log(fn)+O(fn)}. For a rank-j isotropic sublattice the ratio of volumes
  vol(U(n−2j)×GL_j)/vol(U(n)) ≈ ∏(M!)^{−f} is e^{−2jnf log n}. The claimed ½ and ⅓ are weaker than this, so
  they are plausible.

## 3. Children

| name | file:line | statement | weight |
|---|---|---|---|
| `FormulaGap`/`formulaGap` | `ST/EigenfunctionFiniteCoefficients.lean:50`; `FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean:22` | lowest-K-type coefficient = dim τ·∫_K Φ_λ(k⁻¹Pk)·(…) | core; non-standard for non-holomorphic discrete series |
| `DecGap` | `ST/EigenfunctionFiniteCoefficients.lean:58` | Gaussian-then-linear decay with rate h/8 | core (derived from `FormulaGap`) |
| `AbstractGroupProjectorExists`, `globalProj_holds` | `PlaceDegreeData.lean:297` | R(φ) = projection onto the σ-isotypic image of w | standard (Schur orthogonality, integrable discrete series) |
| `CuspFrame`, `kernelB'` | `ST/CuspFrame.lean:39`; `…FiniteAndBounds.lean:80` | range cuspidal; kern(x,x) = Σ\|F_i\|², ∫ = D | standard (Wallach) |
| `NearUnip` | `ST/ConvolutionSmoothL2.lean:136` | near γ unipotent | standard idea (Kronecker + Minkowski); body unopened |
| `NearModerate`, `ConstantBound` | `SWL/NearNonzeroTerms.lean:26`; `SKI:104` | near terms ≤ e^{−nf log n/4}·M; κ(j) ≤ e^{−½ j n f log n} | core (unopened) |
| `FarModerate`, `FarBound` | `SWL/FarTermSum.lean:24`; `ST/CuspFrame.lean:27` | far terms ≤ e^{−n²f}·M | core (unopened) |
| `DeepBound` + deep point bound | `SWL/DeepSetBound.lean:15` | ∫_deep kern ≤ D·e^{−n²f} | core (unopened) |
| `FlagRare`/`NonzeroFlagBound` | `SWL/RareFlags.lean:10`; `SKI:112` | thin part ≤ e^{−nf log n/4} (resp. /3) | core; Siegel mean-value in shape |
| `VolumeStep` ← `SiegelWeilUnitaryConvergent` | `SKI:32`; `FM/VolumeStepOfSiegelWeil.lean:12` | volume recursion | standard (Siegel / GHY); SW is a Prop input |
| `definiteUnitaryGroup_count_eq_mainTerm` | `…FiniteAndBounds.lean:58` | q = 0: D = D* exactly | glue for the family (q ≥ 1) |
| `node_gaps_large`, `szRow_sizeNodes` | `SHF:1307`; `ExplicitChoiceSizeNodes.lean:11` | family gap ≥ C r¹⁹f⁵L | glue (explicit choice h0 = ⌈x^{ch}⌉) |

## 4. Oddities

1. **Unconditional in name only.** `CountingTheorem` is reached only through `count_constants_of_siegelWeil hSW`.
   `SiegelWeilUnitaryConvergent` (`Formalism/UnipotentAdelicQuotients/SiegelWeilUnitaryConvergent.lean:46`) is a
   `def … : Prop` that is passed in. Its statement was not read.
2. **The compression formula is the one statement I could not place in the literature.** Everything in the decay
   rests on it (§2(iii)). An expert should check it on a non-holomorphic discrete series of U(2,1).
3. `CountHyp` does not demand E/F unramified, yet `ConstantBound` is stated for `IsCMUnram E`. I did not trace how
   `FlagMeasureBound` passes from one to the other.
4. `VolumeStep` asserts that x^⊥ again carries a **self-dual** lattice, which `AutInst` requires (`GA:51-52`).
   This is true when E/F is unramified, but needs the unramified hypothesis (see 3).
5. **The hypotheses are generous.** b may be as large as exp(exp(nf log n/16)) and weights up to b², with a relative
   error independent of b. This is consistent, because the far-term decay is in h ∝ log b.
6. **Proof scripting.** The statement file closes with
   `first | exact @… | exact … | (intros; apply … <;> assumption)`
   (`FM/DiscreteSeriesCountingOfFiniteAndBoundsStatement.lean:18`). This is harmless if it compiles.
7. Nothing read was false as literally stated. The brief's "equal middle coordinates" concern does not arise,
   because the gap is only required on noncompact roots.

## 5. Coverage

Read:
- `SWL/LatticeCountingTheorem.lean` (all); `LP` (all); `GA:1-260`; `PlaceDegreeData.lean:297-400`.
- `FM/UnitaryAutomorphicCountingOfCompactDualVolumeRat.lean`; `FM/DiscreteSeriesCountingOfFiniteAndBounds{,Statement}.lean`.
- `ST/EigenfunctionFiniteCoefficients.lean`; `ST/CuspFrame.lean:1-46`; `SKI:1-131`; `ST/ConvolutionSmoothL2.lean:136-145`.
- `FM/LowestKTypeDecayGapOfCompressionFormulaGap.lean`; `FM/LowestKTypeCompressionFormulaOfStrictLowestKType.lean`.
- `SWL/PointwiseKernelBound.lean:12`; `SWL/NearNonzeroTerms.lean:10-40`; `SWL/FarTermSum.lean:10-40`;
  `SWL/RareFlags.lean:10-18`; `SWL/DeepSetBound.lean:15-25`.
- `FM/CountConstantsOfSiegelWeil.lean`; `FM/VolumeStepOfSiegelWeil.lean`.
- Statement lines of `FM/NearTermsModerate*`, `FM/DeepPoint*`, `FM/MeasureFundamentalDomain*`
  (grep for `CountHyp`).
- `ReciprocityTheory/.../IsInfUnitary.lean:1-130` (a different `GapAtLeast`, same definition);
  `Formalism/FormalDegreeBessel/StatementDS.lean:1-60`.
- `RelevantZeroGramTerms.lean:140-190`; `SHF:300-530, 1307-1320, 1380-1470, 1595-1640`; `SND` (all).
- `AdmissibleBoundsFromSource.lean:1-140`; `DataParams.lean:30-60, 215-240`; `DataParams₂.lean:120-166`;
  `ElevenLe.lean:80-110`.
- `.../ExplicitConstantsParameterConditionsLarge.lean:60-160`; `.../ExplicitChoiceSizeNodes.lean:1-62`.

Not opened:
- Bodies of `germ_jet_zero`, `psiPolar`, `phiPos`, `kernelB'`, `globalProj_holds`, `near_unipotent`,
  `nearModerate`, `farBound_of_ptBound`, `deepRegion_kernelDiagonal_bound`.
- Bodies of the flag and volume bounds (`isotropicFlagProbabilityBound_of_volumeRatio`,
  `nonzeroFlagProbabilityBound_of_volumeRatioInduction`, `flag_explicit_constant_le_exp_neg_half`).
- The `SiegelWeilUnitaryConvergent` statement, and `AutTie` (taken from NODE-SLEAVES).
