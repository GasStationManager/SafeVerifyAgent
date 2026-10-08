# READ-E: paper §4 (polynomial multiplication: C(a,b), P(a,b), Lemma 4.1, Lemma 4.2)

Reader E. Paper text lines 242–376. All paths below are relative to
`/home/user/openai-math/repo/lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/`
unless they start with `Tensor/Complex…` or `Polynomial/Complex…`, which are under
`…/MatrixMultiplication/`.

## 1. Files

Read whole (with `cat -n` / `sed -n`), leaves first:

| file | lines |
|---|---|
| Convolution/Basic.lean | 161 |
| Convolution/Rank.lean | 71 |
| Convolution/RankLowerBound.lean | 51 |
| Convolution/Symmetry.lean | 161 |
| Determinant/Kernel.lean | 286 |
| Determinant/Basis.lean | 111 |
| Determinant/Filtration.lean | 343 |
| Determinant/Character.lean | 181 |
| Determinant/Bounds.lean | 181 |
| Sector/Weights.lean | 266 |
| Sector/Degeneration.lean | 242 |
| Sector/Branches.lean | 290 |
| Sector/Character.lean | 142 |
| Polynomial/Laws.lean | 65 |
| Polynomial/Interpolation.lean | 204 |
| Polynomial/ProductBounds.lean | 103 |
| Polynomial/Inequalities.lean | 126 |
| Growth/Profile.lean | 139 |
| Growth/NormalizedProfile.lean | 81 (extra: defines the profile lemmas I consume) |
| Character/Permutation.lean | 116 |
| Character/Dot.lean | 175 |
| Character/Symmetrization.lean | 120 (extra: `sixfoldProduct`, `symmetrizedProfile`) |
| Character/Basic.lean | 158 (extra: the `Character` structure) |
| Separation/BranchTagging.lean | 82 (extra: `value_sharedFirstTensor_eq_sum`) |

Read in part (interfaces only): Tensor/TagInequality.lean lines 100–222 (`integral_type_comparison`,
`sharedFirst_tag`); Entropy/Tag.lean (theorem list + `tag_of_integral_type_comparison` 201–213);
Tensor/SupportExtension.lean 1–83 (`tensor_eq_extendByZero_pullback`, `value_eq_pullback_of_support`);
Character/Degeneration.lean (theorem list + `value_polynomialRestrictionDegeneration_le` 139–158);
Entropy/Optimization.lean 23–57 (`binary_entropy_log_partition`); Tensor/ComplexTensor.lean 14–60,
195–250 (`Tensor`, `RankAtMost`, `restrict`, `product`, `directSum`, `pullback`, `DegeneratesTo`);
Tensor/ComplexDotPairing.lean 10–25; Tensor/ComplexTensorSymmetrization.lean 10–20 (`cyclic`);
Polynomial/ComplexPolynomialDegenerationComposition.lean 94–138 (`PolynomialRestrictionDegeneration`,
`basePolynomial`); Entropy/ComplexFiniteEntropy.lean 46–49 (`FiniteLaw`).

## 2. Argument reconstruction (Lean chain ↦ paper)

**Objects.**
1. `convolution a b` (Convolution/Basic.lean:24) — `Tensor ℂ (Fin a) (Fin b) (Fin (a+b-1))`,
   entry 1 iff `i + j = k`, else 0. This is (4.1) exactly. `convolution_nonzero` (:69) needs
   `0 < a`, `0 < b`; `convolution_nonzero_iff` (:79) shows it is zero otherwise. For a=0 the output
   type is `Fin (b-1)` (natural subtraction) but the tensor is empty/zero; no consumer uses a=0 or b=0.
2. `Character` (Character/Basic.lean:35): real valued, nonneg, `value 0 = 0`, `value unit = 1`,
   additive on `directSum`, multiplicative on `product`, monotone under arbitrary `restrict`.
   `pX := cyclicCharacter.cyclicCharacter.pZ` (Character/Dot.lean:114), i.e. log₂ of the value on
   `cyclic (cyclic (dotPairing (Fin 2)))` = B_X(2) (singleton first leg). `value_cyclic_cyclic_dotPairing`
   (:142) gives value(B_X(m)) = m^pX. Matches the paper's p_X.
3. `sixfoldProduct T` (Character/Symmetrization.lean:30) = product of χ on T in all six leg orders;
   `symmetrizedProfile t T := sixfoldProduct T ^ (1/(6t))` (:94); `meanExponent := (pX+pY+pZ)/3`
   (Convolution/Symmetry.lean:76); `convolutionProfile a b := symmetrizedProfile meanExponent (convolution a b)`
   (:109). This is (4.4) with t the paper's t. It is a real `rpow`; it is *defined* for every t (rpow
   is total), and `0 < t` is used only where the exponent arithmetic needs it.
4. `permutedCharacter i` (Character/Permutation.lean:59): χ, χ∘cyc, χ∘cyc², χ∘swap23, … — each a
   bona fide `Character` (cyclic/swap23 versions re-prove all axioms, Dot.lean:29, Permutation.lean:24).
   `prod_permutedCharacter_value` (:65) = `sixfoldProduct`; `sum_permutedCharacter_pX` (:107) is (4.3):
   Σ_π p_X^{(π)} = 2(pX+pY+pZ) = 6t.

**(4.2)/(4.5).**
5. `convolution_rankAtMost` (Convolution/Rank.lean:50): RankAtMost (C(a,b)) (a+b−1), by
   `convolution_eq_sum_rankOne` (:37) — explicit: nodes v_r = r ∈ ℂ (r < a+b−1, injective), factors
   (v_r^i), (v_r^j), (coeff_k of the Lagrange basis polynomial ℓ_r), proved from Mathlib's
   `Lagrange.eq_interpolate` applied to X^{i+j} (degree < a+b−1). Evaluation/interpolation, as in paper.
6. `convolutionProfile_le` (Symmetry.lean:127, needs `0 < meanExponent`): P(a,b) ≤ (a+b−1 : ℕ)^{1/t},
   via `symmetrizedProfile_le_rank` (NormalizedProfile.lean:53): each of six values ≤ r, so ≤ (r^6)^{1/(6t)}.
   The lower bound (`convolution_rank_lower`, `exactRank_convolution`, RankLowerBound.lean:106/113,
   identity-minor in the output flattening) is proved but OFF-ROUTE: grep for its names over
   `…/MatrixMultiplication/` finds no consumer; the module is only imported by `Main.lean`.
7. `convolutionProfile_comm` (Symmetry.lean:113): from `sixfoldProduct_convolution_comm`
   (Symmetrization.lean:81): `pullback refl refl (finCongr) (C(b,a)) = fun j i k => C(a,b) i j k`, and
   `sixfoldProduct_swap12` (:45, `ring` on the six factors) — the six factors are permuted, exactly the
   paper's remark. Holds for all a, b, no hypothesis.
8. `convolutionProfile_one_left` (Symmetry.lean:132, needs `0<t`, `0<b`): C(1,b) reindexes to
   `cyclic (cyclic (dotPairing (Fin b)))` = B_X(b) (`convolution_one_left_dotPairing`, Basic.lean:130);
   sixfold product is invariant under cyclic leg rotation, so equals sixfold(dotPairing) =
   (b^{pZ}·b^{pY}·b^{pX})² = b^{6t} (`sixfoldProduct_dotPairing_eq_rpow`, :90), then ^(1/(6t)) = b.
9. `convolutionProfile_pos` (:122) for a,b ≥ 1 (each value ≥ 1 on a nonzero tensor).

**Lemma 4.1 (discrete concavity).** a = d+1, b = e+1, e ≥ 1.
10. Affine chart u = 1 (Determinant/Kernel.lean): a form A(u,v)s + B(u,v)w ↦ (A(1,X), B(1,X)).
    `diagonal (A,B) = A + X·B` is (s,w)↦(u,v); `determinant p = (−X p, p)` is multiplication by
    D = uw − vs. Quotient lifts `quotientMonomial j = (X^j, 0)` = u^{e−j}v^j s (j ≤ e), `quotientTop e
    = (0, X^e)` = v^e w; kernel `kernelMonomial j = determinant (X^j)` = D u^{e−1−j}v^j (j < e).
    These are exactly the paper's bases. `adaptedVectors_linearIndependent` (:261) and the dimension
    count (Basis.lean:81, 89) make them a basis of the (e,1)-forms — this replaces the exactness
    argument for (4.7). (4.7) itself is proved separately in Determinant/Bounds.lean
    (`kernelEquiv`, `finrank_kernel`, `diagonalToDegreeLT_surjective`) but Bounds is OFF-ROUTE (only
    imported by Main.lean; grep for `DeterminantBounds.`, `finrank_kernel`, `diagonalToDegreeLT` finds
    no consumer).
11. Slice compatibility, for EVERY first-input monomial X^i, i ≤ d, hence for every f by linearity:
    `multiply_quotientVector_ordinary` (Kernel.lean:217), `multiply_quotientVector_top_cross` (:226:
    X^i·v^e w = quotient(e+1+i) + kernel(e+i) for i < d — the ∗ entry), `…_top_last` (:236, i = d: no
    cross term), `multiply_kernelVector` (:243: kernel ↦ kernel, so the upper-right block is ZERO).
12. `adaptedTensor d e` (Filtration.lean:32) is the explicit coefficient tensor in those bases:
    quotient→quotient `i+j=k` (= C(a,b+1)); kernel→kernel `i+j=k` (= C(a,b−1)); quotient→kernel only at
    j = e+1, i < d, k = e+i; kernel→quotient **defined 0**. `adaptedTensor_reconstruct` (:60) proves it
    reproduces multiplication on every basis input, `adaptedTensor_unique` (:95) that it is the unique
    such tensor (linear independence), and `boundedMultiply_adapted_coordinates` (:291) that the actual
    representation coefficients equal it. So the zero upper-right block is PROVED, not assumed.
13. `sourceTensor d e` (:223) = coefficients of multiplication V_{a−1} × (V_{b−1}⊗W₁) → V_{a+b−2}⊗W₁ in
    monomial bases; `sourceTensor_product` (:259) = pullback (along bijections) of
    `product (C(a,b)) (cyclic (cyclic (dotPairing Bool)))` = C(a,b) ⊗ B_X(2). `sourceTensor_coordinate_change`
    (:309): `restrict fixedFirst inputChange outputDualChange sourceTensor = adaptedTensor` — identity on
    leg 1, change of basis on leg 2, inverse (dual) change on leg 3. One restriction of the WHOLE tensor.
14. `degeneration d e` (:148): `PolynomialRestrictionDegeneration adaptedTensor gradedTensor 1 0 1 1`
    with diagonal maps: leg 1 ≡ 1, leg 2 quotient ↦ ε, kernel ↦ 1, leg 3 quotient ↦ 1, kernel ↦ ε.
    This is the paper's weights (input kernel −1, output-kernel +1) shifted by +1 on leg 2, read at
    order ε¹: q→q and k→k have degree 1 (kept), ∗ (q→k) degree 2 (dropped), k→q degree 0 but zero.
    `vanishes`/`leading` are checked entrywise. `gradedTensor` = the two diagonal blocks;
    `gradedTensor_quotient`/`_kernel` (:108/:115) identify them with C(d+1,e+2) = C(a,b+1) and
    C(d+1,e) = C(a,b−1).
15. Determinant/Character.lean: `branch d e n` pads the two blocks into common spaces;
    `value_determinant_branch_zero/one` (:66/:89) λ(branch) = λ(C(a,b±1)) via injective support
    embeddings; `value_determinant_source_le` (:127): λ(source) ≤ 2^{pX} λ(C(a,b)) (product + pullback);
    `value_determinant_graded_le` (:136): λ(graded) ≤ λ(adapted) (degeneration) ≤ λ(source) (restriction)
    ≤ 2^{pX}λ(C(a,b)). `convolution_concavity_tag` (:166, `0<a`, `2≤b`, `0≤q≤1`):
    e^{pX·H(q)} λ(C(a,b+1))^q λ(C(a,b−1))^{1−q} ≤ 2^{pX} λ(C(a,b)), via `sharedFirst_tag` (Cor 3.2;
    branches labelled by the inl/inr part of legs 2 and 3, shared leg 1) and
    `value_sharedFirstTensor_eq_sum` (branch tags are recoverable, so tagged = Σ branches = graded).
    This is the paper's displayed inequality verbatim, natural-log entropy (`Real.binEntropy`).
16. `finite_product_concavity` (ProductBounds.lean:87): multiply six inequalities with the SAME q,
    Σ p_i = s = 6t, take ^(1/s), and choose q = b/(b+c) where b, c are the normalized products
    (= P(a,b+1), P(a,b−1)). It uses the exact identity H(q) + q log b + (1−q) log c = log(b+c) at that q
    (`binary_entropy_log_partition`, Entropy/Optimization.lean:23) instead of AM–GM; since b, c > 0,
    q ∈ (0,1) strictly, so the boundary/continuity remark of the paper is not needed.
    `convolutionProfile_concave` (Inequalities.lean:54, `0<t`, `0<a`, `2≤b`) =
    P(a,b−1)+P(a,b+1) ≤ 2P(a,b). = (4.6).

**Lemma 4.2 (shifted tripling).**
17. Sector/Weights.lean: `MiddleY` = [h, 2h+a−2] (`h ≤ j < 2h+a−1`), `MiddleZ` = [h+a−1, 2h+a−2];
    left/right as in the paper table (0-based, exactly the paper's integer intervals). Weights +1 on
    middle Y, −1 on middle Z. `middleY_of_middleZ` (:60): on support, a middle Z forces a middle Y, so
    weight ∈ {0,1} (`totalWeight_eq_zero_or_one`, :67) — equivalent to the paper's "left Y ⇒ left Z,
    right Y ⇒ right Z". `support_and_weight_zero_iff` (:197): weight-zero support = Left ∪ Middle ∪ Right
    with explicit parametrizations; Middle: i = a−1−u, j = h+u+r, k = h+a−1+r — the paper's display.
18. Sector/Degeneration.lean: `source a h = convolution a (3h+a−1)`; `restriction a h` (:176) is a
    `PolynomialRestrictionDegeneration source retained 1 0 1 1` with leg-1 map identity, leg 2 ε on
    middle, leg 3 ε on outer (paper's −1 shifted by +1). `polynomial_identity` (:131): every entry is
    ε·retained + ε²·erased. `retained_eq_three_branches` (:65): retained = left + middle + right, all in
    the ORIGINAL ambient coordinates with the ORIGINAL first leg.
19. Sector/Branches.lean: `leftTensor_pullback`/`rightTensor_pullback` (:88/:101): pull back along
    id and (translated) injective embeddings to C(a,h). `middleTensor_pullback` (:123): pullback along
    `Fin.rev` on leg 1 and embeddings on legs 2,3 equals `exchangedConvolution a h = fun i s r =>
    C(a,h) i r s` (legs 2,3 exchanged). `value_middleTensor` (:248): λ(middleTensor) = λ(exchanged C).
    The reversal is used ONLY to compute the value of the middle branch as a standalone tensor;
    the degeneration (item 18) and the tagged tensor (item 20) use `middleTensor` in the shared
    coordinates with no first-leg map. This matches the paper's caveat exactly and is legitimate,
    because Cor 3.2 consumes only the branch values λ(B_a).
20. Sector/Character.lean `convolution_tripling_tag` (:123, `0<a`, `0<h`):
    3^{pX} λ(C(a,h))^{2/3} λ(C^σ)^{1/3} ≤ λ(C(a,3h+a−1)) — `sharedFirst_tag` with the uniform law on
    Fin 3 (entropy factor 3^{pX}, Laws.lean:48), labels `yLabel`/`zLabel` (interval of leg 2 / leg 3,
    `branchFamily_labels` :49), then λ(retained) ≤ λ(source) by the degeneration.
21. `finite_product_tripling` (ProductBounds.lean:138) with hypothesis Π C_i = Π B_i, supplied by
    `prod_permutedCharacter_swapped_convolution` (Inequalities.lean:46: both sides are sixfold products,
    `sixfoldProduct_swap23`). Gives 3^{6t}·Π λ_π(C) ≤ Π λ_π(C(a,B)), then ^(1/(6t)).
    `convolutionProfile_tripling` (Inequalities.lean:75, `0<t`, `0<a`, `0<h`): 3P(a,h) ≤ P(a,3h+a−1). = (4.9).

**Assembly.**
22. `toScalarProfile` (Inequalities.lean:97) fills every field of `ScalarProfile t`
    (Growth/Profile.lean:23) from items 6–9, 16, 21; `meanExponent_le_three_quarters` (:110) and
    `exponent_sum_le_nine_quarters` (:117), consumed at Arithmetic/RankBound.lean:25 (only consumer, grep).

## 3. Definitions checked

| Lean name | file:line | what it is | matches paper? | note |
|---|---|---|---|---|
| `convolution` | Convolution/Basic.lean:24 | 0/1 tensor, 1 iff i+j=k, on Fin a×Fin b×Fin(a+b−1) | yes, (4.1) | a or b = 0 gives zero tensor; unused |
| `convolutionOutput` | Basic.lean:50 | k = i+j as Fin (a+b−1) | yes | bound by omega |
| `Character` | Character/Basic.lean:35 | normalized, additive, multiplicative, restriction-monotone ℝ-valued | Strassen spectral point axioms | reader B owns |
| `pX`,`pY`,`pZ` | Character/Dot.lean:107–114 | log₂ χ on dot products with singleton on Z / Y / X | yes | value(B(m)) = m^p proved, :129 |
| `sixfoldProduct` | Character/Symmetrization.lean:30 | product over 6 leg orders | yes, Π_π λ_π | |
| `symmetrizedProfile` | Symmetrization.lean:94 | sixfold^(1/(6t)) | yes, (4.4) | rpow total; 0<t used in lemmas |
| `meanExponent` | Convolution/Symmetry.lean:76 | (pX+pY+pZ)/3 | yes, t | `0 ≤ t ≤ 1` proved (:78, :82) |
| `convolutionProfile` | Symmetry.lean:109 | P(a,b) with t = meanExponent | yes | |
| `permutedCharacter` | Character/Permutation.lean:59 | the six λ_π as Characters | yes | |
| `ScalarProfile` | Growth/Profile.lean:23 | positivity, symmetry, P(1,b)=b, concavity (h≥2), tripling (h≥1), rank bound, all for indices ≥ 1 | yes, (4.5)+(4.6)+(4.9) | reader F owns use |
| `DeterminantKernel.diagonal/determinant` | Determinant/Kernel.lean:32/38 | (s,w)↦(u,v); multiplication by uw−vs, chart u=1 | yes | |
| `quotientVector`/`kernelVector` | Kernel.lean:198/202; Basis.lean:39/46 | paper's quotient lifts and kernel basis | yes | e+2 and e vectors |
| `adaptedTensor` | Determinant/Filtration.lean:32 | slice matrix (4.8) incl. explicit ∗ entries; k→q block 0 | yes | proved equal to actual coefficients :291 |
| `gradedTensor` | Filtration.lean:40 | C(a,b+1) ⊕ C(a,b−1) sharing leg 1 | yes | :108, :115 |
| `sourceTensor` | Filtration.lean:223 | multiplication on (V_{b−1}⊗W₁) in monomial basis | = C(a,b)⊗B_X(2), :259 | |
| `degeneration` | Filtration.lean:148 | ε-diagonal maps, order 1 | paper weights shifted by +1 on leg 2 | equivalent |
| `binaryLaw` | Polynomial/Laws.lean:23 | (q, 1−q) | yes | entropy = binEntropy, :38 |
| `Sector.Support/MiddleY/MiddleZ` | Sector/Weights.lean:25/29/32 | support, middle intervals | yes, paper table | 0-based closed intervals agree |
| `Sector.restriction` | Sector/Degeneration.lean:176 | ε-diagonal maps, order 1 | paper weights shifted +1 on leg 3 | equivalent |
| `leftTensor/middleTensor/rightTensor` | Degeneration.lean:52/56/60 | the three retained blocks in common coordinates | yes | no first-leg map |
| `exchangedConvolution` | Sector/Branches.lean:117 | C(a,h) with legs 2,3 swapped | C^σ | reversal applied only in `middleTensor_pullback` |
| `finite_product_concavity` | Polynomial/ProductBounds.lean:87 | six-fold product + optimal q | yes | exact identity, q∈(0,1) |
| `finite_product_tripling` | ProductBounds.lean:138 | six-fold product with uniform law | yes | needs ΠC=ΠB |
| `toScalarProfile` | Polynomial/Inequalities.lean:97 | P as ScalarProfile | yes | needs 0<t only |

## 4. Escalations (all resolved; none blocking)

E1 (resolved, OFF-ROUTE). The rank LOWER bound of (4.2) (RankLowerBound.lean:94–116) and the exact
sequence (4.7) (Determinant/Bounds.lean) are proved but not consumed by the route: grep over
`…/MatrixMultiplication/` for `exactRank_convolution`, `convolution_rank_lower`, `convolution_identity_minor`,
`DeterminantBounds.`, `finrank_kernel`, `diagonalToDegreeLT` finds only their own files; both modules
are imported only by AuxiliarySeparation/Main.lean. Not needed: Lemma 5.1 only uses P ≤ (a+b−1)^{1/t},
and the adapted basis is established by linear independence + count (Basis.lean:75–93). Harmless.

E2 (resolved). `meanExponent_le_three_quarters` (Inequalities.lean:110) splits on `0 < t`; in the
other case t ≤ 0 ≤ 3/4 trivially. Honest: the conclusion is the true statement t ≤ 3/4 in both cases,
and t ≥ 0 is in fact proved (`meanExponent_nonneg`, Symmetry.lean:78), so the branch only covers t = 0.
The `0 < t` guard elsewhere (`convolutionProfile_le`, `_one_left`, `_concave`, `_tripling`) is needed
for rpow arithmetic and never hides content, since the final consumer needs no hypothesis on t.

E3 (resolved). `ScalarProfile.rank_bound` states ((a:ℝ)+(b:ℝ)−1)^{1/t}; `convolutionProfile_le` states
((a+b−1 : ℕ) : ℝ)^{1/t}; bridged by `Nat.cast_sub` with 1 ≤ a+b (Inequalities.lean:104–107). Correct
for a,b ≥ 1.

E4 (resolved). Upper-right block of (4.8) (kernel input → quotient output, the only potentially
weight −1 block) is ZERO by proof: `adaptedTensor` sets it to 0 (Filtration.lean:36) and
`boundedMultiply_adapted_coordinates` (:291) proves the true coefficients equal `adaptedTensor`
(uniqueness from `adaptedVectors_linearIndependent`). The ∗ block (q→k) is exactly the entries
j = e+1, i < d, k = e+i, at ε² — dropped. Independently confirmed in Python (§ below).

E5 (resolved). Middle-branch first-leg reversal: the Lean never applies a first-leg map to the whole
tensor. `retained_eq_three_branches` and `restriction` (Sector/Degeneration.lean:65, :176) use the
identity on leg 1; `Fin.rev` appears only in `middleTensor_pullback`/`value_middleTensor`
(Branches.lean:123, :248) to compute λ of the middle branch alone, which is all Cor 3.2 consumes.
This is what the paper says.

E6 (note). `Polynomial/Interpolation.lean` is NOT the convolution evaluation/interpolation (that is
Convolution/Rank.lean via Mathlib `Lagrange`). It supplies `restrictionDegeneration_eval` and
`restrictionDegeneration_approximation`, consumed by `value_polynomialRestrictionDegeneration_le`
(Character/Degeneration.lean:141), which is the "degeneration monotonicity" both lemmas use. Its
soundness (χ(U) ≤ χ(T) from a polynomial degeneration without continuity, via
`value_le_of_polynomialApproximation`) belongs to another reader; I checked only that both lemmas
build genuine `PolynomialRestrictionDegeneration` certificates (structure at
Polynomial/ComplexPolynomialDegenerationComposition.lean:94: lower coefficients vanish, ε^k coefficient = U).

E7 (cosmetic). Docstrings cite "Section 5", "Section 5.1/5.2", "Lemma 6.1" (e.g. Basic.lean:23,
Kernel.lean:16, Weights.lean:9, Profile.lean:11/106) where the posted paper has §4, §4.1/4.2, Lemma 5.1.
Numbering drift only; statements match.

E8 (§7 question, resolved). No `attribute [...]` lines in my files (grep). `open scoped Classical` in
Sector/Degeneration.lean:19, Sector/Branches.lean:18, Sector/Character.lean:21 and two
`instance : Decidable (MiddleY …)` / `(MiddleZ …)` (Weights.lean:34/37, `inferInstanceAs` of the
unfolded definition) only choose decision procedures for `if`; `Decidable` is a subsingleton, so no
statement's meaning changes.

E9 (hypotheses, §6). All exact:
`convolutionProfile_concave {a b} (ht : 0 < χ.meanExponent) (ha : 0 < a) (hb : 2 ≤ b)`;
`convolutionProfile_tripling {a h} (ht : 0 < χ.meanExponent) (ha : 0 < a) (hh : 0 < h)`;
`convolution_concavity_tag (a b) (ha : 0 < a) (hb : 2 ≤ b) (q) (0 ≤ q) (q ≤ 1)`;
`convolution_tripling_tag χ (a h) (ha : 0 < a) (hh : 0 < h)`.
`toScalarProfile (ht : 0 < meanExponent)`: positive (a,b ≥ 1), symmetric (no hyp), boundary (b ≥ 1),
concave (a ≥ 1, h ≥ 2), tripling (a ≥ 1, h ≥ 1), rank_bound (a,b ≥ 1). These are exactly the
ranges ScalarProfile requires and the paper states; no extra hypothesis.

## Independent computation (python3 -I, scratchpad `readE/`)

- `check.py` (i): for a,b ≤ 6 the three flattening ranks of C(a,b) (exact Fractions) are (a, b, a+b−1).
  (ii): with the three flattening-rank characters (pX,pY,pZ) = (0,1,1) for the X-flattening, t = 2/3,
  P(a,b) = (ab(a+b−1))^{1/2}: (4.5), (4.6), (4.9) hold for all a,b,h ≤ 12; also each of the three
  per-character tag inequalities (concavity for q ∈ {0,.1,.3,.5,.77,1}, tripling with C^σ legs
  (a, a+h−1, h)) holds for a ≤ 9, b,h ≤ 9.
- `det.py` (iii): built the (e,1)-forms in the paper's two-variable monomials, the paper's quotient lifts
  and kernel basis D u^{e−1−j}v^j, multiplied by u^{d−i}v^i, solved for coordinates. For a=b=2 the only
  off-diagonal entry is (x=u, input v·w, output kernel D·v) — the paper's u(vw) = v²s + vD; no
  negative-weight entry, upper-right block empty, weight-zero q→q part = C(2,3), k→k part = C(2,1).
  For all a ≤ 5, 2 ≤ b ≤ 6 the computed coefficient tensor equals the Lean `adaptedTensor` formula
  entry-for-entry and the same block facts hold.
- `sector.py` (iv): a=2,h=1 reproduces Figure 1 (8 terms, erased (x0,y1,z1) and (x1,y2,z3)); a=3,h=2
  (24 terms, 6 erased, weights only 0/1). For all a,h ≤ 8: outer branches are translates of C(a,h), the
  middle branch maps to C(a,h) under x ↦ a−1−x, (y,z) ↦ (z−(h+a−1), y−h), and equals the Lean
  `MiddleBranch` parametrization; every erased term has middle Y and outer Z.

## 5. Verdict

§4 is formalized faithfully: C(a,b), the rank upper bound, the symmetrized profile and (4.5), Lemma 4.1
(explicit adapted bases, proved-zero upper-right block, ε-degeneration of the whole tensor, two-branch
Cor 3.2, exact optimal q) and Lemma 4.2 (paper's interval table, whole-tensor degeneration with a shared
first leg, branch-local reversal, uniform Cor 3.2, Π λ_π(C^σ) = Π λ_π(C)) hold for exactly the index
ranges Lemma 5.1 needs, with no extra hypotheses; I found no discrepancy.

NOT read: the proofs of Cor 3.2 (`integral_type_comparison`'s dependencies, `finiteSeparation_bound`,
Entropy/Tag.lean bodies), `value_le_of_polynomialApproximation` / Character/Degeneration.lean bodies,
`value_extendByZero` and the rest of Tensor/CharacterBounds.lean, `positiveMultiplicative_eq_rpow`
(Growth/MultiplicativePower.lean), Tensor/SixfoldProductBounds.lean (`sixfoldProduct_le_rank`,
`_pos`), the Growth lemmas behind `ScalarProfile.exponent_le_three_quarters`, and
Arithmetic/RankBound.lean beyond its line 25. These are other readers' parts; my conclusions assume
their interfaces as stated.
