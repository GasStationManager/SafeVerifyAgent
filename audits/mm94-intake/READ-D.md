# READ-D: Paper §3 (Prop 3.1 finite separation, Cor 3.2 shared-leg entropy inequality)

Reader D. Paper text lines 142–241. Lean root:
`/home/user/openai-math/repo/lean/OAI/LinearAlgebra/MatrixMultiplication/` (abbreviated `MM/`;
`AS/` = `MM/AuxiliarySeparation/`). Every file:line below was read with `cat -n`/`sed -n`.

## 1. Files read

Read WHOLE (assigned subtree, leaves first):

| file | lines |
|---|---|
| AS/Separation/Fourier.lean | 69 |
| AS/Separation/NoWrap.lean | 100 |
| AS/Separation/SquareWeights.lean | 115 |
| AS/Separation/FiniteProjection.lean | 193 |
| AS/Separation/Basic.lean | 383 |
| AS/Separation/BranchTagging.lean | 82 |
| AS/Entropy/Optimization.lean | 95 |
| AS/Entropy/Tag.lean | 221 |
| AS/Tensor/SupportExtension.lean | 83 |
| AS/Tensor/SharedPadding.lean | 147 |
| AS/Tensor/TagInequality.lean | 222 |
| AS/Tensor/SixfoldProductBounds.lean | 111 |
| AS/Character/Degeneration.lean | 165 |
| AS/Character/FiniteSeparation.lean | 101 |

Shared modules read WHOLE (directly consumed): MM/Polynomial/ComplexPolynomialApproximation.lean (182),
MM/Entropy/ComplexFiniteEntropy.lean (175), MM/Entropy/ComplexTypeEntropy.lean (383),
MM/Tensor/ComplexDotPairing.lean (~40).

Read in PART (definitions / statements of consumed theorems only):
MM/Tensor/ComplexTensor.lean (315; lines 1–60 `Tensor`, `restrict`, `product`, `directSum`, `power`;
195–260 `pullback`, `restrictionOrbit`, `DegeneratesTo`); MM/Tensor/ComplexTensorSymmetrization.lean
10–26 (`cyclic`); MM/Entropy/ComplexEntropyContinuity.lean 1–66, 169–175; MM/Entropy/ConditionalContinuity.lean
1–75; MM/Separation/ComplexTypeCounting.lean 1–40, 95–116 (`ExactWords`, `exactWords_card`);
MM/Separation/ComplexRationalTypes.lean 15–30, 85–91, 118–121; MM/Tensor/ComplexFactorialLogBounds.lean
statements at 15, 61, 116, 124, 134; AS/Tensor/CharacterBounds.lean 25–100 (`value_extendByZero`,
`value_power`, `value_copies`); AS/Character/Basic.lean 1–80 (the `Character` structure, `value_reindex`);
AS/Character/Dot.lean 20–60, 100–147 (`pX`, `value_cyclic_cyclic_dotPairing`);
AS/Growth/PolynomialOverhead.lean 47–49, 70–75; AS/Polynomial/Interpolation.lean 22–35, 104–147;
MM/Polynomial/ComplexPolynomialDegenerationComposition.lean 94–108 (structure only);
consumers AS/Determinant/Character.lean 130–175, AS/Sector/Character.lean 60–150.

NOT read, with reason: MM/Separation/ComplexFiniteSeparation.lean (169),
MM/Separation/ComplexLabelHierarchySeparation.lean (597), MM/Tensor/ComplexSeparatedTensorDecomposition.lean
(308), MM/Tensor/ComplexTensorRestrictionComposition.lean (206). They are in the route closure only as
transitive imports. `grep` for their declarations (`dependentDirectSum`, `separatedTensor*`,
`labelFiber*`, ...) across my 14 files found no use. The one use of ComplexTensorRestrictionComposition in my
files is `DegeneratesTo.restrict` at AS/Separation/Basic.lean:360, inside an off-route theorem (see E1).
I did not read the rest of CharacterBounds (dependent direct sums), the existence proof of characters
(Lemma 2.2), or `positiveMultiplicative_eq_rpow`.

## 2. Argument reconstruction

**Prop 3.1, executed construction (AS/Separation/Basic.lean):**

1. `sharedFirstTensor B` (Basic.lean:46–48) is the paper's A. B : Fin M → Tensor ℂ X Y Z gives the blocks,
   and the coordinates are X, (Fin M × Y), (Fin M × Z), with value `if y.1 = z.1 then B y.1 x y.2 z.2 else 0`.
   The second and third legs carry a sector tag, so the sectors Y_h = {h}×Y and Z_h = {h}×Z are disjoint.
   The `if` encodes "no terms between unmatched sectors". X is shared.
2. There are three local maps on 5M copies (Basic.lean:51–70). Copies are r ∈ Fin(5M), and sectors are
   numbered `sectorNumber i = i+1` ∈ {1..M} (31–43).
   x^{(r)}_a ↦ Σ_g ζ^{r·2g} X_{a,g}; y^{(r)}_{h,b} ↦ Σ_u ζ^{r(u−h)} Y_{h,b,u};
   z^{(r)}_{h,c} ↦ (5M)^{-1} Σ_v ζ^{r(−v−h)} Z_{h,c,v}. These are exactly the paper's substitutions,
   including the 1/L on the z leg (line 69).
3. `finiteProjection_restrict` (Basic.lean:110–156) computes the restriction of `directSum (fun _ : Fin (5M) => A)`
   by these maps. Each target coefficient is L^{-1} Σ_r ζ^{r·phase}·B_h(a,b,c) with
   phase = u−v+2(g−h) (`phase`, SquareWeights.lean:18), and it is 0 when the sectors are unmatched.
4. Fourier filter: `sum_zpow_primitive_root` (Fourier.lean:28–38) gives Σ_{r<L} ζ^{re} = L·[L ∣ e] for
   `IsPrimitiveRoot ζ L`. `normalized_sum_zpow_primitive_root` (41–46) gives the normalized form.
   No-wrap: `fourierPhase_abs_le` (NoWrap.lean:19–24) proves |u−v+2(g−h)| ≤ 3(M−1) for labels in [1,M],
   `fourierRadius_lt_modulus` (27–29) proves 3(M−1) < 5M, and `fiveMFourierCoefficient_eq_ite`
   (FiniteProjection.lean:46–56) combines them. The ranges match, because the Lean feeds
   `sectorNumber` ∈ [1,M] (`sectorNumber_bounds`, Basic.lean:33–37).
5. Weights: `firstWeight g = g²`, `secondWeight h u = hu − h²`, `thirdWeight h v = −(hv)`
   (SquareWeights.lean:21–27), all ℤ. `totalWeight_eq_square_add_phase` (33–36) proves
   total = (g−h)² + h·phase, which is a ring identity.
   `totalWeight_eq_zero_iff_of_phase_eq_zero` (50–61) proves that on the support, total = 0 ⟺ g = h ∧ u = v.
   `totalWeight_le_of_labels` (77–84) gives the degree bound (M−1)².
6. Negative weights: `firstSeparationMap` etc. (Basic.lean:222–233) multiply each map by t^{w} with `zpow`.
   `separationPolynomial` (159–165) is the polynomial tensor whose branch is
   monomial((g−h)²)·[phase=0]·B. Surviving weights are ≥ 0, so it is a genuine polynomial.
   `separationPolynomial_eval` (250–276) proves that for every t ≠ 0, its evaluation at t equals the restriction of
   the 5M copies by the weighted maps. This is how negative individual weights enter, exactly as in the paper.
7. `separationPolynomial_coeff_zero` (175–187) shows that the constant coefficient is `separationTarget B`
   (169–172): value B_h(a,b,c) iff g = h = h' and u = v.
   `separationTarget_eq_directSum` (332–347) proves that this is, up to an explicit coordinate bijection, exactly
   `directSum (fun h => product (B h) (cyclic (cyclic (dotPairing (Fin M)))))`, i.e. ⊕_h (A_h ⊗ B_X(M)).
   Check: cyclic∘cyclic of dotPairing U : Tensor U U Unit is (unit, c, a) ↦ [c = a], which is x·Σ_u y_u z_u = B_X(M).
   Each h gets its own copy of X (first coordinate X × Fin M).
8. Character form, which is ON ROUTE: `separationPolynomialApproximation` (AS/Character/FiniteSeparation.lean:43–55)
   packages the polynomial as a `PolynomialApproximation` with d = 0 and D = (M−1)².
   `value_separationTarget_le` (63–78) proves χ(target) ≤ 5M·χ(A). It uses `value_le_of_polynomialApproximation`
   (Degeneration.lean:89–125), the paper's Lemma 2.3 interpolation, applied with
   ζ = exp(2πi/(5M)) (`Complex.isPrimitiveRoot_exp`, line 67–69) and `value_copies`.
   `value_separationTarget` (81–86) gives χ(target) = (Σ_h χ(B_h))·M^{pX}.
   `finiteSeparation_bound` (90–94) concludes (Σ_h χ(B_h))·M^{pX} ≤ 5M·χ(sharedFirstTensor B).
9. Lemma 2.3 as used here (Degeneration.lean:67–125) works as follows. Interpolation at nodes 1..nD+1
   (`interpolationNode`, Interpolation.lean:23, nonzero) writes coeff_d of P^{⊗n} as a linear combination of
   evaluations. A linear combination is a restriction of a direct sum (`value_sum_le`, `value_scale_le`, 28–63),
   which gives χ(U)^n ≤ (nD+1)·b^n. Then `le_of_pow_le_linear_mul_pow` (PolynomialOverhead.lean:47) yields χ(U) ≤ b.
   This is the paper's proof, with no continuity of χ.

**Cor 3.2 (AS/Tensor/TagInequality.lean + AS/Entropy/Tag.lean):**

10. `branchWordTensor B w` (TagInequality.lean:30–32) is ⊗_i B_{w_i} for a word w : Fin n → Fin s.
    `value_branchWordTensor` (35–58) proves χ = Π_i χ(B_{w_i}) by induction with `Fin.consEquiv` reindexing,
    `value_reindex` and `map_product`. This is the paper's "product of the T_i up to reordering factors" step.
    `value_exact_branchWordTensor` (61–69) gives C = Π_a χ(B_a)^{counts a} for every word of exact type.
11. `exactType_power_pullback` (81–98): pulling T^{⊗N} back along y = (h, ys) ↦ (w_h(i), ys_i)_i on legs 2 and 3,
    with the same map on both legs and h ranging over Fin |ExactWords counts|, gives exactly
    `sharedFirstTensor (fun h => branchWordTensor B (e h))`. When h ≠ h', the words differ at some position,
    where the matched-sector `if` vanishes. This is the paper's "retain words of type N q".
    `exactType_value_le_power` (101–107) gives χ ≤ χ(T)^N.
12. `integral_type_comparison` (111–141) proves |ExactWords counts|^{pX}·Π χ(B_a)^{counts a} ≤ 5·χ(T)^{Σcounts}.
    It is finiteSeparation_bound applied to the M = multinomial sectors, followed by cancelling M once.
    This is the paper's 5Mλ(T)^N ≥ 5Mλ(A) ≥ M^{1+pX}C_N.
13. Entropy limit (Entropy/Tag.lean): `typeContribution_rate` (54–72) together with
    `tendsto_log_exactWords_card_mul` (MM/Entropy/ComplexTypeEntropy.lean:305–312) gives
    N^{-1} log multinomial(t·counts) → H(counts/Σcounts) as t → ∞.
    `log_type_bound` (76–90) uses `exp_le_of_tendsto_log_div` (PolynomialOverhead.lean:70–75) to remove C = 5.
    `rational_log_tag_of_finite_type_bounds` (93–103) handles rational q, via `exists_type_representation`.
    `log_tag_of_finite_type_bounds` (107–122) extends to all q through a rational sequence
    (`exists_rational_law_sequence`, ConditionalContinuity.lean:63–75) and continuity of `finiteEntropy` and of the
    linear term. `tag_of_integral_type_comparison` (201–213) is the character version, using χ(B_a) ≥ 1 > 0.
14. `Character.sharedFirst_tag` (TagInequality.lean:156–171) states
    exp(χ.pX·H(q))·Π_a χ(B_a)^{q_a} ≤ χ(sharedFirstTensor B) for every `FiniteLaw (Fin s)` q,
    assuming only ∀a, B a ≠ 0. This is exactly (3.3).
    `sharedFirstDependent_tag` (197–204) is the version with sector-dependent Y_a, Z_a, via zero padding
    (SharedPadding.lean).
15. Bridge to the paper's "T = Σ T_i" form: `value_sharedFirstTensor_eq_sum` (BranchTagging.lean:54–75) proves χ(sharedFirstTensor B) = χ(Σ_i B_i). It requires label maps
    ly : Y → Fin M and lz : Z → Fin M with B_i(x,y,z) ≠ 0 → ly y = i ∧ lz z = i, which is precisely
    "matched, pairwise disjoint sectors on legs 2, 3, shared leg 1".
    Both downstream consumers use this bridge: AS/Determinant/Character.lean:155–157 and AS/Sector/Character.lean:85–89, 128.

## 3. Definitions checked

| Lean name | file:line | what it is | matches paper? | note |
|---|---|---|---|---|
| `Tensor`, `restrict` | MM/Tensor/ComplexTensor.lean:16, 31–35 | coefficient array; restriction (A,B,C linear maps on each leg) | yes | |
| `directSum` | ComplexTensor.lean:45–47 | block-diagonal on ι×X, ι×Y, ι×Z | yes (full direct sum) | |
| `product` | ComplexTensor.lean:41–43 | Kronecker product | yes | |
| `DegeneratesTo` | ComplexTensor.lean:239–243 | U ∈ closure(restriction orbit of T) | topological, not the paper's algebraic ⇝ | off route for §3 (E1) |
| `dotPairing U` | MM/Tensor/ComplexDotPairing.lean:16–17 | Σ_i x_i y_i z (Tensor U U Unit) | B_Z(m) | cyclic∘cyclic gives B_X(m) |
| `Character` | AS/Character/Basic.lean:36–55 | ℝ≥0-valued, χ(0)=0, χ(1)=1, additive on directSum, multiplicative on product, restriction-monotone, over all finite index types | Def 2.1 | |
| `pX` | AS/Character/Dot.lean:114 | log₂ χ(cyclic(cyclic(dotPairing (Fin 2)))) | p_X of (2.3) | `value_cyclic_cyclic_dotPairing` (Dot.lean:142) gives m^{pX} for every m>0 |
| `sharedFirstTensor` | AS/Separation/Basic.lean:46 | sector-tagged block tensor with shared X | Prop 3.1's A (uniform Y, Z per sector) | sector-dependent sizes via SharedPadding.lean:26 |
| `firstProjectionMap`…`thirdProjectionMap` | Basic.lean:51–70 | paper's 3 substitutions incl. 1/L | yes | |
| `firstWeight`/`secondWeight`/`thirdWeight` | SquareWeights.lean:21–27 | g², hu−h², −hv | yes | integers, negatives allowed via zpow |
| `separationPolynomial` | Basic.lean:159 | weighted projected polynomial tensor | the transformed tensor F(ε) | degree ≤ (M−1)² as in paper |
| `separationTarget` | Basic.lean:169 | weight-zero tensor D | yes | = ⊕_h A_h ⊗ B_X(M) (Basic.lean:332) |
| `PolynomialApproximation` | MM/Polynomial/ComplexPolynomialApproximation.lean:60–65 | polynomial tensor whose lowest nonzero coeff (index d) is T, degree ≤ D | interpolation input | |
| `finiteEntropy`/`entropyTerm` | MM/Entropy/ComplexFiniteEntropy.lean:19–21 | Σ −p log p, natural log | H(q) | `= Real.negMulLog` by rfl (ComplexEntropyContinuity.lean:16); 0 log 0 = 0 since `Real.log 0 = 0` |
| `FiniteLaw` | ComplexFiniteEntropy.lean:46–49 | nonneg mass summing to 1 | probability vector | zeros allowed |
| `ExactWords counts` | MM/Separation/ComplexTypeCounting.lean:30–31 | words in Fin(Σcounts) → A with exact letter counts | words of fixed frequency | card = multinomial (95–96) |
| `branchWordTensor` | TagInequality.lean:30 | ⊗_i B_{w_i} | sector tensor ∏T_i up to reorder | |
| `typeContribution` | Entropy/Tag.lean:28 | card(ExactWords(t·counts))^p·Π values^{t·counts} | M^{pX}C_N | |

## 4. Escalations (all resolved; none blocking)

E1. **Two degeneration notions; the route uses the right one.** `finiteSeparation_degeneratesTo` /
`finiteSeparation_directSum_degeneratesTo` (Basic.lean:306–318, 351–377) state Prop 3.1 literally as
A^{⊕5M} ⇝ ⊕_h(A_h ⊗ B_X(M)), but use the *closure* notion `DegeneratesTo`, and `Character` has no
closure-monotonicity axiom. `grep` shows these two theorems have no consumer: the only reference is
Basic.lean:359 inside the second one. The ON-ROUTE statement is the character inequality
`finiteSeparation_bound` (FiniteSeparation.lean:90). It is obtained from the SAME explicit polynomial
(`separationPolynomial`) through `value_le_of_polynomialApproximation`, which is the paper's Lemma 2.3 proof.
So the Fourier/weight construction really is executed and the character bound really comes from it.
No continuity of χ is used. Resolved.

E2. **Negative weights.** `PolynomialRestrictionDegeneration` (ComplexPolynomialDegenerationComposition.lean:94–107)
has polynomial local maps, so it allows only nonnegative weights. The separation does NOT use that structure.
It builds the combined polynomial directly and proves eval_t = restriction for t ≠ 0 with zpow local maps
(Basic.lean:222–276). This is sound: interpolation only evaluates at the nonzero nodes 1..D+1
(Interpolation.lean:23–34). Resolved; it matches the paper's "individual weights may be negative".

E3. **5M is generous, not tight.** The no-wrap bound needs only L > 3(M−1). My script confirms that L = 3M−2
already works for M = 3, while L = 6 for M = 3 and L = 9 for M = 4 wrap and produce negative-weight survivors.
The constant 5 only enters as 5·χ(T)^N and is removed in the N-th-root limit (Entropy/Tag.lean:76–90,
C = 5 at 197/213). This is harmless for the result. I note it because the paper says the 5M is "the cost of the Fourier copies".

E4. **Hypothesis audit (Q6).** My files contain no `0 < pX` or `0 < t` guard. `finiteSeparation_bound` needs
`0 < M`, which holds for any multinomial count (`exactWords_card_pos`). `sharedFirst_tag` needs ∀a, B a ≠ 0,
the same as the paper's "nonzero tensors". s = 0 is excluded automatically, because FiniteLaw.total = 1
(TagInequality.lean:161–166). q with zero entries is covered, because rational approximation preserves zero
patterns (ComplexRationalTypes.lean:118–121) and entropy is continuous (negMulLog). Nothing the paper covers is dropped.

E5. **Statement shape for Cor 3.2.** Lean states (3.3) for the *tagged* tensor `sharedFirstTensor B` with uniform
Y, Z, rather than for an arbitrary T = ΣT_i. The equivalence with the paper's form needs the label-map
hypothesis of `value_sharedFirstTensor_eq_sum` (BranchTagging.lean:54–75). That hypothesis is
exactly matched disjoint sectors. Both consumers discharge it with concrete label maps (`branchLabel`,
`yLabel`/`zLabel`), which I did not audit (reader E). Sector-dependent dimensions are handled by
`sharedFirstDependent_tag`, but the two consumers do not use it.

E6. **Cosmetic: draft provenance.** NoWrap.lean:9–10 cites "Section 4.1 of *Matrix Multiplication via
Auxiliary Separation and Polynomial Multiplication*", and SquareWeights.lean:8 cites "Sections 4.1–4.3".
The title and numbering differ from the paper (§3). This is docstring only; no semantic effect.

E7. **Attributes / instances (Q7).** None of my 14 files has an `attribute` line (`grep -rn attribute` came back empty).
SupportExtension.lean:16, SharedPadding.lean:18 and TagInequality.lean:22 use `open scoped Classical`, and
`classical` appears in proofs. This only supplies Decidable instances, which are propositionally unique.
It changes no statement's meaning.

## 5. Q&A summary (per the task)

Q1. Prop 3.1 appears in Lean twice:
- As a closure degeneration (Basic.lean:306/351, off route).
- As the character inequality `finiteSeparation_bound` (FiniteSeparation.lean:90).

The encoding is `sharedFirstTensor` with tag-matched Y/Z: a block-diagonal `if y.1 = z.1`, not a sigma type.
A sigma-typed variant exists in SharedPadding.lean:26. The Fourier/weights construction is explicitly executed.
Its weight-zero part is computed and shown equal to ⊕_h(A_h⊗B_X(M)) up to an explicit bijection.

Q2. ζ = `Complex.exp(2πi/(5M))` with `IsPrimitiveRoot` from Mathlib (Basic.lean:311–313, FiniteSeparation.lean:67–69).
Orthogonality is proved at Fourier.lean:28. The bound 3(M−1) < 5M is proved for labels in [1,M]
(paper ranges, via sectorNumber = i+1) and also for 0-based Fin M (NoWrap.lean:73–96).

Q3. Negative weights are allowed via zpow in the route's interpolation (E2).
The surviving weight is (g−h)², and it is 0 iff g = h (and then u = v), proved at SquareWeights.lean:50.
The weight-zero tensor equals the full direct sum (Basic.lean:332). The 1/L is on the z map (Basic.lean:69),
and it is matched against `finiteFourierCoefficient`'s L⁻¹ (FiniteProjection.lean:26–27).

Q4. Cor 3.2 = `Character.sharedFirst_tag` (TagInequality.lean:156). H is natural-log Shannon entropy
(negMulLog, 0 log 0 = 0). All q are covered: rational q via an exact type with t·counts, t → ∞, then a rational
sequence plus continuity. The multinomial estimate is TWO-SIDED:
|log multinomial − N·H| ≤ (|A|+1)(1+log(N+1)) (ComplexTypeEntropy.lean:108–143).
It is built on `factorialLogRemainder` bounds (ComplexFactorialLogBounds.lean:116, 134).
The limit form is at ComplexTypeEntropy.lean:255/305.

Q5. A "tag" inequality is exp(p·H(q))·Π values^q ≤ source (Entropy/Tag.lean:125–130). The character version is
at 201–213, and `sharedFirst_tag` instantiates p = χ.pX, values = χ(B_a), source = χ(sharedFirstTensor B).
`convolution_concavity_tag_dims` (Determinant/Character.lean:149–164) applies it with the binary law and
2 sectors. `convolution_tripling_tag` (Sector/Character.lean:123–138) applies it with the uniform law on 3 sectors.
In both, the hypothesis is the tagged sum, bridged by `value_sharedFirstTensor_eq_sum`.

Q6. No guard excludes a case the paper covers (E4). Multiplicativity up to reordering is `value_branchWordTensor`
(TagInequality.lean:35), via `value_reindex` (Character/Basic.lean:73).

Q7. No attribute lines; see E7.

## 6. Independent computation

The script is `scratchpad/readD/sep.py`, run with `python3 -I`. It builds the paper's construction from scratch,
not from the Lean definitions: L source copies of A = Σ_h A_h with random integer-complex blocks, the three
ζ-substitutions with 1/L on z, and the integer weights g², hu−h², −hv, keeping the polynomial in ε as
{exponent: coefficient}. It then checks four things for every target coefficient:
- (i) It is nonzero iff u−v+2(g−h) = 0.
- (ii) Its exponent is (g−h)², and in particular ≥ 0.
- (iii) The minimum surviving weight is 0, attained only at g = h, u = v.
- (iv) The weight-0 tensor equals ⊕_h(A_h ⊗ B_X(M)) entrywise: X_{a,h}Y_{h,b,u}Z_{h,c,u} with coefficient A_h[a,b,c].

Results:
- The requested case M = 2, dim X = Y = Z = 1, L = 10 passes all four checks, with max |phase| = 3 = 3(M−1).
- M = 1..5 with dim X = Y = 2, Z = 1 and L = 5M pass all four checks.
- Negative controls: L = 6 (M = 3) and L = 9 (M = 4) fail (wrap-around survivors with weights −14 and −27).
  L = 7 (M = 3) passes (see E3).

## 7. Verdict

The Lean faithfully formalizes Prop 3.1 and Cor 3.2. The Fourier projection, no-wrap bound, square weights
and weight-zero direct-sum identification are all explicitly executed. The on-route character inequality is
derived from that explicit polynomial by the paper's own interpolation argument. Cor 3.2 holds for every
probability vector with a two-sided multinomial/Stirling estimate. I found no discrepancy that affects the result.

Not read: listed in §1. In short:
- the CW shared modules not consumed by this subtree (ComplexFiniteSeparation, ComplexLabelHierarchySeparation,
  ComplexSeparatedTensorDecomposition, ComplexTensorRestrictionComposition);
- proof bodies of ComplexFactorialLogBounds, ComplexRationalTypes and the rest of ComplexEntropyContinuity;
- `positiveMultiplicative_eq_rpow` and the remainder of Dot.lean / CharacterBounds.lean;
- the label-map support proofs in the two consumers (reader E).
