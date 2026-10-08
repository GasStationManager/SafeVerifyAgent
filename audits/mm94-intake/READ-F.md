# READ-F — Lemma 5.1 (diagonal growth), proof of Thm 1.1 up to ν ≤ 9/4, assembly

Reader F. Paper text lines 377–430 (§5). Lean root:
`OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/` (abbreviated `AS/` below).
All file:line citations were read with `cat -n`/`sed -n` in this session.

## 1. Files read

Read WHOLE (line counts from `wc -l`):

| file | lines | role |
|---|---|---|
| Growth/ConcaveSlopes.lean | 123 | Lemma 5.1: concave rows ⇒ antitone increments, nonneg limiting slope g_a |
| Growth/ProfileSlopes.lean | 149 | Lemma 5.1: iterated shifted tripling ⇒ P(a,a) ≤ ((3a−1)/2)·g_a; symmetry ⇒ diagonal step (5.1) |
| Growth/Product.lean | 65 | Lemma 5.1: product (5.2) as `growthProduct`, (1+1/(3m))³ ≥ 1+1/m, G³ ≥ n |
| Growth/Recurrence.lean | 183 | Lemma 5.1: simultaneous induction ⇒ n⁴ ≤ D_n³ |
| Growth/Profile.lean | 139 | `ScalarProfile` structure; Lemma 5.1 assembly; `exponent_le_three_quarters` |
| Arithmetic/ExponentComparison.lean | 89 | `rpow_exponent_le_of_nat_bound`, `diagonal_exponent_le_three_quarters` (the a→∞ step) |
| Growth/NormalizedProfile.lean | 81 | NOT Lemma 5.1: properties of `symmetrizedProfile` (positivity, rank bound r^{1/t}) — §4 (4.5) |
| Growth/MultiplicativePower.lean | 159 | NOT Lemma 5.1: monotone multiplicative f on ℕ_{>0} is n^p, p = log f(2)/log 2 — §2.1 (2.3)/(2.4) |
| Growth/PermutationProduct.lean | 118 | NOT Lemma 5.1: finite identities over Perm(Fin 3); imported but effectively unused |
| Growth/PolynomialOverhead.lean | 97 | NOT Lemma 5.1: "linear/constant prefactor doesn't change exponential rate" — §2.3 interpolation, entropy, spectrum |
| Growth/SpectralLimit.lean | 76 | NOT Lemma 5.1: removing slack δ in a spectral bound — consumed by Spectrum/Obstruction (detecting-character route) |
| Growth/Floor.lean | 63 | NOT Lemma 5.1: floor-rounded exponent limits — imported only by Main.lean, no theorem consumed (dead) |
| Polynomial/Inequalities.lean | 126 (brief said 131) | `toScalarProfile`, `meanExponent_le_three_quarters`, `exponent_sum_le_nine_quarters` |
| Arithmetic/CharacterRounding.lean | 122 | rounding k_d = ⌈d^ν⌉−1, exponent comparison with C = 2 |
| Arithmetic/RankBound.lean | 29 | `exactRankExponent_le_nine_quarters` |
| Main.lean (AS/) | 33 | `matrix_multiplication_cost_le`, `omega_le_nine_quarters` |

Grepped/skimmed only (statements, not proofs): `Convolution/Symmetry.lean:70–140`
(`meanExponent`, `convolutionProfile`, `_comm`, `_pos`, `_le`, `_one_left`),
`Character/Symmetrization.lean:25–35, 90–100` (`sixfoldProduct`, `symmetrizedProfile`),
`Character/Dot.lean:120–135, 160–172` (`value_dotPairing`, `value_matrixMultiplication`),
`Character/Existence.lean:20–35` (statement of `exists_detecting_character`),
`Arithmetic/RankExponent.lean:130–160` (`exactRankExponentSet`, `exactRankExponent`).

Consumers of the non-5.1 Growth files (`grep -rn` of each theorem name over `AS/`):
- `NormalizedProfile` → imported by Convolution/Symmetry.lean:4; `symmetrizedProfile_le_rank` used at Convolution/Symmetry.lean:129 (gives `rank_bound`). `mul_symmetrizedProfile_le_of_le`, `symmetrizedProfile_le_iff`, `one_le_symmetrizedProfile`, `symmetrizedProfile_product` have no consumer by name in `AS/`.
- `MultiplicativePower` → Character/Dot.lean:2 (import), `positiveMultiplicative_eq_rpow` used at Dot.lean:131 (`value_dotPairing = m^{pZ}`, i.e. p_X = log₂ f(2), §2.1). `positiveMultiplicative_is_rpow` unused.
- `PolynomialOverhead` → `le_of_pow_le_linear_mul_pow` at Character/Degeneration.lean:95; `le_of_eventually_pow_le_const_mul_pow` at Spectrum/Obstruction.lean:101; `exp_le_of_tendsto_log_div` at Entropy/Tag.lean:85.
- `SpectralLimit` → `spectral_coefficient_le_of_all_nat` at Spectrum/Obstruction.lean:153.
- `PermutationProduct` → imported at Character/Symmetrization.lean:1, but `grep -rln LegPermutation AS/` returns only PermutationProduct.lean itself: no consumer.
- `Floor` → imported only at AS/Main.lean:5; none of its four theorem names occurs anywhere else. Dead code; harmless.

No `attribute [...]` line occurs in any of my files (`grep -n attribute` over Growth/*.lean, Inequalities, CharacterRounding, RankBound, Main, ExponentComparison, Convolution/Symmetry: empty). Q7: nothing to report.

## 2. Argument reconstruction

### 2a. The hypotheses (Q1) — `ScalarProfile t`, Growth/Profile.lean:23–33, verbatim

```
structure ScalarProfile (t : ℝ) where
  value : ℕ → ℕ → ℝ
  positive : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 0 < value a b
  symmetric : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → value a b = value b a
  boundary : ∀ b : ℕ, 1 ≤ b → value 1 b = (b : ℝ)
  concave : ∀ a h : ℕ, 1 ≤ a → 2 ≤ h →
    value a (h - 1) + value a (h + 1) ≤ 2 * value a h
  tripling : ∀ a h : ℕ, 1 ≤ a → 1 ≤ h →
    3 * value a h ≤ value a (3 * h + a - 1)
  rank_bound : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    value a b ≤ ((a : ℝ) + (b : ℝ) - 1) ^ (1 / t)
```

Comparison with Lemma 5.1 ("P : ℕ²_{>0} → ℝ_{>0} symmetric, P(1,b) = b, (4.6) for a ≥ 1, b ≥ 2, (4.9) for a, h ≥ 1"):
- `positive` = codomain ℝ_{>0}, both indices ≥ 1. ✔
- `symmetric` on positive indices only. ✔ (weaker than global symmetry, i.e. at least as general as the paper)
- `boundary` for all b ≥ 1. ✔
- `concave` for a ≥ 1, h ≥ 2. `h − 1` is ℕ-subtraction but h ≥ 2 so h − 1 ≥ 1; it never reads index 0. ✔ Exactly (4.6).
- `tripling` for a, h ≥ 1. `3*h + a - 1` with a ≥ 1 is ≥ 3, no truncation. ✔ Exactly (4.9).
- `rank_bound` is (4.5)'s third clause, outside Lemma 5.1. The Lean Lemma 5.1 (`ScalarProfile.diagonal_fourth_power_lower`, Profile.lean:78–104) does not use it. Its only use is Profile.lean:115, at the diagonal (a = b = n), giving (2n−1)^{1/t}.
- Index 0: nothing constrains `value 0 _` or `value _ 0`, and the proof never needs them. The one place a 0 index shows up is `Tendsto (fun h => P a h / h)` (ConcaveSlopes.lean:102, Profile.lean:42), where P(a,0)/0 = 0 in Lean. That is one term of a sequence and has no effect on a limit.
- No hypothesis outside the paper's. **Nothing beyond the lemma's own hypotheses (plus `0 < t` for the final comparison) appears anywhere in the chain.** This answers Q3: Recurrence.lean's side conditions are `1 ≤ n` on indices and the base values `1 ≤ g 1`, `1 ≤ D 1`, and both base values are derived from `boundary` (Profile.lean:95–102). Floor.lean is not on this chain.

The polynomial profile instantiates all six fields (Inequalities.lean:97–107) under `0 < meanExponent` only. `boundary` needs ht (Symmetry.lean:132–139: (b^{6t})^{1/(6t)} = b). `rank_bound` casts `(a+b−1 : ℕ)` with `Nat.cast_sub` (1 ≤ a+b), which is correct.

### 2b. The Lean proof of Lemma 5.1 (Q2, Q4). It is not the paper's proof verbatim.

The paper works with the finite increment Δ_{a,a} and telescopes over h = a..4a−2. The Lean replaces Δ_{a,a} by the limiting row slope g_a = inf_h Δ_{a,h} = lim_h P(a,h)/h and iterates tripling infinitely often. The scalar recurrence afterwards is the same. Chain:

1. `antitone_nat_of_succ_le` + `concave` ⇒ the increments n ↦ P(a,n+2)−P(a,n+1) are antitone (Profile.lean:43–50). This is the paper's "Δ_{a,h} nonincreasing".
2. `increment_nonneg_of_antitone` (ConcaveSlopes.lean:46–56): a nonnegative sequence with antitone increments has no negative increment. It uses `positive`. `exists_nonneg_limit_of_antitone_increments` (:79–92): increments converge to their infimum g ≥ 0, and u_n/n → g by Cesàro (`tendsto_div_nat_of_tendsto_increments`, :68–75). `exists_concave_slope_limit` (:96–119) is the positive-index version with g ≤ every increment.
3. `ScalarProfile.exists_row_slope(s)` (Profile.lean:39–74): a choice of g_a for every a ≥ 1, with g_a ≤ Δ_{a,h} for all h ≥ 1 and P(a,h)/h → g_a.
4. `shiftedTripling_profile_lower` (ProfileSlopes.lean:52–63): 3^j P(a,h) ≤ P(a, h_j) where h_{j+1} = 3h_j + (a−1). `shiftedTriplingIndex_cast` (:41–49) gives the exact solution h_j + c/2 = 3^j (h + c/2). `profile_le_affine_slope` (:67–103) divides by 3^j and lets j → ∞: P(a,h) ≤ (h + (a−1)/2)·g_a. `profile_diagonal_le_slope` (:124–132) takes h = a: **P(a,a) ≤ ((3a−1)/2)·g_a**, i.e. g_a ≥ H_a := 2D_a/(3a−1). This is the paper's "Δ_{a,a} ≥ H_a", obtained from a stronger statement (g_a ≤ Δ_{a,a}).
5. `diagonal_increment_of_slope_lower` (ProfileSlopes.lean:136–145): D_{n+1} = P(n+1,n+1) = [P(n+1,n+1) − P(n+1,n)] + P(n,n+1) (symmetry) ≥ g_{n+1} + [P(n,n) + g_n]. This is **(5.1) with g in place of Δ**: D_n + g_n + g_{n+1} ≤ D_{n+1}.
6. `growthRecurrence_step_real` (Recurrence.lean:18–43), carried by `growthRecurrence_induction(_shifted)` (:65–118). Simultaneous induction on n: G_n ≤ g_n and ((3n−1)/2)G_n ≤ D_n, with G_{n+1} = (1+1/(3n))G_n and G_1 = 1. The step is pure algebra. From the upper bound (3n+2)/2·g_{n+1} ≥ D_{n+1} ≥ (3n−1)/2·G + G + g_{n+1} we get (3n/2) g_{n+1} ≥ ((3n+1)/2) G, so g_{n+1} ≥ (1+1/(3n))G. This is the paper's recurrence H_a ≥ (1+1/(3(a−1)))H_{a−1}. The Lean carries the bound on g rather than on H, which is equivalent and slightly stronger. Base: g_1 ≥ 1 comes from step 4 at a = 1 with P(1,1) = 1 (Profile.lean:98–102); D_1 = 1.
7. `growthProduct` (Product.lean:17–19) = ∏_{m=1}^{n}(1+1/(3m)), indexed so that growthProduct n = G_{n+1}. This is (5.2). `one_add_recip_three_cube_lower` (:34–41) proves **1+1/a ≤ (1+1/(3a))³ for real a > 0** by `nlinarith`, after writing 1/a = 3x with x = 1/(3a): (1+x)³ − 1 − 3x = 3x² + x³ ≥ 0. Note that this covers all real a > 0, not just integers m ≥ 1. `growthProduct_cube_lower` (:44–61) telescopes this to (n+1) ≤ G_{n+1}³.
8. `diagonal_fourth_power_lower` (Recurrence.lean:140–163): (n+1)·G ≤ ((3n+2)/2)·G ≤ D_{n+1} (uses (3a−1)/2 ≥ a), hence (n+1)⁴ ≤ (n+1)³G³ ≤ D_{n+1}³. `_of_one_le` (:166–179) reindexes. `ScalarProfile.diagonal_fourth_power_lower` (Profile.lean:78–104) proves **n⁴ ≤ P(n,n)³ for all n ≥ 1**. With P > 0 this is exactly P(n,n) ≥ n^{4/3}, the paper's conclusion. It is not weaker.
9. `diagonal_exponent_le_three_quarters` (ExponentComparison.lean:43–74): from (2n−1)^{1/t} ≤ (2n)^{1/t}, cubing gives n⁴ ≤ 2^{3/t}·n^{3/t} for all n ≥ 1. `rpow_exponent_le_of_nat_bound` (:19–39) then gives 4 ≤ 3/t, so t ≤ 3/4 (multiplying by t > 0). `ScalarProfile.exponent_le_three_quarters` (Profile.lean:108–116) needs `0 < t` and nothing else.

**Q4 (off-by-one).** The Lean never forms the finite sum Σ_{h=a}^{4a−2}. The constant (3a−1)/2 arises as the fixed-point offset of the affine map h ↦ 3h + (a−1): h + c/2 with c = a−1 at h = a gives a + (a−1)/2 = (3a−1)/2 (ProfileSlopes.lean:131, `ring`). This agrees with the paper's count: P(a,4a−1) − P(a,a) is Σ_{h=a}^{4a−2} Δ_{a,h}, which is (4a−2) − a + 1 = 3a−1 terms. The script asserts that count. Both derivations give 2D_a ≤ (3a−1)·(slope), so the constant 3 and the exponent 4/3 are right. The numerics in §2d also show that (3a−1)/2·∏ is attained exactly by the least feasible table, so an off-by-one in either direction would have been visible.

**Q5 (the limit, and t ≤ 0).** The limit is done as described in step 9: an explicit for-all-n comparison lemma with C = 2^{3/t} > 0, evaluated at n = 2^k. `ht : 0 < t` is used for `0 ≤ 1/t` (rpow monotonicity, :49) and for the final multiplication (:70–73). `meanExponent_le_three_quarters` (Inequalities.lean:110–114) splits on `0 < meanExponent`. In the other branch meanExponent ≤ 0 ≤ 3/4 and the conclusion is immediate. In fact `meanExponent_nonneg` (Symmetry.lean:78) means that branch is only t = 0, where `toScalarProfile` would be ill-posed (1/(6t) = 0 in Lean). The split is harmless because the conclusion is trivially true there.

### 2c. From t ≤ 3/4 to ν ≤ 9/4 (Q6, rounding)

10. `exponent_sum_le_nine_quarters` (Inequalities.lean:117–120): meanExponent = (pX+pY+pZ)/3 (Symmetry.lean:76), so pX+pY+pZ ≤ 9/4, for EVERY `χ : Character`, with no hypothesis.
11. `exactRankExponent_le_nine_quarters` (RankBound.lean:18–25). `value_matrixMultiplication (by omega)` (Dot.lean:165–168, needs 0 < m, discharged from 2 ≤ d) gives χ(T_d) = d^{pX+pY+pZ}. `Real.rpow_le_rpow_of_exponent_le` needs 1 ≤ d, which is supplied at RankBound.lean:25 from 2 ≤ d. This is (2.4) at d: λ(T_d) ≤ d^{9/4}. ✔ Q6.
12. `exponent_le_of_detecting_characters` (CharacterRounding.lean:79–91): for d ≥ 2, `exists_nat_sub_one_le_lt` (:22–29) gives k = ⌈d^ν⌉₊ − 1 with d^ν − 1 ≤ k < d^ν (correct also when d^ν is an integer). `detect` gives χ with k ≤ χ(T_d), and `bound` gives χ(T_d) ≤ d^{9/4}. So d^ν − 1 ≤ d^{9/4} for all d ≥ 2. The character is chosen per d (and per k), which is what the paper does.
13. `rpow_exponent_le_of_nat_sub_one_bound` (:33–44) feeds `rpow_exponent_le_of_nat_bound` with **C = 2** for **every n ≥ 1**:
    - d ≥ 2: d^ν ≤ d^τ + 1 ≤ 2d^τ, since d^τ ≥ 1 when τ = 9/4 ≥ 0.
    - d = 1: 1 ≤ 2·1 (`simp`).
    - The comparison lemma (ExponentComparison.lean:19–39) gets C > 0 from n = 1. If ν > τ it picks k > log C/((ν−τ)log 2) and evaluates at n = 2^k: k(ν−τ)log 2 ≤ log C, a contradiction.
    This is honest for ALL d, not only large d. It replaces the paper's "take logs and let d → ∞" by a cofinal subsequence argument, which is equivalent.
14. `exactRankExponent` (RankExponent.lean:142–146) = sInf{log_n R(T_n) : n ≥ 2}. `detect` is `exists_detecting_character` (Existence.lean:25–27), whose statement matches Lemma 2.2's use: k < d^ν ⇒ ∃χ, k ≤ χ(T_d). Its proof belongs to another reader. AS/Main.lean:28–29: ω ≤ ν (`omega_le_exactRankExponent`, Exponent.lean:105) composed with ν ≤ 9/4. Main.lean:21–25 is the uniform-constant cost form.

### 2d. Independent computation

Script: `<scratch>/lemma51_check.py`, output in `lemma51_check.out` beside it. Run with `python3 -I`. scipy is not installed, so (iii) is not done with an LP library. Instead it uses an exact lattice argument:
- Every constraint has the form P(x) ≥ (nonnegative combination of other P values), plus the fixed equalities P(1,b) = P(b,1) = b and symmetry.
- The feasible set is therefore closed under pointwise min, so it has a pointwise least element. That element simultaneously solves the LP "minimize P(a,a)" for every a.
- It is computed by monotone iteration: replace each row by its least concave majorant, apply tripling lower bounds, symmetrize, repeat to convergence.
- The script checks that the limit is feasible.
- Truncating to [1..N]² drops constraints, so a truncated value is a lower bound on the true minimum.

```
== (i) elementary inequality and product bound (exact rationals)
m=1..10^6 violations of (1+1/(3m))^3 >= 1+1/m: 0
identity (3m+1)^3 - 27m^2(m+1) == 9m+1 for m<=1000: True
a=1..2000 violations of (prod_{m<a}(1+1/(3m)))^3 >= a: 0 ; H_2000^3/2000 = 1.4041164642751998
== (ii) profiles on [1..N]^2, N=60
sqrt(ab(a+b-1)): positive=True symmetric=True P(1,b)=b=True concave(4.6)=True tripling(4.9)=True
   min P(a,a)/a^(4/3): 1.000000 at a=1; over a>=2: 1.374730 at a=2; paper-argument steps hold: True
a*b: all hypotheses True; min ratio 1.000000 at a=1; over a>=2: 1.587401 at a=2; steps hold: True
a+b-1+(a-1)(b-1)/3: all hypotheses True; min ratio 1.000000 at a=1; over a>=2: 1.322834 at a=2; steps hold: True
a+b-1: positive/symmetric/boundary/concave True, tripling(4.9)=False [first violations (2,1),(2,2),(2,3); 570 total]
   min ratio 0.506616 at a=60  (growth fails, as it must without tripling)
== (iii) least feasible P(a,a)
N=12: a=1..4 equal to the proof bound; a>=5 lower (truncation: 4a-1 > 12), a=11: 22.12 < a^{4/3}=24.46, a=12: 0
N=48 and N=120 (identical):
  a   minP(a,a)  a^(4/3)  ratio   (3a-1)/2*prod_{m<a}(1+1/(3m))
  1    1.0000    1.0000  1.0000   1.0000
  2    3.3333    2.5198  1.3228   3.3333
  3    6.2222    4.3267  1.4381   6.2222
  4    9.5062    6.3496  1.4971   9.5062
  5   13.1070    8.5499  1.5330  13.1070
  6   16.9767   10.9027  1.5571  16.9767
  7   21.0822   13.3905  1.5744  21.0822
  8   25.3990   16.0000  1.5874  25.3990
  9   29.9082   18.7208  1.5976  29.9082
 10   34.5947   21.5443  1.6057  34.5947
 11   39.4459   24.4638  1.6124  39.4459
 12   44.4513   27.4731  1.6180  44.4513
```

Findings from the computation:
- (1+1/(3m))³ − (1+1/m) = (9m+1)/(27m³) > 0 exactly.
- For a ≤ 12 the hypotheses force D_a ≥ a^{4/3}, as the lemma says.
- Once the table is large enough to contain index 4a−1 (N ≥ 48 here), the least feasible diagonal **equals the proof's intermediate bound (3a−1)/2·∏_{m<a}(1+1/(3m)) exactly**. So steps 4–7 are tight under these hypotheses: the constant 3a−1 and the recurrence factor are sharp. Since ∏ ~ c·a^{1/3}, the least diagonal grows like a^{4/3}. The exponent 4/3 is the best these hypotheses can give, so t ≤ 3/4 (hence 9/4) is exactly what Lemma 5.1 can deliver, not an artifact of a loose step.
- At N = 12 the hypotheses do NOT force growth for a ≥ 5: tripling from row a reaches column 4a−1 > 12, and those constraints fall outside the table. This is a truncation effect. The Lean quantifies over all of ℕ, so it does not arise there.
- a+b−1 satisfies everything except tripling, and its diagonal is 2a−1 ≪ a^{4/3}. Tripling is the hypothesis that does the work.

## 3. Definitions checked

| Lean name | file:line | what it is | matches paper? | note |
|---|---|---|---|---|
| `ScalarProfile t` | Growth/Profile.lean:23 | the six fields quoted above | yes: Lemma 5.1 hyps + (4.5) rank clause | no extra field; index 0 unconstrained and unused |
| `shiftedTriplingIndex c h` | ProfileSlopes.lean:19 | h_0 = h, h_{j+1} = 3h_j + c | n/a (formalization device) | c = a−1 (ℕ, a ≥ 1, cast checked :118) |
| `growthProduct n` | Product.lean:17 | ∏_{m=1}^{n}(1+1/(3m)) = G_{n+1} | (5.2) | — |
| `meanExponent` | Convolution/Symmetry.lean:76 | (pX+pY+pZ)/3 | t of (4.4) | ≥ 0 (:78) |
| `convolutionProfile a b` | Convolution/Symmetry.lean:109 | (∏ over 6 leg orders of χ(C(a,b)))^{1/(6t)} | profile (4.4) | definitions of sixfoldProduct/C(a,b) belong to readers D/E |
| `symmetrizedProfile t T` | Character/Symmetrization.lean:94 | sixfoldProduct^{1/(6t)} | (4.4) | — |
| `exactRankExponent` | Arithmetic/RankExponent.lean:146 | sInf{log_n R(T_n) : n ≥ 2} | ν | lower bound 2 (:149) |
| `toScalarProfile` | Polynomial/Inequalities.lean:97 | the polynomial profile as a ScalarProfile | "the profile satisfies all hyps of Lemma 5.1" | inputs (concavity, tripling) are reader E's |

## 4. Escalations (all resolved; none blocking)

1. **The proof route differs from the paper (resolved, sound).** The Lean uses the limiting row slope g_a = inf_h Δ_{a,h} with infinitely iterated tripling (ProfileSlopes.lean:67–132), where the paper uses Δ_{a,a} and one tripling step with a finite telescope. Both give D_a ≤ ((3a−1)/2)·slope, and g_a ≤ Δ_{a,a}, so the Lean's inequality chain is valid and needs the same hypotheses. Two things only the Lean route needs: a limit object, and `positive`, used to make g_a ≥ 0 and well defined. `positive` is a hypothesis of Lemma 5.1 (ℝ_{>0}), so this adds nothing. The numerics confirm that the constants coincide with the paper's.
2. **Docstring numbering drift (cosmetic).** Profile.lean:11, :21, :106, Product.lean:7, :16, ProfileSlopes.lean:8 and ConcaveSlopes.lean:10, :94 say "Section 6 / Lemma 6.1". The paper has §5 / Lemma 5.1. Probably an earlier draft's numbering; the statements match §5's content.
3. **Dead or unused code (harmless).** `Growth/Floor.lean`: no consumer in `AS/`, imported only by AS/Main.lean:5. `Growth/PermutationProduct.lean`: imported by Symmetrization.lean:1, but `LegPermutation` is not referenced elsewhere. Also unused: `positiveMultiplicative_is_rpow`, four NormalizedProfile lemmas, `profile_exponent_le_three_quarters`, `three_mul_diagonal_exponent_le_nine_quarters`, `exponent_le_of_integer_rounding_of_pos`, `exponent_le_of_detecting_character_exponents`. Not a soundness issue; worth knowing when sizing the trusted route.
4. **t = 0 branch (resolved).** `meanExponent_le_three_quarters` (Inequalities.lean:110–114) settles t ≤ 0 trivially, and since meanExponent ≥ 0 that branch is only t = 0. If a character had t = 0, the 9/4 bound for it would still hold trivially (pX+pY+pZ = 0). No case is hidden.
5. **`bound` quantifies over every `Character` (CharacterRounding.lean:82).** It is discharged unconditionally by `exponent_sum_le_nine_quarters`. So the whole headline rests on (a) `Character` really being the class Lemma 2.2 produces, and (b) concavity and tripling (the `toScalarProfile` inputs) holding for every such χ. Those are other readers' scope (A/D/E). My part adds no assumption.
6. **Brief line count.** The brief lists Polynomial/Inequalities.lean as 131 lines; `wc -l` gives 126. The cited `exponent_sum_le_nine_quarters` is at :117 as stated.

## 5. Verdict and what I did not read

**Verdict:** For my part, the Lean proves exactly Lemma 5.1: same hypotheses, none extra, conclusion n⁴ ≤ P(n,n)³ ⇔ P(n,n) ≥ n^{4/3}. It uses a sound variant of the paper's argument (limiting slopes instead of Δ_{a,a}) with the same constants (3a−1)/2 and 1+1/(3(a−1)). The a → ∞ and d → ∞ limits are done honestly for all a, d ≥ 1 through a 2^k exponent-comparison lemma (C = 2^{3/t} and C = 2). Independent computation confirms the elementary inequality, the product bound, and that the hypotheses force exactly the proof's bound, which grows like a^{4/3}.

Not read: the proofs of concavity (4.6) and tripling (4.9) for the polynomial profile (`convolution_concavity_tag`, `Sector.convolution_tripling_tag`, `finite_product_concavity/tripling` — reader E); the definitions of `Character`, `sixfoldProduct` beyond its statement, `convolution`, `convolution_rankAtMost`; the proof of `exists_detecting_character` / Spectrum/Obstruction.lean; Arithmetic/Exponent.lean and RankExponent.lean beyond the lines cited; the challenge statement and top-level `Main.lean` outside `AS/`.
