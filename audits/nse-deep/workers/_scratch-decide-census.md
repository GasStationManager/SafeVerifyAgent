# Kernel-numeral / `decide` census — `Euler/EulerProof.lean`

- **Target**: `/home/gsm/.openclaw/workspace/repos/NSE/Euler/EulerProof.lean` (20,756 lines; OpenAI `NavierStokesAndEuler` @ `f9e8bc5`)
- **Method**: read-only source analysis (grep/regex/Python). No file under `repos/NSE` was modified. `lake build` was **not** run (no built Mathlib, disk pressure), so all claims are *source-level*; kernel cost is argued from the standard Lean 4 kernel reduction model, not measured.
- **Threat model**: kernel-level recomputation — (a) `Decidable` instance reduction forced by `decide`, (b) GMP-backed Nat/Int numeral evaluation (`Nat.pow/div/mod/gcd/beq/ble`, huge literals, `norm_num` certificates the kernel must recheck).

---

## 1. Every `decide` site (40 of 40)

`grep -n decide` returns exactly **40** lines, and **all 40 are the tactic `by decide`**. There is:
- no `native_decide` (0 hits),
- no `decide (` / `Decidable.decide` term application (0 hits),
- no `decide_eq_true_eq`-style *simp-lemma* use of the word `decide` (0 hits),
- no occurrence of `decide` as a substring of some other identifier (all 40 lines were read individually; each is a real `by decide` term).

The single `Decidable` hit in the file (L11389, `[DecidableEq ι]` on `finite_product_bound`) is an **instance binder** — SIMP-LEMMA-ARG class, no kernel decide.

| Line | Declaration | Tactic / term text | Proposition decided | Class | Kernel cost |
|---|---|---|---|---|---|
| 5781 | `besselWeight_six_le_pure_six` (L5768) | `exact (by decide : Even 6).pow_abs (ξ i)` | Even (6:ℕ) | TRIVIAL-DECIDE | Nat.even instance → `Nat.decEq (6 % 2) 0`; kernel GMP mod on 6. Search space 1. |
| 10394 | `terminal_poincare` (L10365) | `simp only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_eq_mul]` | (2:ℕ) ≠ 0 | TRIVIAL-DECIDE | `instDecidableNot (Nat.decEq 2 0)` → `Nat.beq 2 0`. Max numeral 2. |
| 15729 | `triangular_ray_formula` (L15680) | `simp only [sub_self, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, sub_zero] at...` | (2:ℕ) ≠ 0 (exponent of zero_pow) | TRIVIAL-DECIDE | as above; max numeral 2. |
| 15930 | `triangular_ray_difference_bound` (L15872) | `simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at herr` | (2:ℕ) ≠ 0 (exponent of zero_pow) | TRIVIAL-DECIDE | as above; max numeral 2. |
| 16073 | `scaled_ray_entry_identity` (L16066) | `simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>` | (2:ℕ) < 3 (Fin 3 mk proof) | TRIVIAL-DECIDE | `Nat.decLt 2 3`→`Nat.ble 3 2`; the surrounding `from rfl` also forces defeq `(⟨2,_⟩:Fin 3) = (2:Fin 3)`, i.e. kernel whnf of `Fin.instOfNat` → `2 % 3`. Fin 3 → 3 cases. |
| 16272 | `scaled_velocity_entry_identity` (L16265) | `simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>` | (2:ℕ) < 3 (Fin 3 mk proof) | TRIVIAL-DECIDE | same as L16073. |
| 16425 | `scaled_unprojected_entry_identity` (L16413) | `simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>` | (2:ℕ) < 3 (Fin 3 mk proof) | TRIVIAL-DECIDE | same as L16073. |
| 16615 | `velocity_rhs_error` (L16579) | `have h45 : Θ ^ 4 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by decide)` | (4:ℕ) ≤ 5 | TRIVIAL-DECIDE | `Nat.decLe`→`Nat.ble 4 5`, GMP O(1). |
| 16665 | `velocity_rhs_error` (L16579) | `have h2 : Θ ^ 2 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` | (2:ℕ) ≤ 12 | TRIVIAL-DECIDE | Nat.ble 2 12. |
| 16666 | `velocity_rhs_error` (L16579) | `have h4 : Θ ^ 4 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` | (4:ℕ) ≤ 12 | TRIVIAL-DECIDE | Nat.ble 4 12. |
| 16667 | `velocity_rhs_error` (L16579) | `have h6 : Θ ^ 6 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` | (6:ℕ) ≤ 12 | TRIVIAL-DECIDE | Nat.ble 6 12. |
| 16668 | `velocity_rhs_error` (L16579) | `have h7 : Θ ^ 7 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` | (7:ℕ) ≤ 12 | TRIVIAL-DECIDE | Nat.ble 7 12. |
| 16669 | `velocity_rhs_error` (L16579) | `have h8 : Θ ^ 8 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` | (8:ℕ) ≤ 12 | TRIVIAL-DECIDE | Nat.ble 8 12. |
| 16670 | `velocity_rhs_error` (L16579) | `have h11 : Θ ^ 11 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)` | (11:ℕ) ≤ 12 | TRIVIAL-DECIDE | Nat.ble 11 12. |
| 16928 | `controlled_velocity_relative_error` (L16887) | `have hh := pow_le_pow_right₀ hΘ (show 5 ≤ 21 by decide)` | (5:ℕ) ≤ 21 (explicit `show`) | TRIVIAL-DECIDE | Nat.ble 5 21. |
| 17335 | `frame_cross_numerator_error` (L17321) | `have h24 : Θ ^ 2 ≤ Θ ^ 4 := pow_le_pow_right₀ hΘ (by decide)` | (2:ℕ) ≤ 4 | TRIVIAL-DECIDE | Nat.ble 2 4. |
| 17942 | `frame_error_polynomial_bounds` (L17913) | `have hh := hp 0 (by decide)` | (0:ℕ) ≤ 40  (side goal of `hp n (hn : n ≤ 40)`, L17936) | TRIVIAL-DECIDE | Nat.ble 0 40. |
| 17950 | `frame_error_polynomial_bounds` (L17913) | `have hρb : ρ ≤ 1 / 2 := by have hh := hp 5 (by decide); dsimp [ρ]; nlinarith only [hh, hMb]` | (5:ℕ) ≤ 40  (`hp`, L17936) | TRIVIAL-DECIDE | Nat.ble 5 40. |
| 17951 | `frame_error_polynomial_bounds` (L17913) | `have hηb : η ≤ 1 / 2 := by have hh := hKp 29 (by decide); dsimp [η]; nlinarith only [hh, hMb]` | (29:ℕ) ≤ 40 (`hKp`, L17937) | TRIVIAL-DECIDE | Nat.ble 29 40. |
| 17952 | `frame_error_polynomial_bounds` (L17913) | `have hAb : 210 * e * Θ ^ 2 ≤ 1 := by have hh := hp 2 (by decide); nlinarith only [hh, hMb]` | (2:ℕ) ≤ 40  (`hp`) | TRIVIAL-DECIDE | Nat.ble 2 40. |
| 17953 | `frame_error_polynomial_bounds` (L17913) | `have hEb : dE ≤ 1 := by have hh := hεp 4 (by decide); dsimp [dE]; nlinarith only [hh, hMb]` | (4:ℕ) ≤ 40  (`hεp`, L17947) | TRIVIAL-DECIDE | Nat.ble 4 40. |
| 17955 | `frame_error_polynomial_bounds` (L17913) | `have h4 := hp 4 (by decide)` | (4:ℕ) ≤ 40  (`hp`) | TRIVIAL-DECIDE | Nat.ble 4 40. |
| 17956 | `frame_error_polynomial_bounds` (L17913) | `have h5 := hp 5 (by decide)` | (5:ℕ) ≤ 40  (`hp`) | TRIVIAL-DECIDE | Nat.ble 5 40. |
| 17957 | `frame_error_polynomial_bounds` (L17913) | `have h31 := hKp 31 (by decide)` | (31:ℕ) ≤ 40 (`hKp`) | TRIVIAL-DECIDE | Nat.ble 31 40. |
| 17970 | `frame_error_polynomial_bounds` (L17913) | `have h9 := hp 9 (by decide)` | (9:ℕ) ≤ 40  (`hp`) | TRIVIAL-DECIDE | Nat.ble 9 40. |
| 17971 | `frame_error_polynomial_bounds` (L17913) | `have h6 := hεp 6 (by decide)` | (6:ℕ) ≤ 40  (`hεp`) | TRIVIAL-DECIDE | Nat.ble 6 40. |
| 17976 | `frame_error_polynomial_bounds` (L17913) | `have h8 := hεp 8 (by decide)` | (8:ℕ) ≤ 40  (`hεp`) | TRIVIAL-DECIDE | Nat.ble 8 40. |
| 17980 | `frame_error_polynomial_bounds` (L17913) | `have h9 := hp 9 (by decide)` | (9:ℕ) ≤ 40  (`hp`) | TRIVIAL-DECIDE | Nat.ble 9 40. |
| 17981 | `frame_error_polynomial_bounds` (L17913) | `have h33 := hKp 33 (by decide)` | (33:ℕ) ≤ 40 (`hKp`) | TRIVIAL-DECIDE | Nat.ble 33 40. |
| 17982 | `frame_error_polynomial_bounds` (L17913) | `have h6 := hp 6 (by decide)` | (6:ℕ) ≤ 40  (`hp`) | TRIVIAL-DECIDE | Nat.ble 6 40. |
| 17983 | `frame_error_polynomial_bounds` (L17913) | `have h4 := hεp 4 (by decide)` | (4:ℕ) ≤ 40  (`hεp`) | TRIVIAL-DECIDE | Nat.ble 4 40. |
| 17987 | `frame_error_polynomial_bounds` (L17913) | `have hh := hεp 4 (by decide)` | (4:ℕ) ≤ 40  (`hεp`) | TRIVIAL-DECIDE | Nat.ble 4 40. |
| 18344 | `scalar_coefficient_bounds` (L18324) | `· have hh : \|t\| ^ 3 ≤ \|t\| ^ 4 := pow_le_pow_right₀ (le_of_not_ge ht) (by decide)` | (3:ℕ) ≤ 4 | TRIVIAL-DECIDE | Nat.ble 3 4. |
| 18529 | `controlled_stage_references` (L18488) | `have hpow21 : Θ ^ 21 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)` | (21:ℕ) ≤ 40 | TRIVIAL-DECIDE | Nat.ble 21 40. |
| 18530 | `controlled_stage_references` (L18488) | `have hpow29 : Θ ^ 29 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)` | (29:ℕ) ≤ 40 | TRIVIAL-DECIDE | Nat.ble 29 40. |
| 18890 | `target_compression_order40` (L18873) | `have hh := hp 5 (by decide)` | (5:ℕ) ≤ 40  (`hp`, L18888) | TRIVIAL-DECIDE | Nat.ble 5 40. |
| 18894 | `target_compression_order40` (L18873) | `have hh := hp 6 (by decide)` | (6:ℕ) ≤ 40  (`hp`, L18888) | TRIVIAL-DECIDE | Nat.ble 6 40. |
| 18919 | `target_compression_order40` (L18873) | `have hm := hp 2 (by decide)` | (2:ℕ) ≤ 40  (`hp`, L18888) | TRIVIAL-DECIDE | Nat.ble 2 40. |
| 19804 | `source_neighbor_error_summable` (L19785) | `pow_le_pow_right₀ hp (by decide)` | (4:ℕ) ≤ 7 | TRIVIAL-DECIDE | Nat.ble 4 7. |
| 20168 | `source_good_interval_cost_summable` (L20150) | `(by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_right₀ hp (by decide : 5 ≤ 7))` | (5:ℕ) ≤ 7 (explicit ascription) | TRIVIAL-DECIDE | Nat.ble 5 7. |

### 1.1 Class tally

| Class | Count |
|---|---|
| TRIVIAL-DECIDE | **40** |
| NUMERAL-DECIDE (kernel must evaluate real numeral arithmetic) | **0** |
| SIMP-LEMMA-ARG (`Decidable` plumbing only) | 1 non-`decide` hit (L11389 `[DecidableEq ι]`) |
| OTHER | 0 |

### 1.2 Shape of the 40 sites

Four syntactic families, nothing else:

1. **`m ≤ n` on ℕ literals — 33 sites.** All are the side goal of `pow_le_pow_right₀` (`Θ^m ≤ Θ^n`) or of a local helper `hp/hKp/hεp (n : ℕ) (hn : n ≤ 40)` (declared at L17936-17937, L17947, L18888). Decided by `Nat.decLe` → `Nat.ble a b`, which the Lean 4 kernel implements with a GMP fast path. **Largest number the kernel touches: 40.** Search space: 1 comparison each.
2. **`(2 : ℕ) ≠ 0` — 3 sites** (L10394, L15729, L15930), the exponent side condition of `zero_pow`. `instDecidableNot (Nat.decEq 2 0)` → `Nat.beq 2 0`. Largest number: 2. Note: these `by decide` terms sit *inside a `simp only [...]` lemma list*, but the proof term is still elaborated and kernel-checked, so they are genuine (trivial) decides, **not** mere simp configuration.
3. **`(2 : ℕ) < 3` — 3 sites** (L16073, L16272, L16425), the `Fin 3` membership proof in `show (⟨2, by decide⟩ : Fin 3) = 2 from rfl`. `Nat.decLt` → `Nat.ble 3 2`. The enclosing `from rfl` additionally forces the kernel to whnf the `Fin.instOfNat` chain for `(2 : Fin 3)`, i.e. reduce `2 % 3`. Search space `Fin 3` → 3 inhabitants; largest number: 3.
4. **`Even (6 : ℕ)` — 1 site** (L5781, `besselWeight_six_le_pure_six`), used as `(… : Even 6).pow_abs (ξ i)`. Mathlib's ℕ parity instance goes through `Nat.even_iff`, so the kernel reduces `6 % 2 = 0` behind a `decidable_of_iff` wrapper. Largest number: 6.

**No `decide` in this file ranges over a large finite type, a `Fintype` product, a `Finset` enumeration, or a numeral bigger than 40.**

---

## 2. `norm_num` census and sampling

`grep -n norm_num` → **260 lines**. 155 of them carry at least one integer literal. Programmatic maximum of every literal appearing on *any* `norm_num` line: **6425** (L6019, `four_dimensional_H6_algebra`). There is **no `norm_num` line in the file with a literal ≥ 10^4**.

42 sampled sites, spread from L129 to L20728 (36 evenly spaced by index over the 260 hits, plus the 6 largest-literal `norm_num` sites):

| Line | Declaration | Text | Largest literal on the line |
|---|---|---|---|
| 129 | `sum_inv_choose_le_three` (L126) | `\| zero => norm_num` | — |
| 2766 | `smoothFieldLp_translation_hasDerivAt` (L2717) | `· filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht` | 1 |
| 5636 | `real_three_dimensional_sobolev` (L5633) | `embeddingConstant 3 2 (by norm_num) * (2 * Real.pi) ^ k *` | 3 |
| 5778 | `besselWeight_six_le_pure_six` (L5768) | `norm_num [besselWeight, EuclideanSpace.norm_sq_eq]` | — |
| 6312 | `pointwise_le_L2_third_derivatives` (L6304) | `norm_num` | — |
| 6479 | `eLpNorm_cover_chart` (L6472) | `norm_num` | — |
| 6917 | `cylinder_pointwise_le_H3` (L6894) | `(mul_nonneg (show 0 ≤ embeddingConstant 4 3 (by norm_num) from norm_nonneg _) (by norm_nu...` | 25 |
| 7206 | `product_word_L2_le` (L7190) | `have hc : 0 ≤ 64 * lowDerivativeConstant period := mul_nonneg (by norm_num) (lowDerivativ...` | 64 |
| 7763 | `coordinateCommutator_pointwise_le` (L7732) | `have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn` | 2 |
| 8087 | `pointwise_le_L2_second_derivatives` (L8081) | `(show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)` | 3 |
| 8275 | `coordinateDerivative_tensor_bound` (L8269) | `apply L.opNorm_le_bound (by norm_num)` | — |
| 8702 | `mixedProductConstant_nonneg` (L8699) | `(mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)))` | — |
| 8777 | `list_product_pointwise_le` (L8734) | `(mul_nonneg (by norm_num : (0 : ℝ) ≤ 85) (cylinderEmbeddingConstant_nonneg period)))` | 85 |
| 9778 | `finite_set_integral_norm_le` (L9772) | `(by norm_num) (hf.restrict K).1` | — |
| 11202 | `rawBump_pos_zero` (L11201) | `apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> norm_num` | — |
| 11498 | `shift_one_bound` (L11485) | `_ = _ := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num` | 2 |
| 11679 | `innerCutoff_gevrey` (L11673) | `simpa only [innerCutoff, show (16 : ℝ) * 4 = 64 by norm_num,` | 64 |
| 11948 | `profile_gevrey` (L11913) | `(40 * (δ ^ 2)⁻¹) 3 (10 * (δ ^ 2)⁻¹) hBi (by norm_num) (by positivity) hn hi n t` | 40 |
| 12220 | `source_residual_budget` (L12212) | `norm_num` | — |
| 13489 | `riccati_upper_bound` (L13475) | `· norm_num` | — |
| 14174 | `equation30_global_positive` (L14161) | `have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num` | 2 |
| 14381 | `equation30_prefix_monotone` (L14371) | `have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num` | 2 |
| 15745 | `triangular_ray_kernel_bound` (L15733) | `simp only [abs_mul, abs_of_nonneg hβ, abs_of_nonneg hd, abs_of_nonneg (by norm_num : (0 :...` | 2 |
| 16317 | `normalized_velocity_entry_error` (L16277) | `norm_num [normalizedVelocityEntry, idealVelocityEntry, Fin.ext_iff] <;>` | — |
| 16846 | `ray_controlled_velocity_error` (L16796) | `norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]` | 2 |
| 17363 | `frame_cross_numerator_error` (L17321) | `have hNr := abs_product_difference hN hr (by norm_num : \|(1 : ℝ)\| ≤ 1) hrabs` | 1 |
| 17554 | `quotient_error_half_denominator` (L17546) | `norm_num` | — |
| 17634 | `ideal_frame_absolute_bounds` (L17611) | `have hh := mul_le_mul hεsmall hzupper hz (by norm_num : (0 : ℝ) ≤ 1 / 4)` | 4 |
| 18104 | `frame_renewal_order40` (L18003) | `have hpressure := pressure_ratio_error hΘ hη hηsmall hj (by norm_num : (0 : ℝ) < 1)` | 1 |
| 18639 | `early_forward_exponential_suppression` (L18566) | `have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)` | 6 |
| 19324 | `sourceParameterExponent_relative_tendsto_zero` (L19286) | `· have h := stage_sq_div_real_power_tendsto_zero J hJ1 5 (by norm_num)` | 5 |
| 19855 | `source_prior_error_summable` (L19847) | `C 4 (1 / 4) 0 hC (by norm_num) (by norm_num) (by norm_num) A` | 4 |
| 20062 | `source_time_width_eventually_contracts` (L20057) | `(by norm_num : (0 : ℝ) < 1 / 2)` | 2 |
| 20259 | `base_horizon_tendsto_zero` (L20257) | `have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 498)).const_mul (6 * J ^ 2)` | 498 |
| 20471 | `polynomial_logs_uniformly_absorbed` (L20448) | `have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)` | 2 |
| 20728 | `source_activation_ode_guards` (L20705) | `norm_num only [mul_one, sqrt_one, div_one] at htime` | — |
| 6019 | `four_dimensional_H6_algebra` (L6017) | `(6425 * embeddingConstant 4 3 (by norm_num)) *` | 6425 | (added: top-literal site)
| 20268 | `base_core_volume_cost_tendsto_zero` (L20265) | `have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2498)).const_mul (6 * J ^ 2)` | 2498 | (added: top-literal site)
| 20272 | `base_core_volume_cost_tendsto_zero` (L20265) | `have hid : (-2498 : ℝ) = 1000 + (-1000) * 3 + (-498) := by norm_num` | 2498 | (added: top-literal site)
| 8716 | `tensor_list_product_term_le` (L8704) | `have hK : 0 ≤ 1024 * 1024 * (85 * cylinderEmbeddingConstant period) := mul_nonneg (by nor...` | 1024 | (added: top-literal site)
| 8776 | `list_product_pointwise_le` (L8734) | `(mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024*1024)` | 1024 | (added: top-literal site)
| 20224 | `first_stage_coefficient_error_tendsto_zero` (L20218) | `have h₁ := (base_power_decay T (-500) 61 10 (by norm_num)).const_mul 8` | 500 | (added: top-literal site)

### 2.1 Is any numeral in this file big enough to matter?

**No.** Evidence:

- Largest literal anywhere in the file: **320000000** (3.2 × 10^8), at L18479-18481 (`stabilityConstant`, `stabilityConstant_ge`). It is a **coefficient in an ℝ-valued definition/inequality**, discharged by `nlinarith only [hh]` from `(1:ℝ) ≤ exp 6` (L18482-18484). The kernel rechecks a linear-arithmetic certificate whose numerals are of order 10^8-10^9 — a handful of GMP ops on ≤ 30-bit numbers.
- Only **5 distinct literals ≥ 10^6** exist in the whole file: 320000000, 160000000, 30000000, 8000000, 1000000 (23 occurrences total, all as ℝ coefficients in the "order-40 smallness" bookkeeping around L16892-L19963). Even a pessimistic `nlinarith` cross-product (e.g. `1000000 * 30000000`) stays around 3 × 10^13 — far below any GMP concern.
- **Exponents are all small or symbolic.** Numeric `^` exponents: max 40 (21 sites, L17916 ff.), then 29, 21, 20, 17, 16, 12, ... The apparent giants `^ 1000` (L20216, L20240, L20252, L20266), `^ 2000` (L20252) and `^ 60` (L20222) are exponents of a **real variable `x`** inside `Tendsto`/`rpow` statements. They are never applied to a numeral base, so the kernel never computes `b ^ 1000`.
- The only "combinatorial" numerals — `5461` (L7225/L7235) and `85` (L7655/L7665) — come from `∑ n ∈ Finset.range 7, ∑ _w : Fin n → Fin 4, A`. The proofs (L7235-7238, L7665-7668) rewrite the cardinality **symbolically** via `Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin` and then `norm_num [Finset.sum_range_succ]`. The kernel therefore checks `4^0 + … + 4^6 = 5461` (max intermediate 4096); it **never enumerates** `Finset.univ : Finset (Fin 6 → Fin 4)` (4096 elements) — that would have required `decide`/`rfl` on the Finset, which does not happen.

### 2.2 Top 10 distinct integer literals in the file

| # | Literal | Occurrences | First lines | Declaration at first hit |
|---|---|---|---|---|
| 1 | `320000000` | 2 | 18479, 18481 | stabilityConstant |
| 2 | `160000000` | 3 | 16925, 18519, 18542 | controlled_velocity_relative_error |
| 3 | `30000000` | 8 | 17925, 17926, 17994, 17995, 18024, 18025 | frame_error_polynomial_bounds |
| 4 | `8000000` | 2 | 16892, 18531 | controlled_velocity_relative_error |
| 5 | `1000000` | 8 | 17916, 17935, 18007, 18492, 18877, 18887 | frame_error_polynomial_bounds |
| 6 | `883420` | 1 | 17979 | frame_error_polynomial_bounds |
| 7 | `200000` | 6 | 16592, 16664, 16815, 16944, 16949, 16953 | velocity_rhs_error |
| 8 | `17490` | 1 | 17954 | frame_error_polynomial_bounds |
| 9 | `10000` | 3 | 16582, 16799, 16927 | velocity_rhs_error |
| 10 | `6425` | 1 | 6019 | four_dimensional_H6_algebra |

(Literals were extracted with `(?<![\w.])(\d[\d_]*)(?!\w)` over all 20,756 lines, so this includes literals inside statements, `def`s and doc-comments, not just proofs.)

---

## 3. Kernel-relevant construct grep

| Pattern | Count (lines) | Lines / note |
|---|---|---|
| `native_decide` | 0 | — **none** |
| `Nat.pow` | 0 | — none |
| `Nat.gcd` | 0 | — none |
| `Nat.mod` | 0 | — none |
| `Nat.div` | 0 | — none |
| `%` (mod operator, any type) | 0 | — none anywhere in the file |
| `Nat.beq` / `Nat.ble` (explicit) | 0 | — none |
| `decide (` / `Decidable.decide` | 0 | — none; every decide is the tactic `by decide` |
| `decide_eq_true_eq` / `decide_eq_true` in simp sets | 0 | — none |
| `by decide` | 40 | 5781, 10394, 15729, 15930, 16073, 16272, 16425, 16615, 16665-16670, 16928, 17335, 17942, 17950-17953, 17955-17957, 17970, 17971, 17976, 17980-17983, 17987, 18344, 18529, 18530, 18890, 18894, 18919, 19804, 20168 (= all 40 `decide` hits) |
| `Decidable` / `DecidableEq` | 1 | 11389 only — `[DecidableEq ι]` instance **binder** on `finite_product_bound`; pure plumbing, SIMP-LEMMA-ARG-like, no kernel decide |
| `interval_cases` | 0 | — none |
| `simp_arith` | 0 | — none |
| `omega` | 228 | 111, 118-120, 123, 140, 157, ... 20597, 20612, 20658, 20668, 20672 (spread over whole file) |
| `norm_num` | 260 | 129 ... 20728; 155 of those lines carry a literal, max literal on any of them = **6425** (L6019) |
| `norm_num [` (with simp set) | 17 | 5778, 6984, 7237, 7667, 8063, 9959, 12011, 16074, 16126, 16273, 16317, 16353, ... |
| `Finset.sum` / `∑` | 177 | 851-853, 898, 920, 1637, 3103, ... — all over *abstract* index types or `Finset.range n` with symbolic `n` |
| `Finset.range` with an explicit numeral | 11 | 6971, 6974, 7228, 7235, 7657, 7665, 8300, 9946, 9949, 12007, 12016 — bounds are 3+1, 4, 7 only |
| `Finset.Icc/Ico/Iio/Iic` with a numeral | 0 | — none |
| `Finset.prod` | 12 | 5889, 6048, 6232, 6858, 7116, 8209, 8750, 11371, 11408, 11661, 11668, 11714 — abstract |
| `from rfl` (rfl on a term/numeral) | 9 | 5853, 6003, 6281, 8058 (`(-6:ℤ) = -(6:ℤ)` etc.), 12809 (lambda defeq), 16073, 16272, 16425 (`(⟨2,_⟩:Fin 3) = 2`), 20233 (`(61:ℕ) = 60+1`) |
| `by rfl` | 0 | — none |
| `nlinarith` / `linarith` / `positivity` | 433 | 433 / 713 / 379 lines — the real proof engine of the numeric part; certificates are rational-coefficient ℝ arithmetic |

Notable absences that matter for the threat model: **`native_decide` = 0**, **`%` = 0**, **`Nat.pow`/`Nat.div`/`Nat.mod`/`Nat.gcd` = 0**, **`interval_cases` = 0**, **`decide (` = 0**. The file contains no explicit modular / gcd / big-power arithmetic at all.

---

## 4. Bottom line — kernel numeral risk in `Euler/EulerProof.lean`

1. All 40 `decide` sites are TRIVIAL-DECIDE: 33 are `m ≤ n` on ℕ literals with `n ≤ 40`, 3 are `(2:ℕ) ≠ 0`, 3 are `2 < 3` for a `Fin 3` index, 1 is `Even (6:ℕ)`. **NUMERAL-DECIDE count: 0.**
2. Every one reduces to a single GMP-accelerated `Nat.ble`/`Nat.beq`/`Nat.mod` on numbers ≤ 40, i.e. O(1) kernel work; total added kernel time for all 40 is microseconds.
3. Worst kernel-cost `decide` sites are L16073 / L16272 / L16425 (`scaled_ray_entry_identity` L16066, `scaled_velocity_entry_identity` L16265, `scaled_unprojected_entry_identity` L16413), only because the `by decide` is wrapped in `show (⟨2, by decide⟩ : Fin 3) = 2 from rfl`, which additionally forces `Fin.instOfNat` unfolding (`2 % 3`) — still trivial. Runner-up: L5781 (`Even 6`, one `decidable_of_iff` unfold + `6 % 2`).
4. `norm_num` is used 260 times but only ever on small rationals: the biggest literal on any `norm_num` line is 6425 (L6019); the biggest literal in the file is 320000000 (L18479/L18481) and it appears as an ℝ coefficient for `nlinarith`, not as a `decide`/`Nat` computation.
5. **Verdict: this file poses essentially no Lean-kernel numeral or `Decidable`-reduction risk.** Its checking cost is dominated by ordinary term-level elaboration of ~1227 declarations plus 433 `nlinarith` / 713 `linarith` / 379 `positivity` certificates — none of which forces large numeral recomputation. Any soundness concern about this file must be sought in its *statements* (definitions, hypotheses, `sorry`/axiom surface), not in kernel-forced computation.
