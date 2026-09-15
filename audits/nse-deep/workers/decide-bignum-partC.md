# decide-bignum Part C — Does the Lean KERNEL have to compute binomial coefficients / factorials?

Scope: read-only audit of `Euler/EulerProof.lean` (clone of openai/NavierStokesAndEuler @ f9e8bc5 at
`/home/gsm/.openclaw/workspace/repos/NSE`). **No `lake build` was run** (no built Mathlib on this box).
Source reading only. Mathlib lemma existence/signatures were cross-checked against an on-disk Mathlib
source tree at `/tmp/junk_packages_w4/mathlib` (toolchain `v4.29.0`); the repo pins
`leanprover/lean4:v4.34.0-rc2` + mathlib rev `85e3a25e006c35636f0e53b0e9296caca2685bc0`
(`lake-manifest.json:22-25`), so name checks are *near-version*, not exact-version. Flagged where it matters.

Bottom line first: **the kernel never has to evaluate a nontrivial `Nat.choose` or factorial numeral.**
Every step is symbolic (rewrites by `Nat.choose_*` lemmas, `omega`/`linarith`/`nlinarith` over choose/factorial
terms treated as opaque atoms). The only closed numeral factorial in the whole repository is `Nat.factorial 0`
(`Euler/GevreyInverseMap.lean:119`); there is no closed-numeral `Nat.choose` term anywhere, and no
`native_decide` anywhere.

---

## 1. `le_choose_of_interior` — `Euler/EulerProof.lean:108`

Verbatim (108-123):

```lean
theorem le_choose_of_interior (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      by_cases hk1 : k = 1
      · simp [hk1]
      by_cases hkn' : k = n
      · subst k
        simp
      have hklt : k < n := by omega
      have hkp : 0 < k - 1 := by omega
      have hp := ih (k - 1) hkp (by omega)
      have hq := ih k hk hklt
      rw [Nat.choose_succ_left n k hk]
      omega
```

**Claim in words.** Any strictly-interior entry of Pascal's row `n` (`0 < k < n`) is at least `n`.
This is a true, standard fact (row `n` interior minimum is `C(n,1)=C(n,n-1)=n`).

**Vacuity / weakness.** Hypotheses are satisfiable for every `n ≥ 2`, so not vacuous. The bound `n ≤ C(n,k)`
is deliberately weak (true value can be exponential), but it is exactly what is needed for the `1/(n+1)`
per-term reciprocal bound in §2, so "weak" here is not "free": it is the sharp corner value at `k=1`.

**Proof mechanism (kernel view).**
| step | line | what it does | kernel numerals? |
|---|---|---|---|
| `induction n generalizing k` | 110 | reverts `k, hk, hkn`, induct on `n`, reintroduces | no |
| `| zero => omega` | 111 | `hkn : k < 0` is contradictory | no |
| `simp [hk1]` (k = 1) | 114 | `Nat.choose_one_right : n.choose 1 = n` (simp) | no — symbolic in `n` |
| `subst k; simp` (k = n) | 116-117 | `Nat.choose_succ_self_right : (n+1).choose n = n+1` (simp) | no — symbolic |
| `rw [Nat.choose_succ_left n k hk]` | 122 | Pascal: `(n+1).choose k = n.choose (k-1) + n.choose k` | no |
| `omega` | 123 | linear over ATOMS `n.choose (k-1)`, `n.choose k` with `hp, hq : n ≤ …` | no |

`Nat.choose_succ_left (n k : ℕ) (hk : 0 < k) : choose (n+1) k = choose n (k-1) + choose n k` exists
(`Mathlib/Data/Nat/Choose/Basic.lean:68`, checked in the on-disk tree). Note its own Mathlib proof ends in
`rfl` — but that `rfl` is *definitional unfolding of the recursion at symbolic `n`*, not numeral arithmetic.
`omega` atomises the two `choose` subterms; it does not evaluate them.

**Verdict: [OK]** — true statement, genuine inductive proof, fully symbolic; no numeral `choose` reaches the kernel.

---

## 2. `sum_inv_choose_le_three` — `Euler/EulerProof.lean:126`

Verbatim (126-147):

```lean
theorem sum_inv_choose_le_three (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) ≤ 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hsum : ∑ k ∈ range n, (1 : ℝ) / ((n + 1).choose (k + 1) : ℝ)
          ≤ n * (1 / (n + 1) : ℝ) := by
        calc
          _ ≤ ∑ _k ∈ range n, (1 / (n + 1) : ℝ) := by
            apply sum_le_sum
            intro k hk
            apply one_div_le_one_div_of_le hn
            exact_mod_cast le_choose_of_interior (n + 1) (k + 1)
              (by omega) (by have := mem_range.mp hk; omega)
          _ = _ := by simp
      have hquot : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hn]
        linarith
      rw [sum_range_succ', sum_range_succ]
      norm_num only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one]
      linarith
```

**Claim in words.** The reciprocal binomial row sum `∑_{k=0}^{n} 1/C(n,k)` is `≤ 3`, for all `n` including `n = 0`.
True: the two edge terms are `1` each, and the `n-1` interior terms are each `≤ 1/n` by §1, giving
`≤ 2 + (n-1)/n < 3`. (Actual max is `8/3` at `n = 3`; asymptote `2`.) Constant `3` is loose but not free —
it is the whole point of the convolution constant downstream.

**Vacuity.** None: no hypotheses at all, quantified over every `n : ℕ`.

**Proof mechanism (kernel view).**
- `| zero => norm_num` (129) is the only place a *closed* binomial can appear: the goal is
  `∑ k ∈ range (0+1), 1/((Nat.choose 0 k : ℝ)) ≤ 3`, i.e. after `Finset.sum_range_one` the term
  `1/((0:ℕ).choose 0 : ℝ)`. `Nat.choose_self` / `Nat.choose_zero_right` are `simp` lemmas, so this is
  discharged by rewriting, and even in the worst case the kernel would decide `Nat.choose 0 0 = 1` — O(1).
- The `succ` branch peels the two edges with `rw [sum_range_succ', sum_range_succ]` (145) and kills them with
  `norm_num only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one]` (146). This is an
  **explicit whitelist of symbolic choose rewrites** at symbolic index `n+1`; `norm_num only` with that list
  cannot start evaluating a binomial, because there is no numeral binomial in the goal.
- Interior terms: `one_div_le_one_div_of_le hn` (138, Mathlib `Algebra/Order/Field/Basic.lean:69`) plus
  `exact_mod_cast le_choose_of_interior (n + 1) (k + 1) …` (139-140). Side conditions `0 < k+1` and
  `k+1 < n+1` come from `omega` with `mem_range.mp hk`. Symbolic.
- Final `linarith` (147) combines `hsum`, `hquot` and the two `1`s. Symbolic.

**Verdict: [OK]** — true, non-vacuous, proof is symbolic; the only closed binomial the kernel could ever see is
`Nat.choose 0 0`.

**Downstream use (grep, whole repo).** `sum_inv_choose_le_three` is used exactly **once**:
`Euler/EulerProof.lean:239`, inside `majorant_convolution` (`Euler/EulerProof.lean:226`). `majorant_convolution`
in turn is used at `Euler/EulerProof.lean:410` (inside `sequence_product_majorant`,
`Euler/EulerProof.lean:387`) and at `Euler/GevreyProductLp.lean:83`. So the lemma is live, not dead code, and
it is what produces the constant `3` in `sequence_product_majorant`'s
`≤ 3 * A * B * majorant R (d₁ + d₂) n` (`Euler/EulerProof.lean:392`).

---

## 3. `choose_le_shifted` — `Euler/EulerProof.lean:150`

Verbatim (150-159):

```lean
theorem choose_le_shifted (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    n.choose k ≤ (n + d₁ + d₂).choose (k + d₁) := by
  calc
    n.choose k = n.choose (n - k) := (Nat.choose_symm hkn).symm
    _ ≤ (n + d₁).choose (n - k) := Nat.choose_le_add n d₁ (n - k)
    _ = (n + d₁).choose (k + d₁) := by
      apply Nat.choose_symm_of_eq_add
      omega
    _ ≤ (n + d₁ + d₂).choose (k + d₁) :=
      Nat.choose_le_add (n + d₁) d₂ (k + d₁)
```

**Claim in words.** Shifting the top index up by `d₁ + d₂` and the bottom index up by `d₁` cannot decrease the
binomial coefficient (given `k ≤ n`). True; the `n - k` symmetry trick is needed because raising only the top
index is monotone (`choose_le_add`), and the bottom shift is absorbed by symmetry
(`(n+d₁)-(n-k) = k+d₁`, discharged by `omega` at 157).

**Vacuity.** `k ≤ n` is the standard non-degeneracy hypothesis; satisfiable, not vacuous. Note the statement is
`≤` in `ℕ`, so it carries real content (it is not an artefact of truncated subtraction: `Nat.choose_symm`
requires `hkn`).

**Proof mechanism (kernel view).** Four `calc` steps, each a named Mathlib lemma applied at symbolic arguments:
`Nat.choose_symm` (`Choose/Basic.lean:197`), `Nat.choose_le_add` (`Choose/Basic.lean:348`, proved by induction
on the shift), `Nat.choose_symm_of_eq_add` (`Choose/Basic.lean:201`). The single tactic is `omega` on the index
identity `n + d₁ = (n - k) + (k + d₁)` — pure linear `ℕ` arithmetic over index variables, **no `choose` evaluation**.

**Verdict: [OK]** — symbolic, lemma-driven, no kernel numeral binomial.

---

## 4. `choose_ratio_le_inv` — `Euler/EulerProof.lean:162`

Verbatim (162-169):

```lean
theorem choose_ratio_le_inv (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2
      ≤ 1 / (n.choose k : ℝ) := by
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hle : (n.choose k : ℝ) ≤ (n + d₁ + d₂).choose (k + d₁) := by
    exact_mod_cast choose_le_shifted n k d₁ d₂ hkn
  apply (div_le_div_iff₀ (sq_pos_of_pos (lt_of_lt_of_le hc hle)) hc).2
  nlinarith
```

**Claim in words.** With `C = C(n,k) ≥ 1` and `D = C(n+d₁+d₂, k+d₁) ≥ C`, we have `C / D² ≤ 1 / C`.
True and essentially immediate: cross-multiplied it is `C·C ≤ 1·D²`, i.e. `C² ≤ D²`, from `hle`.
This is a *weak* inequality (it throws away the gain `D² / C²`), but weak in the safe direction — it is exactly
the reciprocal-binomial "gain" that §2 later sums.

**Vacuity.** Only `k ≤ n`; positivity of `C(n,k)` comes from `Nat.choose_pos` (`Choose/Basic.lean:116`).
Non-vacuous.

**Proof mechanism (kernel view).** `Nat.choose_pos`, `choose_le_shifted` (§3), `div_le_div_iff₀`
(`Algebra/Order/GroupWithZero/Unbundled/Basic.lean:1418`), `sq_pos_of_pos` (same file:519), then `nlinarith`.
`exact_mod_cast` on lines 165 and 167 pushes `ℕ`→`ℝ` casts over `Nat.cast_le`/`Nat.cast_pos`; casts of
`Nat.choose` terms stay **opaque cast atoms** — `push_cast` has no `Nat.choose` numeral evaluation rule and
there are no numerals here. `nlinarith` works on the atoms `(C : ℝ)`, `(D : ℝ)`. No kernel binomial arithmetic.

**Verdict: [OK]** — symbolic; the only risk word here (`nlinarith`) operates on cast atoms, not numerals.

---

## 5. `shifted_factorial_kernel_le` — `Euler/EulerProof.lean:172`

Verbatim (172-193):

```lean
theorem shifted_factorial_kernel_le (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
        ((n - k + d₂).factorial : ℝ) ^ 2
      ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 / (n.choose k : ℝ) := by
  have hlarge : k + d₁ ≤ n + d₁ + d₂ := by omega
  have hsub : n + d₁ + d₂ - (k + d₁) = n - k + d₂ := by omega
  have hfac : ((n + d₁ + d₂).choose (k + d₁) : ℝ) *
      ((k + d₁).factorial : ℝ) * ((n - k + d₂).factorial : ℝ) =
      ((n + d₁ + d₂).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hlarge
    rw [hsub] at h
    exact_mod_cast h
  have hC : ((n + d₁ + d₂).choose (k + d₁) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hlarge
  calc
    _ = ((n + d₁ + d₂).factorial : ℝ) ^ 2 *
        ((n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2) := by
      rw [← hfac]
      field_simp
    _ ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 * (1 / (n.choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left (choose_ratio_le_inv n k d₁ d₂ hkn) (sq_nonneg _)
    _ = _ := by ring
```

**Claim in words.** One Leibniz-convolution term of the squared-factorial (Gevrey-2) majorant is bounded by the
shifted majorant divided by `C(n,k)`. It is a true rearrangement: with `N = n+d₁+d₂`, `K = k+d₁`,
`K! · (N-K)! = N! / C(N,K)` (`Nat.choose_mul_factorial_mul_factorial`, `Choose/Basic.lean:143`), so
LHS `= C(n,k) · (N!)² / C(N,K)²`, and §4 gives `C(n,k)/C(N,K)² ≤ 1/C(n,k)`.

**Vacuity.** `k ≤ n` only; both index side conditions (`hlarge`, `hsub`) are `omega` facts about `ℕ` truncated
subtraction, both genuinely true (`hsub` needs `k ≤ n`). Non-vacuous.

**Proof mechanism (kernel view).**
| step | line | mechanism | kernel numerals? |
|---|---|---|---|
| `hlarge`, `hsub` by `omega` | 176-177 | linear index arithmetic | no |
| `Nat.choose_mul_factorial_mul_factorial hlarge` + `rw [hsub]` + `exact_mod_cast` | 181-183 | symbolic factorial identity, cast to `ℝ` | no |
| `Nat.choose_ne_zero hlarge` (`Choose/Basic.lean:127`) | 185 | nonzero denominator | no |
| `rw [← hfac]; field_simp` | 189-190 | algebraic rearrangement over cast atoms | no |
| `mul_le_mul_of_nonneg_left (choose_ratio_le_inv …) (sq_nonneg _)` | 191-192 | monotone multiply | no |
| `ring` | 193 | closing identity | no |

`field_simp`/`ring` manipulate `((… ).factorial : ℝ)` and `((… ).choose … : ℝ)` as opaque atoms; there is no
numeral factorial anywhere in the goal, so no kernel `Nat.factorial`/`Nat.choose` reduction is triggered.

**Verdict: [OK]** — true rearrangement, symbolic proof, no kernel factorial evaluation.
(One caveat that is *not* a kernel risk: the name "kernel" here is the author's word for an integral/convolution
kernel, not the Lean kernel.)

---

## Repo-wide census: closed-numeral binomials / factorials

Method: scanned all 2659 `.lean` files under the clone; 2004 lines mention `choose` / `factorial` /
`descFactorial`. Then filtered for terms whose arguments are **entirely numeric literals** (patterns:
`Nat.choose <lit> <lit>`, `<lit>.choose <lit>`, `Nat.factorial <lit>`, `<lit>.factorial`, `<lit>!`,
`descFactorial`/`ascFactorial` with literal args).

| # | site | line text | numeral |
|---|---|---|---|
| 1 | `Euler/GevreyInverseMap.lean:119` | `change ‖iteratedFDeriv ℝ 1 Y x‖ ≤ C * L^0 * (Nat.factorial 0 : ℝ)^2` | `0` |

That is the **only** closed-numeral factorial/binomial in the repository. **Biggest such numeral: `0`**
(`Nat.factorial 0 = 1`). There is **no** closed-numeral `Nat.choose` term textually anywhere; the only
implicit one is `Nat.choose 0 0` arising in the `| zero => norm_num` branch of `sum_inv_choose_le_three`
(`Euler/EulerProof.lean:129`), which is O(1).

Supporting negative results (grep, whole repo):
- `native_decide`: **0 occurrences** (repo-wide).
- `decide` occurrences are all of the form `by decide : 2 ≠ 0`, `by decide : 10 ≠ 0`, small `Fin`/index
  side conditions (e.g. `NavierStokes/ShapeTransition.lean:830`,
  `NavierStokes/PositiveAxisExistence.lean:622-625`, `NavierStokes/ActualInitialExcluded.lean:187`).
  None is applied to a `choose`/factorial term.
- All `Nat.choose_*` simp/rewrite uses are symmetry/edge lemmas at symbolic indices:
  `Nat.choose_zero_right`, `Nat.choose_self` (e.g. `Euler/EulerProof.lean:146,899,6123,6135,7644,11441`,
  `NavierStokes/AxisOperators.lean:48,345`, `Euler/ParameterWordProduct.lean:61`). No `Nat.choose_two_right`
  anywhere. No `Nat.choose` numeral appears under `norm_num`/`simp`/`decide`.
- `descFactorial`/`ascFactorial` uses are symbolic only, via named lemmas
  (`Nat.descFactorial_le_pow`, `Nat.descFactorial_succ`, `Nat.factorial_mul_ascFactorial`,
  `Nat.pow_succ_le_ascFactorial`): `NavierStokes/AxisEvaluation.lean:30-98,321,374,463`,
  `NavierStokes/AxisEvaluationAlgebra.lean:98-279`, `NavierStokes/VolterraAnalyticBounds.lean:448-451`,
  `Euler/GevreyGeneratingAlgebra.lean:81`.

## Threat-vector conclusion

For this block (`Euler/EulerProof.lean:108-193`) and for the repository as a whole, the **big-number /
kernel-blowup threat vector is not present**: no `Nat.choose` or `Nat.factorial` is ever forced to a concrete
numeral beyond `0`/`0 choose 0`. All combinatorial content is carried by symbolic Mathlib lemmas
(`choose_succ_left`, `choose_symm`, `choose_le_add`, `choose_symm_of_eq_add`,
`choose_mul_factorial_mul_factorial`, `choose_pos`, `choose_ne_zero`) plus linear/nonlinear arithmetic over
opaque cast atoms (`omega`, `linarith`, `nlinarith`, `field_simp`, `ring`).

Residual caveats (honest limits of this audit):
1. **Not compiled.** No `lake build` was possible, so I cannot confirm the tactic blocks actually close the
   goals or that every name resolves at mathlib rev `85e3a25e`. Name checks used a `v4.29.0` mathlib source
   tree; all five external names used in this block were found there with matching signatures.
2. `induction n generalizing k` (line 110) relies on core Lean reintroducing `hk`/`hkn` in the `succ` goal;
   the later `omega` calls (118-121) and `ih k hk hklt` presuppose that. This is standard behaviour but is a
   compile-time fact I could not execute.
3. This audit says nothing about whether these combinatorial lemmas are *used* to prove anything analytically
   meaningful about Euler; the file's own docstring at lines 97-101 states they "do not assert the analytic
   estimates needed to apply the implications to Euler". Treated as author evidence, not proof evidence,
   per the task instruction.
