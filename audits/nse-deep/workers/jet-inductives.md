# Worker report: jet inductives, well-founded recursions, kernel-numeral surface
# Target: NSE/Euler/EulerProof.lean (openai/NavierStokesAndEuler @ f9e8bc5)

Auditor: child `jet-inductives`. READ-ONLY. No file under `/home/gsm/.openclaw/workspace/repos/NSE`
was modified. No `lake build` (no built Mathlib on this box). Everything below is
source-level reading; every claim carries `file:line` against the ORIGINAL, non-stripped
file (I re-read every line I cite; the parent's first line list was off by ~49 lines and
I use my own).

## Scope

File: `Euler/EulerProof.lean`, 20755 lines (20756 with trailing split).

Exact declaration census (lines whose first token is a declaration keyword, `noncomputable`/
`private`/attribute prefixes allowed):

| kind | count |
|---|---|
| `theorem` | 996 |
| `def` (incl. 96 `noncomputable def`) | 219 |
| `abbrev` | 6 |
| `inductive` | 2 |
| `structure` | 1 |
| `lemma` | 1 |
| `instance` (explicit keyword at line start) | 2 |
| **total** | **1227** |

Other whole-file counts (regex on whole words): `axiom` 0, `macro` 0, `elab` 0, `syntax` 0,
`set_option` 0, `native_decide` 0, `unsafe` 0, `sorry` 0, `partial` 0 (the 40-odd `partial`
grep hits are all the identifier `partialDerivative`, e.g. 10836), `decide` 40,
`norm_num` 260 lines, `termination_by` 7.

Read coverage, honestly: **119 of 1227 declarations (9.7%) read line-by-line**
(90 theorems, 27 defs, 2 inductives). That is the whole assigned region plus its
consumers. Specifically, fully read:

* 2993-3060 (the three `hasDerivAt` lemmas the jet constructors consume),
* **3061-3480** — the entire jet block: both inductives and all 28 declarations in
  `EulerSpatialSobolevInverse.SpatialJet` / `.CoefficientJet`,
* 4544-4680 (`EulerPressureJetIdentities.SpatialJet.*`, 8 decls),
* 4680-5102 (`EulerJetProductBounds.*`, 27 decls: `levelNorm`, `boundLevel`, Leibniz/commutator
  convolution machinery, `pressure_level_recurrence`, `levelNorm_eq_zero_of_lt`),
* 5450-5485 + 5886-5950 + 6044-6110 (the *other* `sobolevNorm`/`embeddingConstant`, for the
  `attribute [local irreducible]` question),
* 6520-6570 (`standardDirection`, `iteratedFieldDerivative`, `liftSobolevNorm`),
* 7900-7966 (`compactSmoothJet` — the jet **producer**), 8455-8495, 9450-9545, 9900-9995,
  10000-10125, 10275-10312, 12960-12992 (jet **consumers**),
* 17915-17962 (a representative `by decide` cluster), and every one of the 40 `decide` lines.

Skimmed only (not verified): 5120-5182 (`pressure_gevrey_majorant`, read statement + proof
skeleton but not the imported `triangular_inverse_majorant`), 4972-5056
(`commutatorLevel_succ_le`/`commutatorLevel_le` — statements read, ~80 lines of calc skimmed).
Not looked at: the remaining ~1100 declarations of the file (Fourier/Schwartz Sobolev layer,
heat/viscous layer, packet constants, the `nlinarith` constant chains at 15000-20700).
A sibling worker covered the `decide`/numeral census file-wide (see Kernel-risk (2)).

## Per-declaration findings

Verdict tags: OK / UNCLEAR / KERNEL-RISK / SUSPICIOUS.

### The two inductive families

| name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `EulerSpatialSobolevInverse.SpatialJet` | EulerProof.lean:3064 | `inductive SpatialJet (directions : Fin 4 → LiftTangent) : ℕ → LiftL2 period → Type` with `zero (f) : SpatialJet .. 0 f` (3065) and `succ {n} {f} (derivatives : Fin 4 → LiftL2 period) (lower : ∀ i, SpatialJet .. n (derivatives i)) (hasDeriv : ∀ i, HasDerivAt (fun t => translation period (translationPath period (directions i) t) f) (derivatives i) 0) : SpatialJet .. (n+1) f` (3066-3070). I.e. a 4-ary tree of depth `n` whose every edge carries an *actual* strong L² translation-derivative witness. | Recursive: yes (`lower`). Indexed: yes, doubly — by `ℕ` (the order, `n → n+1`, non-uniform) and by `LiftL2 period` (the field, which *changes* along `succ`: parent index `f`, child index `derivatives i`). Nested: **no** — the recursive occurrence is under a plain function type `Fin 4 → _`, which is strictly positive and only makes the recursor take a function argument; there is no other inductive applied to `SpatialJet`. No constructor can be built without a genuine `HasDerivAt`, so the family is *not* junk-inhabitable above order 0. | OK |
| `EulerSpatialSobolevInverse.CoefficientJet` | EulerProof.lean:3073 | Same shape over `SmoothCoefficient period`; `succ`'s third field is `derivative_eq : ∀ i x, (derivatives i).coefficient x = fieldDerivative period (directions i) A.coefficient x` (3077-3078) — the child really is the directional derivative of the parent coefficient. | Identical structure to `SpatialJet`. Recursive, doubly indexed, not nested. | OK |

**Why `Type` and not `Prop` — precisely.** Both are declared `... → Type`, and this is
*required*, not decorative: real-valued functions are defined by recursion **on the jet
itself** — `SpatialJet.sobolevNorm : ... → ℝ` (3093), `CoefficientJet.productConstant : ... → ℝ`
(3196), `pressureConstant` (3283), `word : ... → LiftL2 period` (3393), `levelNorm` (4697),
`boundLevel` (4706). A `Prop`-valued inductive with 2 constructors admits no large
elimination, so none of these could exist. Consequences for the audit:

* Because the family lives in `Type`, its recursor is the *ordinary* `SpatialJet.rec` with a
  `Sort u` motive. This is **not** the dangerous "large elimination" case (that phrase names
  eliminating a `Prop` into `Type`, which Lean only allows for subsingletons). There is no
  singleton/subsingleton-elimination special case in play here at all.
* Because the jets are data, `Type`-valued recursion means **the kernel does iota-reduce these
  recursors** while checking the equation lemmas used by `rw`/`simp only` (see Kernel-risk (1)).
* Because they are data, two different jets over the *same* field are a priori different
  objects; the proof therefore needs, and has, `SpatialJet.word_unique` (4549) to show the
  *values* do not depend on the witness tree. Without that theorem the `Type`-valued choice
  would be a genuine soundness-of-statement hole. It is proved by
  `HasDerivAt.unique` + induction on the word length (4557-4561) — i.e. by uniqueness of strong
  derivatives, not by any structural coincidence. This is the single most important
  anti-junk theorem in the region.

### Jet operations and their bounds (3086-3474)

| name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `SpatialJet.truncate` | 3086 | order `n+1` jet → order `n` jet, same field | `match n, J` (3088-3090); structural on `J`, no `termination_by` needed | OK |
| `SpatialJet.sobolevNorm` | 3093 | jet → ℝ, `‖f‖` at leaves, `‖f‖ + ∑ i, (lower i).sobolevNorm` at nodes | structural `match J` (3094-3096) → compiled via `SpatialJet.rec`/`brecOn` | OK |
| `SpatialJet.nonneg` | 3098 | `0 ≤ J.sobolevNorm` | `induction J`, `norm_nonneg` + `Finset.sum_nonneg` | OK |
| `SpatialJet.value_norm_le` | 3105 | `‖f‖ ≤ J.sobolevNorm` | `cases J`; at `succ`, `le_add_of_nonneg_right` of the child sum | OK |
| `SpatialJet.truncate_norm_le` | 3112 | truncation does not increase the norm | induction on `n` generalizing `f`; `Finset.sum_le_sum` of the IH | OK |
| `SpatialJet.lower_norm_le` | 3122 | each child's norm ≤ parent's | `Finset.single_le_sum` + `le_add_of_nonneg_left` | OK |
| `SpatialJet.add` / `.sub` | 3131 / 3141 | jets of `f`,`g` at order `n` → jet of `f±g` | structural double `match`; the derivative witness is `(hJ i).add (hK i)` closed by `convert ... <;> first \| rfl \| (funext t; simp)` (3137-3138, 3147-3148) — the `rfl`/`simp` is about linearity of `translation`, not about numbers | OK |
| `SpatialJet.add_norm_le` / `.sub_norm_le` | 3150 / 3166 | triangle inequality in the jet norm | induction on `n`; `change` to the unfolded `sobolevNorm` (3160, 3176) then `calc` with `norm_add_le`/`norm_sub_le` and `Finset.sum_add_distrib` | OK |
| `CoefficientJet.truncate` | 3189 | as above | structural | OK |
| `CoefficientJet.productConstant` | 3196 | jet → ℝ, `A.bound` at leaves, `A.bound + ∑ i, (J.truncate.productConstant + (lower i).productConstant)` at nodes | **`termination_by n` (3202)** — WF recursion, see below | OK (odd, see note) |
| `CoefficientJet.productConstant_nonneg` | 3205 | `0 ≤ productConstant` | induction on `n`; `rw [productConstant]` (equation lemma) + `NNReal.coe_nonneg` | OK |
| `SpatialJet.multiply` | 3223 | given a coefficient jet and a field jet of the same order, produce the jet of `A.operator f` | **`termination_by n` (3233)**; the `hasDeriv` field is discharged by `A.product_hasDerivAt` (3012) — i.e. by an actual product rule, 4232 | OK |
| `SpatialJet.multiply_norm_le` | 3235 | `(multiply K J).sobolevNorm ≤ K.productConstant * J.sobolevNorm` | induction on `n`; `rw [multiply, sobolevNorm]`, `change`, then a `calc` that ends by `rw [← Finset.sum_mul, ← add_mul, CoefficientJet.productConstant]` — the crude constant of 3196 is exactly what makes this close | OK |
| `CoefficientJet.pressureConstant` | 3283 | `c⁻¹` at leaves, `c⁻¹ + ∑ i, truncate.pressureConstant c * (1 + (lower i).productConstant * truncate.pressureConstant c)` | **`termination_by n` (3291)** | OK |
| `CoefficientJet.pressureConstant_nonneg` | 3294 | `0 < c → 0 ≤ pressureConstant c` | induction + `inv_nonneg` | OK |
| `SpatialJet.solvePressure` | 3315 | coercive pressure solve lifted to jets: produces a jet of `A.pressure κ m c hc hpos f` of the same order | **`termination_by n` (3331)**; children are `solvePressure K₀ .. ((Jf i).sub (multiply (KA i) P₀))` (3328) — the differentiated equation; witness from `A.pressure_hasDerivAt` (3048) | OK |
| `SpatialJet.solvePressure_norm_le` | 3333 | `≤ K.pressureConstant c * J.sobolevNorm` | induction; the `calc` at 3361-3373 is exactly the commutator estimate that `pressureConstant`'s shape was designed for | OK |
| `SpatialJet.word` | 3393 | `J.word w` for `w : Fin n → Fin 4` = the iterated derivative along `w`; **returns `0` when the word is longer than the jet order** (3397: `\| _n + 1, .zero _ => 0`) | **`termination_by s` (3399)** — the measure is the *jet order*, not the word length | OK, but junk-valued: see Escalation E2 |
| `SpatialJet.word_zero` | 3402 | `J.word (w : Fin 0 → _) = f` | `rw [word]` | OK |
| `SpatialJet.word_succ` | 3406 | `(succ df lower hd).word w = (lower (w (Fin.last n))).word (Fin.init w)` | `rw [word]` | OK |
| `SpatialJet.word_hasDerivAt` | 3413 | **guarded** by `hn : n < s`: `J.word (Fin.cons i w)` really is the strong derivative of `J.word w` in direction `directions i` | induction on `n`; the `zero`-constructor cases are killed by `omega` from `n < s` (3420, 3424). This is where the junk branch is fenced off. | OK |
| `SpatialJet.wordSnocEquiv` | 3437 | `(Fin (n+1) → Fin 4) ≃ Fin 4 × (Fin n → Fin 4)` | `Fin.snoc_init_self` + `simp` | OK |
| `SpatialJet.sum_word_succ` | 3444 | re-indexing of the word sum | `Fintype.sum_equiv` + `Fintype.sum_prod_type` | OK |
| `SpatialJet.sobolevNorm_eq_sum_words` | 3458 | **`J.sobolevNorm = ∑ n ∈ range (s+1), ∑ w : Fin n → Fin 4, ‖J.word w‖`** | induction; `Finset.sum_range_succ'`, `sum_word_succ`, `Finset.sum_comm`. This ties the *recursive* norm to the *explicit* word sum, and is the second key anti-junk theorem: it would be false if `word` were junk for `|w| ≤ s`. | OK |

### Jet identities and the product/commutator layer (4549-5100)

| name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `word_unique` | 4549 | words are witness-independent (`f = g`, `n ≤ s`, `n ≤ t` ⟹ `J.word w = K.word w`) | induction + `HasDerivAt.unique` (4561) | OK — load-bearing |
| `word_mem_gradientSpace` / `word_mem_divergenceFreeSpace` | 4564 / 4577 | guarded by `hn : n ≤ s`; membership propagates to every valid word | induction + `gradientSpace_translation_derivative` / `divergenceFree_translation_derivative` applied to `word_hasDerivAt` | OK |
| `SpatialJet.map` | 4590 | a translation-commuting CLM `L` maps jets of `f` to jets of `L f` | structural `match J`; witness by `L.hasFDerivAt.comp_hasDerivAt` + `hL` | OK |
| `map_word` | 4601 | `(map L hL J).word w = L (J.word w)`, **unguarded** (holds even in the junk branch, since `L 0 = 0`) | `induction J generalizing n` | OK |
| `pressure_word_projected_equation` | 4615 | guarded `n ≤ s`; the projected Euler/pressure identity holds at every word | applies `word_unique` to the two `map`ped jets and `liftedPressure_equation` (4626-4632) | OK |
| `pressure_word_inverse` | 4636 | guarded; each pressure word equals the coercive inverse applied to source minus product commutator | `liftedPressure_unique` + the previous lemma | OK |
| `pressure_word_norm_le` | 4658 | guarded; `c⁻¹`-triangle estimate per word | rewrites by 4636 then `A.pressure_norm` | OK |
| `levelNorm` / `boundLevel` | 4697 / 4706 | order-`n` slice of the jet norm / coefficient bound; **junk `0` for `n > s`** (4701, 4710) | **`termination_by s` (4703, 4712)** | OK, junk-valued |
| `levelNorm_nonneg`, `boundLevel_nonneg` | 4716, 4728 | nonnegativity | `induction J`/`induction K`, `rw [levelNorm]` | OK |
| `levelNorm_eq_words` | 4740 | `levelNorm J n = ∑ w : Fin n → Fin 4, ‖J.word w‖` — **unguarded and still true**, because both sides are `0` past the order | `induction J generalizing n` | OK (this is why the junk convention is coherent) |
| `levelNorm_truncate`, `boundLevel_truncate` | 4751, 4769 | guarded `n ≤ s`; truncation does not change low levels | induction on `s` | OK |
| `levelNorm_add_le` | 4786 | level-wise triangle inequality | induction; `rw [SpatialJet.add, levelNorm, ...]` | OK |
| `leibnizConvolution` (+`_succ`, `_congr`, `sum_..._right/left`) | 4803, 4806, 4818, 4826, 4832 | `∑_{l≤n} C(n,l) A l * B (n-l)` and its binomial recurrence | `Finset.sum_choose_succ_mul` (4811) — Pascal, symbolic in `n`; no numerals | OK |
| `multiply_levelNorm_le` | 4841 | guarded `n ≤ s`: the sharp binomial Leibniz bound `levelNorm (multiply K J) n ≤ leibnizConvolution (boundLevel K) (levelNorm J) n` | induction on `n`; uses `_congr` + `boundLevel_truncate`/`levelNorm_truncate` to move between `K` and `K.truncate` (4867-4878), then `leibnizConvolution_succ` | OK |
| `word_add`, `sub_word` | 4894, 9474 | words are additive | induction on `s` | OK |
| `commutatorConvolution` (+ 4914, 4920, 4926, 4933) | 4911 | Leibniz convolution minus the `A 0 * B n` term | `Finset.sum_range_succ'` + `ring` | OK |
| `commutatorLevel` | 4940 | `∑ w, ‖(multiply K J).word w - A.operator (J.word w)‖` | plain def (no recursion) | OK |
| `sum_word_snoc`, `multiply_word_snoc` | 4945, 4952 | snoc re-indexing / the Leibniz split of a product word | `Equiv.sum_comp`; the second unfolds `multiply` at a `succ/succ` pair | OK |
| `commutatorLevel_succ_le`, `commutatorLevel_le` | 4972, 5005 | commutator level ≤ commutator convolution | ~80-line induction; **skimmed**, statements verified, calc chain not re-derived | UNCLEAR (coverage, not suspicion) |
| `pressure_level_recurrence` | 5057 | guarded `n ≤ s`: the triangular recurrence `levelNorm P n ≤ c⁻¹ (levelNorm J n + ∑_{l<n} C(n,l+1) boundLevel K (l+1) levelNorm P (n-l-1))` | `levelNorm_eq_words` → per-word estimate 4658 → `commutatorLevel_le` → `commutatorConvolution_eq_sum`; one `rfl` at 5075 that is pure delta of `commutatorLevel` | OK |
| `levelNorm_eq_zero_of_lt` | 5083 | `s < n → levelNorm J n = 0` — the junk convention stated as a theorem | induction on `s`, `rw [levelNorm]`, `Finset.sum_eq_zero` | OK |
| `pressure_gevrey_majorant` | 5120 | Gevrey majorant bound for the pressure solve, `∀ n` (unguarded conclusion) with hypotheses guarded by `≤ s` | at 5140 and 5166 the out-of-range case is discharged by `levelNorm_eq_zero_of_lt` + `majorant_nonneg`; the in-range case by 5057 and `triangular_inverse_majorant`. **The `∀ n` in the conclusion is therefore only informative for `n ≤ s`** — but the theorem is used exactly that way (5179-5181), and the hypotheses are correspondingly restricted, so this is book-keeping, not inflation. | OK (see E2) |

### Jet producers/consumers outside the block (sampled)

| name | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `compactSmoothJet` | 7911 | for a smooth compactly supported `f`, an order-`n` jet of `smoothFieldLp f` **exists** | structural recursion on `n` (`match n`, 7914-7920); each `hasDeriv` field is `translation_hasDerivAt_smoothFieldLp` (7901). **This is the inhabitation proof: jets are not vacuous hypotheses.** | OK |
| `compactSmoothJet_word` | 7931 | guarded `n ≤ s`: the jet's word is the classical iterated derivative | induction; `rw [compactSmoothJet, SpatialJet.word_succ]` | OK |
| `compactSmoothJet_sobolevNorm` | 7957 | `(compactSmoothJet ..).sobolevNorm = liftSobolevNorm period s f` — the jet norm **equals** the honest classical Sobolev norm (6564) | `sobolevNorm_eq_sum_words` + per-word norm identity 7948 | OK — key anti-vacuity |
| `jet_word_ae`, `jet_classical_memLp`, `jet_sobolevNorm_eq` | 8459, 8475, 8483 | guarded `n ≤ s`: any jet forces the classical derivatives of a smooth representative into L², with the same norm | induction using `word_hasDerivAt` + `translation_derivative_ae` | OK |
| `mollifyJet`, `mollifyJet_word`, `mollifyJet_sobolevNorm_tendsto` | 9455, 9461, 9491 | mollification of a jet is a jet, commutes with words, converges in jet norm | `SpatialJet.map` with `mollify_translation`; convergence via `sobolevNorm_eq_sum_words` + finite sums | OK |
| `word_H3_le_higher` | 9943 | `liftSobolevNorm 3 (∂_w f) ≤ 85 * liftSobolevNorm (m+3) f` | I re-derived the constant: `85 = ∑_{n<4} 4^n = 1+4+16+64`, the number of words of length ≤3 over 4 letters. The proof gets it from `Fintype.card_fun` + `norm_num [Finset.sum_range_succ]` (9958-9959). Constant is correct and not padded. | OK |
| `jet_word_pointwise_bound`, `jet_word_difference_bound`, `jet_sub_triangle`, `smoothMollifier_word_uniformCauchy`, `exists_smoothMollifier_word_uniform_limit`, `smoothMollifier_word_limit_ae`, `exists_continuous_representative` | 9963, 10008, 10027, 10044, 10079, 10092, 10110 | order `m+3` jets give uniform sup bounds on word `m`, hence uniform Cauchyness of mollifiers, hence continuous/smooth representatives | Sobolev embedding `vector_cylinder_pointwise_le_H3` + the `85` factor + completeness; the `3` in `m+3` is the embedding loss and is threaded consistently | OK |
| `exists_smooth_representative` | 10280 | if `U` has jets of **every** order (`J : ∀ s, SpatialJet period standardDirection s U`) then `U` has a `C∞` representative | words of all lengths uniformly Cauchy (10289-10291) → `cylinder_smooth_of_uniformCauchy_words`. Hypothesis is real data at every order, so this is not a cheap statement. | OK |
| `exists_smooth_pressure` | 10299 | all-order jets for `A` and `f` ⟹ the coercive pressure has a `C∞` representative | one line: `exists_smooth_representative` applied to `fun s => (J s).solvePressure (K s) ..` | OK |
| `pressure_shifted_weighted_bound` | 12971 | weighted (Gevrey) pressure bound in terms of `levelNorm`/`boundLevel` | reduction to the abstract `shifted_weighted_inverse` recurrence | OK |
| `standardDirection` | 6526 | `standardDirection i = coordinateEquiv (EuclideanSpace.single i 1)`, with `standardDirection 0 = (0,1)` (6529) and `standardDirection i.succ = (single i 1, 0)` (6535) | These four vectors are a basis of `LiftTangent = Vector3 × ℝ` (1087) — the angle direction plus the three spatial ones. So "all words over `Fin 4`" really is "all iterated partials on the 4-dimensional cylinder"; the jet does not secretly control only a subspace. | OK — checked because the smoothness conclusion at 10280 depends on it |
| `EulerSobolev.embeddingConstant`, `EulerSobolev.sobolevNorm` | 5456, 5472 | Fourier `Hˢ` norm of a Schwartz function and the `L²` norm of the reciprocal Bessel weight | **These are a *different* `sobolevNorm` from the jet one at 3093** (different namespace, argument `𝓢(Domain d, F)`). The `attribute [local irreducible] sobolevNorm embeddingConstant` at 5916 and 6074 therefore does **not** touch the jet norm. | OK — see Escalation E4 |

Verdict counts over the 119 declarations read line-by-line:
**OK 116, UNCLEAR 3 (4972, 5005 — skimmed calc chains; 5120 — depends on the unread
`triangular_inverse_majorant`), KERNEL-RISK 0, SUSPICIOUS 0.**

## Kernel-risk assessment

### (1) Recursive inductive types, recursors, `Acc.rec`, structure eta

**Does the kernel have to reduce a `SpatialJet.rec` application? Yes, but only trivially.**

* `induction J` / `cases J` (3100, 3107, 3115-3120, 3153-3159, 4606, 4718, 4742, 5085-5100, …)
  *build* `SpatialJet.rec`/`casesOn` terms. Type-checking such a term needs no iota-reduction:
  the minor-premise types are already stated at the constructors.
* Iota-reduction *is* forced where a definition-by-`match` is unfolded at a constructor:
  `rw [productConstant]` (3212), `rw [pressureConstant]` (3302), `rw [word]` (3403, 3411),
  `rw [multiply, sobolevNorm]` (3265), `rw [solvePressure, sobolevNorm]` (3374),
  `rw [levelNorm]` (4722, 4736, 4748, 4797, 5090, 5097), `rw [SpatialJet.add, levelNorm,…]` (4799),
  `rw [compactSmoothJet, SpatialJet.word_succ]` (7943), and the `simp only [multiply, sobolevNorm, …]`
  forms (3241, 3341, 4848, 4892, 4907, 9478, 9487). Each such step is **one** iota step on a
  *symbolic* constructor application (`SpatialJet.succ df lower hd` with `df`, `lower`, `hd`
  free variables) at depth 1. There is no concrete jet anywhere in the file — no term of the
  form `succ … (succ … (succ …))` with a literal order — so no recursor unfolding chain of
  length > 1 is ever demanded of the kernel. Cost: O(1) per site, a few hundred sites.
* `change` at 3160, 3176, 3266, 3375 makes the *kernel* check a defeq. In each case the goal
  was already rewritten by the equation lemma first, so what remains is beta/zeta/delta of
  `let K₀ := …` bindings (the bodies of `multiply`/`solvePressure` contain `let`s, 3323-3325).
  No `Acc.rec` is on that path.
* **`Acc.rec` / `WellFounded.fix`:** the 7 `termination_by` definitions (below) are compiled to
  `WellFounded.fix`. Every *use* of them in a proof goes through the generated equation lemmas
  (`rw [name]` / `simp only [name]`), i.e. through a `theorem`, never through a defeq check at
  closed arguments. Therefore **the kernel is never asked to unfold `Acc.rec` on a concrete
  accessibility proof in this file**, which is the expensive/fragile case. Caveat in Residue.
* **Large elimination:** not present in the dangerous sense. Both families are `Type`-valued
  (3064, 3073), so their recursors are ordinary large-motive recursors; nothing here eliminates
  a `Prop` into `Type`, and no `Subsingleton`/singleton-elimination shortcut is used.
* **Structure eta:** the only `structure` in the file is 1 declaration (not in this region); the
  jets are `inductive`, not `structure`, so no eta-for-structures is involved. `SmoothCoefficient`
  projections (`A.bound`, `A.coefficient`, …) are used constantly, but as projections of a
  variable, which is the standard path.
* **Nested/indexed subtlety worth naming:** `succ` changes the *field* index
  (`f ↦ derivatives i`) and the *order* index (`n ↦ n+1`) at once, so the family is a genuine
  indexed family, not a parameterised one. Lean handles this by an `.rec` with the indices as
  motive arguments; correctness of that is bog-standard. The one place where an index mismatch
  could hide a problem is `truncate` (3086, 3189), which pattern-matches on `n` *and* `J`
  simultaneously (`match n, J with | 0, _ => .zero A | _n+1, .succ …`) — I checked the
  index arithmetic by hand: at `n = _n+1` the argument has order `_n+2`, its `lower i` has
  order `_n+1`, and the recursive call returns order `_n`, matching the declared result type
  `CoefficientJet .. n A`. Correct.

### The 7 non-structural recursions

| # | def | file:line | `termination_by` | measure genuine? | who unfolds it |
|---|---|---|---|---|---|
| 1 | `CoefficientJet.productConstant` | 3196 | `n` (3202) | Yes. Calls are `(succ dA lower hd).truncate.productConstant` — `truncate` returns order `n` from order `n+1` (3189) — and `(lower i).productConstant` at order `n`. Both `n < n+1`. Not structural because `truncate J` is not a subterm of `J`, hence the explicit measure. | `rw [productConstant]` 3212; `rw [… CoefficientJet.productConstant]` 3274 |
| 2 | `SpatialJet.multiply` | 3223 | `n` (3233) | Yes, same pattern: recursive calls on `K.truncate`/`J.truncate` and on `(KA i)`/`(Jf i)`, all at order `_n` from `_n+1` (3230-3231). | `rw [multiply, …]` 3265; `simp only [multiply, …]` 3241; 4880, 4952-4970 |
| 3 | `CoefficientJet.pressureConstant` | 3283 | `n` (3291) | Yes (3288-3290, calls at order `n`). | `rw [pressureConstant]` 3302; 3384 |
| 4 | `SpatialJet.solvePressure` | 3315 | `n` (3331) | Yes: `solvePressure K₀ … J₀` and `solvePressure K₀ … ((Jf i).sub (multiply (KA i) P₀))` are all at order `_n` (3325, 3328); the argument is *built* (`sub`, `multiply`) rather than a subterm, which is exactly why a measure is needed. | `rw [solvePressure, …]` 3374; `simp only [solvePressure, …]` 3341 |
| 5 | `SpatialJet.word` | 3393 | **`s`** (3399) — the jet order, *not* the word length `n` | Yes, and note the subtlety: the recursion pattern-matches on `n` but recurses on `lower (w (Fin.last n))`, whose jet order is `s-1`. So `n` would *not* be a valid measure in the `zero`-jet branch and `s` is the right one. Decreasing genuinely: `s-1 < s`. | `rw [word]` 3403, 3411; then everything goes through `word_zero`/`word_succ` |
| 6 | `EulerJetProductBounds.levelNorm` | 4697 | `s` (4703) | Yes, same shape as `word`: recursion on `lower i` at order `s-1` (4702). | `rw [levelNorm]` 4722, 4736, 4748, 4797, 4799, 4880, 5090, 5097; `simp [levelNorm]` 4719, 4743, 4746, 4848 |
| 7 | `EulerJetProductBounds.boundLevel` | 4706 | `s` (4712) | Yes (4711). | `rw [boundLevel]` 4734, 4736; `simp [boundLevel]` 4731, 4848, 4892 |

So: 7/7 measures are genuine and I could see the decrease in the source in each case. Later
theorems *do* unfold all seven — dozens of times — but always via the equation lemmas
(`rw`/`simp only [name]`), which is the `WellFounded.fix_eq` route, not a kernel `Acc.rec`
reduction. No `decide`, `rfl`, or `Nat.rec`-style computation is ever performed *at* one of
these definitions with closed arguments.

### (2) Nat/GMP numeral arithmetic

In my region: essentially none. `Fin 4` is a *type index*, never enumerated by the kernel
(`Fintype.card_fun`/`Fintype.card_fin` are used symbolically, e.g. 3467-3468, 9958).
`Nat.choose` appears only as `(n.choose l : ℝ)` with `n`, `l` free variables (4804, 4916, 5063) —
Pascal's rule is applied as a lemma (`Finset.sum_choose_succ_mul`, 4811), never computed.
`Nat.factorial` likewise appears only under a cast with a variable argument (5144-5155).
The one concrete numeral I checked in this region is `85` at 9945, which I independently
re-derived as `1+4+16+64` and which the proof establishes with `norm_num [Finset.sum_range_succ]`
(9959): four additions and three tiny powers.

File-wide (delegated to a sibling child, report
`audits/nse-deep/workers/_scratch-decide-census.md`, and cross-checked by me against my own
grep of all 40 sites): all 40 `decide` uses are `by decide` on tiny goals —
33 of the form `m ≤ n` with `n ≤ 40` (e.g. `hp 5 (by decide)` at 17950 discharging
`5 ≤ 40` for the helper `hp (n : ℕ) (hn : n ≤ 40)` at 17936), 3 of `(2 : ℕ) ≠ 0`
(10394, 15729, 15930), 3 of `2 < 3` inside `(⟨2, by decide⟩ : Fin 3)` (16073, 16272, 16425),
1 of `Even (6 : ℕ)` (5781). Each is one `Nat.ble`/`Nat.beq`/`Nat.mod` on numbers ≤ 40 —
GMP is invoked, but on single-limb values. The largest integer literal anywhere in the file is
`320000000` (18479/18481), used as a real coefficient for `nlinarith`, not as a `Nat` the kernel
must exponentiate. `^1000`, `^2000` (20216-20266) are exponents applied to a real *variable*,
so no numeral is ever raised to a large power in a kernel-checked computation. Zero
`native_decide`, zero `Nat.pow/div/mod/gcd` calls, zero `%`.

**Conclusion for (2): the kernel's GMP path is exercised, but only on values ≤ 40. There is no
numeral computation in this file big enough for a GMP/bignum bug to be a plausible attack
surface, and no `decide` on a nontrivial `Decidable` instance.**

### (3) Custom metaprogramming

Confirmed for this file: `macro`/`elab`/`syntax`/`set_option`/`native_decide`/`axiom`/
`unsafe`/`partial` all **0** (whole-word regex over all 20755 lines; the `partial` hits are the
identifier `partialDerivative`, e.g. 10836).

**But the "zero" claim needs one qualification, and it is a finding:** the repo *does* use
`attribute` commands — 25 of them repo-wide (`grep -rn 'attribute \['`), 2 of them in this file:

* `Euler/EulerProof.lean:5916` and `:6074` — `attribute [local irreducible] sobolevNorm embeddingConstant`.
  These refer to `EulerSobolev.sobolevNorm` (5472, the Fourier `Hˢ` norm of a Schwartz map) and
  `EulerSobolev.embeddingConstant` (5456, `‖reciprocalWeightLp d s hs‖`), **not** to the jet norm
  at 3093. Purpose: from 5918 / 6076 onward the proofs are `gcongr`/`positivity`/`nlinarith`
  chains over products of these constants (e.g. 5918-5933, 6076-6091); marking them irreducible
  stops `simp`/`gcongr`/`positivity` from unfolding into `Lp` norms and Fourier multipliers, which
  is a *performance and goal-shape* device. It is not a soundness device and it cannot hide
  anything from the kernel: reducibility attributes are elaborator-only hints; the kernel ignores
  them entirely and delta-reduces whatever it needs. Note that the file itself then still writes
  `unfold embeddingConstant` / `unfold sobolevNorm` two lines later (5924-5925, 6082-6083), which
  is consistent (`unfold` uses equation lemmas, not reducibility) and shows the attribute is
  local scoping, not concealment. **Verdict: OK, but the repo-level statement "zero
  `set_option`" should be read as "zero `set_option`, 25 `attribute` commands".**
* Elsewhere in the repo (outside my scope, flagged for whoever owns it):
  `attribute [local instance] Classical.propDecidable` at
  `NavierStokes/ActualSignedPhysicalData.lean:22`, `PositiveTimeSignedData.lean:24`,
  `ActualParticularPhysicalData.lean:24`, `InitialPhysicalData.lean:28`. That makes *every*
  proposition "decidable" via `Classical.choice`. It is the standard trick for writing
  `if h : P then _ else _` in noncomputable definitions and is harmless for soundness, but it
  interacts with `decide`-style tactics (they cannot evaluate such an instance) and it is a
  `Classical.choice` dependency. `Euler/Solution.lean:41` also does
  `attribute [local instance] CompletePartialOrder.toSupSet`, and 8 files add
  `attribute [local irreducible] Parent.child initialParent` (e.g.
  `Euler/BaseFirstPacketChoice.lean:25`) — that one deserves a look by the worker who owns the
  packet-induction files, because making a *recursive tree accessor* irreducible is exactly the
  move you would make if you wanted `simp`/`decide` to stop discovering that the tree is
  degenerate. I have not checked it.

### Dependency-path status of this region

On the path, definitely not dead weight, on grep evidence:

* `SpatialJet`/`CoefficientJet` are referenced in **145 `.lean` files** across `Euler/`
  (`grep -rln 'SpatialJet\|CoefficientJet'`), including `Euler/PacketCylinderSpatialJet.lean`,
  `Euler/ComparatorUniformSpatialJets.lean`, `Euler/GevreyPressureTransport.lean`,
  `Euler/AllOrderLiftedCorrection.lean`.
* Within this file the chain is visible end-to-end: constructors (3064) → norms/ops (3093-3474)
  → per-word identities (4549-4676) → level bounds (4697-5100) → Gevrey majorant (5120) →
  jet producer (7911) → smooth representative (10280) → smooth pressure (10299) → weighted
  pressure bound (12971).
* The headline theorems live in `Euler/Solution.lean:33` (`euler_breakdown_R3`) and
  `Euler/Solution.lean:43` (`exists_compact_smooth_euler_singularity`), restated in
  `ComparatorChallenges/Euler.lean:85` and `:170`, with `Euler/EulerSingularity.lean:133`
  the underlying construction. A transitive reverse-dependency graph is being built by a
  sibling child (`audits/nse-deep/workers/_scratch-depgraph.md`); at the time of writing its
  result had not landed, so the reachability claim above rests on the name-occurrence chain
  I read myself, not on a computed closure. `exists_smooth_representative` (10280) and
  `exists_smooth_pressure` (10299) are precisely the shape the singularity construction needs
  (`∀ s, jet` ⟹ `C∞`), which is strong circumstantial evidence for on-path.

## Escalations

**E1 (highest value, cheap for an expert). Are the generated equation lemmas for the 7
well-founded definitions the *only* route by which their bodies enter proofs?**
Sites: 3196/3202, 3223/3233, 3283/3291, 3315/3331, 3393/3399, 4697/4703, 4706/4712.
Question to answer: after `lake build`, does `#print axioms` plus a `set_option
diagnostics true` / `count_heartbeats` on the theorems at 3235, 3333, 4841, 5057 show any
`Acc.rec` or `WellFounded.fix` unfolding *in the kernel*, i.e. does `lean --stats` show
kernel time spent in `whnf` on these constants? What would settle it: build the file with
`set_option diagnostics true` and inspect the unfolded-constant counters for
`WellFounded.fix`/`Acc.rec`; or, decisively, re-elaborate the four theorems with
`set_option maxHeartbeats 400000` and confirm they still compile with the definitions marked
`irreducible` (if they do, no defeq path through the recursion is used).
My reading says the answer is "yes, equation lemmas only", so this should come back clean —
I flag it because it is the one claim in my report that source reading alone cannot close.

**E2. The junk-`0` convention on out-of-range words/levels: is any *consumer* using the
unguarded form to get a bound it did not earn?**
Sites: `word` junk branch 3397; `levelNorm`/`boundLevel` junk branches 4701, 4710;
`levelNorm_eq_zero_of_lt` 5083; the unguarded conclusions at
`map_word` 4601, `levelNorm_eq_words` 4740, `word_add` 4894, `sub_word` 9474, and especially
`pressure_gevrey_majorant` 5120 (conclusion `∀ n`, hypotheses `∀ n ≤ s`) and
`pressure_word_sum_majorant` 5170 (same). Question: does any downstream theorem instantiate
these at `n > s` and then *use* the resulting `0 ≤ majorant` as if it were a statement about a
real derivative? What would settle it: for each call site of 5120/5170 in the other 145 files,
check whether the `n` supplied is bounded by the `s` of the supplied jet. Inside
EulerProof.lean every use I read is guarded (5179-5181 passes the same `n`; 12980 sums
`n ∈ range (s+1)`), so this is a cross-file question.
Note what makes this *not* already a finding: the guarded lemmas that actually carry
mathematical content — `word_hasDerivAt` (3413, needs `n < s`), `word_unique` (4549, needs
`n ≤ s` on both), `pressure_word_inverse` (4636, needs `n ≤ s`) — all carry the guard, and
`sobolevNorm_eq_sum_words` (3458) plus `compactSmoothJet_sobolevNorm` (7957) pin the jet norm
to the classical Sobolev norm, so junk values cannot inflate a norm bound downward.

**E3. `CoefficientJet.productConstant` (3196) has an `i`-independent term inside the `∑ i`.**
`A.bound + ∑ i : Fin 4, (J.truncate.productConstant + (lower i).productConstant)` — the first
summand does not depend on `i`, so the definition is really
`A.bound + 4 * J.truncate.productConstant + ∑ i, (lower i).productConstant`. Same shape in
`pressureConstant` (3283, 3288). Question for an expert: is this the intended Leibniz constant,
or the residue of an edit? It cannot make anything *unsound* (it is only ever used as an upper
bound, and `multiply_norm_le` at 3235 / `solvePressure_norm_le` at 3333 close with it), but if
the intent was `∑ i, (…)` over distinct data then the constant is 4× larger than believed, and
later Gevrey radius arithmetic (5120, 12971) may be quoting a tighter constant than the
definition supports. What would settle it: check whether any downstream numeric budget quotes
`productConstant` with a factor 1 rather than 4 per level.

**E4. `attribute [local irreducible] Parent.child initialParent`** at
`Euler/BaseFirstPacketChoice.lean:25`, `BaseFirstPacketEvolution.lean:61`,
`ParentGeometryJoinedChoice.lean:24`, `ParentGeometryForwardChoice.lean:75`,
`ParentGeometryForwardChoiceNoOptions.lean:100`, `ParentGeometryJoinedChoiceInvestigation.lean:60`,
`BaseInductionStage.lean:18`, `BaseInductionStageNoOptions.lean:44`,
`BaseFirstPacketChoiceNoOptions.lean:61`, `BaseFirstPacketEvolutionNoOptions.lean:94`.
Not my file, but it is the same *class* of device as E-nothing-here and it is applied to what
looks like a recursive tree accessor. Question: what do `Parent.child` and `initialParent`
unfold to, and does any theorem in those files depend on the accessor *not* being unfolded
(i.e. would it break if the attribute were removed)? What would settle it: delete the attribute
locally and rebuild those files.

## Residue — what I could not check and why

1. **No build.** Disk is full and there is no compiled Mathlib, so I could not run `lake build`,
   `#print axioms`, `#print` the elaborated proof terms, or ask Lean which recursor/equation
   lemmas are actually generated. Everything about *kernel behaviour* above is inference from
   the source plus knowledge of how Lean 4 compiles `match`/`termination_by`, not observation.
   In particular I could not observe the machine-generated equation lemmas for the 7
   well-founded definitions; their proof terms (built from `WellFounded.fix_eq`) are the one
   part of the kernel's workload in this region that is invisible in the source. That is E1.
2. **90.3% of the file unread** (1108 of 1227 declarations). The unread mass is the
   Fourier/Schwartz Sobolev layer (5400-6500), the heat/viscous and packet-constant layers
   (13000-20700, including the long `nlinarith` chains), and the smooth-limit machinery
   (5187-7900). I verified the *numeral* surface of that mass only through the delegated
   `decide`/`norm_num` census, not its mathematics.
3. **Two skimmed proofs inside my own region:** `commutatorLevel_succ_le` (4972) and
   `commutatorLevel_le` (5005), ~80 lines of `calc`. I read and believed the statements and the
   induction skeleton; I did not re-derive the inequality chain. Tagged UNCLEAR.
4. **Imported lemmas taken on trust** (statements read where visible, proofs not):
   `triangular_inverse_majorant` and `majorant`/`majorant_nonneg` (used at 5135-5141),
   `shifted_weighted_inverse` (12985), `vector_cylinder_pointwise_le_H3` (9973),
   `cylinder_smooth_of_uniformCauchy_words` (10293), `liftedPressure_unique`/`_equation`
   (4628, 4648), `HasDerivAt.unique` (Mathlib).
5. **Cross-file instantiation of the unguarded lemmas** (E2) — 145 files reference the jets and
   I read none of them beyond a `grep -l` and one 65-line file listing.
   The sibling `dep-path` child's transitive graph had not landed when I wrote this, so
   "on the dependency path" is my own name-chain evidence, not a computed reachability closure.
6. **`Fin`-arithmetic side conditions** inside `word`/`wordSnocEquiv` (`Fin.last`, `Fin.init`,
   `Fin.snoc`, `Fin.tail`, `Fin.cons`) rest on Mathlib lemmas plus two `rfl`/`cases j using
   Fin.cases <;> rfl` steps (3431, 3434, 3454). Those `rfl`s are on symbolic `Fin` indices, so I
   claim they are cheap; I did not verify that the kernel does not get stuck on the
   `Nat.decLt` guard inside `Fin.snoc` at some instantiation, because that would need a build.


## Addendum: dependency-path result (from sibling `dep-path` child, landed after the body above)

`audits/nse-deep/workers/_scratch-depgraph.md`, grep-based transitive graph over the 1829
modules in `Euler/Solution.lean`'s import closure (16221 decls; no build, so no kernel check):

* `Euler/EulerProof.lean` imports only Mathlib and is imported by 32 repo modules; it **is** in
  the import closure of both `Euler.Solution` and `Euler.EulerSingularity`.
  `ComparatorChallenges/Euler.lean:85,:170` import only Mathlib — reference copies, not the proof.
* Reachable from the two headline theorems: **653 of 1239 decls in this file (52.7%)**;
  586 unreachable. In lines 3060-4720: 102 decls, **63 reachable, 39 unreachable**.
* `SpatialJet` (3064), `CoefficientJet` (3073), `productConstant` (3196), `multiply` (3223),
  `pressureConstant` (3283), `word` (3393), `levelNorm` (4697), `boundLevel` (4712):
  **ON-PATH**, with explicit chains (e.g. `Solution.lean:33` → `PacketFiniteLifespan.lean:42`
  → … → `CylinderSobolevSpace.lean:78 ofJet` → `EulerProof.lean:3064`). So 6 of the 7
  well-founded definitions are load-bearing.
* Reported **NOT REACHED**: `solvePressure` (3315), `solvePressure_norm_le` (3333),
  `sub_norm_le` (3166), `leibnizConvolution_succ` (4806). Treat with care: `solvePressure` is
  used *inside* this file at 3328, 3341, 3374, 4642, 5061, 10308 and 12984, so "not reached"
  can only mean that its in-file consumers (notably `exists_smooth_pressure`, 10299, and
  `pressure_shifted_weighted_bound`, 12971) are themselves not reached — i.e. the headline proof
  reaches the *jet* layer through `CylinderSobolevSpace.ofJet` but obtains its pressure solve
  elsewhere. **New escalation E5:** if `solvePressure` (3315) is genuinely dead, then the
  well-founded definition with the most intricate measure argument in this file is not on the
  path at all, and whichever module *does* supply the on-path pressure jet needs the same audit.
  What would settle it: `grep -rn 'solvePressure' Euler/*.lean` restricted to the 653 reachable
  declarations, or a built `#print axioms` / `--deps` run.
* Graph limits (the child's own caveat): name-suffix matching over-approximates (LOOSE variant
  gives 779 reachable), namespace-visibility filtering under-approximates (STRICT gives 474),
  and `simp`-implicit lemmas, instance resolution and `gcongr`/`positivity` extensions produce
  edges no grep can see — so the 39 "unreachable" in my region are *candidates* for dead weight,
  not proven dead.

* Child's final message adds: `CoefficientJet`/`SpatialJet` constructors are matched by 56
  reachable decls; qualified on-path refs hand-verified at `Euler/H6Pressure.lean:21,:86`,
  `Euler/SobolevCoefficientPressure.lean:79`, `Euler/CorrectionEnergyData.lean:21`.
  `solvePressure` (3315): no reachable decl names it, all 24 in-file consumers unreachable, its
  177-decl backward closure dead. Dead *blocks* inside my region: `EulerNoncompactTransport`
  3837-4087, `Metric*Evolution` 4120-4466, and **the whole `EulerPressureJetIdentities`
  namespace 4533-4658** — i.e. `word_unique` (4549), `map` (4590), `pressure_word_projected_equation`
  (4615), `pressure_word_inverse` (4636), `pressure_word_norm_le` (4658). If that holds, the
  region's most important anti-junk theorem (`word_unique`) and the whole per-word pressure
  identity layer are dead weight, and the on-path proof must re-establish witness-independence
  of derivative words somewhere else. **E5 is upgraded**: ask not only "is `solvePressure` dead"
  but "where does the ON-PATH argument get `word_unique`'s content (uniqueness of strong
  derivatives across witness trees)?" What would settle it: a build plus `--deps`/`#print axioms`,
  or grepping the 653 reachable decls for `word_unique`/`solvePressure`. The child rates
  "ON-PATH" robust (hand-read qualified references) and "dead" fragile (simp/instance/unfold
  edges are invisible to grep).
