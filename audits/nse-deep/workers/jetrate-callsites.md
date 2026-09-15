# Worker report: JetRate call sites (circularity / junk values / filter escape / recursor watch)

Auditor: `jetrate-callsites` (READ-ONLY on `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`).
Method: source reading only (no built Mathlib, no `lake build`). Every line number was read in the
original file before being cited. Companion report read first:
`audits/nse-deep/workers/expr-inductives.md` (definitions of `Expression`, `FieldFactor`,
`FactorSupportAt`, `ApproximationRates`, `polynomial_jetRate_of_stages`).

## Scope

| file | lines | decls (`theorem`/`def`/`structure`) | read line-by-line |
|---|---|---|---|
| `NavierStokes/GenericSupportLocalCoefficients.lean` | 227 | 10 | 227/227 (all) |
| `NavierStokes/GenericSupportedPolynomial.lean` | 286 | 18 | 286/286 (all) |
| `NavierStokes/GenericTupleSupport.lean` | 190 | 10 | 190/190 (all) |
| `NavierStokes/GenericSupportLocalSummation.lean` | 165 | 3 | 165/165 (all) |
| `NavierStokes/GenericSummationRealization.lean` | 133 | 3 | 133/133 (all) |
| **total (primary scope)** | **1001** | **44** | **1001 (100%)** |

`GenericSupportedPolynomial.lean` was added to the primary scope because it, not
`GenericDifferentialPolynomial.lean:247`, holds the theorem that the consumers actually use
(`TailRates.flat_of_residuals`, :130). Nothing in the five files was skimmed.

Read in full outside the primary scope (needed to answer A/B/C, cited but not tabulated):
`GenericJetRateAlgebra.lean:1-62` (all), `GenericRealization.lean:20-50`,
`GenericTupleRealization.lean:1-120` + `:165-214`, `GenericRealizationBounds.lean:20-80` +
`:200-243`, `JetBounds.lean:88-120`, `DiagonalResidual.lean:28-60` + `:106-113`,
`SeedHandbackJets.lean:83-92` + `:195-235`, `PaperAdditionalResults.lean` (all 31 lines),
`DiagonalJetBounds.lean:251-253`.

### One-line answers to the four questions

* **A (circularity):** no circularity, and no `J → ∞` / derivative-order interchange — but for a
  blunter reason than expected: **`polynomial_jetRate_of_stages` has zero call sites**, the
  consumers go through the parallel `TailRates.flat_of_residuals`, and **`hres` is never
  discharged anywhere in the repo**. The whole cone is a conditional, currently unused library.
* **B (junk values):** no consumer concludes anything about a `directional` tree without
  `IsOpen U` + `ContDiffOn ℝ ∞ … U` for all inputs. The one lemma that does drop smoothness
  (`Expression.zero_germ`, `GenericSupportedPolynomial.lean:150`) is mathematically legitimate
  (germ-determinacy of `fderiv`) and has no consumers.
* **C (filter escape):** no escape. Every generic lemma carries `hlU : ∀ᶠ x in l, x ∈ U`
  explicitly, and every instantiation uses `l = scaleApproach U q = comap q (𝓝[>]0) ⊓ 𝓟 U`
  (`GenericRealization.lean:23`), which is `≤ 𝓟 U` by construction. Ambient-vs-within
  derivatives are bridged with `iteratedFDerivWithin_of_isOpen` (`JetBounds.lean:91-107`).
* **D (recursor watch):** confirmed clean. No file instantiates `approximation_eval`,
  `PolynomialExpression.bounds`, `Expr.jetOrder` or `FieldFactor.expression` at a closed tree
  and then closes a goal by reduction. Greps and full outputs below.

## A. The `hres` chain, hop by hop

`polynomial_jetRate_of_stages` (`GenericDifferentialPolynomial.lean:247`) is **dead code**:

```
$ grep -rn 'polynomial_jetRate_of_stages' --include=*.lean .
./NavierStokes/GenericDifferentialPolynomial.lean:247:theorem polynomial_jetRate_of_stages {ι κ : Type*}
```

The consumers use a structurally identical but `TailRates`-valued route. The real chain, top
(most concrete) to bottom (the limit argument), with the `hres` obligation at every hop:

| hop | declaration | `hres` there | passed to |
|---|---|---|---|
| 1 | `Result.flat_residual_of_support_local_raw_bounds` `GenericSupportLocalSummation.lean:105` | **hypothesis** `:127-129`: pointwise `‖iteratedFDeriv m (P.eval (stageComponents … J)) x‖ ≤ Cr J m (1+|log q|)^{Pr J m} q^{rho J - Kr m} + error J m x`, with `he :160`-style flat majorant `:130` | converted to a `JetRate` at `:149-159` by `jetRate_of_log_bound_add_flat` (`GenericRealizationBounds.lean:205`), then `:160` |
| 2 | `Result.flat_residual_of_support_local_factors` `:67` | **hypothesis** `:87-88` | `:91` |
| 3 | `Result.flat_residual_support_local` `:21` | **hypothesis** `:43-44` | `:61-62` |
| 4 | `SupportedPolynomial.flat_of_support_local_coefficients` `GenericSupportLocalCoefficients.lean:183` | **hypothesis** `:201` | `:222-223` |
| 5 | `TailRates.flat_of_residuals` `GenericSupportedPolynomial.lean:130` | **parameter** `:136` | consumed here |

The non-support-local twin chain is identical: `GenericSummationRealization.lean:75` (`hres`
`:96-98`) → `GenericTupleSupport.lean:157` (`hres` `:176-177`) → `GenericTupleRealization.lean:171`
(`hres` `:193-194`) → `flat_of_local_coefficients` (`GenericSupportedPolynomial.lean:254`, `hres`
`:272`) → the same `:130`.

**Who proves `hres`? Nobody.** Both chain tops are terminal:

```
$ grep -rn 'flat_residual_of_support_local_raw_bounds|flat_residual_of_raw_bounds' --include=*.lean .
./NavierStokes/GenericSummationRealization.lean:75:theorem Result.flat_residual_of_raw_bounds …
./NavierStokes/GenericSupportLocalSummation.lean:105:theorem Result.flat_residual_of_support_local_raw_bounds …
```

`GenericSupportLocalSummation.lean` is imported by exactly one file,
`PaperAdditionalResults.lean:23`, and that file is **31 lines of nothing but `import`s** — it
never mentions any of these names. So `hres` is an undischarged leaf hypothesis of the whole
cone. Consequences:

* **There is no circularity** (nothing downstream feeds the conclusion back into `hres`), and
* **there is no limit interchange.** `TailRates.loss`/`threshold` are functions of the derivative
  order `m` **only** (`GenericSupportedPolynomial.lean:52-53`), fixed when the `TailRates`
  structure is built and independent of `J`; `hres` is assumed for **all** `J` and **all** `m`;
  and the single `J` used is chosen only after `m` and the target order `n` are given
  (`:138-141`, `J := max (a.threshold m) J₀`). That is the safe quantifier order. I re-derived the
  arithmetic: `hj.1 : n + a.loss m ≤ gain J`, `hj.2 : n + Lres m ≤ rho J`, so both the tail term
  (rate `gain J - a.loss m ≥ n`) and the stage term (rate `rho J - Lres m ≥ n`) are weakened to
  `n` by `JetRate.weaken` (`DiagonalResidual.lean:41`, sound because `0 < q ≤ 1`), then added
  (`:145`) and re-associated by `congr_on`. Honest.
* **But the strength is entirely in `hres`**, which is a strong assumption: the finite-stage
  residual is already flat with a gain `rho J → ∞` *and* a loss `Lres m` that does **not** depend
  on `J`. See E2.

## Per-declaration findings

Verdict legend: OK / UNCLEAR / KERNEL-RISK / SUSPICIOUS. "DEAD" = no consumer repo-wide.

### `GenericSupportLocalCoefficients.lean` (10 decls)

| # | name | line | statement (my words) | mechanism | verdict |
|---|---|---|---|---|---|
| 1 | `norm_jet_mul_at` | 20 | if all jets of `f` and `g` up to order `m` at the single point `x` are `≤ A`, `≤ B`, and both are `C^∞` at `x`, then `‖D^m(fg)(x)‖ ≤ 2^m A B` | `ContDiffAt.contDiffOn'` produces open `V`,`W ∋ x` with `ContDiffOn ℝ m`; `JetBounds.norm_iteratedFDeriv_mul_le_on` (`JetBounds.lean:97`, ambient derivatives via `iteratedFDerivWithin_of_isOpen`) then `∑ C(m,i)AB = 2^m AB` by `Nat.sum_range_choose` (`:46`) | OK. I re-derived the constant. Note it needs jets only **at** `x`, which is what makes the support-local story work |
| 2 | `rate_mul_at` | 48 | product of two `FiniteJetRate`s is a `JetRate` with exponent `r+s`, smoothness required only `∀ᶠ x in l` | #1 pointwise under `filter_upwards`; `Real.rpow_add hqx` needs `0 < q x`, supplied | OK |
| 3 | `mul_zero_germ` | 64 | `f =ᶠ[𝓝 x] 0 → c*f =ᶠ[𝓝 x] 0` | `filter_upwards`, `mul_zero` | OK |
| 4 | `iteratedFDeriv_mul_eq_zero_of_zero_germ` | 70 | all jets of `c*f` vanish at `x` when `f` has a zero germ | `SolenoidalDiagonal.iteratedFDeriv_eventuallyEq … .self_of_nhds` | OK — germ-local, no differentiability needed and none claimed |
| 5 | `smooth_mul_of_support_local` | 77 | `c*f` is `C^∞` on open `U` if `f` is `C^∞` on `U`, `c` is `C^∞` at points of `U ∩ S`, and `f` has a zero germ at points of `U \ S` | `by_cases x ∈ S`; in-`S` branch multiplies `ContDiffAt`s (openness used via `hU.mem_nhds`), out-of-`S` branch `contDiffAt_const.congr_of_eventuallyEq` | OK. This is the "singular coefficient is harmless off the support" lemma and it is stated and proved correctly |
| 6 | `smooth_mul_inv_of_support_local` | 90 | same with `c = r⁻¹`, `r ≠ 0` on `U ∩ S` | `ContDiffAt.inv` + #5 | OK |
| 7 | `ApproximationRates.mul_coefficient_support_local` | 98 | from an `ApproximationRates` package for `f` and a **support-local** growth bound for `c` on `l ⊓ 𝓟 S`, build `TailRates` for `c*f` with `loss m = maxJetLoss Lc m + maxJetLoss a.tailLoss m`, `threshold m = sup_{k≤m} a.threshold k` | `finiteJetRate_of_jetRate` over `k ≤ m` (needs `a.threshold k ≤ J` for **all** `k ≤ m`, which is exactly what the `sup` threshold buys, `:124-125`), `rate_mul_at`, `mul_sub` via `congr_on`, then `rate_of_restricted_support` (`GenericSupportedPolynomial.lean:32`) to lift from `l ⊓ 𝓟 S` back to `l` | OK. Loss algebra checked by hand; the `sup`-threshold detail is the correct fix for the "uniform in `k ≤ m`" requirement |
| 8 | `smooth_evalTerms_of_products` | 148 | a list of (coefficient × monomial) products, each `C^∞` on `U`, sums to something `C^∞` on `U` | `induction terms` (List recursor, variable list) | OK |
| 9 | `termsTail_of_products` | 158 | `TailRates` for the list sum from `TailRates` for each term | `induction terms`, `TailRates.add` | OK |
| 10 | `flat_of_support_local_coefficients` | 183 | **the payload**: given (i) `ApproximationRates` for every input field, (ii) coefficients smooth and rate-bounded only on their own `region t`, (iii) each monomial's zero germ off `region t` for the limit and every stage, (iv) `hres` for the finite stages with `rho J → ∞`, then `JetRate l q (P.eval u) m n` for **every** real `n` | #7 per term → #9 → `TailRates.fixed P.constant |>.add` → `TailRates.flat_of_residuals` (`:222`) | OK **as an implication**, DEAD in practice (only consumer is `GenericSupportLocalSummation.lean:61`, itself dead). All strength sits in `hres` (`:201`) |

### `GenericSupportedPolynomial.lean` (18 decls)

| # | name | line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| 11 | `rate_filter_mono` | 14 | a `JetRate` survives passing to a finer filter `l' ≤ l` | `Eventually.filter_mono` | OK (direction is the sound one: finer filter = weaker claim) |
| 12 | `ApproximationRates.filter_mono` | 20 | same for the whole package | field-wise #11 | OK |
| 13 | `rate_of_restricted_support` | 32 | a rate on `l ⊓ 𝓟 S` upgrades to a rate on `l` **if** `f` has a zero germ at every point of `U \ S` and `l` is eventually in `U` | `eventually_inf_principal`, `by_cases x ∈ S`, off-`S` branch rewrites the jet to `0` via germ | OK, and this is the load-bearing "outside the support there is nothing to bound" step. `hlU` is used (`:40`), i.e. filter-inside-`U` is genuinely required |
| 14 | `TailRates` (structure) | 50 | `loss, threshold : ℕ → …` plus `rate : ∀ m J, threshold m ≤ J → JetRate l q (f - stage J) m (gain J - loss m)` | data + proof field | OK; note `loss`/`threshold` depend on `m` only — this is what forbids a limit interchange downstream |
| 15 | `ApproximationRates.tail` | 57 | forget everything but the tail | projection | OK |
| 16 | `ApproximationRates.mul_coefficient_local` | 63 | #7 with a globally `C^∞` coefficient | `rate_mul` (`GenericJetRateAlgebra.lean:19`) instead of `rate_mul_at`; otherwise identical | OK |
| 17 | `TailRates.add` | 104 | sums: `loss = max`, `threshold = max` | `.weaken` twice then `JetRate.add` + `congr_on` with `ring` | OK |
| 18 | `TailRates.fixed` | 121 | a field-independent function is its own stage; `loss = 0`, `threshold = 0` | residual is `c - c`, closed by `sub_self` + `rate_zero` (`GenericJetRateAlgebra.lean:16`) | OK, not a cheat: `rate_zero` is the true statement that `0` has every rate |
| 19 | `TailRates.flat_of_residuals` | 130 | **the limit argument**: tail rates + `hres` for all `J` ⇒ `JetRate l q f m n` for every `n` | choose `J₀` from `hgain`/`hrho` eventualities (`:138-140`), `J := max (a.threshold m) J₀`, weaken both parts to `n`, add, `congr_on` | OK; see A for the quantifier-order audit. This is the theorem that the sibling's E3 was really about |
| 20 | `Expression.zero_germ` | 150 | if every input field has a zero germ at `x`, so does `e.eval` — **for a tree containing `directional`, with no smoothness hypothesis at all** | `induction e`; `directional` case (`:164-169`) uses `EventuallyEq.fderiv` then `rw` + `simp` | OK **and this is the honest use of germ-locality**: `f =ᶠ[𝓝 y] g → fderiv f =ᶠ fderiv g` holds with no differentiability, so junk `0` values are not being exploited, they are being *respected*. **DEAD** (no consumer) |
| 21 | `SupportedPolynomial` (structure) | 172 | `constant : D → ℝ` + `terms : List ((D → ℝ) × Expression D ι Empty)` | data | OK. Coefficient family is `Empty`, so no `coeff` node can ever appear in a term |
| 22-23 | `evalTerms` :180, `eval` :184 | list-recursive evaluation, `eval = constant + evalTerms` | List recursion | OK |
| 24-25 | `smooth_evalTerms` :187, `smooth_eval` :199 | `C^∞` on `U` when coefficients and inputs are | `induction terms`, `Expression.smooth_eval` | OK (needs `hU`, supplied) |
| 26 | `termTail` | 209 | per-term `TailRates` from `approximation_eval` + #16 | function composition, no tactics | OK. `t.2` is a **variable** tree — see D |
| 27 | `termsTail` | 230 | list version | `induction terms`, `TailRates.add` | OK |
| 28 | `flat_of_local_coefficients` | 254 | globally-smooth-coefficient twin of #10 | #27 → #18 `.add` → #19 | OK as an implication; consumers `GenericRealization.lean:195`, `GenericTupleRealization.lean:211` |

### `GenericTupleSupport.lean` (10 decls)

| # | name | line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| 29-31 | `baseComponents` :12, `incrementComponents` :17, `cutIncrementComponents` :23 | package `(velocity components, scalars)` as one family indexed by `Fin 3 ⊕ κ` | `match` on the sum type | OK; the velocity entries are `spatialCurl (positiveStages A j) + positiveStages B j`, i.e. the curl is *inside* the increment, which is what makes the sum identities below true |
| 32-34 | `smooth_baseComponents` :29, `smooth_incrementComponents` :38, `smooth_cutIncrementComponents` :54 | each family is `C^∞` on `U` | `cases i`; `EuclideanSpace.proj i |>.contDiff.comp_contDiffOn`, `contDiffAt_spatialCurl`, `cutStage_contDiffAt`, all requiring `hU.mem_nhds` | OK — openness of `U` is used at every step; nothing is derived from a `ContDiffOn` on a non-open set |
| 35 | `spatialCurl_sum_on` (private) | 75 | curl of a finite sum is the sum of curls, on `U` | `fderiv_fun_sum` with differentiability **supplied** (`:80-83`) | OK — positive sign: the linearity is proved, not assumed via junk `fderiv` |
| 36 | `stageComponents_local_sum` | 89 | there is `N` (`= J+1`) with each stage component `=ᶠ[𝓝 x] base + ∑_{j<N} increment j` | `filter_upwards [hU.mem_nhds hx]`; velocity branch uses #35 + `Finset.sum_add_distrib`; scalar branch is `rfl` (`:110`) | OK. The `rfl` is a delta step: `stage base A J = base + uncutPrefix (positiveStages A) (J+1)` (`GenericRealizationBounds.lean:27-29`) and `uncutPrefix A N x = ∑ j ∈ range N, A j x` (`DiagonalJetBounds.lean:251-252`); `J` stays symbolic so no numeral or recursor is evaluated |
| 37 | `components_local_sum` | 114 | the **infinite** realized sum also equals `base + ∑_{j<N} cutIncrement j` near `x`, with `N` chosen from the scale alone | `scaledCutoffs_zero_on_common_neighborhood` gives `N` with all cutoffs `= 0` for `j ≥ N` on a neighbourhood of `q x /2`-level; `tsum_eq_sum` (`:130`) then truncates the `tsum` | OK, and this is the key non-trivial step: `N` is chosen **before** any derivative is taken (docstring `:112-113` matches the proof) so there is no "N depending on the order" cheat |
| 38 | `Result.flat_residual_of_factor_support` | 157 | replaces the two abstract zero-germ hypotheses of `Result.flat_residual` by `FactorSupportAt` for the base+raw and base+cut families | `H.flat_residual` with the two germ goals discharged by `FactorSupportAt.zero_germ` (`GenericFactorSupport.lean:126`) fed with `smooth_baseComponents`, `smooth_(cut)IncrementComponents`, and #36/#37 | OK. Smoothness **is** supplied at `:183-188`; `hres` still a hypothesis `:176` |

### `GenericSupportLocalSummation.lean` (3 decls)

| # | name | line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| 39 | `Result.flat_residual_support_local` | 21 | pointwise `δ,C` flatness of `P.eval (components …)` on `U`, from `ApproximationRates` supplied by `H.approximation` and `hres` | `hu`/`hus` from `H.smooth_velocity`, `H.smooth_scalars`, `positiveStage_smooth`, `stage_smooth` (`:49-58`); `hgain` from `hgtop` (`:59-60`); then `flat_of_support_local_coefficients` + `uniform_bound_of_rate` | OK. `l := scaleApproach U q`, `hlU := eventually_domain U q` (`:47`) — filter provably inside `U` |
| 40 | `Result.flat_residual_of_support_local_factors` | 67 | same with `FactorSupportAt` instead of the raw germ hypotheses | `FactorSupportAt.zero_germ` twice (`:94-99`) with real smoothness and #36/#37 | OK |
| 41 | `Result.flat_residual_of_support_local_raw_bounds` | 105 | same with **printed** log-power coefficient bounds and a residual bound + arbitrary flat error | `jetRate_of_log_bound` (`:146`) and `jetRate_of_log_bound_add_flat` (`:157`), each costing one power of `q` (`Lc := Kc+1`, `Lres := Kr+1`, `:161-162`) | OK arithmetic; **DEAD** (no consumer). This is the cone's terminal statement |

### `GenericSummationRealization.lean` (3 decls)

| # | name | line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| 42 | `base_rate_of_raw_log` | 14 | a printed log-power bound on `U` gives `JetRate … (-(K m + 1))` | `jetRate_of_log_bound` | OK — the `+1` is the honest price of the log factor |
| 43 | `exists_angular_realization` | 29 | existence of the cut schedule `a` and a `Result` package, for angular-field increments, with solenoidality/tangency **derived** from `angular_admissibility` rather than assumed | `exists_realization` (`GenericTupleRealization.lean:80`) after discharging `hdivB`/`htan` (`:55-65`) | OK. **This is the file's non-vacuity witness**: `Result` really is constructible, so `H.approximation` in #39 is not an empty interface |
| 44 | `Result.flat_residual_of_raw_bounds` | 75 | global-coefficient twin of #41 | `hcoeffRate`/`hresRate` then `flat_residual_of_factor_support` | OK; **DEAD** |

## B. Junk-value audit (`Expression.eval` at a `directional` node)

`eval (directional v a) = fun x => fderiv ℝ (eval a) x v`
(`GenericDifferentialPolynomial.lean:202`) is `0` by definition where `eval a` is not
differentiable. Findings at the consumers named in the brief:

1. **Every `JetRate`/flatness conclusion about a tree is guarded.** `flat_of_support_local_coefficients`
   (`GenericSupportLocalCoefficients.lean:183`) takes `hU : IsOpen U` (`:187`), `hu : ∀ i, ContDiffOn ℝ ∞ (u i) U`
   (`:190`) and `hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U` (`:191`), and its conclusion is a `JetRate`
   along a filter that is eventually in `U` (`:188`). Openness + `ContDiffOn` gives `ContDiffAt` at
   each point of `U` (used e.g. `:86`, `:139`), so on `U` the `fderiv` in the `directional` node is
   the genuine derivative, not a junk `0`. **The `IsOpen U` hypothesis is load-bearing here**; if it
   were dropped, `ContDiffOn` on a non-open set would not pin the ambient `fderiv` and the whole
   file would be about junk. It is present at every one of the 44 decls that needs it.
2. **The germ hypotheses are the safe direction.** `hzero`/`hszero` (`:196-199`) say
   `t.2.eval … =ᶠ[𝓝 x] 0` off the region. Junk values could only make such a hypothesis
   *spuriously true*; they are consumed only by `smooth_mul_of_support_local` (`:77`, produces
   `ContDiffAt` of the product by congruence with a constant) and `rate_of_restricted_support`
   (`GenericSupportedPolynomial.lean:32`, rewrites the jet to `0`). Both are statements about the
   *same* function whose junk value is `0`, so nothing false is derived. No consumer ever infers
   "the true derivative vanishes" from "the `eval` term vanishes".
3. **`GenericTupleSupport.lean:172,174` and `GenericSupportLocalSummation.lean:83,85,122,124` and
   `GenericSummationRealization.lean:91,93`** all use `FactorSupportAt` only as a *hypothesis*, and
   discharge the resulting germ goals through `FactorSupportAt.zero_germ` with smoothness supplied
   (`GenericTupleSupport.lean:183-188`, `GenericSupportLocalSummation.lean:94-99`). Never the other
   way round.
4. **The one smoothness-free lemma is legitimate.** `Expression.zero_germ`
   (`GenericSupportedPolynomial.lean:150-169`) proves `e.eval … =ᶠ[𝓝 x] 0` for a tree with
   `directional` nodes from nothing but `hu : ∀ i, u i =ᶠ[𝓝 x] 0`, using `EventuallyEq.fderiv`
   (`:165`). This is valid without differentiability (germ-determinacy), so it is not junk-value
   abuse. It is also dead code.
5. **Positive sign nearby:** `directional_sub_eqOn` (`GenericJetRateAlgebra.lean:52-60`) explicitly
   supplies both differentiability arguments to `fderiv_sub` (`:58-59`) rather than exploiting
   junk additivity; `smooth_directional` (`:37-39`) uses `ContDiffOn.fderiv_of_isOpen`.

**Verdict B: no junk-value exploitation in the consumers.** The only way to break this would be to
weaken `IsOpen U`, which no consumer does.

## C. Filter-escape audit (`iteratedFDeriv` global vs `ContDiffOn … U`)

* `JetRate l q f m r := ∃ C ≥ 0, ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r`
  (`DiagonalResidual.lean:33`) — yes, ambient `iteratedFDeriv`.
* Every generic lemma that mixes it with `ContDiffOn … U` carries `hlU : ∀ᶠ x in l, x ∈ U` as an
  explicit hypothesis: `GenericSupportLocalCoefficients.lean:102,184`;
  `GenericSupportedPolynomial.lean:66,106,132,212,233`; `GenericJetRateAlgebra.lean:19,41`.
* Every instantiation uses `l := scaleApproach U q = comap q (𝓝[>] 0) ⊓ 𝓟 U`
  (`GenericRealization.lean:23-24`) and discharges `hlU` by `eventually_domain`
  (`GenericRealization.lean:26-28`, literally `inf_le_right` on the principal factor):
  `GenericSupportLocalSummation.lean:47,134`, `GenericSummationRealization.lean:21,103`,
  `GenericTupleRealization.lean:123,197`. **A filter of the form `… ⊓ 𝓟 U` cannot escape `U`.**
* The coefficient bounds live on the still finer `l ⊓ 𝓟 (region t)` (`GenericSupportLocalCoefficients.lean:194`),
  which is `≤ l`, hence also inside `U`; the code re-derives both facts explicitly at
  `:113-116` (`hqr`, `hlr`, `hregion`).
* The ambient/within bridge is done correctly and only on open sets:
  `JetBounds.norm_iteratedFDeriv_mul_le_on` (`JetBounds.lean:97-107`) converts
  `norm_iteratedFDerivWithin_mul_le` to ambient derivatives using `hs.uniqueDiffOn` and
  `iteratedFDerivWithin_of_isOpen`. So no `iteratedFDerivWithin`-vs-`iteratedFDeriv` slack.
* **Vacuity boundary (not a soundness bug, but worth stating):** `scaleApproach U q` is `⊥` when
  `U = ∅` or `q` is bounded away from `0` on `U`; then every `JetRate` in the chain is trivially
  true. It does not manufacture strength, because `uniform_bound_of_rate`
  (`GenericRealization.lean:38-50`) converts back to `∃ δ C > 0, ∀ x ∈ U, 0 < q x → q x < δ → …`,
  which degenerates in exactly the same cases. See E3.

## D. Vector-(1) watch item: no recursor is ever reduced on a closed tree

Greps run (from the NSE root, `--include=*.lean`, full outputs):

```
$ grep -rn 'approximation_eval' --include=*.lean .
./NavierStokes/GenericSupportLocalCoefficients.lean:214:    (t.2.approximation_eval hU hlU hq (fun k => Empty.elim k) hu hus hgain
./NavierStokes/GenericDifferentialPolynomial.lean:217:def approximation_eval (e : Expression D ι κ)
./NavierStokes/GenericDifferentialPolynomial.lean:264:    e.approximation_eval hU hlU hq hc hu hus hgain Lc hcg
./NavierStokes/GenericSupportedPolynomial.lean:224:  (t.2.approximation_eval hU hlU hq (fun k => Empty.elim k) hu hus hgain

$ grep -rn 'PolynomialExpression|\.bounds k' --include=*.lean . | grep -v ClosedIntervalJetAlgebra
./NavierStokes/SeedHandbackJets.lean:63:abbrev Expr := PolynomialExpression (Fin 19)
./NavierStokes/SeedHandbackJets.lean:106:    PolynomialExpression.eval, v, c, basis, div_eq_mul_inv, mul_inv_rev]
./NavierStokes/SeedHandbackJets.lean:224:  let C := ∑ i : Fin 4, ((outputExpression h i).bounds k BB CC).2
./NavierStokes/SeedHandbackJets.lean:225:  have hCn (i : Fin 4) : 0 ≤ ((outputExpression h i).bounds k BB CC).2 :=
./NavierStokes/SeedHandbackJets.lean:226:    (PolynomialExpression.bounds_nonneg k hBB hCC _).2
./NavierStokes/SeedHandbackJets.lean:231:  have hresult := PolynomialExpression.eval_pairBound hbas (outputExpression h i)

$ grep -rn 'jetOrder' --include=*.lean . | grep -v 'FlatKernelBounds|EdgeWeightJets'
(no output)

$ grep -rn 'FieldFactor' --include=*.lean . | grep -v GenericFactorSupport
(no output)
```

Readings:

* **`approximation_eval`: 4 hits, 0 concrete trees.** The two consumer hits apply it to `t.2`
  where `t` is bound by `∀ t ∈ P.terms` / `fun t ht =>` over a `List` **variable**
  (`GenericSupportLocalCoefficients.lean:205-217`, `GenericSupportedPolynomial.lean:209-229`).
  The result is used only as data fed to `mul_coefficient_local`/`mul_coefficient_support_local`;
  no `rfl`, `decide`, `simp` or `norm_num` ever touches its `growthLoss`/`tailLoss`/`threshold`
  fields. So `Expression.rec` into `Type` is only ever **type-checked**, never **reduced**.
* **`PolynomialExpression.bounds`: one near-miss, still safe.** `SeedHandbackJets.lean:224-226`
  forms `C := ∑ i : Fin 4, ((outputExpression h i).bounds k BB CC).2`. `outputExpression h`
  (`:85-88`) is a `Matrix.cons` vector of four genuinely concrete trees, but the index `i` is a
  **bound variable** there, and both goals about the term are closed *structurally* —
  `bounds_nonneg` at `:226` (a theorem by `induction p`, so it works on an unreduced term) and
  `Finset.single_le_sum` at `:233-234`. The numeral `C` is never computed. Kernel cost: zero
  recursor reduction over a closed tree.
* **`Expr.jetOrder` / `FieldFactor.expression`: no consumers at all outside their defining files.**
  In particular **`FieldFactor` is never constructed anywhere in the repo**, so `FactorSupportAt`
  is never instantiated with concrete data — the `hrawsupport`/`hcutsupport` hypotheses of
  `GenericTupleSupport.lean:171-174`, `GenericSupportLocalSummation.lean:82-85` and
  `GenericSummationRealization.lean:90-93` have never been checked against a real monomial. See E5.

## Kernel-risk assessment

### Vector (1) — recursive inductives / recursor reduction

Present, in the **weak** mode only. The complete inventory of eliminations in the five scope files:

* `induction terms with | nil | cons` over a **variable** `List`: `GenericSupportLocalCoefficients.lean:153,170`,
  `GenericSupportedPolynomial.lean:192,241`.
* `induction e with` over a **variable** `Expression`: `GenericSupportedPolynomial.lean:154`
  (goal is a `Prop`, small elimination).
* `cases i with | inl | inr` over `Fin 3 ⊕ κ` with **variable** `i`: `GenericTupleSupport.lean:34,47,68,98,136`,
  `GenericSupportLocalSummation.lean:51,56`.
* `by_cases hs : x ∈ S` twice (`GenericSupportLocalCoefficients.lean:83`,
  `GenericSupportedPolynomial.lean:41`) — `Classical.em`, no `Decidable` instance is evaluated.
* Exactly **one** `rfl` in 1001 lines: `GenericTupleSupport.lean:110`. It is a delta/iota step
  through `stage` (`GenericRealizationBounds.lean:27`) and `uncutPrefix`
  (`DiagonalJetBounds.lean:251`), with the range bound `J+1` symbolic; both sides contain the same
  `Finset.range (J+1)` term, so the kernel compares identical subterms.

Consequently **the kernel never has to reduce `Expression.rec`, `List.rec` or `Sum.rec` applied to
a closed constructor tree** anywhere in my scope. The `Type`-valued recursion
(`approximation_eval`, `GenericDifferentialPolynomial.lean:217`) is applied twice, both times to a
variable, so its iota rule is never fired. No `Acc.rec`, no `termination_by`/`decreasing_by`, no
nested or indexed *data* family, no `mutual`. Structure eta is used in the ordinary way for the
anonymous constructors `⟨fun m => …, M, ?_⟩` (`GenericSupportLocalCoefficients.lean:110`,
`GenericSupportedPolynomial.lean:76`) and for the `where`-style `TailRates` instances
(`GenericSupportedPolynomial.lean:110-119,121-126`).

### Vector (2) — Nat / GMP numeral work

**Absent.** The largest numeral the kernel meets in the five files is `2`, and it appears only in
`(hgtop.comp (tendsto_add_atTop_nat 1)).atTop_div_const (by norm_num)`
(`GenericSupportLocalSummation.lean:60`, `GenericSummationRealization.lean` has the same shape via
`Result.flat_residual`), where `norm_num` proves `(0:ℝ) ≠ 2` / `0 < 2`. There is no `decide`, no
`Decidable` instance evaluation, no `Nat.pow/div/mod/gcd/beq/ble`, no `omega`, no literal above
`2`, and no `norm_num` certificate over a big number. `Finset.range (m+1)`, `Finset.sup`,
`2 ^ m`, `q x ^ r` all keep symbolic arguments. `maxJetLoss` (`DiagonalResidual.lean:106`) is a
`Finset.sup` over a symbolic range — never evaluated.

### Vector (3) — custom metaprogramming

**Zero.** Grep over the five files for
`decide|native_decide|macro |elab |syntax |set_option|axiom |sorry|unsafe |partial |deriving`
returns **no output**. The only attribute in the cone is none at all; all five files open with
`noncomputable section`, so the trees have no compiled evaluator either.

## Escalations

**E1 (HIGH — value, not soundness). The entire support-local cone is unconsumed, and `hres` is
never proved.** `GenericSupportLocalSummation.lean:105` (`Result.flat_residual_of_support_local_raw_bounds`)
and `GenericSummationRealization.lean:75` (`Result.flat_residual_of_raw_bounds`) have no call
sites; their only importer, `PaperAdditionalResults.lean:23`, is 31 lines of pure `import`s;
`formalization.yaml` (130 lines) does not mention any of these names. *Question for an expert:*
is this cone claimed as a paper result (§"sum:realization", cited in the docstrings at
`GenericSummationRealization.lean:70-74` and `GenericSupportLocalSummation.lean:102-104`), and if
so, is the paper's corresponding step's hypothesis exactly `hres`, i.e. does the manuscript itself
*prove* the finite-stage residual estimate elsewhere? *What settles it:* the paper's statement
list vs. `formalization.yaml`; plus a repo-wide search for any theorem whose conclusion is
`∀ J m, JetRate … (P.eval (stageComponents …)) m (rho J - Lres m)` (I found none).

**E2 (MEDIUM — mathematical strength of the assumption). `GenericSupportLocalSummation.lean:127-130`
and `:87-88`; `GenericSupportedPolynomial.lean:136`.** `hres` assumes the finite-stage residual is
bounded by `Cr J m (1+|log q|)^{Pr J m} q^{rho J - Kr m} + error J m`, with `rho J → ∞` and
`Kr m` **independent of `J`**, plus a flat majorant for `error` at every polynomial order
(`he`, `:130`). *Question:* in the manuscript, is the stage-`J` residual estimate really uniform
in `J` in this way — i.e. is the derivative-order loss `Kr m` free of `J`? If the paper's loss
actually grows with `J` (as loss terms usually do when each stage adds cutoff derivatives), the
Lean hypothesis is **stronger than the paper's lemma**, and the flatness conclusion would not
follow from what the paper proves. *What settles it:* match `Kr`/`rho` against the paper's stage
estimate; alternatively look for the intended supplier of `hres` and check its `L`-bookkeeping.

**E3 (LOW-MEDIUM — vacuity boundary). `GenericRealization.lean:23-24` and `:38-50`.** All rates
live on `scaleApproach U q = comap q (𝓝[>]0) ⊓ 𝓟 U`, which is `⊥` if `U = ∅` or `inf_{U} q > 0`;
then every hypothesis *and* the conclusion of the whole cone is vacuous. *Question:* at the
(currently missing) real call site, is there a proof that `U` contains points with `q` arbitrarily
small — i.e. that `scaleApproach U q ≠ ⊥`? *What settles it:* a `NeBot` instance or an explicit
witness at the instantiation. Not a soundness problem, but the difference between a theorem and a
tautology.

**E4 (LOW — recursor watch, confirms sibling's E5). `SeedHandbackJets.lean:224-226`.** This is the
only place in the repo where a `PolynomialExpression.bounds` term is built over concrete trees
(`outputExpression h`, `:85-88`, over `ι = Fin 19`). Today the constant is never reduced (goals go
through `bounds_nonneg` and `Finset.single_le_sum`). *Question:* if anyone later needs a numeric
value of `C`, `simp`/`norm_num`/`decide` would force the kernel to reduce `PolynomialExpression.rec`
over ~42 nodes with `Fin 19` `Matrix.cons` index resolution. *What settles it:* keep the grep in
`## D` as a regression check; today it is clean.

**E5 (MEDIUM — expressibility, cannot create unsoundness). `GenericFactorSupport.lean:106-114`
consumed at `GenericTupleSupport.lean:171-174`, `GenericSupportLocalSummation.lean:82-85`,
`GenericSummationRealization.lean:90-93`.** `FieldFactor` is never constructed anywhere in the
repo (grep in `## D` returns nothing outside its defining file), so `FactorSupportAt` has never
been instantiated for an actual residual monomial. Its `mul` constructor requires **both** factors
to be supported away from `x`. *Question:* can the manuscript's residual monomials — which
typically contain an undifferentiated factor that does *not* vanish near the axis — be expressed at
all in this predicate? *What settles it:* write down one real monomial from the paper's residual and
try to build the `FactorSupportAt` term. If it cannot be built, the `_of_factor_support` theorems
are unusable rather than unsound (the hypothesis is harder to satisfy than needed).

**E6 (LOW — library signature, inherited). `GenericSupportLocalCoefficients.lean:24-31`.**
`hf.contDiffOn' (m := (m : WithTop ℕ∞)) (by simp) (by simp)` followed by
`Set.insert_eq_of_mem (Set.mem_univ x)` assumes `ContDiffAt.contDiffOn'` returns a neighbourhood of
the form `insert x u ∩ univ`. *Question:* is that the pinned Mathlib's exact shape? *What settles
it:* one `#check`. Comparator passed, so the file elaborates; noted only because the `simp only`
at `:29` would silently be a no-op if the shape differed, and then `hfs`/`hgs` would be about a
different set.

## Residue

* **No elaboration.** No built Mathlib, so I could not `#check` a signature, `#print axioms` any
  of these theorems, or verify that a `simp only`/`convert … using 1`/`ring` actually closes its
  goal. Specifically unverified: the `convert … using 1; ring` steps at
  `GenericSupportLocalCoefficients.lean:141-146`, `GenericSummationRealization.lean:115-117,126-128`,
  `GenericSupportLocalSummation.lean:146-148,157-159`; the `simpa only [...]` chains at
  `GenericTupleSupport.lean:107-109,147-149`; and the exact Mathlib signatures of
  `EventuallyEq.fderiv`, `ContDiffAt.contDiffOn'`, `fderiv_fun_sum`, `tsum_eq_sum`,
  `iteratedFDerivWithin_of_isOpen`, `mem_nhdsGT_iff_exists_Ioo_subset`.
* **Constant algebra checked by hand, not by machine.** I re-derived: the `2^m A B` Leibniz
  constant (`GenericSupportLocalCoefficients.lean:20-47`), the loss/threshold algebra of
  `mul_coefficient_support_local` (`:110`), `TailRates.add` (`GenericSupportedPolynomial.lean:111-119`),
  the `J`-selection inequalities in `flat_of_residuals` (`:138-146`), and the one-power price of
  the log factor (`GenericRealizationBounds.lean:47-73`, `:205-242`). I did not check the
  `linarith` certificates at `GenericSupportedPolynomial.lean:143,144`.
* **Not audited (upstream, cited only):** `exists_realization`
  (`GenericTupleRealization.lean:80-160`, i.e. whether the `Result` package is *correctly*
  constructed — I only confirmed that it *is* constructed), `GenericDiagonalSchedule.exists_finite_diagonal_cut_bounds_with_tests`,
  `SmoothCutoffs.scaledCutoffs_zero_on_common_neighborhood`, `cutStage`/`potentialSum`
  (`SolenoidalDiagonal`), `CutStageEstimates.positiveStages_smooth`, `SpatialCurl.*`,
  `DiagonalScale.tendsto_logPowerWeight`, and `SeedHandbackJets.lean:1-194,236-393`.
* **Not in scope, flagged for whoever owns the main theorem:** because `hres` is never discharged
  in this cone, the question "is the *actual* Navier-Stokes residual flat?" is answered elsewhere
  in the repo (the `Actual*` files) by machinery I did not read. The five files audited here
  cannot be the place where a flatness claim is manufactured.

## Addendum: cone status of every scope declaration (CONE.csv cross-check)

Parent's `audits/nse-deep/CONE.csv` (52,516 decls, 33,163 in cone) was joined against my scope.

**(A) confirmed dead, verbatim grep as requested:**

```
$ cd /home/gsm/.openclaw/workspace/repos/NSE && grep -rn 'polynomial_jetRate_of_stages' --include=*.lean . ; echo EXIT=$?
./NavierStokes/GenericDifferentialPolynomial.lean:247:theorem polynomial_jetRate_of_stages {ι κ : Type*}
EXIT=0
```

One hit, the definition itself. No caller. Parent's instrument is right; escalation (A) has no
call sites to trace, and my independent chain analysis above explains why: the consumers use
`TailRates.flat_of_residuals` (`GenericSupportedPolynomial.lean:130`) instead, and `hres` is a leaf
hypothesis there too.

**Cone status of the five scope files (44 decls):** 11 flagged in-cone, of which only **2 are
theorems** (`rate_filter_mono` `GenericSupportedPolynomial.lean:14`, `Expression.zero_germ` `:150`);
the other 9 are `def`/`structure`. **26 of 28 theorems are out of cone**, including every terminal
statement of the chain:

| declaration | file:line | in_cone | callers found by my own grep (all out of cone) |
|---|---|---|---|
| `Result.flat_residual_of_support_local_raw_bounds` | `GenericSupportLocalSummation.lean:105` | False | none |
| `Result.flat_residual_of_raw_bounds` | `GenericSummationRealization.lean:75` | False | none |
| `exists_angular_realization` | `GenericSummationRealization.lean:29` | False | none |
| `base_rate_of_raw_log` | `GenericSummationRealization.lean:14` | False | none |
| `Result.flat_residual_of_support_local_factors` | `GenericSupportLocalSummation.lean:67` | False | `:160` (same file) |
| `Result.flat_residual_support_local` | `GenericSupportLocalSummation.lean:21` | False | `:91` (same file) |
| `flat_of_support_local_coefficients` | `GenericSupportLocalCoefficients.lean:183` | False | `GenericSupportLocalSummation.lean:61` |
| `Result.flat_residual_of_factor_support` | `GenericTupleSupport.lean:157` | False | `GenericSummationRealization.lean:129` |
| `Result.flat_residual` | `GenericTupleRealization.lean:171` | False | `GenericTupleSupport.lean:180` |
| `flat_of_local_coefficients` | `GenericSupportedPolynomial.lean:254` | False | `GenericRealization.lean:195`, `GenericTupleRealization.lean:211` |
| `TailRates.flat_of_residuals` | `GenericSupportedPolynomial.lean:130` | False | `GenericSupportLocalCoefficients.lean:222`, `GenericSupportedPolynomial.lean:280` |
| `rate_of_restricted_support` | `GenericSupportedPolynomial.lean:32` | False | `GenericSupportLocalCoefficients.lean:139`, `GenericSupportedPolynomial.lean:98` |
| `uniform_bound_of_rate` | `GenericRealization.lean:38` | False | `GenericRealization.lean:194`, `GenericTupleRealization.lean:211`, `GenericSupportLocalSummation.lean:61` |
| `exists_realization` | `GenericTupleRealization.lean:80` | False | `GenericSummationRealization.lean:66` |
| all 6 `smooth_*Components` / `*_local_sum` | `GenericTupleSupport.lean:29,38,54,75,89,114` | False | only `GenericTupleSupport.lean:183-188` and `GenericSupportLocalSummation.lean:94-99` |
| `norm_jet_mul_at`, `rate_mul_at`, `mul_zero_germ`, `iteratedFDeriv_mul_eq_zero_of_zero_germ`, `smooth_mul_(inv_)of_support_local`, `smooth_evalTerms(_of_products)`, `termTail`, `termsTail`, `termsTail_of_products`, `mul_coefficient_(support_)local`, `TailRates.fixed` | various | False | only inside the same dead cluster |

So my grep-based conclusion and parent's graph agree: **the entire generic support-local
realization/flatness cluster is unreachable from the four headline theorems.** Every consumer I was
asked to audit for (B), (C) and (D) is itself out of cone. Concretely for the brief's list:
`GenericTupleSupport.lean:172,174` (in `flat_residual_of_factor_support`, out of cone),
`GenericSupportLocalSummation.lean:83,85,122,124` (out of cone),
`GenericSummationRealization.lean:91,93` (out of cone),
`GenericSupportLocalCoefficients.lean:151-214` (out of cone). The (B)/(C)/(D) verdicts above
therefore stand as "this library is clean" rather than "the headline proof is clean via this path".

**LOUD instrument note (over-approximation is real and I can name the mechanism).** Two of the
`in_cone = True` flags in my scope are demonstrably false positives caused by matching a reference
token against a **string** suffix of the qualified name rather than a **dot-segment** suffix:

* `NavierStokes.GenericDifferentialPolynomial.rate_filter_mono` (`GenericSupportedPolynomial.lean:14`)
  is flagged True, but its only four callers are `GenericSupportLocalCoefficients.lean:126` and
  `GenericSupportedPolynomial.lean:26,27,89` — all out of cone. `"rate_filter_mono".endswith("filter_mono")`
  is true, and `Filter.Eventually.filter_mono` is used all over the in-cone part of the repo
  (e.g. `GenericSupportLocalCoefficients.lean:112`, `GenericSummationRealization.lean:109-110`).
* `NavierStokes.GenericDifferentialPolynomial.FieldFactor.zero` (`GenericFactorSupport.lean:56`)
  is flagged True, yet `grep -rn 'FieldFactor' --include=*.lean . | grep -v GenericFactorSupport`
  returns **nothing** — `FieldFactor` is never named outside its defining file. Any `Nat.zero`-style
  token ending in `.zero` will match it.
* Same class of artifact explains `Expression.eval`, `TailRates.add`, `ApproximationRates.tail`,
  `Expression.zero_germ` (`zero_germ` alone has 581 grep hits across unrelated declarations) being
  flagged True while every theorem that actually *uses* them is flagged False.

Recommended fix if the graph is to be used for stronger claims: require the matched suffix to start
at a `.` boundary (or resolve the namespace stack for references, not just for declarations), then
recompute. The direction of the bias is safe for **exclusion** claims (out-of-cone is conservative:
a decl can only be wrongly marked *in*), so all `in_cone = False` verdicts above — the ones my
report relies on — are unaffected.
