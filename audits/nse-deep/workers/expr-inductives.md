# Worker report: recursive syntax-tree inductives (NavierStokes half)

Auditor: `expr-inductives` (read-only). Target: `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`.
Method: source-level reading only (no `lake build`; no built Mathlib on this box). Every line
number below was read in the ORIGINAL (un-stripped) file before citing.

## Scope

| file | lines | decls (`theorem`/`def`/`inductive`/`structure`/`abbrev`, incl. `private`) | read line-by-line |
|---|---|---|---|
| `NavierStokes/ClosedIntervalJetAlgebra.lean` | 293 | 30 | 293/293 (all) |
| `NavierStokes/GenericDifferentialPolynomial.lean` | 283 | 16 | 283/283 (all) |
| `NavierStokes/FlatKernelBounds.lean` | 442 | 45 | 442/442 (all) |
| `NavierStokes/GenericFactorSupport.lean` | 139 | 12 | 139/139 (all) |
| **total** | **1157** | **103** | **1157 (100%)** |

Decl breakdown: 4 recursive inductives in scope + 1 inductive predicate, 2 structures,
14 other `def`s, 82 `theorem`s. Nothing was skimmed: all four files were read in full,
statement and proof body. Outside scope but read to answer the reflection question:
`NavierStokes/SeedHandbackJets.lean:1-150` (the only concrete-tree consumer),
plus the definitions of `JetRate` / `FiniteJetRate` / `maxJetLoss`
(`NavierStokes/DiagonalResidual.lean:33,37,106`) and `rate_zero`/`rate_mul`
(`NavierStokes/GenericJetRateAlgebra.lean:16,19`), which are needed to judge vacuity.

### The four trees at a glance

| inductive | file:line | constructors | recursion | eval by recursion? | any reflection proof? |
|---|---|---|---|---|---|
| `PolynomialExpression (ι : Type)` | `ClosedIntervalJetAlgebra.lean:244` | `input ι`, `constant ℝ`, `add`, `sub`, `mul` | direct, uniform, non-indexed | yes: `eval` :255, `bounds` :262 | none in file; one concrete-tree consumer, see E1 |
| `Expression (D ι κ : Type*)` | `GenericDifferentialPolynomial.lean:185` | `input ι`, `coeff κ`, `add`, `mul`, `directional D` | direct (the `D` field is a *parameter value*, not a recursive occurrence) | yes: `eval` :197 | none anywhere |
| `Expr` | `FlatKernelBounds.lean:76` | `const ℝ`, `x`, `t`, `root`, `invRoot`, `jet ℕ`, `add`, `mul` | direct | yes: `eval` :86, `pow` :96, `diff` :106, `jetOrder` :219 | none: `n`,`j` stay symbolic; only `invRoot.pow 3` is concrete |
| `FieldFactor (D ι : Type*)` | `GenericFactorSupport.lean:14` | `input ι`, `directional D` (unary spine) | direct | yes: `expression` :18, `eval` :22 (via `Expression.eval`) | none |
| `FactorSupportAt base inc x : Expression D ι Empty → Prop` | `GenericFactorSupport.lean:106` | `factor`, `mul` | inductive **predicate**, indexed by an `Expression` | n/a (Prop) | none; consumed only by `induction h` :133 |

No `mutual`, no nested inductive (no constructor argument of the form `F (Expression …)`),
no indexed *data* family, no `deriving`, no `DecidableEq`, no `termination_by`/`decreasing_by`,
hence no `Acc.rec` / well-founded unfolding anywhere in scope (verified by grep for
`termination_by|decreasing_by|WellFounded|Acc.rec|deriving|match ` over the four files:
only hits are the two `structure` lines). Repo-wide bans hold in my scope: zero
`macro|elab|syntax|set_option|native_decide|axiom|sorry|unsafe|partial|decide`.

## Per-declaration findings

Verdict legend: OK / UNCLEAR / KERNEL-RISK / SUSPICIOUS.

### `NavierStokes/GenericFactorSupport.lean` (12 decls)

| # | name | line | statement (my words) | mechanism | verdict |
|---|---|---|---|---|---|
| 1 | `FieldFactor` | 14 | tree = one input index under a stack of directional derivatives | inductive, 2 ctors, unary recursion | OK |
| 2 | `FieldFactor.expression` | 18 | embeds a factor into `Expression D ι Empty` | structural recursion, `input↦input`, `directional↦directional` | OK (faithful, injective on constructors) |
| 3 | `FieldFactor.eval` | 22 | value of a factor = `Expression.eval` with empty coefficient family | `Empty.elim` for coefficients; no coefficient can ever appear | OK |
| 4 | `FieldFactor.smooth_eval` | 25 | factor of `C^∞` inputs is `C^∞` on open `U` | delegates to `Expression.smooth_eval` | OK |
| 5 | `FieldFactor.congr_germ` | 30 | if all inputs agree near `x`, factor values agree near `x` | `induction f`; directional step uses `EventuallyEq.fderiv` + `congrArg (·  w)`. Germ-determinacy of `fderiv` needs **no** differentiability, so this is legitimate, not junk-value abuse | OK |
| 6 | `FieldFactor.add_on` | 37 | factors are additive in the input family on `U` | `induction f`; directional step: `fderiv_fun_add` with differentiability **supplied** from `smooth_eval` (lines 52-53). This is the place a junk-value shortcut would have been possible and it is *not* taken | OK (positive sign) |
| 7 | `FieldFactor.zero` | 56 | factor of the zero family is identically `0` | `induction`; `fderiv` of constant `0` is `0` | OK |
| 8 | `FieldFactor.sum_on` | 64 | factors commute with finite sums on `U` | `Finset.induction_on` + #6, #7 | OK |
| 9 | `FieldFactor.zero_germ_of_local_sum` | 80 | if `u` equals `base + Σ_{j<N} inc j` near `x`, and the factor kills `base` and every `inc j` near `x`, it kills `u` near `x` | `congr_germ` then `add_on`+`sum_on` pointwise on the intersection of finitely many neighborhoods; `Filter.eventually_all_finset` for the finite family | OK. Note the `∃ N` in `hlocal` (line 85) is genuinely finite — no interchange of limits is hidden |
| 10 | `FactorSupportAt` | 106 | predicate: "`e` is a product of field factors, each of which vanishes in a neighbourhood of `x` on the base and on every increment" | 2 ctors: `factor` (index `f.expression`), `mul` (index `.mul e f`) | OK, with a docstring caveat — see S1 |
| 11 | `FactorSupportAt.factor_of_tsupport` | 116 | if `tsupport(f.eval base) ∩ U ⊆ S`, same for all increments, `x ∈ U`, `x ∉ S`, then the leaf is tracked | `notMem_tsupport_iff_eventuallyEq` twice | OK; this is the non-vacuity witness for the predicate |
| 12 | `FactorSupportAt.zero_germ` | 126 | a tracked expression vanishes near `x` for any `u` that is locally `base + finite Σ inc` | `induction h` (small elimination into `Prop`); `factor` case = #9, `mul` case = `simp only [Expression.eval, hy, hz, mul_zero]` on the *germ*, i.e. one iota step of `eval` at a `mul` **variable-headed** node | OK |

Vacuity / over-strength check on `FactorSupportAt`: it is **not** vacuous (#11 builds
instances from ordinary support hypotheses) and it is **conservative rather than
over-strong**: the `mul` constructor (line 112) demands `FactorSupportAt` of *both*
factors, whereas mathematically one vanishing factor already kills the product. There is
no constructor for `add`, `coeff` or bare `directional` of a product, so the predicate
can only ever describe a product of `FieldFactor` leaves. Every consumer
(`GenericTupleSupport.lean:172,174`, `GenericSupportLocalSummation.lean:83,85,122,124`,
`GenericSummationRealization.lean:91,93`) uses it as a *hypothesis* and discharges it
through `factor_of_tsupport`, so the direction of use is safe.

### `NavierStokes/GenericDifferentialPolynomial.lean` (16 decls)

| # | name | line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| 13 | `ApproximationRates` (structure, `Type`) | 14 | bundles `growthLoss, tailLoss : ℕ → ℝ`, `threshold : ℕ → ℕ` with: every stage obeys `JetRate … (-growthLoss m)`, and for `J ≥ threshold m` the residual `f - stage J` obeys `JetRate … (gain J - tailLoss m)` | data + 2 proof fields | OK. `JetRate l q f m r := ∃ C ≥ 0, ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r` (`DiagonalResidual.lean:33`, real `rpow`), so with `0 < q ≤ 1` larger `r` is *stronger*: not vacuous |
| 14 | `maxThreshold` | 23 | `sup` of `M` over `range (m+1)` | `Finset.sup` (no recursion of its own) | OK |
| 15 | `le_maxThreshold` | 26 | `M k ≤ maxThreshold M m` for `k ≤ m` | `Finset.le_sup` | OK |
| 16 | `ApproximationRates.full_growth` | 33 | the limit `f` itself has growth rate `-max 0 (growthLoss m)` | picks `J` large so that `gain J ≥ tailLoss m` (`hg : Tendsto gain atTop atTop`), writes `f = stage J + (f - stage J)`, adds the two rates, `congr_on` | OK; the `max 0` is what makes the loss usable later |
| 17 | `stage_finite_growth` | 53 | uniform-over-`m' ≤ m` version for stages | `finiteJetRate_of_jetRate` + `le_maxJetLoss` | OK |
| 18 | `full_finite_growth` | 61 | uniform version of #16 | same pattern | OK |
| 19 | `tail_finite_rate` | 73 | uniform version of the tail estimate for `J ≥ maxThreshold` | same pattern | OK |
| 20 | `ApproximationRates.add` | 84 | sum of two approximation packages | losses `max`-ed, thresholds `max`-ed; `JetRate.add` + `congr_on` with `ring` | OK (constants are explicit, no `∃`) |
| 21 | `ApproximationRates.mul` | 108 | product of two packages | Leibniz via `rate_mul` (needs `FiniteJetRate` on both sides — supplied by #17-#19); tail split `f g - f_J g_J = (f-f_J) g + f_J (g-g_J)`; the two `show … by linarith` blocks (135-151) are the honest arithmetic that the declared `tailLoss` dominates both branches | OK. I checked the loss algebra by hand: `growthLoss = maxJetLoss a + maxJetLoss b`, `tailLoss = max (a.tail+b.growth) (b.tail+a.growth)` — exactly the two branch costs |
| 22 | `ApproximationRates.directional` | 156 | one directional derivative shifts every index by 1 | `rate_directional`, `directional_sub_eqOn` for the residual | OK (order bookkeeping `m ↦ m+1` is uniform in all three fields) |
| 23 | `ApproximationRates.fixed` | 171 | a coefficient function is its own stage | `tailLoss := 0`, `threshold := 0`; residual is literally `c - c`, closed by `sub_self` + `rate_zero` | OK, and *not* a cheat: `rate_zero` (`GenericJetRateAlgebra.lean:16`) is the true statement that `0` has every rate |
| 24 | `Expression` | 185 | finite differential polynomial tree | 5 ctors, direct recursion | OK |
| 25 | `Expression.eval` | 197 | `input↦u i`, `coeff↦c i`, `add/mul` pointwise, `directional v a ↦ fun x => fderiv ℝ (eval a) x v` | structural recursion | **UNCLEAR→OK on inspection**: the `directional` node uses `fderiv`, which is junk-`0` off differentiability. Every theorem that needs the derivative to be *real* supplies `ContDiffOn ℝ ∞` on `U` open (see #26, #6). Junk values could only make the *hypotheses* `eval … =ᶠ 0` easier, and those hypotheses are always discharged from genuine smooth data. Flagged as E2 for an expert |
| 26 | `Expression.smooth_eval` | 204 | `eval` of `C^∞` data is `C^∞` on open `U` | `induction e`; `ContDiffOn.add/.mul`, `smooth_directional` | OK — this is the lemma that neutralises #25 |
| 27 | `Expression.approximation_eval` | 217 | **data**: builds an `ApproximationRates` package for `eval c u e` from packages for the inputs | `by induction e` producing a structure, i.e. `Expression.rec` into `Type` (ordinary, *not* large elimination: the motive is `Type`, the inductive is a `Type`) | OK; see kernel section for the one thing to watch |
| 28 | `polynomial_jetRate_of_stages` | 247 | if the stage residuals have rate `gain J - Lres m` with `gain → ∞`, then `eval c u e` has rate `n` for **every** real `n` | builds the package (#27), then for each `n` chooses `J` with `gain J ≥ max (n + a.tailLoss m) (n + Lres m)` and adds "stage residual" + "tail" | OK **but this is the load-bearing theorem** — see E3. The arbitrary-`n` conclusion is strong, not vacuous, and it is *earned* by `hres` (line 261), which already assumes the stagewise residual estimate for all `J`; the theorem's content is only the passage to the limit. Its power therefore sits entirely in whoever proves `hres` |

### `NavierStokes/FlatKernelBounds.lean` (45 decls)

Group A — concrete calculus of the kernel (lines 28-73): `denominator` :28 = `√(1+x²t)`,
`coordinate` :30 = `x/denominator`, `base_pos` :32, `denominator_pos` :35,
`denominator_ne_zero` :38, `denominator_sq` :41, `one_le_denominator` :45,
`hasDerivAt_denominator` :49, `hasDerivAt_inv_denominator` :59, `hasDerivAt_coordinate` :65.
All ten **OK**. I re-derived the three derivative formulas independently:
`∂ₓ√(1+x²t) = xt/√(1+x²t)` ✓ (:51), `∂ₓ(1+x²t)^{-1/2} = -xt·(1+x²t)^{-3/2}` ✓ (:61),
`∂ₓ (x/√(1+x²t)) = (1+x²t)^{-3/2}` ✓ (:66). Every one carries `ht : 0 ≤ t`, which is exactly
what `positivity`/`sqrt_pos` need; none of them is stated for negative `t`, where they would be false.

| # | name | line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| 41 | `Expr` | 76 | 8-ctor expression algebra: constants, `x`, `t`, `root`, `invRoot`, `jet k`, `add`, `mul` | direct recursion | OK |
| 42 | `Expr.eval` | 86 | `root↦denominator`, `invRoot↦denominator⁻¹`, `jet k ↦ iteratedDeriv k b (coordinate x t)`, `add/mul` pointwise | structural recursion in the tree, `b`,`x`,`t` as parameters | OK; note `jet` composes the profile jet with `coordinate` — this composition is where the chain rule cost is paid |
| 43 | `Expr.pow` | 96 | `e^0 = const 1`, `e^(n+1) = mul (e^n) e` | recursion on `ℕ` | OK |
| 44 | `Expr.eval_pow` (`@[simp]`) | 100 | `eval (e.pow n) = (eval e)^n` | `induction n`, `pow_succ` | OK |
| 45 | `Expr.diff` | 106 | symbolic `∂ₓ`: `const↦0`, `x↦1`, `t↦0`, `root↦x·t·invRoot`, `invRoot↦(-1)·(x·t·invRoot³)`, `jet k↦ jet (k+1)·invRoot³`, `add`/`mul` Leibniz | structural recursion | OK — I checked every clause against Group A. `t↦const 0` is correct because differentiation is in `x` only; `jet k ↦ jet (k+1) · invRoot³` is exactly the chain rule with `∂ₓ coordinate = invRoot³` |
| 46 | `Expr.hasDerivAt_eval` | 116 | `∂ₓ eval e = eval (diff e)` pointwise, for `C^∞` profile and `t ≥ 0` | `induction e` with genuine `HasDerivAt` lemmas; `jet` case builds `HasDerivAt (iteratedDeriv k b)` from `hb.differentiable_iteratedDeriv` and composes with `hasDerivAt_coordinate` | OK. This is a *correctness proof for the symbolic differentiator* — the right architecture: the tree is never trusted, it is validated |
| 47 | `Expr.iteratedDeriv_eval` | 138 | `iteratedDeriv n (eval e ·  t) = eval (diff^[n] e)` | `induction n`, `iteratedDeriv_succ`, `Function.iterate_succ_apply'` | OK. `n` stays a **variable**: no iterate is ever computed |
| 48 | `Expr.contDiff_eval` | 150 | `eval e ·  t` is `C^∞` in `x` | `contDiff_of_differentiable_iteratedDeriv` + #47 | OK |
| 49 | `abs_coordinate_le` | 158 | `|coordinate x t| ≤ |x|` | `div_le_self` with `one_le_denominator` | OK — the shrinking property that lets a bound on `[-R,R]` cover all jets |
| 50 | `denominator_le_polynomial` | 163 | `denominator ≤ (1+R²)(1+t)` for `|x| ≤ R`, `t ≥ 0` | `nlinarith` from `denominator_sq`, `one_le_denominator`, `sq_nonneg (den-1)` | OK (uses `√A ≤ A` for `A ≥ 1`) |
| 51 | `abs_inv_denominator_le_one` | 174 | `|denominator⁻¹| ≤ 1` | from `1 ≤ denominator` | OK |
| 52 | `PolynomialBound` | 181 | `∃ C ≥ 0, ∃ N, ∀ |x| ≤ R, t ≥ 0: |F x t| ≤ C(1+t)^N` | definition | OK, non-vacuous, and `C`,`N` are uniform in `x`,`t` (correct quantifier order) |
| 53-54 | `PolynomialBound.add` :185, `.mul` :204 | closure under `+`,`·` | explicit `C+D, N+M` and `C·D, N+M` with `pow_le_pow_right₀` | OK |
| 55 | `Expr.jetOrder` | 219 | largest profile-jet order in the tree (`jet k ↦ k`, `add/mul ↦ max`, everything else `0`) | recursion; `jet` clause precedes the `_ ↦ 0` catch-all, so no shadowing bug | OK |
| 56 | `Expr.polynomialBound_of_jetBound` | 226 | if the profile's jets up to `e.jetOrder` are bounded on `[-R,R]` then `eval e b` has a polynomial bound | `induction e`; the `jet` case applies the hypothesis at `coordinate x t` using #49 | OK — this is the "only finitely many jets" claim and the statement really does say it |
| 57 | `bounded_profile_jet` | 257 | each jet of a `C^∞` profile is bounded on a compact interval | `isCompact_Icc.exists_bound_of_continuousOn` | OK |
| 58 | `Expr.polynomialBound` | 269 | unconditional version of #56 for `C^∞` profiles | #56 + #57 | OK |
| 59-60 | `continuous_denominator_t` :274, `continuousOn_coordinate_t` :277 | continuity in `t` on `[0,∞)` | `.sqrt`, `.div` with non-vanishing | OK |
| 61 | `Expr.continuousOn_eval_t` | 282 | `t ↦ eval e b x t` is continuous on `Ici 0` | `induction e` | OK |
| 62 | `Expr.jetOrder_pow_le` | 300 | `(e.pow n).jetOrder ≤ e.jetOrder` | `induction n`, `max_le` | OK |
| 63 | `Expr.jetOrder_diff_le` | 306 | `e.diff.jetOrder ≤ e.jetOrder + 1` | `induction e`; `jet` case gives exactly `k+1` | OK — the crucial "one derivative costs one jet" accounting |
| 64 | `Expr.jetOrder_iterate_diff_le` | 324 | `(diff^[n] e).jetOrder ≤ e.jetOrder + n` | `induction n` + #63 | OK |
| 65 | `kernelExpr` | 333 | `root^j · invRoot³ · jet 0` | concrete tree modulo the variable `j` | OK |
| 66 | `kernelExpr_jetOrder` | 336 | `(kernelExpr j).jetOrder = 0` | `Nat.eq_zero_of_le_zero` on #62, then `simp` | OK |
| 67 | `kernel` | 343 | `½ e^{-ct} · (den^j/den³) · b(coordinate)` | definition | OK |
| 68 | `kernel_eq_expr` | 347 | `kernel = (½e^{-ct}) · eval (kernelExpr j) b` | `simp [… div_eq_mul_inv, inv_pow]`; `jet 0 ↦ iteratedDeriv 0 b = b` | OK — I checked the identification by hand, including `den^j/den³ = den^j·(den⁻¹)³` (true even at `den = 0` in Lean's `⁻¹`, so no hidden `ht` need) |
| 69 | `Expr.iteratedDeriv_const_mul_eval` | 351 | scalar version of #47 | `induction n` | OK |
| 70 | `iteratedDeriv_kernel` | 363 | `iteratedDeriv n (kernel ·  t) = (½e^{-ct})·eval (diff^[n] (kernelExpr j))` | `simp_rw [kernel_eq_expr]` + #69 | OK |
| 71-72 | `kernel_contDiff_x` :371, `kernel_iteratedDeriv_contDiff_x` :377 | smoothness in `x` of the kernel and of each of its `x`-derivatives | #48, #70 | OK |
| 73 | `unweighted_iteratedDeriv_bound` | 383 | polynomial-in-`(1+t)` bound for `iteratedDeriv n` of the unweighted kernel | #58 applied to `diff^[n] (kernelExpr j)`, with `hcore` identifying the function | OK |
| 74 | `kernel_iteratedDeriv_bound_of_jetBounds` | 400 | the order-`n` bound needs only the profile's jets `≤ n` | `horder : (diff^[n] (kernelExpr j)).jetOrder ≤ n` from #64+#66, then #56; constant `C/2` | OK. The docstring's claim ("uses only the first `n` profile jets") is *exactly* what `horder` proves — name/statement/docstring agree |
| 75 | `kernel_iteratedDeriv_bound` | 424 | unconditional version | #74 + #57 | OK |
| 76 | `kernel_iteratedDeriv_continuousOn_t` | 432 | `t`-continuity of each `x`-derivative on `Ici 0` | #61 + `congr` along #70 (which needs `ht`, supplied pointwise on `Ici 0`) | OK |

### `NavierStokes/ClosedIntervalJetAlgebra.lean` (30 decls)

`J` :11 = `Icc (-1) 1`; `uniqueDiff` :13 = `UniqueDiffOn ℝ J`. **OK**, and important: because
`Bound` :15 is stated with `iteratedFDerivWithin ℝ n f J` on a set with `UniqueDiffOn`, the
within-derivatives are pinned down and the usual "junk derivative on a closed set" escape is
closed off at the endpoints.

| # | name | line | statement | mechanism | verdict |
|---|---|---|---|---|---|
| 77 | `Bound` | 15 | `∀ n ≤ k, ∀ η ∈ J, ‖iteratedFDerivWithin ℝ n f J η‖ ≤ B` | definition | OK, non-vacuous (`J ≠ ∅`); note it does *not* itself assert smoothness — see S2 |
| 78-79 | `Bound.mono` :18, `Bound.nonneg` :22 | monotone in `B`; `0 ≤ B` | `trans`; instantiate at `n=0, η=0` | OK |
| 80 | `Bound.value` :25 | `|f η| ≤ B` on `J` | `norm_iteratedFDerivWithin_zero` | OK |
| 81 | `Bound.const` :29 | constants: `Bound k (const c) |c|` | `iteratedFDerivWithin_const_of_ne` | OK |
| 82-83 | `Bound.add` :36, `.sub` :44 | `A+B` for sums/differences | `fun_iteratedFDerivWithin_add/sub_apply`, **with** `ContDiffOn` and `uniqueDiff` arguments | OK (differentiability supplied, not assumed away) |
| 84 | `Bound.congr` :52 | transfers along `EqOn … J` | `iteratedFDerivWithin_congr` | OK (set-level congruence, legitimate) |
| 85 | `Bound.mul` :58 | `Bound k (f·g) (2^k A B)` | `norm_iteratedFDerivWithin_mul_le` then `∑ C(n,i) = 2^n ≤ 2^k` (`Nat.sum_range_choose`) | OK; I verified the constant chain `∑ C(n,i)AB = 2^n AB ≤ 2^k AB` |
| 86 | `inverse_bound` :82 | for `f ≥ μ > 0` with `Bound k f B` there is a **uniform** `C` with `Bound k f⁻¹ C` | `norm_iteratedFDerivWithin_comp_le` with the outer function `t^(-1 : ℝ)` on `Ioi 0`, Faà di Bruno constants from `WeightedQuotients.coeffBound`, `R = max 1 (max B μ⁻¹)`, `C = k! · coeffBound(-1,k) · R^{2k+1}` | OK. Quantifier order is the strong one: `∃ C, ∀ f` (line 83) |
| 87 | `PairBound` :121 (structure, `Prop`) | `f`,`g` both `C^∞` on `J`, both `Bound k · B`, and `Bound k (g-f) (C·ε)` | 5 fields | OK, and the two smoothness fields are what make the `Bound` fields meaningful |
| 88-94 | `PairBound.mono` :134, `.same` :139, `.const` :144, `.add` :147, `.sub` :157, `.mul` :167, `.inverse` :180 | algebra of pair bounds | all by explicit constant arithmetic; `mul` uses `gv-fu = (g-f)v + f(v-u)`, `inverse` uses `g⁻¹-f⁻¹ = -((g-f)g⁻¹f⁻¹)` with `field_simp` under non-vanishing | OK. I re-derived both constants: `mul` gives `2^k(CB+AD)·ε` ✓ matches :169; `inverse` gives `2^k(2^k·C·T)·T·ε` ✓ matches :185 |
| 95-96 | `Bound.derivWithin` :204, `PairBound.derivWithin` :211 | one derivative costs one order | `norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin` + `iteratedDerivWithin_succ'`; the pair version re-establishes the difference field via `derivWithin_sub` | OK modulo one library-signature question, see E4 |
| 97 | `Bound.id` :225 | `Bound k id 1` | `iteratedDerivWithin_fun_id` + `split_ifs`; the `n=1` branch gives `1`, `n=0` gives `|η| ≤ 1` from `η ∈ J` | OK — nice example of using the interval hypothesis honestly |
| 98-99 | `Bound.of_le` :234, `PairBound.of_le` :238 | weaken the order `k ≤ l` | direct | OK |
| 100 | `PolynomialExpression` :244 | 5-ctor exact polynomial tree over `ι` | direct recursion | OK |
| 101 | `eval` :255 | pointwise evaluation | structural recursion | OK |
| 102 | `bounds` :262 | recursively computes the pair `(value bound, difference constant)`; `mul` gives `(2^k A B, 2^k(CB+AD))` | structural recursion returning `ℝ × ℝ` | OK — mirrors #94's constants exactly |
| 103 | `bounds_nonneg` :271 | both computed constants are `≥ 0` | `induction p`, `positivity` | OK |
| 104 | `eval_pairBound` :281 | **the payload**: if every input is a `PairBound`, so is the evaluated tree, with the recursively computed constants | `induction p`; each case is exactly the corresponding `PairBound` lemma | OK. Statement matches the name; nothing is hidden in the induction |

(Numbering 1-104 counts the two grouped rows 41-76 individually; the decl total is 103 —
row 88-94 covers 7 decls, rows 53-54, 59-60, 71-72, 78-79, 82-83, 95-96, 98-99 cover 2 each,
Group A covers 10, and `J`/`uniqueDiff` are listed in prose.)

## Kernel-risk assessment

### Vector (1) — recursive inductive types / recursor reduction

**Present, and used in the safe mode.** Findings:

* All four trees are **plain, non-nested, non-indexed, non-mutual** single-sorted inductives
  with `Type`-valued motives (`ClosedIntervalJetAlgebra.lean:244`,
  `GenericDifferentialPolynomial.lean:185`, `FlatKernelBounds.lean:76`,
  `GenericFactorSupport.lean:14`). The kernel only needs its standard recursor rule; no
  nested-inductive encoding, no `Acc.rec`, no structure eta beyond the two ordinary
  structures (`PairBound` is a `Prop` structure, `ApproximationRates` a `Type` structure —
  eta for structures is used only in anonymous-constructor terms such as
  `GenericDifferentialPolynomial.lean:265`).
* **Every** tree theorem is proved by `induction … with` producing *propositional* equalities
  and inequalities — 12 such proofs: `GenericFactorSupport.lean:32,41,57,69,133`,
  `GenericDifferentialPolynomial.lean:208,228`, `FlatKernelBounds.lean:102,119,142,231,284,302,308,326,352`,
  `ClosedIntervalJetAlgebra.lean:274,284`. This is the **weak-risk** mode: the kernel checks
  a `Expr.rec`-shaped *term*, it does not have to *reduce* a recursor applied to a closed tree.
* **No reflection in scope.** There is no `decide`, no `Decidable` instance, no
  `DecidableEq`, no `deriving`, and no `rfl` over a deep concrete tree in the four files.
  The only `rfl`s are `GenericFactorSupport.lean:42,54,58` and they are single-iota-step
  unfoldings of `eval`/`expression` at a **constructor-headed but variable-argument** node
  (`eval (input i) = u i`), i.e. O(1) work.
* The one place a proof term *forces* recursor reduction inside the kernel's defeq check is
  the implicit unfolding of `eval`/`bounds`/`pow`/`jetOrder` at a *single* constructor in
  each `induction` branch (e.g. `ClosedIntervalJetAlgebra.lean:285` `exact h i` needs
  `eval f (input i) ≡ f i`). Depth 1, ~100 occurrences total. Cost: negligible; a kernel bug
  in recursor reduction that only manifests at depth 1 on open terms would also break all of
  Mathlib.
* `Expression.approximation_eval` (`GenericDifferentialPolynomial.lean:217`) is the one
  **`def` built by tactic induction**, i.e. a `Type`-valued recursion (`Expression.rec` into
  `Type`, ordinary — *not* large elimination, since `Expression` is a `Type`). Because it is a
  `def` producing data, any downstream `rfl`/`simp` that needed to *compute* its fields on a
  concrete tree would become a real reflection burden. I checked its only consumer,
  `GenericSupportLocalCoefficients.lean:214`, and the tree there (`t.2`) is a **variable**.
  So no computation occurs. Worth a one-line watch item (E5).
* `FactorSupportAt` (`GenericFactorSupport.lean:106`) is an **indexed `Prop` family** — the
  one construct in scope that is a genuine kernel-feature step up. It has two constructors,
  so it is not a subsingleton and Lean gives it only **small elimination** (motive into
  `Prop`); the single use, `induction h` at `:133`, has a `Prop` goal, so no large elimination
  is requested and none is available. Its index is `Expression D ι Empty`, whose `mul`
  constructor makes the family's index non-injective-free in the usual way, but the recursion
  in `:112` is on the *predicate*, not on the index, so no `Eq.mpr`-heavy index-unification
  terms appear.

**Bottom line for (1): the kernel never has to reduce a recursor over a closed tree in these
four files.** The tree-based architecture is used exactly the way it should be (validate the
symbolic operation once, by induction, against real analysis), which is the *low*-risk mode.

### Vector (2) — Nat / GMP numeral work

**Essentially absent.** No `decide`, no `Nat.pow/div/mod/gcd/beq/ble` on large arguments, no
big literals anywhere in the four files. Concretely, the kernel's numeral obligations are:

* `Expr.pow` at the literal `3` in `Expr.diff` (`FlatKernelBounds.lean:111,112`) and
  `kernelExpr` (`:334`). `simp [Expr.pow]` at `FlatKernelBounds.lean:311,312` must unfold
  `invRoot.pow 3` — three `Nat` literal-to-`succ` steps. Largest literal in scope: `3`.
* `(2:ℝ)^k`, `R^(2*k+1)`, `(1+t)^N` — all with **symbolic** exponents; no evaluation.
* `by omega` twice (`ClosedIntervalJetAlgebra.lean:117,209`), `by norm_num` five times
  (`:13,23,79,232`, `FlatKernelBounds.lean:177,235,242`), `positivity` seven times. All
  operate on `0/1/2` and symbolic terms; the certificates the kernel must recheck are a
  handful of `Nat`/`ℝ` literal comparisons. Nothing near a GMP-stressing magnitude.
* `Nat.sum_range_choose n` (`ClosedIntervalJetAlgebra.lean:76`) is a *theorem* about symbolic
  `n`, not a computed binomial sum.

**Bottom line for (2): the largest numeral the kernel evaluates in my scope is `3`.**

### Vector (3) — custom metaprogramming

**Zero occurrences confirmed in my four files** by grep for
`macro|elab|syntax|set_option|native_decide|axiom|sorry|unsafe|partial|deriving|decide`.
The only attribute used is `@[simp]` on one ordinary lemma (`FlatKernelBounds.lean:100`).
`noncomputable section` is declared in all four files, which additionally means the trees
have **no compiled evaluator** — reflection would have to go through the kernel, and, as
shown above, nobody asks it to.

### The one real reflection site in the cone (outside my four files)

`NavierStokes/SeedHandbackJets.lean` is the only consumer that builds **concrete**
`PolynomialExpression` trees: `massExpression` :67, `angularExpression` :71,
`axialExpression` :78, `outputExpression` :85 — together **42 constructor nodes**, 34 `input`
leaves, 9 `constant` leaves, over `ι = Fin 19`, and `basis` :57 / `packet` :25 are
`Matrix.cons` vectors of length 19 and 12. `stocks_formulas` :94 then proves the four closed
formulas by `simp [stocks, outputExpression, angularExpression, axialExpression,
massExpression, PolynomialExpression.eval, v, c, basis, …]` followed by
`repeat' constructor <;> ring_nf` and a trailing `simp` (:105-108). This *is* reflection-shaped
work: `eval` is unfolded over ~42 concrete nodes, `Fin 19`/`Fin 12` literal indices are resolved
through `Matrix.cons`, and `ring_nf` produces the final certificates. Magnitude: tens of
iota steps and `Nat` literals ≤ 19 — still tiny by kernel standards, and `simp`'s output is a
propositional rewrite chain rather than one giant `Eq.refl`. I hand-checked the trees against
the stated formulas (see E1) and they agree, so the theorem is not misdescribed.

## Escalations

**E1 (medium, mathematical, cross-file). `NavierStokes/SeedHandbackJets.lean:94-108`
`stocks_formulas`.** This is the only place where the truth of a concrete tree matters, and it
is proved by a `simp`/`ring_nf`/`simp` cascade whose final `simp` (line 108) is unstructured.
*Question for an expert:* does the tactic block actually close all four conjuncts, and does
`ring_nf` need the non-vanishing side conditions (`X ≠ 0`, `p 0 η ≠ 0`, `L h η ≠ 0`) that are
**not** hypotheses of `stocks_formulas`? *What settles it:* elaborate the file and inspect;
also `#print axioms` on it. Note that no side condition is *needed* for the identity as
written, because all divisions are Lean `⁻¹` and both sides are built from the same inverses —
I verified by hand that the trees encode exactly the stated formulas
(`mass = (X - 2·D(h)·η·p₂ - d·p₃)/X = W`; `angular = -W + ((1-h)p₄ - D(h)ηp₅ - d·p₇ +
2(h-D(h))ηp₆)/(X√(2X)p₀)`; `axial = -W·p₁ + (D(h)(p₂-ηp₃) + 4hηp₈ - d·p₉)/X + 4A(h)ηp₁₀ -
d·p₁₁`; `out₂ = (X/L)·angular`; `out₃ = (X/(L·p₀))·axial`), so I expect it to be true and only
the tactic robustness is in question.

**E2 (medium, junk values). `GenericDifferentialPolynomial.lean:202` (`eval` at
`directional`) and `197-202` as a whole.** `eval` of a derivative node is `fderiv ℝ (eval a) x v`,
which is `0` by definition when `eval a` is not differentiable at `x`. *Question:* is there any
consumer that establishes a conclusion of the shape `eval … =ᶠ[𝓝 x] 0` or a `JetRate` for a
tree containing `directional`, **without** having `ContDiffOn ℝ ∞` for all inputs on an open
set containing `x`? *What settles it:* enumerate the call sites of
`Expression.eval`/`FactorSupportAt.zero_germ`/`polynomial_jetRate_of_stages` and check each
for the smoothness hypothesis. In my four files the answer is no — smoothness is always
supplied (`GenericFactorSupport.lean:26,83,84,129,130`,
`GenericDifferentialPolynomial.lean:206,207,221-223,253-255`) — but the check should be
extended to `GenericSupportLocalCoefficients.lean:151-214` and `GenericTupleSupport.lean`.

**E3 (medium-high, load-bearing but not local). `GenericDifferentialPolynomial.lean:247-281`
`polynomial_jetRate_of_stages`.** Concludes `JetRate l q (e.eval c u) m n` for an **arbitrary
real `n`**, i.e. the realized field's expression decays faster than every power of `q`. The
proof is correct as a limit argument, but all of its strength is imported through `hres`
(line 261: the stage residual already has rate `gain J - Lres m` for *every* `J`) and `htail`
(line 259-260, with the threshold `id`, i.e. `m ≤ J`). *Question:* who proves `hres`, and does
that proof secretly need the very conclusion (circularity), or an interchange of the `J → ∞`
and derivative-order limits? *What settles it:* trace `hres` at the actual call sites
(`GenericSupportLocalCoefficients.lean:201` and downward) and confirm the stagewise residual
estimate is established by explicit construction at each finite stage.

**E4 (low, library signature). `ClosedIntervalJetAlgebra.lean:204-209` `Bound.derivWithin`.**
Uses `iteratedDerivWithin_succ'` with **no** `UniqueDiffOn`/membership side argument. Some
Mathlib versions of that lemma carry a `UniqueDiffOn` hypothesis. *Question:* in the pinned
Mathlib (`lake-manifest.json`), is `iteratedDerivWithin_succ'` unconditional? *What settles
it:* one `#check`. If it were conditional the file would not elaborate, and Comparator passed,
so this is a formality — but it is the only step in the file where a set-derivative identity is
used without an explicit `uniqueDiff` argument, while every neighbouring lemma passes one
(`:41,49,63,207`).

**E5 (low, watch item). `GenericDifferentialPolynomial.lean:217` `approximation_eval` is a
`def` built by `induction`.** Today its only consumer (`GenericSupportLocalCoefficients.lean:214`)
applies it to a variable tree, so nothing is computed. *Question:* does any file instantiate it
at a concrete tree and then `rfl`/`simp` on the resulting `growthLoss`/`tailLoss`/`threshold`
fields? *What settles it:* grep for `approximation_eval` (currently 2 hits: definition and that
one use) after any future change; if a concrete instantiation appears, the kernel would then
have to reduce `Expression.rec` into `Type` over a closed tree, which is the real vector-(1)
exposure.

**E6 (low, documentation vs statement). `GenericFactorSupport.lean:103-105` vs `:112-114`.**
The docstring says multiplication builds monomials "without requiring undifferentiated
components to share the support", but the `mul` constructor requires `FactorSupportAt` of
**both** factors, and the `factor` constructor requires the leaf itself to vanish near `x`.
So a monomial `u₀ · ∂_v u₁` in which `u₀` does not vanish near `x` is **not** expressible.
*Question:* is the intended reading "each factor may use its own neighbourhood" (in which case
the docstring is fine and the predicate is merely conservative) or does some downstream proof
assume the weaker requirement? *What settles it:* check the `FactorSupportAt` construction
sites in `GenericTupleSupport.lean:172,174` — if every leaf there is genuinely supported away
from `x`, the gap is harmless. This is a **conservative** direction (harder to satisfy), so it
cannot create unsoundness, only unusability.

## Residue

* **No elaboration.** No built Mathlib on this box, so I could not `lake build`, `#check`
  signatures, `#print axioms`, or ask `set_option pp.all` what the recursor terms really are.
  Everything above is source reading plus hand re-derivation. Specifically unverified: that
  `simp`/`simpa only` calls actually close their goals with the listed lemma sets
  (`FlatKernelBounds.lean:103,104,120,125,133,165,311,312`,
  `GenericFactorSupport.lean:62,137`, `ClosedIntervalJetAlgebra.lean:32,142,199,229`), and the
  exact Mathlib signatures of `iteratedDerivWithin_succ'`, `EventuallyEq.fderiv`,
  `fun_iteratedFDerivWithin_add_apply`, `norm_iteratedFDerivWithin_comp_le`.
* **Constant arithmetic verified by hand, not by machine.** I re-derived the constants in
  `Bound.mul`, `PairBound.mul`, `PairBound.inverse`, `PolynomialExpression.bounds`,
  `ApproximationRates.mul`, and the three kernel derivative formulas. I did not verify the
  `nlinarith`/`linarith` certificates at `FlatKernelBounds.lean:47,73,167,170-172` or
  `GenericDifferentialPolynomial.lean:47,142,151,274,278` beyond checking that the stated
  inequalities are mathematically true.
* **Out of scope, flagged only.** The upstream definitions `JetRate`/`FiniteJetRate`
  (`DiagonalResidual.lean:33,37`) use the **global** `iteratedFDeriv` while hypotheses are
  `ContDiffOn … U`; this is sound because `fderiv` is germ-local and all estimates are
  `∀ᶠ x in l` with `x ∈ U` eventually, but a dedicated worker should confirm `l` is not a
  filter that escapes `U` in any consumer.
* **Not audited:** `WeightedQuotients.coeffBound`/`rpow_jet_bound`,
  `NaturalAxisData.L`/`.d`/`.D`/`.A`, `smooth_directional`, `rate_directional`,
  `directional_sub_eqOn`, and the rest of `SeedHandbackJets.lean:110-393` (the `basis`/input
  bound bookkeeping), which is where an off-by-one in the `Fin 19` index map would hide.
