# Worker report: Euler higher-energy **uniformity in the derivative order `m`** (`6^m` in `tameEnergyConstant`)

Repo audited (READ-ONLY): `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`
(clone of `openai/NavierStokesAndEuler`). **Nothing under `NSE/` was modified.**
No Mathlib build on this box (disk full) and no vendored Mathlib source, so this is
source-level reading (grep + line-by-line) only. No `lake build` was run.

Predecessor read first: `workers/euler-gronwall.md`, section **B3** and **Escalation 1**
(the `tameEnergyConstant m = 6·h3ProductConstant·∑_{n≤m}6ⁿ` growth item).

**Headline (the assigned item CLOSES): every consumer of the higher-energy estimate fixes the
order `m` (or `q`) BEFORE the constant is produced.** The universal-quantifier order is
`∀ q, ∃ C, …` in all three consumer chains, never `∃ C, ∀ q`, and never a series in `m`.
The existence *time* is built from order **3** only, so `6^m` never shortens the interval.
The Euler Gevrey layer neither consumes `tameEnergyConstant` nor lives downstream of it
(it is strictly **upstream** in the import DAG), and the top-level Euler claim contains **no
analyticity / Gevrey / radius-of-convergence statement at all**. Kernel-risk surface of this
scope is empty.

---

## Scope

Files read **in full, line by line** (114 declarations total, `theorem`/`def`, zero `inductive`,
zero `structure`; counts re-derived from source and cross-checked against `CONE.csv`):

| file | lines | theorem | def | decls | read |
|---|---|---|---|---|---|
| `Euler/OrdinaryTameEnergy.lean` | 146 | 8 | 3 | 11 | lines 75–146 line-by-line; 1–74 skimmed (audited by `euler-gronwall`) |
| `Euler/OrdinaryEulerHigherEnergy.lean` | 110 | 10 | 3 | 13 | **all 13, line-by-line** |
| `Euler/OrdinaryRegularizedEnergy.lean` | 170 | 10 | 4 | 14 | **all 14, line-by-line** |
| `Euler/OrdinaryEulerCauchy.lean` | 123 | 7 | 1 | 8 | **all 8, line-by-line** |
| `Euler/OrdinaryEulerGradientControl.lean` | 143 | 13 | 3 | 16 | lines 100–143 line-by-line (5 decls); rest skimmed |
| `Euler/OrdinaryEulerL2Stability.lean` | 161 | 10 | 3 | 13 | lines 120–161 line-by-line (4 decls) for item **D**; rest read by `euler-gronwall` |
| `Euler/OrdinaryEulerLimit.lean` | 124 | 7 | 4 | 11 | lines 80–115 line-by-line (5 decls); rest skimmed |
| `Euler/OrdinaryEulerLocalExistence.lean` | 157 | 10 | 5 | 15 | lines 100–158 line-by-line (8 decls); rest skimmed |
| `Euler/OrdinaryH3Products.lean` | 171 | 12 | 1 | 13 | lines 1–30 line-by-line; rest skimmed (audited by `euler-gronwall`) |

Also read for the top-level-claim check: `Euler.lean` (1 line), `Euler/EulerSingularity.lean:100–153`.
Also read: `Euler/EulerProof.lean:8226–8235` and `Euler/MeanCutoffCurlBound.lean:19–22`
(the two embedding constants), `Euler/EulerProof.lean` import header (lines 1–20).
**Line-by-line: 61 declarations. Skimmed: 53.**

Delegated corroboration (read-only child `gevrey-index`, report
`workers/_sub-gevrey-index-radius.md`): the internal Gevrey weight form and quantifier order of
`pressure_gevrey_majorant` / `pressure_word_sum_majorant` (`Euler/EulerProof.lean:5120,5170`).
My part-C conclusion below does **not** depend on that child: it is settled by the import DAG.

---

## A. Consumers of `tameEnergyConstant` and of the higher-energy estimate — full grep output

`grep -rn --include=*.lean -E "tameEnergyConstant" .` (35 hits, **five** files, complete):

```
Euler/OrdinaryEulerCauchy.lean:78:    refine ⟨wordCount q*Real.sqrt (wordCount q*R^2*Real.exp (tameEnergyConstant q*M*T)),?_⟩
Euler/OrdinaryEulerHigherEnergy.lean:58,67,75,78,87,92,97,104   (the estimate itself)
Euler/OrdinaryRegularizedEnergy.lean:30,49,72,76,78,86,88,91,96,103,110,114,121,126,129,141,143,145,160
Euler/OrdinaryEulerGradientControl.lean:122,129,137
Euler/OrdinaryTameEnergy.lean:86 (def), 89, 126, 144
```

`grep -rn -E "\bhigher_energy_of_h3\b"` — **exactly two** hits (definition + one consumer):

```
Euler/OrdinaryEulerCauchy.lean:83:    apply ((V k).higher_energy_of_h3 q hq M (hM k) t).trans
Euler/OrdinaryEulerHigherEnergy.lean:101:theorem higher_energy_of_h3 (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
```

`\binteger_energy_uniform\b`:

```
Euler/OrdinaryEulerHigherEnergy.lean:84 (def), :99 (in tensorNorm_uniform), :105 (in higher_energy_of_h3)
Euler/OrdinaryEulerGradientControl.lean:123:  U.integer_energy_uniform m hm _ (U.wordBound_of_gradientIntegral G hG) t
```

`\binteger_energy_bound\b`: `OrdinaryEulerHigherEnergy.lean:64` (def), `:88` (used by `integer_energy_uniform`). No other consumer.

`\btensorNorm_uniform\b`: `OrdinaryEulerHigherEnergy.lean:94` (def), `OrdinaryEulerGradientControl.lean:130`. No other consumer.

Second-level consumers (`\ball_order_bounds_of_h3\b`, `\blimitEvolutionOfH3\b`, `\bregularized_all_order\b`):

```
Euler/OrdinaryEulerCauchy.lean:70 (def), :101, :111, :120
Euler/OrdinaryGradientLimit.lean:60, :73, :86
Euler/OrdinaryEulerCauchy.lean:97 (def limitEvolutionOfH3), :109, :110, :119
Euler/OrdinaryEulerLocalCauchy.lean:81:  refine ⟨L,hL,hLT,limitEvolutionOfH3 W hL M hM hb hc.cauchySeq,?_⟩
Euler/OrdinaryEulerEndpoint.lean:71:  let W := limitEvolutionOfH3 V hT M hb hb0 hc.cauchySeq
Euler/OrdinaryRegularizedEnergy.lean:153 (def regularized_all_order)
Euler/OrdinaryEulerLocalExistence.lean:121:  obtain ⟨M,hM⟩ := regularized_all_order A q
```

`\bhigher_energy_of_gradientIntegral\b`, `\bhigher_tensorNorm_of_gradientBound\b`: **one hit each — their own
declaration**. Both are DEAD (see Escalation 3).

So the complete consumer set of the `6^m` constant is: (i) `all_order_bounds_of_h3`
(`Euler/OrdinaryEulerCauchy.lean:70`) → `limitEvolution`; (ii) `regularized_all_order`
(`Euler/OrdinaryRegularizedEnergy.lean:153`) → local existence; (iii) `regularizedTime` /
`short_energy` (`:125`, `:88`), which use `tameEnergyConstant` **3** only; (iv) three dead
gradient-control corollaries.

---

## B. Does any consumer need uniformity in `m`? No — quantifier order, verbatim

**(i) `all_order_bounds_of_h3` (`Euler/OrdinaryEulerCauchy.lean:70-73`) — `q` fixed first.**

```lean
theorem all_order_bounds_of_h3 (V : ℕ → Evolution T hT) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : ∀ q, ∃ R : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ R) :
    ∀ q, ∃ C : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ C := by
```

The conclusion is `∀ q, ∃ C`, i.e. `intro q` (`:74`) happens **before** the witness
`⟨wordCount q*Real.sqrt (wordCount q*R^2*Real.exp (tameEnergyConstant q*M*T)),?_⟩` (`:78`) is
produced. `6^q` is inside a per-`q` constant. The *uniformity that matters* here is in the
approximation index `k`, and the exponent `tameEnergyConstant q*M*T` is `k`-free.
The consumer interface it feeds requires exactly this shape
(`Euler/OrdinaryEulerLimit.lean:86`, `:80`, `:91`, `:99`, `:106`):

```lean
    (hb : ∀ q, ∃ M : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ M)
```

and `limitEvolution` (`Euler/OrdinaryEulerLimit.lean:85-88`) only ever *instantiates* it at a
single order to build the object: `(Classical.choose (hb 3)) (Classical.choose_spec (hb 3))`.
`limitEvolution_bound` (`:105-110`) likewise takes `(q : ℕ) (M : ℝ) (hM : …)` with `q` bound
first. **No single constant over all `q`, no sum over `q`.** ⇒ `6^q` harmless.

**(ii) `regularized_all_order` (`Euler/OrdinaryRegularizedEnergy.lean:153-160`) — `q` is a
parameter, before `∃ C`.**

```lean
theorem regularized_all_order (A : SmoothL2Field Space) (q : ℕ) :
    ∃ C : ℝ, ∀ (S : SmoothingOperator)
      (U : RegularizedEvolution S (regularizedTime A) (regularizedTime_pos A).le), …
  let m := max 3 q
  refine ⟨wordCount q*Real.sqrt (wordEnergy m A*
    Real.exp (tameEnergyConstant m*regularizedH3 A*regularizedTime A)),?_⟩
```

`q` is a binder of the theorem, `C` is chosen after it, `m := max 3 q` (`:158`). Its only
consumer keeps the same shape: `regularizedSolution_bounds`
(`Euler/OrdinaryEulerLocalExistence.lean:118-122`) states `∀ q, ∃ M, ∀ n t, …` and obtains the
witness *after* `intro q` (`:120-121`). Downstream, `localLimit`/`localEvolution`
(`:133`, `:139-143`) only instantiate it at `q = 4`:
`Classical.choose (regularizedSolution_bounds A hA 4)`. ⇒ `6^m` harmless.

**(iii) The crucial one — the existence TIME does not depend on `m`
(`Euler/OrdinaryRegularizedEnergy.lean:125-126`):**

```lean
def regularizedTime (A : SmoothL2Field Space) : ℝ :=
  (2*(1+tameEnergyConstant 3)*(1+wordEnergy 3 A))⁻¹
```

The literal `3`. `short_energy`'s smallness hypothesis is likewise
`tameEnergyConstant 3*T ≤ (1+U.energy 3 …)⁻¹/2` (`:88`), and `regularized_h3` (`:136-151`)
discharges it for `T = regularizedTime A` by the arithmetic at `:143-147`. So the lifespan
comes from the **H³** quadratic estimate only; the `6^m` constant enters **after** the time is
fixed, and only as a per-order amplitude. This is exactly what the docstring at
`Euler/OrdinaryEulerHigherEnergy.lean:4-6` ("no order-dependent shortening of time") claims, and
here the statements bear it out: the same `T`/`Icc 0 T` appears for every `m` in
`integer_energy_bound` (`:64-67`), `integer_energy_uniform` (`:84-87`), `higher_energy_of_h3`
(`:101-104`).

**(iv) The gradient-control variants** (`Euler/OrdinaryEulerGradientControl.lean:119`, `:125`,
`:132`) all take `(m : ℕ) (hm : 3 ≤ m)` as leading binders and produce a bound with
`tameEnergyConstant m` in the exponent, per `m`. They are dead code (no consumer), so they
cannot even in principle be the place where uniformity is needed.

**Conclusion for B: every consumer fixes `m` first. The item closes.** No `∃ C, ∀ m`, no
`∑_m`, no `limsup_m`, no radius `R` built from a supremum over `m` anywhere in the consumer set.

---

## C. The Gevrey layer: it cannot consume the tame-energy constant (import DAG), and there is no analyticity claim to break

Three independent pieces of evidence.

1. **Zero name-level contact.**
   `grep -rn -E 'tameEnergyConstant|wordEnergy|integer_energy' Euler/*Gevrey*.lean Euler/Gevrey*.lean`
   → **no output**. `grep -rln 'EulerOrdinarySobolev' Euler/ | grep -i gevrey` → **no output**.
   `grep -rn -E 'import Euler.Ordinary' Euler/*Gevrey*.lean Euler/Gevrey*.lean` → **no output**.
   Repo-wide, `tameEnergyConstant` occurs in exactly 5 files, none of them Gevrey (section A).

2. **The import DAG runs the other way — Gevrey is UPSTREAM of the energy layer.**
   ```
   Euler/OrdinarySmoothWords.lean:3:import Euler.SmoothL2Gevrey
   Euler/OrdinarySobolevTower.lean:2:import Euler.FieldTowerGraphGevrey
   Euler/OrdinaryWordBounds.lean:3:import Euler.GevreyProductLp
   ```
   The `Ordinary…` (energy/Grönwall) files *import* Gevrey files; no Gevrey file imports an
   `Ordinary…` file. Since imports are acyclic, nothing in the Gevrey layer can mention a name
   defined at `Euler/OrdinaryTameEnergy.lean:86`. In particular
   `pressure_gevrey_majorant` / `pressure_word_sum_majorant` live in
   `Euler/EulerProof.lean:5120` / `:5170`, and `Euler/EulerProof.lean` imports **only Mathlib**
   (header lines 1–20 are all `import Mathlib.…`) while 32 repo files import it — so it is a
   base file, strictly upstream of `tameEnergyConstant`. **The Gevrey majorants are producers of
   bounds for the packet construction, not consumers of the tame energy estimate.**

3. **There is no analytic / fixed-radius Gevrey claim in the top-level Euler theorem, so no
   Gevrey class can be silently weakened by a `6^m`.** `Euler.lean` is one line
   (`import Euler.EulerSingularity`), and the two headline theorems
   (`Euler/EulerSingularity.lean:115-127` `initialDatum_singularity`, `:133-151`
   `exists_compact_smooth_euler_singularity`) claim only: `ContDiff ℝ ∞` + `HasCompactSupport` +
   `≠ 0` + `divergence = 0` initial datum, `0 < duration ≤ 1`, existence iff `0 < T < duration`,
   `limsup … maximalC1Norm = ⊤` and `∫⁻ … maximalVorticityDensity = ⊤`. **No analyticity, no
   Gevrey index, no radius of convergence, no `∀ m` bound with a single constant.** A `6^m`
   amplitude at order `m` is compatible with `C^∞` (which is what is claimed) by definition,
   because `C^∞` is a per-order statement.

Corroboration of the *internal* Gevrey weight form (`R^m/m!` vs `R^m (m!)^s`) and of the
quantifier order inside `pressure_gevrey_majorant` was delegated to child `gevrey-index`
(`workers/_sub-gevrey-index-radius.md`). It can only *strengthen*, not overturn, points 1–3:
even a Gevrey-1 fixed-radius majorant proved **upstream** cannot be damaged by a constant
defined downstream of it.

---

## D. Bookkeeping: `l2_stability_of_h3` is dead — verified

`grep -rn --include=*.lean -E "\bl2_stability_of_h3\b" .` — complete output:

```
Euler/OrdinaryEulerL2Stability.lean:148:theorem l2_stability_of_h3 (U V : Evolution T hT) (M : ℝ)
```

**One hit: its own declaration.** No consumer repo-wide. `CONE.csv` agrees:
`Euler/OrdinaryEulerL2Stability.lean,148,theorem,EulerOrdinarySobolev.Evolution.l2_stability_of_h3,False,True`
(`in_cone=False`, in import closure only). Read line-by-line (`:148-158`): it is a correct,
non-vacuous corollary — `apply U.l2_stability V` with `K := 9*smoothEmbeddingConstant*M`, the
gradient bound supplied by `real_smooth_fderiv_le_H3 3 …` (`:154-155`) plus
`tensorNorm_eq` rewriting (`:156`) — not a stub, not `True`, not circular. Verdict: **OK, dead.**
Item closed.

---

## Per-declaration findings

Cone column is from `SafeVerifyAgent/audits/nse-deep/CONE.csv` (`in_cone`; all rows below have
`in_import_closure=True`).

| decl | file:line | statement (my words) | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `tameEnergyConstant` | `Euler/OrdinaryTameEnergy.lean:86` | `6*h3ProductConstant*(∑ n ∈ range (m+1), (6:ℝ)^n)` | plain `def`, no field/`M`/`T` argument — solution-independent, grows `~6^m` | True | **OK** (growth is real, harmless per B) |
| `tameEnergyConstant_nonneg` | `:89` | `0 ≤ tameEnergyConstant m` | `mul_nonneg`+`sum_nonneg`+`positivity`; no numeral evaluation | True | **OK** |
| `integerEnergyProduction` | `:93` | `2*∑_{n≤m}∑_{w:Fin n→Fin 3} ⟪∂^w A, ∂^w Q⟫` | `def` | True | **OK** |
| `eulerRhs_word_tame` | `:97` | per-word production `≤ 3·2ⁿ·h3ProductConstant·M·E_m` | `X := √(wordEnergy m A)`, `tame_transportCommutator`, Cauchy–Schwarz (`:117-121`); pressure+transport killed by `eulerRhs_pairing` (`:115`) | True | **OK** — coefficient `3·2ⁿ` bounds `3(2ⁿ-1)` (`:112`), honest |
| `integer_energy_tame` | `:123` | `integerEnergyProduction m A (eulerRhs A P) ≤ tameEnergyConstant m*M*wordEnergy m A` | `sum_le_sum` over `3ⁿ` words × `2ⁿ` per word ⇒ `6ⁿ`, `simp_rw`+`← sum_mul`, closed by `unfold tameEnergyConstant; ring` (`:144`) | True | **OK** — this is *exactly where the `6^m` is born*, and it is forced by counting `3ⁿ` words, not padded |
| `h3ProductConstant` | `Euler/OrdinaryH3Products.lean:16` | `1+13*smoothEmbeddingConstant+4*(1+3*sobolevConstant)^2` | `def` over two opaque Mathlib-derived embedding constants (`Euler/EulerProof.lean:8227`, `Euler/MeanCutoffCurlBound.lean:20`) | True | **OK** — no numeral, no field |
| `wordCount` | `Euler/OrdinaryEulerHigherEnergy.lean:17` | `∑_{n≤m} 3ⁿ` | `def` | True | **OK** |
| `tensorNorm_le_wordCount` / `tensorNorm_le_energy` | `:21`, `:28` | `Hᵐ` tensor norm ≤ `wordCount m ×` word bound | `sum_le_sum` + `← sum_mul`; `rfl` at `:26` only unfolds `wordCount` at *symbolic* `m` | True | **OK** |
| `integerEnergyPath` / `integerEnergyDerivative` | `:36`, `:39` | continuous energy path, its candidate derivative | `def`s; continuity from `U.velocity_continuous` | True | **OK** |
| `derivative_eq_eulerRhs` | `:42` | class derivative *is* `-u·∇u-∇p` | `field_ext`+`funext`+two pointwise rewrites | True | **OK** |
| `integerEnergy_hasDerivWithinAt` | `:48` | the candidate is the real one-sided derivative on `Icc 0 T` | `wordEnergy_hasDerivWithinAt` fed `U.time_law` | True | **OK** |
| `integerEnergyDerivative_bound` | `:56` | `d/dt E_m ≤ tameEnergyConstant m*M*E_m` under `∀ t, WordBound 3 M` | `integer_energy_tame` + `U.solenoidal`/`U.gradient` | True | **OK** |
| `integer_energy_bound` | `:64` | `E_m(t) ≤ E_m(0)·exp(C_m·M·t)` on `Icc 0 T` | Grönwall `linear_stability_within` (`:77-79`) with `K := tameEnergyConstant m*M` | True | **OK** — same `T` for every `m` |
| `integer_energy_uniform` | `:84` | same with `T` for `t` | `Real.exp_le_exp.mpr` + `t.property.2`, needs `0 ≤ C_m` and `0 ≤ M` (`:92`) | True | **OK** |
| `tensorNorm_uniform` | `:94` | tensor-norm form | previous + `Real.sqrt_le_sqrt` | **False** | **OK** (only consumer is dead code, `GradientControl:130`) |
| `higher_energy_of_h3` | `:101` | same, hypothesis phrased as `tensorNorm 3 ≤ M` | `wordBound_tensorNorm` conversion (`:106-107`) | True | **OK** — the live entry point, single consumer `Cauchy:83` |
| `SmoothingOperator.rhs_energy` | `Euler/OrdinaryRegularizedEnergy.lean:28` | mollified RHS obeys the same tame bound | transfers the pairing to `B := S.field A.toLp` (`:42-45`) where `fieldSub B B` makes the pressure term `0` and `gradientSpace.zero_mem` applies (`:36-38`); then `integer_energy_tame` | True | **OK** — the "pressure" is literally zero here, but the *hypothesis* `hP : P.toLp ∈ gradientSpace` is genuinely discharged, not bypassed |
| `energy` / `energyDerivative` / `energy_time` | `:57`, `:60`, `:63` | regularized-flow energy path and its derivative | as above, via `pointwise_time` | True | **OK** |
| `energy_tame` | `:70` | `d/dt E_m ≤ C_m·M·E_m` for the regularized flow | direct `S.rhs_energy` | True | **OK** |
| `energy_quadratic` | `:75` | `d/dt E_3 ≤ C_3·(1+E_3)²` | instantiate `M := √E_3` via `wordBound_sqrt_energy` then `nlinarith` (`:83-85`) | True | **OK** — note this is *quadratic*, i.e. the local-existence estimate, order **3 only** |
| `short_energy` | `:88` | if `C_3·T ≤ (1+E_3(0))⁻¹/2` then `E_3(t) ≤ 2E_3(0)+1` | `quadratic_energy_bound` (external ODE comparison) | True | **OK** |
| `energy_uniform` | `:100` | `E_m(t) ≤ E_m(0)·exp(C_m·M·T)` | Grönwall, same shape as `:84` | True | **OK** |
| `regularizedTime` | `:125` | `(2(1+C_3)(1+E_3(A)))⁻¹` | `def` — **order 3 only, `m`-free** | True | **OK** — the key fact for this item |
| `regularizedTime_pos` | `:128` | `0 < regularizedTime A` | `positivity` from the two nonnegativity facts | True | **OK** (non-vacuous: the interval is genuinely nonempty) |
| `regularizedH3` | `:134` | `√(2·E_3(A)+1)` | `def` | True | **OK** |
| `regularized_h3` | `:136` | on `[0, regularizedTime A]` the H³ word bound is `regularizedH3 A` | `short_energy` with the smallness hypothesis discharged by `field_simp`/`nlinarith` at `:143-147` | True | **OK** |
| `regularized_all_order` | `:153` | `∀ q, ∃ C`, uniform in the mollifier `S` and in `t` | `m := max 3 q`, `energy_uniform` at `m`, `tensorNorm_le_wordCount` | True | **OK** — per-`q` constant, `6^m` contained |
| `wordEnergy_le_tensorNorm` | `Euler/OrdinaryEulerCauchy.lean:15` | `E_m ≤ wordCount m·(tensorNorm m)²` | `sum_le_sum` twice + `Fintype.card_fun` at **symbolic** `n` (`:26`) | True | **OK** — no `3ⁿ` numeral is ever evaluated |
| `gradient_le_h3` | `:41` | `‖∇u‖ ≤ 9·smoothEmbeddingConstant·M` pointwise | `real_smooth_fderiv_le_H3 3` + `tensorNorm_eq` | True | **OK** |
| `cauchyPath_of_initial` | `:50` | initial-data Cauchy ⇒ path Cauchy, factor `exp(K·T)` with `K` **`k`-free** | `Metric.cauchySeq_iff`, `ε/exp(K*T)`, `velocityPath_norm_sub_le` | True | **OK** |
| `all_order_bounds_of_h3` | `:70` | `∀ q, ∃ C, ∀ k t, tensorNorm q ≤ C` | see B(i); `q < 3` branch handled separately with `wordCount q*M` (`:87-91`) | True | **OK** — the decisive quantifier order |
| `limitEvolutionOfH3` (+`_convergence`, `_initial`) | `:97`, `:104`, `:114` | the compactness limit is an `Evolution` on the **same** `T` | `limitEvolution` with `all_order_bounds_of_h3`+`cauchyPath_of_initial` | True | **OK** |
| `limitEvolution` (+`_jet_convergence`, `_initial`, `_bound`) | `Euler/OrdinaryEulerLimit.lean:85`, `:90`, `:98`, `:105` | limit object and its per-order bound transfer | `eulerLimitData`; `Classical.choose (hb 3)` at `:88` | True | **OK** — interface requires only `∀ q, ∃ M` |
| `higher_energy_of_gradientIntegral` | `Euler/OrdinaryEulerGradientControl.lean:119` | `E_m` bound with `M := gradientH3Bound G` | one-line `integer_energy_uniform` | **False** | **OK, DEAD** (Escalation 3) |
| `higher_tensorNorm_of_gradientIntegral` | `:125` | tensor-norm version | `tensorNorm_uniform` | **False** | **OK, dead except `:139`** |
| `higher_tensorNorm_of_gradientBound` | `:132` | same from a pointwise gradient bound `K` | previous with `G := K*T` | **False** | **OK, DEAD** |
| `regularizedSolution_bounds` | `Euler/OrdinaryEulerLocalExistence.lean:118` | `∀ q, ∃ M, ∀ n t, tensorNorm q ≤ M` | `regularized_all_order A q` after `intro q` | True | **OK** |
| `regularizedSolution_cauchy` / `localLimit` / `localEvolution` / `localEvolution_initial` / `exists_local_evolution` | `:124`, `:133`, `:139`, `:145`, `:152` | mollifier sequence converges; the limit is an `Evolution` on `regularizedTime A` with the right datum | `Classical.choose … 4` (a **fixed** order 4) throughout | True | **OK** — the construction never needs order-uniformity |
| `l2_stability` / `velocityPath_norm_sub_le` | `Euler/OrdinaryEulerL2Stability.lean:127`, `:136` | L² stability with factor `exp(K t)`, `K = ‖∇u‖_∞` | `l2_energy_bound` + `exp_add`/`nlinarith`; `ContinuousMap.norm_le` | True | **OK** |
| `l2_stability_of_h3` | `:148` | L² stability with `K := 9·smoothEmbeddingConstant·M` from `tensorNorm 3 ≤ M` | `l2_stability` + `real_smooth_fderiv_le_H3` | **False** | **OK, DEAD** (item D) |
| `initialDatum_singularity` / `exists_compact_smooth_euler_singularity` | `Euler/EulerSingularity.lean:115`, `:133` | the top-level Euler claim (read only to check for an analyticity claim) | anonymous constructor over imported facts | (top) | **OK for my question** — no Gevrey/analyticity conjunct |

Verdict counts over the 44 rows above: **OK 44, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0**
(3 of the 44 additionally flagged **DEAD**, 1 flagged "quadratic, order-3 only").

---

## Kernel-risk assessment

Greps over the 8 in-scope `Ordinary…` files (`OrdinaryTameEnergy`, `OrdinaryEulerHigherEnergy`,
`OrdinaryRegularizedEnergy`, `OrdinaryEulerCauchy`, `OrdinaryEulerGradientControl`,
`OrdinaryEulerL2Stability`, `OrdinaryEulerLimit`, `OrdinaryEulerLocalExistence`):

**(1) Recursive inductive types / recursors / well-founded recursion.**
`grep -nE 'WellFounded|Acc\.rec|\.rec\b|Nat\.rec'` → **no output**.
`grep -n 'termination_by'` → **no output**. Zero `inductive`, zero `structure` declared here
(counted above: only `theorem`/`def`). The one recursion-shaped object is
`Finset.range (m+1)` summation, which is `Finset.sum` over a *symbolic* `m` — the kernel never
unfolds it, because no proof instantiates `m` at a literal and then computes. Structure eta is
used only for `Subtype`/`Icc` membership pairs (`⟨0,le_rfl,hT⟩` etc.), which is O(1).
**The kernel does not have to reduce any recursor application to accept these files.**

**(2) Nat/GMP numeral arithmetic.**
`grep -nE '[0-9]{4,}'` → **no output**: there is no literal with 4 or more digits in the whole
scope. The largest literals are `13` (`Euler/OrdinaryH3Products.lean:17`) and `9`
(`Euler/OrdinaryEulerCauchy.lean:43`); the rest are `0,1,2,3,4,6`.
`grep -n 'decide'`, `grep -n 'native_decide'` → **no output**; so **no `Decidable` instance is
ever evaluated** in this scope. `grep -nE 'Nat\.(pow|div|mod|gcd|beq|ble)'` → **no output**.
The `norm_num` uses are four, all trivial: `(by norm_num : 1 ≤ 1)`
(`OrdinaryTameEnergy.lean:48`), `0 ≤ 6` inside `mul_nonneg` (`:90`), `(6:ℝ)=3*2` (`:139`),
`(0:ℝ) ≤ 2` (`:143`), plus `0 ≤ 9` (`OrdinaryEulerCauchy.lean:48,56`). Each certificate the
kernel must recheck is a one-digit `ℝ` numeral identity — microscopic.
Crucially, `tameEnergyConstant 3` (`OrdinaryRegularizedEnergy.lean:88,126,…`) is **never
evaluated numerically**: `h3ProductConstant` (`OrdinaryH3Products.lean:16`) is built from
`smoothEmbeddingConstant` (`Euler/EulerProof.lean:8227`, itself
`embeddingConstant 3 2 … * (…(2*Real.pi)^(-2:ℤ)…)`) and `sobolevConstant`
(`Euler/MeanCutoffCurlBound.lean:20`, `eLpNormLESNormFDerivOfEqInnerConst …`) — both opaque
`noncomputable` reals. Only `0 ≤ …` / `0 < 1+…` facts are ever used (`positivity`, `nlinarith`,
`linarith`). So the `6^m`/`∑ 6ⁿ` shape imposes **zero** kernel arithmetic cost.
**The kernel evaluates no numeral larger than two digits here.**

**(3) Custom metaprogramming.** `grep -nE 'macro|elab|syntax|set_option|axiom|sorry|unsafe|partial|deriving'`
over the scope → **no output at all**. The only attribute in the scope is
`@[simp]` at `Euler/OrdinaryEulerL2Stability.lean:64`. `Classical.choose` appears 5 times
(`OrdinaryEulerLimit.lean:88`; `OrdinaryEulerLocalExistence.lean:112,116,141,143`) — that is
`Classical.choice`, a Mathlib axiom, ordinary and sound, not custom metaprogramming; each use is
immediately paired with its `choose_spec`.

**Net: this scope adds nothing to the kernel-risk budget.** If the artifact is exploiting a
kernel bug, it is not exploiting it here.

---

## Escalations

Ranked. **None is a demonstrated defect.**

1. **(Low, but the honest residue of the assigned question.)
   `Euler/OrdinaryRegularizedEnergy.lean:125` `regularizedTime A = (2(1+C_3)(1+E_3(A)))⁻¹`.**
   I verified that `6^m` does not shrink the lifespan; but the lifespan *is* inversely
   proportional to `1+tameEnergyConstant 3`, i.e. to `h3ProductConstant`
   (`Euler/OrdinaryH3Products.lean:16`), which is built from two Mathlib embedding constants
   I cannot evaluate on this box.
   *Question for an expert:* is `regularizedTime` **provably positive and not degenerate** in a
   stronger sense than `positivity` gives — specifically, is `embeddingConstant 3 2`
   (`Euler/EulerProof.lean:8228`) finite by a *proved* Mathlib statement rather than a junk value
   for an unmet side condition? *What would settle it:* the Mathlib statement of
   `eLpNormLESNormFDerivOfEqInnerConst` and `embeddingConstant`, plus a check that
   `smoothEmbeddingConstant_nonneg` (`:8231`) is not the only fact anyone ever uses about it. (A
   *zero* embedding constant would be the dangerous junk value here, and `0 ≤ C` is compatible
   with `C = 0`; note the lifespan would then be *longer*, not shorter, so this direction is not
   exploitable for a blowup claim — which is why I rank it low.)
2. **(Low.) `Euler/OrdinaryEulerLocalExistence.lean:127-129,141-143`: the choice of order `4`.**
   The whole limit construction is built from `regularizedSolution_bounds A hA 4`. Fixing `4` is
   legitimate (it is what `regularized_cauchy` needs), and per-order bounds for every other `q`
   still follow from `regularizedSolution_bounds A hA q`. *Question:* does the resulting
   `Evolution` object genuinely carry all-order smoothness, or only order-4 control with
   smoothness re-derived elsewhere? *What would settle it:* the `Evolution` structure fields and
   `SmoothLimitData.toEvolution` (`Euler/OrdinaryEulerLimit.lean:88`, and the
   `smoothLimitData`/`regularizedEvolution` definitions) — outside my assigned files; the
   `euler-evolution-class` worker's report is the right place to cross-check.
3. **(Informational.) Three dead higher-energy corollaries:
   `Euler/OrdinaryEulerGradientControl.lean:119`, `:125`(only used by `:132`), `:132`, and
   `Euler/OrdinaryEulerL2Stability.lean:148`.** All four are `in_cone=False` in `CONE.csv` and
   have no repo-wide consumer. Harmless, but they are exactly the shape a reader would *expect*
   to be the consumer of the higher-energy estimate, so a reviewer skimming names could believe
   the gradient-integral route is live when it is not. No question for an expert; just do not
   credit these to the proof.

---

## Residue (what I could NOT check)

* **Mathlib statements.** No Mathlib source on this box, so I could not re-read
  `le_gronwallBound_of_liminf_deriv_right_le`, `Fintype.card_fun`, `Measure.eq_of_ae_eq`,
  `eLpNormLESNormFDerivOfEqInnerConst`, `embeddingConstant`. I took their *names* at face value
  and checked only that the local hypotheses supplied match the local goal shape.
* **No build.** I could not confirm the files elaborate; all verdicts are about *statements and
  proof scripts as written*, on the (Comparator-supported) assumption that they elaborate.
* **`quadratic_energy_bound`** (used at `Euler/OrdinaryRegularizedEnergy.lean:91`) lives in
  `Euler/OrdinaryQuadraticControl.lean`, outside my scope — I did not verify that its
  smallness hypothesis is the one that makes `short_energy` non-vacuous. If that ODE comparison
  lemma were vacuous, `regularizedTime` would still be positive, so the *time* claim would be
  unaffected, but `regularized_h3` would lose its content. Assigned to whoever owns
  `OrdinaryQuadraticControl.lean`.
* **The internal Gevrey weight form.** I settled part C structurally (import DAG + zero grep
  contact + no top-level analyticity claim) and did **not** myself read all 110 `*Gevrey*.lean`
  files; the weight/index/radius detail of `Euler/BaseEulerGevrey.lean`,
  `Euler/GevreyGeneratingDerivatives.lean`, `Euler/GevreyCompositionPartitions.lean` and
  `Euler/EulerProof.lean:5120,5170` is in the child report
  `workers/_sub-gevrey-index-radius.md`. My conclusion does not depend on it.
* **Skimmed regions** (53 declarations, listed in `## Scope`) — mostly re-audited already by
  `workers/euler-gronwall.md`; I did not independently re-verify those proofs.
