# Worker report: rescaling + gradient control + gradient limit

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (clone of openai/NavierStokesAndEuler @ f9e8bc5).
Method: source reading only (grep/python), no `lake build` (no Mathlib on this box). All claims carry file:line.

## Scope

Three files, read IN FULL, every declaration:

| File | lines | decls read |
|---|---|---|
| `Euler/OrdinaryEulerRescaling.lean` | 91 | 5 (`scaleTimeMap` :16, `scaleTimeMap_val` :22, `Evolution.rescale` :29, `rescale_velocity` :76, `rescale_initial` :81) |
| `Euler/OrdinaryGradientLimit.lean` | 90 | 6 (`gradientTensorBound` :16, `h3_tensorNorm_gradient_uniform` :23, `cauchyPath_of_initial_gradient` :35, `limitEvolutionOfGradientIntegral` :54, `_convergence` :64, `_initial` :77) |
| `Euler/OrdinaryEulerGradientControl.lean` | 143 | 16 (`gradientNormPath` :20 … `higher_tensorNorm_of_gradientBound` :132) |

Total 27 declarations, all read line by line.

Skimmed (dependency verification only, cited where load-bearing, NOT audited in full):
`Euler/OrdinaryEulerDifference.lean:21-33` (`structure Evolution`), `Euler/OrdinaryFieldScaling.lean:18-60` (`scaleField` + lemmas),
`Euler/LpSmoothField.lean:31-54` (`SmoothL2Field`, `.derivative`), `Euler/MeanSobolevBoundedField.lean:26-113` (`sobolevField`/`spaceField`/`finiteField`),
`Euler/ContinuousTimeIntegral.lean:53-61` (`realIntegral`), `Euler/VolterraConvolution.lean:20` (`extendPath`),
`Euler/OrdinaryVariableGronwall.lean:14-44` (`variable_linear_stability`), `Euler/OrdinaryGradientEnergy.lean:53-114` (`h3_energy_gradient`),
`Euler/OrdinaryTameEnergy.lean:62-95` (`eulerRhs`, `integerEnergyProduction`), `Euler/OrdinarySmoothWords.lean:91-113` (`wordEnergy`, `WordBound`),
`Euler/OrdinaryEulerHigherEnergy.lean:17-54`, `Euler/OrdinaryEulerCauchy.lean:15-30`, `Euler/OrdinaryGradientStability.lean:18-72`,
`Euler/OrdinaryWordTime.lean:69-97`, `Euler/OrdinaryEulerEndpoint.lean:18-73` (the consumer).

## Per-declaration findings

### A. `Euler/OrdinaryEulerRescaling.lean`

The normalisation actually used in the file (read, not assumed) is the **amplitude + time** Euler symmetry, with **no spatial dilation**:

```lean
-- :29-32
def rescale (U : Evolution S hS) (T : ℝ) (hT : 0 ≤ T)
    (c : ℝ) (hc : 0 < c) (hct : c*T ≤ S) : Evolution T hT where
  velocity t := scaleField c (U.velocity (scaleTimeMap S T c hc.le hct t))
  pressureForce t := scaleField (c*c) (U.pressureForce (scaleTimeMap S T c hc.le hct t))
```
i.e. `u_c(t,x) = c · u(c t, x)`, `P_c(t,x) = c² · P(c t, x)`, where `scaleField c A = c • A` pointwise
(`Euler/OrdinaryFieldScaling.lean:18-22`, `mapField (c • id)`; no argument dilation anywhere).
This IS an exact symmetry of the equation that `structure Evolution` states, because that equation is pointwise in `x`
(`Euler/OrdinaryEulerDifference.lean:28-32`): `d/dt u(t,x) = -Du(t,x)[u(t,x)] - P(t,x)`.
Check: `d/dt (c u(ct,x)) = c²(∂_t u)(ct,x)`, and `-D(c u)[c u] - c² P = c²(-Du[u] - P)`. Factors agree; the `c²` on the
pressure force is required and present.

1. **`scaleTimeMap` (:16-20)** — `C(Icc 0 T, Icc 0 S)`, `t ↦ c*t`, with membership proved from `hc : 0 ≤ c` and
   `hct : c*T ≤ S` (`mul_nonneg`, `mul_le_mul_of_nonneg_left … |>.trans hct`, :18-19). Domain-correct by construction:
   `c*t ∈ [0,S]` for every `t ∈ [0,T]`. Continuity is real (`continuous_subtype_val.const_mul`, :20). **OK**
2. **`scaleTimeMap_val` (:22-23)** — `rfl` on the coercion of a `Subtype.mk`; defeq, no kernel work. **OK**
3. **`Evolution.rescale` (:29-74)** — discharges all 7 fields of `structure Evolution`
   (`Euler/OrdinaryEulerDifference.lean:21-32`) as follows:
   * `velocity` (:31) `= c • u(c t)`; `pressureForce` (:32) `= c² • P(c t)`.
   * `velocity_continuous` (:33-34) / `pressure_continuous` (:35-36): composition of `U`'s jet continuity with the
     continuous `scaleTimeMap`, then `scaleField_continuous` (`OrdinaryFieldScaling.lean:47-51`, which is
     `continuous_jetLp_mapField`, a genuine CLM-pushforward continuity). **Real.**
   * `solenoidal` (:37-39): `scaleField_toLp` (`…FieldScaling.lean:24`) turns it into `c • U.toLp`, then
     `solenoidalSpace.smul_mem`. Submodule closure — correct, `div (c u) = c div u = 0`.
   * `gradient` (:40-42): same with `c*c` and `gradientSpace.smul_mem`.
   * `time_law` (:43-74): **genuinely proved**, chain rule factors correct. Mechanism:
     - `hcs` (:44-45): `c*t ∈ Ioo 0 S` from `mul_pos hc ht.1` and `(mul_lt_mul_of_pos_left ht.2 hc).trans_le hct`.
       This is exactly where `hc : 0 < c` (strictness) and `hct` are needed, and it is what makes the *interior*
       hypothesis of `U.time_law` available at the reparametrised time. Domain-correct.
     - `hi` (:46-47): `HasDerivAt (c*·) c t`.
     - `hd` (:48): `(U.time_law (c*t) hcs x).scomp t hi` gives one factor `c` (chain rule), `.const_smul c` gives the
       second. Total derivative `c • (c • RHS(ct))` = `c²·RHS(ct)`. Both factors present, none double-counted.
     - `he` (:49-57): eventual equality on `𝓝 t` of the rescaled velocity path with `fun r => c • u(projIcc(c*r))`;
       uses `filter_upwards [Ioo_mem_nhds ht.1 ht.2]` and re-proves `r ∈ Icc 0 T`, `c*r ∈ Icc 0 S` (:53-55) so both
       `projIcc`s are the identity. This is the correct and necessary way to handle the clamped domain: the derivative
       is only claimed at interior `t`, and on a neighbourhood of interior `t` no clamping occurs.
     - `hrhs` (:58-73): rewrites the *target* derivative into `c • (c • …)` using `scaleField_fderiv`
       (`…FieldScaling.lean:39-41`, `fderiv (c•A) = c • fderiv A`), `map_smul`, `smul_smul`. So the `c²` on the
       pressure force and the `c²` from `D(c u)[c u]` are matched exactly.
     - closes with `hd.congr_of_eventuallyEq he`.
     **Verdict: OK.** The rescaled object really is an Euler `Evolution`. No `sorry`, no junk field, no re-assumed PDE.
     Caveat (mathematical, not a defect): because there is no spatial dilation, the symmetry does **not** preserve the
     initial datum — it maps datum `A` to `c • A`. See `rescale_initial` and Escalation E1.
4. **`rescale_velocity` (:76-79)** — `rfl`, structure projection. **OK**
5. **`rescale_initial` (:81-88)** — `u_c(0) = c • u(0)`, proved via `Subtype.ext`/`mul_zero`. Statement is honest about
   the amplitude factor (it does NOT claim datum preservation). **OK**

### B. `Euler/OrdinaryGradientLimit.lean`

Verbatim:

```lean
-- :16-17
def gradientTensorBound (R G : ℝ) : ℝ :=
  wordCount 3*Real.sqrt (wordCount 3*R^2*Real.exp (gradientEnergyConstant*G))

-- :23-33
theorem h3_tensorNorm_gradient_uniform (U : Evolution T hT) (R G : ℝ)
    (hR : tensorNorm 3 (U.velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    tensorNorm 3 (U.velocity t) ≤ gradientTensorBound R G := by
  apply (U.h3_tensorNorm_of_gradientIntegral G hG t).trans
  apply mul_le_mul_of_nonneg_left _ (wordCount_nonneg 3)
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact (wordEnergy_le_tensorNorm _ 3).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (tensorNorm_nonneg 3 _) hR 2) (wordCount_nonneg 3))
```

6. **`gradientTensorBound` (:16)** — explicit finite closed form. `wordCount 3 = 1+3+9+27 = 40`
   (`OrdinaryEulerHigherEnergy.lean:17`), `gradientEnergyConstant = 54*(1+6+36+216) = 13986`
   (`OrdinaryGradientEnergy.lean:60`, proved `= 13986` at :65 by `norm_num`). **No `T` occurs**, so the bound is
   uniform in the interval length. **OK**
7. **`h3_tensorNorm_gradient_uniform` (:23)** — the argument is a REAL energy/Gronwall chain, not vacuous and not
   circular. Walk-through of what it composes:
   * `U.h3_tensorNorm_of_gradientIntegral` (`OrdinaryEulerGradientControl.lean:114`) gives
     `tensorNorm 3 (u t) ≤ wordCount 3 * sqrt(wordEnergy 3 (u 0) * exp(13986 * gradientIntegral t))`
     via `WordBound` → `tensorNorm_le_wordCount` (`…HigherEnergy.lean:21`, a finite sum of ≤ 40 word norms).
   * That in turn rests on `h3_energy_gradientIntegral` (`…GradientControl.lean:68-88`), which is a genuine
     differential-inequality + Gronwall step:
     - energy derivative identity from the PDE: `integerEnergyDerivative 3 t = integerEnergyProduction 3 (u t) (eulerRhs …)`
       (`…GradientControl.lean:63`, `derivative_eq_eulerRhs` `…HigherEnergy.lean:42`), with the derivative of the H³
       word energy supplied by `integerEnergy_hasDerivWithinAt` (`…HigherEnergy.lean:48`), which consumes
       `U.time_law` (:54) — so the *actual equation* enters.
     - the production bound is the real commutator estimate `h3_energy_gradient`
       (`OrdinaryGradientEnergy.lean:92-114`): pressure pairing vanishes (`gradientSpace ⟂ solenoidal words`,
       `OrdinaryTameEnergy.lean:70-84`), transport term cancels except the commutator, commutator ≤ `27(2ⁿ-1)K·N`
       (`OrdinaryGradientEnergy.lean:53-56`), summed over the ≤ 40 words → `13986·K·wordEnergy 3`.
     - `K` is instantiated at the *pointwise-in-time sup* of `‖∇u‖` (`pointwise_gradient_le`,
       `…GradientControl.lean:37`), so the constant-K estimate becomes a variable-coefficient one.
     - Gronwall: `variable_linear_stability` (`OrdinaryVariableGronwall.lean:14-44`) is a real proof
       (`Y = X·exp(-C∫K)`, `Y' ≤ 0`, then `linear_stability_within`), producing
       `E(t) ≤ E(0)·exp(C·∫₀ᵗ K)`, i.e. `exp(13986·gradientIntegral t)`.
   * The last three lines of :23 only convert the *initial* energy into `R`: `wordEnergy 3 A ≤ 40·(tensorNorm 3 A)²`
     (`OrdinaryEulerCauchy.lean:15`) and `tensorNorm 3 A ≤ R`. Arithmetic checks out
     (`sqrt(E₀·e) ≤ sqrt(40R²·e)` needs exactly `E₀ ≤ 40R²`).
   * Uniformity: the conclusion contains no `T` and holds for every `t : Icc 0 T`; only `R` (initial H³) and `G`
     (gradient-integral cap) enter. So it IS uniform in the interval length. **OK**
   * Non-vacuity: the hypotheses are satisfiable (e.g. the zero evolution has `gradientIntegral ≡ 0`), and `hG` is a
     hypothesis about the solution, not the conclusion — no circularity (the conclusion is an H³ bound; nothing in the
     chain assumes an H³ bound; `wordBound_sqrt_energy` `OrdinarySmoothWords.lean:109` is unconditional).
     Honest reading: this is a *conditional* BKM-type statement "finite ∫‖∇u‖_∞ ⇒ uniform H³", which is the correct
     mathematical shape.
8. **`cauchyPath_of_initial_gradient` (:35-48)** — from `‖path_j - path_k‖ ≤ ‖data_j - data_k‖·exp G`
   (`velocityPath_norm_sub_le_gradientIntegral`, `OrdinaryGradientStability.lean:63-72`, itself a real L² Gronwall via
   the exact `(u·∇)`-antisymmetry, `…Stability.lean:18-52`) plus an `ε/exp G` choice at :41. The ε-arithmetic is
   correct (`div_mul_cancel₀` at :45). **OK**
9. **`limitEvolutionOfGradientIntegral` (:54-62), `_convergence` (:64-75), `_initial` (:77-88)** — thin wrappers that
   feed 7/8 into `limitEvolution` / `all_order_bounds_of_h3` (`OrdinaryEulerCauchy.lean:70`, :97). Hypothesis lists are
   complete (uniform-in-`k`-and-`t` H³ bound, all-order initial bounds, Cauchy data); no bound is invented. **OK**,
   but see Residue R1: these three are **dead code** — `grep` over the whole repo finds no consumer outside this file.

### C. `Euler/OrdinaryEulerGradientControl.lean`

```lean
-- :20-23
def gradientNormPath (U : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => ‖finiteField (U.velocity t).derivative‖, …⟩
-- :41-42
def gradientIntegral (U : Evolution T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  realIntegral T hT U.gradientNormPath t
```

10. **`gradientNormPath` (:20)** — `‖·‖` of a `Space →ᵇ Space →L[ℝ] Space`, i.e. the **sup over all `x` of
    `‖fderiv ℝ (u t) x‖`**. Two things make this real rather than junk:
    * `.derivative` is literally `field := fderiv ℝ A.field` (`Euler/LpSmoothField.lean:49-54`), so the object is the
      true velocity gradient;
    * the bounded-continuous packaging `finiteField` (`Euler/MeanSobolevBoundedField.lean:104-113`) is built from a
      **proved** Sobolev point-evaluation bound `‖·‖ ≤ sobolevEmbeddingConstant 1 3·‖u‖_{H³}`
      (`…BoundedField.lean:26-35`) plus `finiteField_apply : finiteField A x = A.field x` (:108). So the sup is finite
      *because H³ ↪ L^∞ was proved*, not by a `Classical.choice`/junk-value construction, and it agrees pointwise with
      the honest gradient. Continuity in `t` is real (`continuous_finiteField` :116 ∘ jet continuity). **OK**
11. **`gradientNormPath_nonneg` (:25)**, **`gradientNormPath_le_iff` (:30-35)**, **`pointwise_gradient_le` (:37-39)** —
    the `iff` is `BoundedContinuousFunction.norm_le_of_nonempty` (a genuine two-sided characterisation of the sup norm)
    plus `finiteField_apply` and a defeq `rfl` (:35). `pointwise_gradient_le` extracts `‖∇u(t,x)‖ ≤ gradientNormPath t`
    from `le_rfl`, which is only sound because the `iff` is two-sided. So `gradientNormPath` really is the sup, not
    merely an upper bound placeholder. **OK**
12. **`gradientIntegral` (:41-42)** — `realIntegral T hT f t = ∫ s in (0:ℝ)..t, extendPath T hT f s`
    (`Euler/ContinuousTimeIntegral.lean:53-54`), with `extendPath f = f ∘ projIcc` (`Euler/VolterraConvolution.lean:20`).
    So `gradientIntegral U t = ∫₀^t sup_x‖∇u(s,x)‖ ds` — a genuine BKM-type (gradient-sup) accumulated quantity,
    **not** identically 0, **not** over a degenerate set (`t` ranges over all of `Icc 0 T`), **not** a junk value.
    Integrability is *established, not exploited*: the integrand is a `ContinuousMap` composed with the continuous
    `projIcc`, and the code repeatedly supplies real `IntervalIntegrable` witnesses
    (`extendPath_continuous … |>.intervalIntegrable` at :52/:55, `realIntegral_hasDerivAt`
    `ContinuousTimeIntegral.lean:57-61`). So the Lean "`∫` of a non-integrable function is 0" escape hatch is **not**
    in play. Supporting monotonicity/positivity: `gradientIntegral_nonneg` (:44), `gradientIntegral_mono`
    (`Euler/OrdinaryEulerContinuation.lean:35`). **OK** — this is the strongest point of the three files.
    Only degenerate case: `T = 0` gives `∫₀^0 = 0`, which is honest (empty time interval) and unused (`hT : 0 < T`
    at the consumer, `OrdinaryEulerEndpoint.lean:39`).
13. **`gradientIntegral_nonneg` (:44-47)** — `intervalIntegral.integral_nonneg_of_forall`. **OK**
14. **`gradientIntegral_le_const` (:49-58)** — `∫₀^t sup‖∇u‖ ≤ K·t` with both integrability side goals discharged. **OK**
15. **`integerEnergyDerivative_gradient` (:60-66)** — plugs the real commutator estimate `h3_energy_gradient` in, with
    the divergence-free property of the *representative* supplied by `solenoidal_representative_divergence` (:65-66)
    rather than assumed. **OK**
16. **`h3_energy_gradientIntegral` (:68-88)** — the Gronwall step described in B.7. Note `hd` (:71-75) needs the
    within-derivative on `Ico 0 T` including the left endpoint, and gets it from `integerEnergy_hasDerivWithinAt`,
    which is proved from the *interior-only* `time_law` through
    `OrdinaryWordTime.lean:87` → `:78` → `sobolevPath_hasDerivWithinAt` (`Euler/SmoothFieldSobolevTime.lean:96`).
    That bridge (pointwise-in-`x` interior derivative ⇒ L²-valued within-derivative at endpoints) is the one
    load-bearing step I could not verify inside my scope. **OK (conditional on E2)**
17. **`h3_energy_gradient_bound` (:90-98)** — constant-K corollary, `exp(13986·K·t)`. **OK**
18. **`gradientH3Bound` (:100-101)**, **`wordBound_of_gradientIntegral` (:103-112)**,
    **`h3_tensorNorm_of_gradientIntegral` (:114-117)** — `sqrt(E₀·exp(13986·G))`, `WordBound` for all ≤ 40 words,
    then `tensorNorm ≤ 40·bound`. All monotonicity side conditions are real (`wordEnergy_nonneg`,
    `gradientEnergyConstant_nonneg`). **OK**
19. **`higher_energy_of_gradientIntegral` (:119-123)**, **`higher_tensorNorm_of_gradientIntegral` (:125-130)** —
    orders `m ≥ 3` via the tame estimate `integer_energy_uniform` / `tensorNorm_uniform`. These bounds DO contain `T`
    (`exp(tameEnergyConstant m · gradientH3Bound G · T)`), i.e. they are *not* uniform in interval length — but the
    statements say so explicitly, so no overclaim. **OK**
20. **`higher_tensorNorm_of_gradientBound` (:132-141)** — same with `G := K*T`; `hK0` derived, not assumed. **OK**

### Consumer check (context sanity, `Euler/OrdinaryEulerEndpoint.lean`)

`exists_smooth_endpoint` (:39-73) calls `rescale` with `c := endpointScale n = 1-1/(n+2) ∈ (0,1)` and
`hct := le_rfl` (:52), i.e. `S = c·T` exactly — so the rescaled solution covers the **whole** `[0,T]` and consumes the
whole original interval; domain-correct with no slack lost. The uniform H³ bound at :57-61 is obtained by
`tensorNorm_scaleField_le` (`OrdinaryFieldScaling.lean:57`, valid because `c ≤ 1`) followed by
`h3_tensorNorm_gradient_uniform` applied to the ORIGINAL `U n` — so the gradient-integral hypothesis is used where it
is actually available, and nothing about the rescaled gradient integral has to be re-proved. The datum drift
`c_n • A → A` is handled honestly in `L²` (:68-70, `endpointScale_tendsto`) and the limit's datum is recovered as
`A.toLp` (:71-73). This all hangs together.

## Kernel-risk

Programmatic scan of the three files (regex over every line), plus manual confirmation:

| pattern | Rescaling | GradientLimit | GradientControl |
|---|---|---|---|
| `decide` / `native_decide` | 0 | 0 | 0 |
| `norm_num` / `omega` | 0 | 0 | 0 |
| `Nat.pow`, `^` | 0 | 1 (`R^2`, `:17`) | 0 |
| numerals ≥ 5 digits | 0 | 0 | 0 |
| `.rec` / `recOn` / `Acc.rec` / `WellFounded.fix` | 0 | 0 | 0 |
| `termination_by` / `decreasing_by` | 0 | 0 | 0 |
| `partial` / `unsafe` | 0 | 0 | 0 |
| `macro` / `elab` / `syntax` / `set_option` / `implemented_by` | 0 | 0 | 0 |
| `sorry` / `axiom` / `admit` | 0 | 0 | 0 |
| `rfl` | 4 (`:23,:57,:69,:79`) | 0 | 1 (`:35`) |

* `R^2` (`OrdinaryGradientLimit.lean:17`) is `Monoid.npow 2` on ℝ inside a `Real.sqrt`; no numeral evaluation.
* All 5 `rfl`s are on structure projections / `Subtype.mk` with definitional proof irrelevance
  (`:69` is `scaleTimeMap … ⟨t,_,_⟩ = ⟨c*t,_,_⟩`) or on `finiteField A x` unfolding to `A.field x` after a `simp only`
  (`GradientControl:35`, where `.derivative.field ≡ fderiv ℝ A.field` by `LpSmoothField.lean:50`). No `rfl` on
  recursive data, no forced large closure.
* Indirect numeral exposure: `gradientEnergyConstant = 13986` is *defined* as `54*(∑ n ∈ range 4, 6^n)`
  (`OrdinaryGradientEnergy.lean:60`) and only evaluated in a separate `norm_num` lemma at :65 that these three files
  never use; inside my scope the constant stays symbolic. `wordCount 3` (40) likewise stays symbolic here.
* **Kernel-risk verdict for my scope: none.** No decision procedure, no recursion, no metaprogramming, no big numerals.

## Escalations

* **E1 (mathematical, informational — not a bug).** The "rescaling" is amplitude+time only (`u ↦ c u(ct,·)`), with no
  spatial dilation (`OrdinaryEulerRescaling.lean:31`, `OrdinaryFieldScaling.lean:18-22`). It is a true symmetry of the
  stated equation, but it **changes the initial datum** to `c • A` (`rescale_initial` :81). Hence
  `exists_smooth_endpoint` does not get a solution with datum `A` on `[0,T]` from any single rescaling; it needs the
  limit machinery `limitEvolutionOfH3` + `limitEvolutionOfH3_initial` (`OrdinaryEulerEndpoint.lean:71-73`,
  `OrdinaryEulerCauchy.lean:97`) to recover the datum. **The whole endpoint claim therefore rests on the
  compactness/limit construction, not on the rescaling.** Whoever owns `Euler/OrdinaryEulerCauchy.lean` /
  `limitEvolution` should confirm the limit object's `time_law` is genuinely proved (that is where a vacuous
  construction would hide), and that the limit's datum identification uses `smoothField_eq_of_toLp_eq` soundly.
* **E2 (one load-bearing dependency outside my scope).** Every H³ Gronwall in `OrdinaryEulerGradientControl.lean`
  needs the H³ word energy to be differentiable **within `Icc 0 T` at the left endpoint** (`:71-75` requires
  `r ∈ Ico 0 T`), while `Evolution.time_law` only holds on the **open** `Ioo 0 T`
  (`OrdinaryEulerDifference.lean:28`). The upgrade happens in `OrdinaryWordTime.lean:87` → `:78` →
  `Euler/SmoothFieldSobolevTime.lean:96` (`sobolevPath_hasDerivWithinAt`), which also silently converts a
  pointwise-in-`x` scalar derivative into an `L²`-valued Fréchet derivative. Both moves are non-trivial; please make
  sure some worker audits `SmoothFieldSobolevTime.lean:86-120` and `CylinderTimeRegularity.lean:70`.
* **E3 (hygiene, low).** `limitEvolutionOfGradientIntegral` (+`_convergence`, `_initial`) and
  `cauchyPath_of_initial_gradient` are unreachable from the endpoint theorem (the endpoint path uses
  `limitEvolutionOfH3` directly, `OrdinaryEulerEndpoint.lean:71`). Repo-wide grep finds no other consumer. Not wrong,
  but they are never exercised by the headline results, so a defect there would go unnoticed.

## Residue

* **R1.** Dead code as in E3 (4 declarations).
* **R2.** Not verified by build: no Mathlib available, so all lemma *names/signatures* from Mathlib
  (`HasDerivAt.scomp`, `HasDerivAt.const_smul`, `BoundedContinuousFunction.norm_le_of_nonempty`,
  `intervalIntegral.integral_mono_on`, `pow_le_pow_left₀`, …) were checked for shape/argument order by reading, not by
  elaboration. Argument order of `.scomp t hi` and `.const_smul c` matches the current Mathlib convention
  (`hg.scomp x hh`, `HasDerivAt.const_smul (c) (hf)`), and the produced derivative `c • (c • …)` matches the target
  rewritten at `:58-72`, so an argument-order error would have to be self-consistent to survive; still, unverified.
* **R3.** Not audited (out of scope, only skimmed for the specific facts cited): `limitEvolution`/`all_order_bounds_of_h3`
  (`OrdinaryEulerCauchy.lean`), `variable_linear_stability`'s dependency `linear_stability_within`,
  the commutator estimates in `OrdinaryGradientEnergy.lean` / `OrdinaryTameEnergy.lean` beyond their statements,
  the Sobolev point-evaluation bound in `MeanSobolevBoundedField.lean`, and the whole
  `OrdinaryEulerContinuation.lean` / `OrdinaryBKMReduction.lean` chain that *consumes* `gradientIntegral`
  (i.e. whether the finite-gradient-integral hypothesis is ever discharged unconditionally — the place where a
  circular or false global claim would live).
* **R4.** Verdict counts for my 27 declarations: **OK 27** (one of them, `h3_energy_gradientIntegral` :68,
  is OK *conditional on E2*), UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0.
