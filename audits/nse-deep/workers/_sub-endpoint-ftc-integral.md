# Sub-audit: endpoint FTC / integral machinery behind `Euler/SeparatingTimeDerivative.lean`

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ `f9e8bc5`, toolchain
`leanprover/lean4:v4.34.0-rc2`, mathlib pinned `v4.34.0-rc2` in `lakefile.toml`).
NO build was run (no Mathlib artifacts, disk full). Source-level reading only.
Mathlib statements quoted below were read from an on-disk mathlib checkout at `v4.33.0`
(`/home/gsm/.openclaw/workspace/lean-eval-house-with-two-rooms/.lake/packages/mathlib`, commit `db584cd6d4`),
i.e. ONE minor version behind the pin. Signatures of the FTC lemmas used have been stable for years, but
this is a stated caveat, not a verified equality of versions.

## Scope

| file | lines | decls | read |
|---|---|---|---|
| `Euler/SeparatingTimeDerivative.lean` | 68 | 3 theorems (`eq_initial_add_integral` :24, `hasDerivWithinAt` :49, `hasDerivAt` :63) | FULL, line by line |
| `Euler/ContinuousTimeIntegral.lean` | 134 | 4 defs (`multiplierLinear` :24, `multiplier` :38, `realIntegral` :53, `integralLinear` :64, `integral` :88) + 8 theorems | FULL |
| `Euler/VolterraConvolution.lean` | 147 | 4 defs (`extendPath` :20, `causalIntegrand` :33, `convolution` :108, `kernelMass` :113) + 9 theorems | FULL |
| transitive imports (`Euler/TimeH1OperatorProduct.lean`, `Euler/CylinderSobolevSpace.lean`, …) | – | – | NOT read (residue) |

## 1. Confirmation of the parent's reading of `SeparatingTimeDerivative.lean`

CONFIRMED, in every particular.

* Hypotheses (`:15-21`): `E`,`F` normed real spaces with `[CompleteSpace E]` **and** `[CompleteSpace F]`
  (`:15-16`); `T : ℝ`, `hT : 0 ≤ T`; `f g : C(Icc (0:ℝ) T, E)` (so `f`,`g` are continuous **up to and
  including the endpoints** by type); `L : I → E →L[ℝ] F`;
  `hsep : Function.Injective (fun u : E => fun i : I => L i u)` (`:19`);
  `hd : ∀ i t (ht : t ∈ Ioo 0 T), HasDerivAt (fun r => L i (extendPath T hT f r)) (L i (g ⟨t,…⟩)) t` (`:20-21`)
  — the derivative is hypothesised ONLY on the OPEN interval, and only after applying a functional.
* `eq_initial_add_integral` (`:24-46`): goal `f t = f ⟨0,le_rfl,hT⟩ + integral T hT g t` for `t : Icc 0 T`.
  Proof: `apply hsep; funext i; change …` (`:26-28`) reduces to the scalarised identity; `hc`/`hg` (`:29-32`)
  are genuine continuity facts `(L i).continuous.comp (extendPath_continuous …)`; `hobs` (`:33-44`) is the FTC-2
  step; `rw [map_add,hobs]; abel` (`:45-46`) closes.
* `hasDerivWithinAt` (`:49-60`): exactly the endpoint upgrade. `hp` (`:51-56`) differentiates the primitive by
  `realIntegral_hasDerivAt` + `.const_add` + `.hasDerivWithinAt`; `:57` transfers by
  `hp.congr_of_mem _ t.property`; `:58-60` discharges the congruence using `eq_initial_add_integral`.
* `hasDerivAt` (`:63-66`) is the interior corollary via `Icc_mem_nhds ht.1 ht.2` (needs `0 < t < T`, correct).

Verbatim FTC-2 step (`:36-42`):

```lean
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
      hc.continuousOn (f' := fun r => L i (extendPath T hT g r))
      (fun r hr => by
        have hrT : r ∈ Ioo 0 T := ⟨hr.1,hr.2.trans_le t.property.2⟩
        simpa only [extendPath,projIcc_of_mem hT ⟨hrT.1.le,hrT.2.le⟩]
          using hd i r hrT)
      (hg.intervalIntegrable 0 t)
```

Mathlib (`Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1140-1142`):

```lean
theorem integral_eq_sub_of_hasDerivAt_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a
```

Argument match with `a := 0`, `b := (t : ℝ)`: `hab := t.property.1 : 0 ≤ t` ✔; `hcont := hc.continuousOn` ✔
(continuity of the CLAMPED extension on all of ℝ, hence on `Icc 0 t` — this is where continuity of `f`
**at the endpoints** is consumed); `hderiv` on `Ioo 0 t` is derived from `hd` at `r ∈ Ioo 0 T` using
`hr.2.trans_le t.property.2` (`r < t ≤ T`) ✔ — note the FTC is applied on `[0,t]`, NOT on `[0,T]`, so
`t = T` is admissible and needs no derivative AT `T`; `hint := hg.intervalIntegrable 0 t` ✔
(`Continuous.intervalIntegrable`, `IntervalIntegral/Basic.lean:511-513`) — integrability is PROVED.

## 2. The integral machinery

### (a) `extendPath` is a clamped extension, continuity is a proved lemma

`Euler/VolterraConvolution.lean:20`
```lean
def extendPath (f : C(Icc (0 : ℝ) T, Y)) (t : ℝ) : Y := f (projIcc 0 T hT t)
```
`Euler/VolterraConvolution.lean:24-25`
```lean
theorem extendPath_continuous (f : C(Icc (0 : ℝ) T, Y)) : Continuous (extendPath T hT f) :=
  f.continuous.comp continuous_projIcc
```
So YES: clamped (constant `f 0` on `Iic 0`, constant `f T` on `Ici T`), and continuity is a real proof
from `ContinuousMap.continuous` + Mathlib `continuous_projIcc`. `extendPath_norm_le` (`:29-30`) is likewise real.
`projIcc_of_mem hT h : projIcc 0 T hT r = ⟨r,h⟩` is the Mathlib simp lemma used throughout to collapse the
clamp on `Icc` — used at `SeparatingTimeDerivative.lean:40,43,44,55,59` and `ContinuousTimeIntegral.lean:82,108,112,123`.

### (b) `realIntegral_hasDerivAt` is a genuine TWO-SIDED `HasDerivAt` at EVERY real `t`

VERBATIM, `Euler/ContinuousTimeIntegral.lean:53-61`:

```lean
/-- The literal zero-initial-time integral. -/
def realIntegral (f : C(Icc (0 : ℝ) T,E)) : ℝ → E :=
  fun t => ∫ s in (0 : ℝ)..t, extendPath T hT f s

/-- The integral has the actual classical derivative. -/
theorem realIntegral_hasDerivAt (f : C(Icc (0 : ℝ) T,E)) (t : ℝ) :
    HasDerivAt (realIntegral T hT f) (extendPath T hT f t) t := by
  have hc := extendPath_continuous T hT f
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
```

`t : ℝ` is UNRESTRICTED, and `HasDerivAt` is the two-sided notion (`nhds t`, not `nhdsWithin`). Mechanism:
Mathlib FTC-1, `FundThmCalculus.lean:725-728`:

```lean
theorem integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b
```

All three hypotheses genuinely supplied, none assumed:
* interval integrability: `hc.intervalIntegrable 0 t` = `Continuous.intervalIntegrable` (`Basic.lean:511`),
  needs `[IsLocallyFiniteMeasure volume]` (instance) — real;
* `StronglyMeasurableAtFilter f (𝓝 t)`: `hc.aestronglyMeasurable.stronglyMeasurableAtFilter`
  = `Continuous.aestronglyMeasurable` (`AEStronglyMeasurable.lean:239`, domain `ℝ` is second countable) then
  `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter` (`IntegrableOn.lean:57`) — real;
* `ContinuousAt f t`: `hc.continuousAt` from the PROVED `extendPath_continuous` — real.

Mathematical sanity of the two-sidedness at `t = T`: right of `T` the clamped integrand is constant `f T`,
so `∫_0^u` is affine with slope `f T` there; left of `T` FTC-1 applies with the continuous integrand. So the
two-sided derivative at `T` really is `extendPath T hT f T = f T`. The Lean proof gets this for free because
FTC-1 only needs continuity AT the point plus interval integrability, both of which the clamped extension has
on all of ℝ. VERDICT: OK, and this is the load-bearing step for the endpoint claim.

### (c) Bochner integral with `CompleteSpace`, no junk-value escape on the endpoint path

* `Euler/ContinuousTimeIntegral.lean:50`: `variable [CompleteSpace E] (T : ℝ) (hT : 0 ≤ T)` guards the whole
  `section Primitive` (`:48-132`), so `realIntegral`, `integral`, `realIntegral_hasDerivAt`,
  `integral_hasDerivWithinAt` all live under completeness.
* The Mathlib FTC-1 lemma itself is inside `variable [CompleteSpace E]` (`FundThmCalculus.lean:472`; the nearest
  preceding `end` is at `:461`, none between `472` and `725`), so the lemma cannot even be applied without
  completeness — a junk-value instantiation is impossible in the used direction.
* `SeparatingTimeDerivative.lean:15-16` supplies `[CompleteSpace E]` and `[CompleteSpace F]`;
  `ContinuousLinearMap.intervalIntegral_comp_comm` (`IntervalIntegral/Basic.lean:868-872`) needs BOTH
  (`[CompleteSpace F]` from `:868`, `[CompleteSpace E]` in the statement) and is given a real integrability
  proof `((extendPath_continuous T hT g).intervalIntegrable 0 t)` at `:35`.
* Every `∫` on the endpoint path therefore has an explicit integrability witness. NO junk-value escape.
* ONE separate observation (NOT on the endpoint path): in `VolterraConvolution.lean` the section variables
  (`:15-16`) do NOT include `CompleteSpace X`, yet `convolution` (`:108-110`) and `kernelMass` (`:113`) take
  Bochner integrals in `X`. For an incomplete `X` those integrals are Mathlib's junk `0` and
  `convolution_bound` (`:124`) / `convolution_eq_interval` (`:139`) become vacuously true (`0 ≤ …`, `0 = 0`).
  The statements are still TRUE as written and are meaningful whenever instantiated at a complete `X`; the
  hard work (`causalIntegrand_integrable` `:66`, dominated convergence `:93`) is genuine. Flagged as UNCLEAR/
  cosmetic, not a soundness defect, and it does NOT touch `SeparatingTimeDerivative`.

## 3. Vacuity check on the endpoint claim

* `T = 0`: `Icc 0 0 = {0}`, `𝓝[{0}] 0 = pure 0`, so `HasDerivWithinAt _ v {0} 0` holds for ANY `v`. The
  theorem is indeed trivial in that degenerate case. This is a degenerate instance of a universally
  quantified `T` with `hT : 0 ≤ T`, NOT a vacuity escape: nothing in the file restricts attention to `T = 0`.
* `T > 0`, `t = 0`: `0` is a left-accumulation... precisely, a right-accumulation point of `Icc 0 T`, so
  `HasDerivWithinAt (extendPath T hT f) (g 0) (Icc 0 T) 0` is exactly the assertion that the RIGHT
  (one-sided) derivative of `f` at `0` exists and equals `g 0`. Non-trivial.
* `T > 0`, `t = T`: `T` is a left-accumulation point of `Icc 0 T`, so the claim is exactly the LEFT one-sided
  derivative `= g T`. Non-trivial.
* Why it is really PROVED, not smuggled: (i) FTC-2 at `ContinuousTimeIntegral`-free level gives
  `f t = f 0 + ∫_0^t g` for EVERY `t ∈ Icc 0 T` including `t = T` (`SeparatingTimeDerivative.lean:33-44`),
  using only continuity of `f` on the CLOSED interval plus the derivative on the OPEN interval — the exact
  hypothesis shape of `integral_eq_sub_of_hasDerivAt_of_le`; (ii) the primitive `r ↦ f 0 + realIntegral T hT g r`
  has a two-sided `HasDerivAt` with value `g T` at `T` and `g 0` at `0` by `realIntegral_hasDerivAt`
  (§2(b)); (iii) `congr_of_mem` transports (ii) to `extendPath T hT f` along the equality (i), which holds on
  `Icc 0 T`, giving a within-`Icc` (hence one-sided at each endpoint) derivative. The endpoint content comes
  from the CONTINUITY of `f` and `g` up to the endpoints, which is free from the type `C(Icc 0 T, E)`. The
  mathematics is sound; there is no hidden extra hypothesis at the endpoints, and no weakening of the claim.
* `hsep` non-vacuity: with `I = Empty` the injectivity hypothesis would force `E` subsingleton, so `hsep` is a
  real hypothesis; the actual callers instantiate it honestly, e.g. `Euler/SmoothFlowAcceleration.lean:65-71`
  uses `I := Unit`, `L := fun _ => ContinuousLinearMap.id ℝ E` with
  `hsep := fun u v h => congrFun h ()`. In that instantiation `hd` IS the strong `HasDerivAt` on `Ioo`, so the
  theorem is used precisely as an `Ioo → Icc` endpoint upgrade — the interesting and correct content.
  Other consumers: `Euler/SmoothTimeFieldChain.lean:100`, `Euler/SmoothFieldSobolevTime.lean:90`.

## 4. `HasDerivWithinAt.congr_of_mem` usage at `:57-60`

Mathlib (`Mathlib/Analysis/Calculus/Deriv/Basic.lean:566-568`):
```lean
theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x
```
Project use: `apply hp.congr_of_mem _ t.property` (`:57`) with `hp : HasDerivWithinAt (fun r => f ⟨0,…⟩ +
realIntegral T hT g r) (g t) (Icc 0 T) t`, target `f₁ := extendPath T hT f`. Argument order CONFIRMED
correct: `h := hp` (receiver), `hs := _` (the `intro r hr` goal at `:58-60`), `hx := t.property : ↑t ∈ Icc 0 T`
(`t : Icc (0:ℝ) T` is a subtype, `t.property` is exactly the membership proof). The congruence obligation is
`∀ r ∈ Icc 0 T, extendPath T hT f r = f ⟨0,…⟩ + realIntegral T hT g r`, discharged at `:59-60` by
`simpa only [extendPath, projIcc_of_mem hT hr, integral_apply] using eq_initial_add_integral … ⟨r,hr⟩` — i.e.
only ON the set, which is exactly what the lemma needs (`congr_of_mem` derives `hx`-pointwise agreement via
`h.congr hs (hs _ hx)`). No stronger global agreement is claimed or needed. The identical pattern appears at
`ContinuousTimeIntegral.lean:110-112`. VERDICT: OK.

## Per-declaration findings

| name | file:line | statement (my words) | real proof mechanism | verdict |
|---|---|---|---|---|
| `extendPath` | `VolterraConvolution.lean:20` | clamped extension `ℝ → Y`, `f (projIcc 0 T hT t)` | definition | OK |
| `extendPath_continuous` | `VolterraConvolution.lean:24` | the clamp is continuous on ℝ | `f.continuous.comp continuous_projIcc` | OK |
| `extendPath_norm_le` | `VolterraConvolution.lean:29` | `‖extendPath f t‖ ≤ ‖f‖` | `ContinuousMap.norm_coe_le_norm` | OK |
| `causalIntegrand`(+`_measurable`,`_bound`,`_integrable`,`_continuousAt`) | `VolterraConvolution.lean:33,45,54,66,73` | singular causal kernel integrand: aestrongly measurable, dominated by `k r * ‖f‖`, integrable | `ContinuousOn.aestronglyMeasurable` + `.indicator`; `Integrable.mono'` with a real dominating function | OK (integrability PROVED, not assumed) |
| `causalIntegral_continuous` / `convolution` / `convolution_bound` / `convolution_eq_interval` | `VolterraConvolution.lean:93,108,124,139` | causal convolution is a continuous path with kernel-mass bound, equal to the Duhamel interval integral | `continuousAt_of_dominated` (real DCT), `norm_integral_le_integral_norm`, `integral_indicator` | UNCLEAR (no `CompleteSpace X` in scope ⇒ statements degenerate to `0` for incomplete `X`; harmless, off the endpoint path) |
| `multiplierLinear`/`_bound`/`multiplier`/`multiplier_apply`/`multiplier_norm` | `ContinuousTimeIntegral.lean:24,30,38,41,45` | pointwise CLM multiplier on `C(K,·)` is bounded with `‖·‖ ≤ ‖A‖` | `mkContinuous` + `le_opNorm` | OK |
| `realIntegral` | `ContinuousTimeIntegral.lean:53` | `t ↦ ∫ s in 0..t, extendPath f s` on all of ℝ | definition (under `[CompleteSpace E]`, `:50`) | OK |
| **`realIntegral_hasDerivAt`** | `ContinuousTimeIntegral.lean:57` | two-sided `HasDerivAt` at EVERY `t : ℝ`, value `extendPath f t` | Mathlib FTC-1 `intervalIntegral.integral_hasDerivAt_right` with all 3 hypotheses proved | OK (load-bearing) |
| `integralLinear` / `integral` / `integral_apply` / `integral_norm` / `integral_initial` | `ContinuousTimeIntegral.lean:64,88,91,95,100` | primitive as a bounded linear operator `C(Icc 0 T,E) →L[ℝ] C(Icc 0 T,E)` with `‖·‖ ≤ T` | differentiability ⇒ continuity of the primitive; `intervalIntegral.integral_add/_smul`; `norm_integral_le_of_norm_le_const`; `mkContinuous` | OK (`integral_apply` is `rfl` through `mkContinuous`, defeq of a structure projection, not recursion) |
| `integral_hasDerivWithinAt` | `ContinuousTimeIntegral.lean:105` | primitive has the prescribed within-`Icc` derivative at every `t`, endpoints included | `realIntegral_hasDerivAt` ▸ `.hasDerivWithinAt` ▸ `congr_of_mem _ t.property` | OK |
| `eq_initial_add_integral` (Mean-value version) | `ContinuousTimeIntegral.lean:115` | zero-derivative-difference ⇒ `a t = a 0 + ∫ f` | `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` with `C = 0` (genuine MVT, no hidden hypothesis) | OK |
| `EulerSeparatingTimeDerivative.eq_initial_add_integral` | `SeparatingTimeDerivative.lean:24` | separating-family + interior derivative ⇒ `f t = f 0 + integral g t` | `hsep` reduction, `CLM.intervalIntegral_comp_comm` (needs both `CompleteSpace`s, given), Mathlib FTC-2 `integral_eq_sub_of_hasDerivAt_of_le` on `[0,t]` | OK |
| **`EulerSeparatingTimeDerivative.hasDerivWithinAt`** | `SeparatingTimeDerivative.lean:49` | within-`Icc` derivative `= g t` at EVERY `t`, both endpoints | primitive's two-sided `HasDerivAt` (`realIntegral_hasDerivAt`) + `const_add` + `hasDerivWithinAt` + `congr_of_mem` along the FTC-2 identity | OK, non-vacuous for `T > 0` |
| `EulerSeparatingTimeDerivative.hasDerivAt` | `SeparatingTimeDerivative.lean:63` | two-sided derivative on the interior | `.hasDerivAt (Icc_mem_nhds ht.1 ht.2)` | OK |

## Kernel-risk assessment

Grep over the three audited files (`SeparatingTimeDerivative.lean`, `ContinuousTimeIntegral.lean`,
`VolterraConvolution.lean` = 349 lines total):

| pattern | count | sites |
|---|---|---|
| `decide` | 0 | – |
| `native_decide` | 0 | – |
| numerals ≥ 4 digits | 0 | – |
| `Nat.pow` / `Nat.div` / `Nat.mod` / `Nat.gcd` | 0 | – |
| `termination_by` | 0 | – |
| `WellFounded` | 0 | – |
| `.rec` / `.recOn` / `.brecOn` / `Acc.rec` | 0 | – |
| `macro` / `elab` / `syntax` / `set_option` / `axiom` / `unsafe` / `partial` | 0 | – |
| `sorry` / `admit` | 0 | – (also 0 across ALL of `Euler/`, plus 0 `^axiom`, 0 `native_decide`) |
| `rfl` | 2 | `ContinuousTimeIntegral.lean:42` (`multiplier_apply`), `:92` (`integral_apply`) — both defeq unfolding of `LinearMap.mkContinuous`/`ContinuousMap` coercions, i.e. structure projections, NOT `rfl` on recursive data; kernel cost is a small whnf, no `Nat`/`List` recursion |
| `simp only` | 10 | `SeparatingTimeDerivative.lean:55`; `ContinuousTimeIntegral.lean:41,91,100,112,125`; `VolterraConvolution.lean:59,61,84,89` — all `simp only` with explicit lemma lists except `:100`/`:125` (`by simp`), tiny goals |
| `nlinarith` | 1 | `ContinuousTimeIntegral.lean:85` (`‖f‖ * t ≤ T * ‖f‖` from `t ≤ T`, `0 ≤ ‖f‖`) — trivial, no numerals |

Kernel risk: **NEGLIGIBLE**. No decision procedures, no big numerals, no custom recursion, no metaprogramming,
no `set_option` (note: the `Euler` lib is compiled with `autoImplicit = false, warningAsError = true` per
`lakefile.toml`, which is a strengthening, not a weakening). The `noncomputable section` markers
(`SeparatingTimeDerivative.lean:8`, `ContinuousTimeIntegral.lean:11`, `VolterraConvolution.lean:8`) are
expected for Bochner integrals and carry no soundness weight.

## Escalations

None of soundness type. Two items for the parent's ledger:

1. (LOW / cosmetic) `VolterraConvolution.lean:15-16` lacks `CompleteSpace X` while `convolution` (`:108`) and
   `kernelMass` (`:113`) integrate into `X`. For incomplete `X` those defs are Mathlib's junk `0` and
   `convolution_bound` (`:124`) / `convolution_eq_interval` (`:139`) are vacuous. Statements remain true;
   the endpoint theorem is unaffected (`ContinuousTimeIntegral.lean:50` and `SeparatingTimeDerivative.lean:15-16`
   both have completeness). Suggest a `[CompleteSpace X]` for honest strength.
2. (METHODOLOGICAL) All Mathlib signatures here were checked against a `v4.33.0` mathlib checkout, not the
   pinned `v4.34.0-rc2`. No build was possible. If the campaign wants a hard verdict, re-check
   `integral_hasDerivAt_right`, `integral_eq_sub_of_hasDerivAt_of_le`, `HasDerivWithinAt.congr_of_mem`,
   `ContinuousLinearMap.intervalIntegral_comp_comm` at the pinned revision.

## Residue

* No `lake build`: elaboration success, universe/instance resolution, and `simpa only`/`abel`/`nlinarith`
  closure are ASSUMED to succeed (the repo is presumably CI-green); this audit checks the mathematical and
  lemma-shape correctness only.
* Transitive imports NOT audited: `Euler/TimeH1OperatorProduct.lean` → `Euler/TerminalTimePrimitive.lean`,
  `Euler/TimeLpMultiplier.lean`; `Euler/CylinderSobolevSpace.lean` → `Euler/ClosedTranslationGraph.lean`.
  Any `axiom`/`sorry` there would matter, but a repo-wide grep found NO `sorry`, NO `^axiom`, NO
  `native_decide` anywhere under `Euler/`.
* Consumers of `hasDerivWithinAt` only spot-checked (`SmoothFlowAcceleration.lean:60-71` read in full;
  `SmoothTimeFieldChain.lean:100` and `SmoothFieldSobolevTime.lean:90` only grepped).
* `Euler/WeakHilbertODE.lean:151` uses `intervalIntegral.integral_hasDerivWithinAt_right` directly — a
  parallel endpoint mechanism outside this sub-audit's scope.
