# Euler GEVREY layer: norm / index / radius, and the 6^m question

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5). READ-ONLY; no `lake`
was run (no built Mathlib on this box). Every claim below is a line-by-line source read with `file:line`.

## 0. Executive summary (loud parts first)

1. The Gevrey layer is **Gevrey-2 with a free radius parameter**: the weight is `C * R^n * (n!)^2`
   (`Euler/SmoothL2GevreyCalculus.lean:20-21`, `Euler/SmoothL2Gevrey.lean:19-20`) and its shifted
   form `majorant R d n = R^(n+d) * ((n+d)!)^2` (`Euler/EulerProof.lean:196-197`).
   It is **not** `R^m/m!` (analytic/Gevrey-1) and **not** a sup over a fixed finite set of orders.
2. The constant and radius are chosen **before** the order: `HasSupBound`/`HasJetBound` are `∀ n, ...`
   under a single `C R`, and in `pressure_gevrey_majorant` the arguments `M Rc R` and shift `d` are
   bound **before** `(n : ℕ)` (`Euler/EulerProof.lean:5125-5129`). No series over `m` is involved.
3. A factor growing like `6^m` in the derivative order is **absorbed exactly by the radius**:
   `6^n * R^n * (n!)^2 = (6R)^n * (n!)^2`. The Gevrey index `s = 2` is not even needed for this; the
   monotonicity lemma that performs the swap already exists (`HasSupBound.mono`,
   `Euler/SmoothL2GevreyCalculus.lean:23-27`; `HasJetBound.mono`, `Euler/SmoothL2Gevrey.lean:32-38`).
   The only structural constraint on `R` in this layer is a **lower** bound
   (`hR : 2 * M * (Rc + 1) ≤ R`, `Euler/EulerProof.lean:5126`), which enlarging `R` never violates.
4. **LOUD FINDING (where the real 6^m lives).** A literal `6^m` growth does exist in this repo, but in
   the *ordinary Sobolev energy* layer, not in the Gevrey layer:
   `def tameEnergyConstant (m : ℕ) : ℝ := 6*h3ProductConstant*(∑ n ∈ range (m+1), (6 : ℝ)^n)`
   (`Euler/OrdinaryTameEnergy.lean:86-87`), i.e. `tameEnergyConstant m ≍ 6^(m+1)`. It is used **inside an
   exponential**: `Real.exp (tameEnergyConstant m*M*T)` (`Euler/OrdinaryEulerHigherEnergy.lean:84-88`,
   `Euler/OrdinaryEulerHigherEnergy.lean:101-105`). So that layer's higher-order energy bound grows like
   `exp(C·6^m·M·T)` and is useful only for `T ≲ 6^(-m)`: it carries **no** m-uniform (Gevrey/analytic)
   content. It is honestly stated order-by-order as `∀ q, ∃ C, ∀ k t`
   (`Euler/OrdinaryEulerCauchy.lean:71-74`), so nothing is *false* — it is simply the weak
   (non-uniform) form.
5. The Gevrey layer **never touches** that `6^m` layer (grep + import-closure proof in §4), so the `6^m`
   does not leak in. The converse is also true: the Gevrey layer supplies nothing to the ordinary layer.
6. Two smaller warnings: (a) `pressure_gevrey_majorant`'s object is an `s`-truncated jet, and the
   conclusion is *vacuous* for `n > s` because `levelNorm ... n = 0` there
   (`Euler/EulerProof.lean:5083-5100`); (b) `pressure_gevrey_majorant` / `pressure_word_sum_majorant`
   are consumed by **nothing else in the repo** (§3.3).

---

## 1. `Euler/BaseEulerGevrey.lean` (164 lines) — every declaration

Namespace `EulerBaseDatum` (`:9`), `noncomputable section` (`:7`).
This file contains **no Gevrey norm definition of its own**. It is a chain of pointwise jet bounds all
expressed through the shared `majorant` and `HasSupBound`/`HasJetBound` predicates defined elsewhere.

Declarations, in order:

| line | kind | name | what it states |
|---|---|---|---|
| 16 | theorem | `coordinate_norm_le` | `‖(EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ 1` |
| 22 | theorem | `coordinate_bound_on_ball` | `‖iteratedFDeriv ℝ n (fun y : Space => y i) x‖ ≤ 2*majorant 256 0 n` |
| 28 | theorem | `linear_coordinate_bound_on_ball` | `... ≤ (2*‖L‖)*majorant 256 0 n` |
| 38 | theorem | `linearPotential_bound` | `... ≤ (24*‖L‖)*majorant 256 0 n` |
| 66 | def | `cutoffAmplitude` | `(9*(1+3/EulerGevreyCutoff.bumpMass)^2)^3` |
| 68 | theorem | `cutoffAmplitude_nonneg` | `0 ≤ cutoffAmplitude` |
| 70 | def | `potentialAmplitude` | `3*cutoffAmplitude*(24*‖L‖)` |
| 72 | theorem | `potentialAmplitude_nonneg` | — |
| 76 | theorem | `potential_bound` | `‖iteratedFDeriv ℝ n (potential L i) x‖ ≤ potentialAmplitude L*majorant 256 0 n` |
| 84 | def | `vectorPotential` | `∑ i : Fin 3, potential L i x • EuclideanSpace.single i 1` |
| 87 | theorem | `vectorPotential_apply` (simp) | — |
| 91 | theorem | `vectorPotential_smooth` | `ContDiff ℝ ∞ (vectorPotential L)` |
| 94 | def | `coordinateEmbedding` | — |
| 97 | theorem | `coordinateEmbedding_norm` | `≤ 1` |
| 103 | theorem | `vectorPotential_bound` | `... ≤ (3*potentialAmplitude L)*majorant 256 0 n` |
| 121 | theorem | `velocity_eq_curlOperator` | `velocity L = fun x => curlOperator (fderiv ℝ (vectorPotential L) x)` |
| 131 | def | `velocityAmplitude` | `‖curlOperator‖*(3*potentialAmplitude L*256)` |
| 134 | theorem | `velocityAmplitude_nonneg` | — |
| 140 | theorem | `velocity_sup_bound` | `HasSupBound (velocity L) (velocityAmplitude L) 1024` |
| 154 | def | `volumeFactor` | `(volume (Metric.closedBall (0 : Space) 2)).toReal^(1/2 : ℝ)` |
| 156 | theorem | `volumeFactor_nonneg` | — |
| 158 | theorem | `field_jet_bound` | `(field L).HasJetBound (velocityAmplitude L*volumeFactor) 1024` |

Verbatim, the two load-bearing conclusions:

```lean
-- Euler/BaseEulerGevrey.lean:140
theorem velocity_sup_bound (L : Space →L[ℝ] Space) : HasSupBound (velocity L) (velocityAmplitude L) 1024 := by
```
```lean
-- Euler/BaseEulerGevrey.lean:158-159
theorem field_jet_bound (L : Space →L[ℝ] Space) :
    (field L).HasJetBound (velocityAmplitude L*volumeFactor) 1024 :=
```

### 1.1 The actual Gevrey norm behind these

```lean
-- Euler/SmoothL2GevreyCalculus.lean:20-21   (namespace EulerGevrey)
def HasSupBound (f : E → V) (C R : ℝ) : Prop :=
  ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*R^n*(n.factorial : ℝ)^2
```
```lean
-- Euler/SmoothL2Gevrey.lean:19-20   (namespace EulerLpTranslation.SmoothL2Field)
def HasJetBound (A : SmoothL2Field V) (C R : ℝ) : Prop :=
  ∀ n, ‖A.jetLp n‖ ≤ C*R^n*(n.factorial : ℝ)^2
```
```lean
-- Euler/EulerProof.lean:195-197
/-- The Gevrey-two factorial majorant with a nonnegative integer shift. -/
def majorant (R : ℝ) (d n : ℕ) : ℝ :=
  R ^ (n + d) * ((n + d).factorial : ℝ) ^ 2
```

**Verdict on the index.** Weight = `R^n * (n!)^2`. In the standard convention
`‖D^n u‖ ≤ C R^n (n!)^s`, this is **Gevrey index s = 2** (the repo's own docstring says
"Gevrey-two", `Euler/EulerProof.lean:195`). It is *weaker* than analytic/Gevrey-1 (`R^n * n!`) and much
weaker than `R^n/n!`. `R` is a free real parameter, instantiated at literals `256` and `1024` in this
file; the "radius" of Gevrey-2 regularity is `1/R` in that convention.

### 1.2 Radius bookkeeping is monotone-by-design (relevant to the 6^m question)

```lean
-- Euler/SmoothL2GevreyCalculus.lean:23-27
theorem HasSupBound.mono {f : E → V} {C R D S : ℝ}
    (h : HasSupBound f C R) (hC : 0 ≤ C) (hR : 0 ≤ R) (hCD : C ≤ D) (hRS : R ≤ S) :
    HasSupBound f D S := by
```
```lean
-- Euler/SmoothL2GevreyCalculus.lean:29-31
theorem HasSupBound.derivative {f : E → V} {C R : ℝ}
    (h : HasSupBound f C R) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    HasSupBound (fderiv ℝ f) (C*R) (4*R) := by
```
Taking one derivative already multiplies the radius parameter by **4** — which is exactly why
`BaseEulerGevrey.lean` goes from `256` (`:141`) to `1024` (`:140`, `:159`). So per-derivative radius
inflation is a normal, proved-monotone operation in this layer.

---

## 2. `Euler/GevreyGeneratingDerivatives.lean` (130) and `Euler/GevreyCompositionPartitions.lean` (144)

### 2.1 `GevreyGeneratingDerivatives.lean` — the same `(n!)^2` normalisation, in generating-function form

```lean
-- Euler/GevreyGeneratingDerivatives.lean:21-22
def derivativeSum (f : E → F) (N : ℕ) (z : ℝ) (x : E) : ℝ :=
  generatingSum (ftaylorSeries ℝ f x) N z
```
```lean
-- Euler/GevreyGeneratingComposition.lean:98-102
def normalizedJet (P : FormalMultilinearSeries ℝ E F) (n : ℕ) : ℝ :=
  ‖P n‖/(n.factorial : ℝ)^2

def generatingSum (P : FormalMultilinearSeries ℝ E F) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, normalizedJet P n*z^n
```
So this is the **Gevrey-2 majorant series** `Σ_{n=1}^{N} (‖D^n f‖ / (n!)^2) z^n`, truncated at a finite
order `N` (order `N` is a parameter, not a limit). Declarations: `derivativeSum` (`:21`),
`derivativeSum_nonneg` (`:24`), `derivativeSum_add_le` (`:28`), `norm_iteratedFDeriv_id_le` (`:43`),
`derivativeSum_id_le` (`:58`, `≤ z`), `derivativeSum_id_add_le` (`:82`), `derivativeSum_comp_le` (`:88`),
`rational_fraction_mono` (`:107`), `derivativeSum_comp_id_add_le` (`:116`).

The composition estimate is where a per-order factor is *not* free — it carries a **smallness
hypothesis**:
```lean
-- Euler/GevreyGeneratingDerivatives.lean:88-95
theorem derivativeSum_comp_le (f : E → F) (g : F → G) (N : ℕ)
    (z B R : ℝ) (x : E) (hz : 0 ≤ z) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hf : ContDiffAt ℝ N f x) (hg : ContDiffAt ℝ N g (f x))
    (hgj : ∀ j ∈ Finset.Icc 1 N,
      ‖iteratedFDeriv ℝ j g (f x)‖ ≤ B*R^j*(j.factorial : ℝ)^2)
    (hsmall : R*derivativeSum f N z x < 1) :
    derivativeSum (g ∘ f) N z x ≤
      B*(R*derivativeSum f N z x)/(1-R*derivativeSum f N z x) := by
```
Note `hgj` is again `∀ j, ‖D^j g‖ ≤ B*R^j*(j!)^2` with `B R` fixed before `j` — same Gevrey-2 weight,
constant-before-order. The companion rate:
```lean
-- Euler/GevreyFlowBootstrap.lean:57-60
def rationalRate (B R a u : ℝ) : ℝ := B*(R*(a+u))/(1-R*(a+u))

theorem rationalRate_le (B R a u : ℝ) (hB : 0 ≤ B)
    (hu : R*(a+u) ≤ 1/2) : rationalRate B R a u ≤ B := by
```
**This is the one place a `6^m` factor costs something absolute.** A gain of `6^m` in the inner map's
derivatives multiplies `derivativeSum f N z x` as if `z → 6z`, so the thresholds `R*θ < 1` and
`R*(a+u) ≤ 1/2` require shrinking the generating variable `z` by a factor ~6 (equivalently, a 6× smaller
Gevrey-2 radius). It is a *quantitative* cost, not a break — but any place that pins `z` (or the radius
literals `256`/`1024`) numerically would have to be re-tuned.

### 2.2 `GevreyCompositionPartitions.lean` — the mechanism that absorbs geometric-in-`n` factors

Namespace `EulerGevreyComposition` (`:17`). Declarations: `sum_partSize` (`:21`),
`sum_partSize_real` (`:26`), `sum_partSize_succ_sq_le` (`:30`), `factorialProduct` (`:44`),
`partitionWeight` (`:47`), `partitionSum` (`:50`), `partitionWeight_nonneg` (`:53`),
`factorialProduct_extendLeft` (`:58`), `factorialProduct_extendMiddle` (`:66`),
`partitionWeight_extendLeft` (`:84`), `partitionWeight_extendMiddle` (`:92`),
`partitionSum_succ` (`:99`), `partitionSum_succ_le` (`:113`), `partitionSum_le` (`:128`).

```lean
-- Euler/GevreyCompositionPartitions.lean:47-51
def partitionWeight (x : ℝ) (c : OrderedFinpartition n) : ℝ :=
  x^c.length * ((c.length.factorial : ℝ) * factorialProduct c)^2

def partitionSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, partitionWeight x c
```
```lean
-- Euler/GevreyCompositionPartitions.lean:126-129
/-- The entire factorial-square Faà di Bruno partition sum has one fixed
exponential radius, independent of the differentiation order. -/
theorem partitionSum_le (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    partitionSum n x ≤ (x+2)^n * (n.factorial : ℝ)^2 := by
```
This is precisely the "geometric-in-`n` factor is paid by the radius base" pattern: the Faà di Bruno
partition multiplicity (super-exponential in `n` as a *count*) is bounded by `(x+2)^n (n!)^2`, i.e. it
moves `x` to `x+2` in the radius base. A `6^m` factor is the *same species of object* and is handled the
same way: it changes the base, never the index `s = 2`.

---

## 3. `Euler/EulerProof.lean` 5000-5260: the pressure Gevrey theorems

Section opens at `:5106`; docstring `/-! Gevrey pressure regularity derived from actual cylinder
derivative jets and coercivity. -/` (`:5108`); `namespace EulerPressureGevrey` (`:5111`);
`variable (period : ℝ) [Fact (0 < period)]` (`:5116`); section closes `:5183-5185`.

### 3.1 `pressure_gevrey_majorant` — FULL statement, verbatim

```lean
-- Euler/EulerProof.lean:5118-5129
/-- Every finite pressure solve obeys a Gevrey bound uniform in the cutoff order.
The triangular recurrence is derived from genuine strong translation derivatives. -/
theorem pressure_gevrey_majorant {directions : Fin 4 → LiftTangent}
    {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (M Rc R : ℝ) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M) (hRc : 0 ≤ Rc)
    (hR : 2 * M * (Rc + 1) ≤ R) (d : ℕ)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l)
    (hsource : ∀ n ≤ s, levelNorm period J n ≤ majorant R d n) (n : ℕ) :
    levelNorm period (J.solvePressure K κ m c hc hpos) n ≤ majorant R (d + 1) n := by
```

### 3.2 `pressure_word_sum_majorant` — FULL statement, verbatim

```lean
-- Euler/EulerProof.lean:5169-5181
/-- The same Gevrey inverse estimate written as the actual sum over all coordinate derivative words. -/
theorem pressure_word_sum_majorant {directions : Fin 4 → LiftTangent}
    {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (M Rc R : ℝ) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M) (hRc : 0 ≤ Rc)
    (hR : 2 * M * (Rc + 1) ≤ R) (d : ℕ)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l)
    (hsource : ∀ n ≤ s, levelNorm period J n ≤ majorant R d n) (n : ℕ) :
    (∑ w : Fin n → Fin 4, ‖(J.solvePressure K κ m c hc hpos).word w‖) ≤ majorant R (d + 1) n := by
  rw [← levelNorm_eq_words]
  exact pressure_gevrey_majorant period K J κ m c hc hpos M Rc R hM hcM hRc hR d hcoeff hsource n
```

### 3.3 Quantifier order — exactly what is quantified over what

Reading the binder order literally (`Euler/EulerProof.lean:5120-5129`):

* `M Rc R : ℝ` and the shift `d : ℕ` are bound at `:5125-5126`, i.e. **before** `(n : ℕ)` at `:5128`.
* Both hypotheses are themselves *all-order* statements with the **same** `Rc`, `R`, `d`:
  `hcoeff : ∀ l, 1 ≤ l → l ≤ s → ...` (`:5127`), `hsource : ∀ n ≤ s, ... ≤ majorant R d n` (`:5128`).
* The conclusion at `:5129` uses the **same** `R` and shift `d + 1` for that `n`.

So the shape is the **strong** one: *one constant/radius valid for all orders*
(`∀ M Rc R d, (all-order hyps at that R) → ∀ n, conclusion at that R`). It is **not**
`∀ m, ∃ C` (the constant does not depend on `n`), and it is **not** a series/sum over the order `m`.
The only sum present is the sum over the `4^n` derivative **words** at the *fixed* order `n`
(`:5179`), which the single weight `R^(n+d)((n+d)!)^2` covers — the repo's `levelNorm` is by definition
that word sum (`levelNorm_eq_words`, used at `:5069`, `:5180`).

**Two caveats, stated plainly.**
* The object is a jet **truncated at order `s`**: above `s` the left-hand side is identically zero, so the
  statement is *vacuous* for `n > s`:
  ```lean
  -- Euler/EulerProof.lean:5082-5084
  /-- A finite jet has no stored derivatives above its order. -/
  theorem levelNorm_eq_zero_of_lt {s n : ℕ} {f : LiftL2 period}
      (J : SpatialJet period directions s f) (hn : s < n) : levelNorm period J n = 0 := by
  ```
  The uniformity in `n` is genuine (`R` does not depend on `n`, and `s` is arbitrary), but no statement
  here is about an object with infinitely many nonzero derivative levels.
* Neither theorem is used anywhere else in the repository. `grep -rn` over `Euler/`, `NavierStokes/`,
  `ComparatorChallenges/`, `Euler.lean`, `NavierStokes.lean` returns only the declaration sites
  (`Euler/EulerProof.lean:5120`, `:5170`) and the internal use at `:5181`. They are terminal leaves.

### 3.4 The engine: `triangular_inverse_majorant`

```lean
-- Euler/EulerProof.lean:304-316
/-
The triangular inverse rule with an explicit sufficient radius, uniform in the
derivative order and in the input shift. ...
-/
theorem triangular_inverse_majorant (A Rc R : ℝ)
    (hA : 1 ≤ A) (hRc : 0 ≤ Rc) (hlarge : 2 * A * (Rc + 1) ≤ R)
    (d : ℕ) (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant R d n)
    (hZ : ∀ n, Z n ≤ A * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant R (d + 1) n := by
```
Its budget is purely a **lower** bound on `R`:
`hqhalf : Rc / R ≤ 1 / 2` (`:321`), `hbudget : A / R + 2 * A * (Rc / R) ≤ 1` (`:325`), closed by
`majorant_coefficient_term` (`:285-289`) and `geometric_tail_le_two_mul` (`:269-270`).
Consequence for the `6^m` question: a `6^l` gain in the coefficient bound is literally
`majorant Rc 0 l → majorant (6*Rc) 0 l`, and the hypothesis `2*A*(6*Rc+1) ≤ R` is still satisfiable
because `R` is a free parameter with no upper cap in this layer.

---

## 4. Does any of this consume the ordinary-Sobolev energy layer? **NO.**

### 4.1 Direct grep in the audited files (exit code 1 = no match)

```
$ grep -n "tameEnergyConstant\|wordEnergy\|integer_energy_uniform\|higher_energy_of_h3\|EulerOrdinarySobolev\|Evolution" \
      Euler/BaseEulerGevrey.lean Euler/GevreyGeneratingDerivatives.lean Euler/GevreyCompositionPartitions.lean
EXIT=1
```
```
$ awk 'NR>=5106 && NR<=5185' Euler/EulerProof.lean | \
    grep -n "tameEnergyConstant\|wordEnergy\|integer_energy_uniform\|higher_energy_of_h3\|OrdinarySobolev\|Evolution"
EXIT=1
```
(The `EulerPressureGevrey` section's `open` line is `open MeasureTheory InnerProductSpace
EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerJetProductBounds EulerGevrey`,
`Euler/EulerProof.lean:5113-5114` — no ordinary-Sobolev namespace.)

### 4.2 Import-closure proof (stronger than grep)

Transitive `import` closure of `Euler.BaseEulerGevrey` = **751** modules. The modules that *define* the
ordinary energy layer are **absent** from it:

| module (defines) | in closure of `Euler.BaseEulerGevrey`? |
|---|---|
| `Euler.OrdinaryTameEnergy` (`tameEnergyConstant`, `:86`) | **False** |
| `Euler.OrdinaryEulerHigherEnergy` (`integer_energy_uniform` `:84`, `higher_energy_of_h3` `:101`) | **False** |
| `Euler.OrdinarySmoothWords` (`wordEnergy`) | **False** |
| `Euler.OrdinaryBKMReduction` | **False** |
| `Euler.EulerSingularity` (`namespace EulerOrdinarySobolev`, `:22`) | **False** |

Closure of `Euler.GevreyGeneratingDerivatives` = **5** modules, none of them `Ordinary*`.
(`Euler/GevreyCompositionPartitions.lean:1-2` imports only `Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno`
and `Mathlib.Tactic`.)
The `*Evolution*` modules that *are* in the 751-set (`Euler.InviscidSobolevEvolution`,
`Euler.FrozenEvolutionGevrey`, `Euler.LpSupportedEvolution`, `Euler.MeanOrdinaryLift`, ...) are
name-collisions on the word "Evolution", not the `EulerOrdinarySobolev.Evolution` energy structure used
by `integer_energy_uniform` / `higher_energy_of_h3`.

**Verdict (c): NO.** The Gevrey layer neither mentions nor transitively depends on `tameEnergyConstant`,
`wordEnergy`, `integer_energy_uniform`, `higher_energy_of_h3`, or `EulerOrdinarySobolev.Evolution`.

### 4.3 …and here is the actual `6^m`, in the layer the Gevrey files avoid

```lean
-- Euler/OrdinaryTameEnergy.lean:86-87
def tameEnergyConstant (m : ℕ) : ℝ :=
  6*h3ProductConstant*(∑ n ∈ range (m+1), (6 : ℝ)^n)
```
`∑_{n≤m} 6^n = (6^(m+1)-1)/5`, so `tameEnergyConstant m ≍ (6/5)·h3ProductConstant·6^(m+1)`, i.e.
**exponential base 6 in the derivative order**. `h3ProductConstant` itself is an order-independent
constant (`Euler/OrdinaryH3Products.lean:16-17`:
`1+13*smoothEmbeddingConstant+4*(1+3*(sobolevConstant : ℝ))^2`). It is consumed inside an exponential:

```lean
-- Euler/OrdinaryEulerHigherEnergy.lean:84-88
theorem integer_energy_uniform (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : ∀ t, WordBound 3 M (U.velocity t)) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*M*T) := by
```
```lean
-- Euler/OrdinaryEulerHigherEnergy.lean:101-105
theorem higher_energy_of_h3 (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : ∀ t, tensorNorm 3 (U.velocity t) ≤ M) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*M*T) := by
```
Note the word "uniform" in `integer_energy_uniform` means *uniform in `t`*, **not** uniform in `m`: the
factor is `exp(≈6^(m+1)·h3ProductConstant·M·T)`. Its downstream consumer is honest about the quantifier
order — the constant is chosen **after** the order `q`:

```lean
-- Euler/OrdinaryEulerCauchy.lean:71-78
theorem all_order_bounds_of_h3 (V : ℕ → Evolution T hT) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : ∀ q, ∃ R : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ R) :
    ∀ q, ∃ C : ℝ, ∀ k t, tensorNorm q ((V k).velocity t) ≤ C := by
  intro q
  ...
    refine ⟨wordCount q*Real.sqrt (wordCount q*R^2*Real.exp (tameEnergyConstant q*M*T)),?_⟩
```
`∀ q, ∃ C` — **order fixed before the constant**. So nothing there is *false*; but that layer provides
**no** m-uniform / Gevrey / analytic control, and its `T`-window of usefulness degrades like `6^(-m)`.
This is exactly the "silent weakening" to watch for — and it is confined to the ordinary layer.
Also note `wordCount m = ∑_{n≤m} 3^n` (`Euler/OrdinaryEulerHigherEnergy.lean:17`) and the `3*(2:ℝ)^n`
factor at `Euler/OrdinaryTameEnergy.lean:100-102` — the ordinary layer is full of geometric-in-order
factors, which is where the `6` comes from (3 directions × 2 sides in the Leibniz/commutator count).

### 4.4 Would a `6^m` factor break or weaken the **Gevrey** layer?

**No — it is absorbed by the radius, and the Gevrey index is untouched.** Reasons, all from the source:

1. Algebra: `6^n * (C * R^n * (n!)^2) = C * (6R)^n * (n!)^2`, and the weight is exactly
   `C*R^n*(n.factorial : ℝ)^2` (`Euler/SmoothL2GevreyCalculus.lean:20-21`) with `R` a free parameter.
   Equivalently `6^n * majorant R d n ≤ majorant (6*R) d n` for `d ≥ 0`
   (`majorant R d n = R^(n+d)*((n+d)!)^2`, `Euler/EulerProof.lean:196-197`).
2. Mechanised: enlarging the radius is a proved, available step — `HasSupBound.mono`
   (`Euler/SmoothL2GevreyCalculus.lean:23-27`), `HasJetBound.mono` (`Euler/SmoothL2Gevrey.lean:32-38`),
   `majorant_radius_mono` (`Euler/OperatorGevreyCalculus.lean:21`).
3. The layer already does the same thing for its own geometric factors: `4*R` per derivative
   (`Euler/SmoothL2GevreyCalculus.lean:31`), `(x+2)^n` for the whole Faà di Bruno partition sum
   (`Euler/GevreyCompositionPartitions.lean:128-129`), and the `4^n`-many words per order absorbed by
   `R^n` in `levelNorm` (`Euler/EulerProof.lean:5179`).
4. The only constraints on `R` in the pressure/triangular layer are **lower** bounds
   (`hR : 2 * M * (Rc + 1) ≤ R`, `Euler/EulerProof.lean:5126`; `hlarge`, `:310`), which enlargement
   never breaks. There is no upper cap on `R` there.
5. The `(n!)^2` (index `s = 2`) is not even consumed by the `6^m`: a `6^m` is *geometric*, and only
   factors growing like `m!^{s'}` could raise the Gevrey index. So there is **no silent index loss**.

**Where a `6^m` does cost something in the Gevrey layer:** the generating-function/flow-bootstrap
smallness thresholds `hsmall : R*derivativeSum f N z x < 1`
(`Euler/GevreyGeneratingDerivatives.lean:93`) and `hu : R*(a+u) ≤ 1/2`
(`Euler/GevreyFlowBootstrap.lean:59-60`) are **absolute**. A `6^m` gain there is equivalent to `z → 6z`,
so the admissible generating variable / Gevrey-2 radius shrinks by ~6, and any *hard-coded* radius
numeral (`256`, `1024` in `Euler/BaseEulerGevrey.lean:140-141,159`) would need re-tuning. That is a
constant-chase, not a structural break.

---

## 5. Kernel-risk pass (audited ranges only)

Ranges: `Euler/BaseEulerGevrey.lean` 1-164, `Euler/GevreyGeneratingDerivatives.lean` 1-130,
`Euler/GevreyCompositionPartitions.lean` 1-144, `Euler/EulerProof.lean` 5106-5185.

Regex-searched for `\bdecide\b`, `native_decide`, `termination_by`, `WellFounded|Acc\.rec`, `\.rec\b`,
`macro|elab|syntax|declare_syntax`, `set_option`, `^\s*axiom\b`, `\bsorry\b`, `\bunsafe\b`,
`\bpartial\b`, `\bderiving\b`, and numeric literals with 5+ digits. Result table (hits):

| pattern | BaseEulerGevrey | GevreyGeneratingDerivatives | GevreyCompositionPartitions | EulerProof 5106-5185 |
|---|---|---|---|---|
| `decide` / `native_decide` | none | none | none | none |
| `termination_by` | none | none | none | none |
| `WellFounded` / `Acc.rec` | none | none | none | none |
| explicit `.rec` | none | none | none | none |
| `macro`/`elab`/`syntax` | none | none | none | none |
| `set_option` | none | none | none | none |
| `axiom` | none | none | none | none |
| `sorry` | none | none | none | none |
| `unsafe` / `partial` / `deriving` | none | none | none | none |
| numeral ≥ 5 digits | none | none | none | none |
| `noncomputable section` | `:7` | `:8` | `:13` | (file-level) |

Largest numerals in the audited ranges: **`256` and `1024`** (both only in
`Euler/BaseEulerGevrey.lean`, at `:23,24,26,30,34,36,40,47,51,77,80,104,113,117,118,132,140,141,143,145,150,151,159,162`);
the other three ranges contain **no** literal of 3+ digits. Nothing here forces the kernel to evaluate a
big numeral: `256`/`1024` occur only as arguments to `majorant`/`HasSupBound`/`HasJetBound` and are
discharged by `norm_num`/`positivity`, never by `decide`.

Recursion used is structural / Mathlib-provided only: `induction n with | zero | succ` inside
`Euler/GevreyCompositionPartitions.lean:130-142` and `Euler/GevreyGeneratingDerivatives.lean` proofs;
`Nat.strong_induction_on` in `triangular_inverse_majorant` (`Euler/EulerProof.lean:330`, outside the
5106-5185 range, well-founded recursion via Mathlib's own lemma, no custom `WellFounded` construction);
`OrderedFinpartition` / `extendEquiv` from `Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno`.
One note, not a kernel risk: `Euler/GevreyCompositionPartitions.lean:2` imports all of `Mathlib.Tactic`.

**Kernel-risk verdict: clean.** No `decide`/`native_decide`, no `axiom`/`sorry`, no custom well-founded
recursion, no metaprogramming, no `set_option`, no big numerals in the audited ranges.
(Caveat, stated openly: this is a source-level audit only — no `lake build` / `#print axioms`
was run, because there is no built Mathlib on this machine.)
