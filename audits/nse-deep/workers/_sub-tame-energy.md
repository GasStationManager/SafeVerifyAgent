# Sub-audit: `Euler/OrdinaryTameEnergy.lean` (tame higher-order energy estimate)

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` = openai/NavierStokesAndEuler @ `f9e8bc5`.
Method: SOURCE READING ONLY (no Mathlib build available, `lake build` NOT run). Every claim below
is a re-derivation from the actual statements/proof terms at the cited `file:line`. I did NOT
verify that the files compile; all "OK" verdicts are "the argument as written is valid and
non-circular", not "the kernel accepted it".

## Scope

Full line-by-line read of `Euler/OrdinaryTameEnergy.lean` (146 lines, 8 declarations), plus one
level down (statements AND proofs read) in:

| file | what was read |
|---|---|
| `Euler/OrdinarySmoothWords.lean` | `wordField` :31, `wordEnergy` :94, `WordBound` :97, `wordBound_sqrt_energy` :109, `wordBound_wordField` :115 |
| `Euler/OrdinaryWordInterpolation.lean` | `wordMaximum` :17, `wordMaximum_logconvex` :31, `wordMaximum_product_le` :52, `wordField_pointwise_maximum` :106 |
| `Euler/NonnegativeLogConvex.lean` | `cross` :15, `pair` :37, `between` :46 (whole file, 51 lines) |
| `Euler/OrdinaryTameProduct.lean` | whole file (102 lines): `wordPointBound` :17, `wordPointBound_product` :24, `coordinateProduct_tame` :63, `tame_outer_product` :83 |
| `Euler/OrdinaryH3Products.lean` | `h3ProductConstant` :16 + :19/:24/:28, `scalarProduct_h1_bound` :32, `gradient_outer_product` :133 |
| `Euler/OrdinaryL2Integration.lean` | `field_inner_integrable` :20, `field_directional_ibp` :33, `field_directional_inner` :46 |
| `Euler/OrdinaryWordBounds.lean` | `real_pointwise_H2` :67, `wordBound_pointwise` :76 |
| `Euler/OrdinaryTransportCancellation.lean` | `advection_inner_zero` :42 (whole file) |
| `Euler/OrdinaryFieldAlgebra.lean` | `coordinateProduct` :109, `advectionField` :118 |
| `Euler/OrdinaryH3Commutator.lean` | `advection_directional` :14, `transportCommutator` :25, `transportCommutator_snoc` :32 |
| `Euler/OrdinaryWordConstraints.lean` | `word_solenoidal` :32, `word_gradient` :40, `word_pressure_pairing_zero` :49 (whole file) |
| `Euler/MeanSolenoidalSpace.lean` | `gradientSpace` :50, `solenoidalSpace` :58, `pressure_pairing_zero` :129 |
| `Euler/LpSmoothField.lean` | `structure SmoothL2Field` :31-34 |
| `Euler/EulerProof.lean` | `smoothEmbeddingConstant` :8227, `smooth_pointwise_le_H2` :8237 |
| `Euler/MeanCutoffCurlBound.lean` | `sobolevConstant` :20, `homogeneous_sobolev` :24 |
| consumers (for question 4) | `Euler/OrdinaryEulerHigherEnergy.lean` :39-63, `Euler/OrdinaryWordTime.lean` :69-97, `Euler/OrdinaryEulerDifference.lean` :21-54, `Euler/OrdinaryRegularizedEnergy.lean` :22-49, `Euler/OrdinaryEulerCauchy.lean` :70-91 |

## Answers to the six questions

### 1. Exact statement of `integer_energy_tame` (`Euler/OrdinaryTameEnergy.lean:123-126`)

```lean
theorem integer_energy_tame (A P : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : WordBound 3 M A) (hdiv : ∀ x, divergence A.field x=0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    integerEnergyProduction m A (eulerRhs A P) ≤ tameEnergyConstant m*M*wordEnergy m A
```

Literal unfoldings:

* `integerEnergyProduction m A Q = 2*(∑ n ∈ range (m+1), ∑ w : Fin n → Fin 3, ⟪(wordField A w).toLp,(wordField Q w).toLp⟫_ℝ)` (`:93-95`).
  Sum over ALL `3^n` words of each length `n ≤ m`; `wordField A w` = the iterated coordinate
  derivative `∂_{w 0} … ∂_{w (n-1)} A` (`OrdinarySmoothWords.lean:31-33`, characterised in L²
  by `wordField_field` :43).
* `eulerRhs A P = fieldNeg (addField (advectionField A A) P)` (`:62-63`), pointwise
  `= -fderiv ℝ A.field x (A.field x) - P.field x` (`eulerRhs_field` :65-68). So `P` is the
  pressure FORCE `∇p`, and `eulerRhs` is `-(u·∇u) - ∇p`.
* `wordEnergy m A = ∑ n ∈ range (m+1), ∑ w, ‖(wordField A w).toLp‖^2` (`OrdinarySmoothWords.lean:94`).
* `WordBound s M A = ∀ n ≤ s, ∀ w : Fin n → Fin 3, ‖(wordField A w).toLp‖ ≤ M`
  (`OrdinarySmoothWords.lean:97`), i.e. `M` bounds each individual L² derivative word of order ≤ 3
  (an H³-max norm, equivalent to the H³ norm up to the fixed factor `∑_{n≤3}3^n = 40`).

So the content is: `2 Σ_{|w|≤m} ⟪D^w u, D^w(-u·∇u-∇p)⟫_{L²} ≤ C(m)·‖u‖_{H³-max}·‖u‖²_{H^m-word}`.
The index range of the production sum is `range (m+1)` — the SAME range as `wordEnergy m`
(no off-by-one weakening), and it matches the derivative formula
`wordEnergy_hasDerivWithinAt` (`OrdinaryWordTime.lean:87-90`) exactly, factor 2 included.

### 2. Is `tameEnergyConstant m` a function of `m` only? YES.

`tameEnergyConstant m = 6*h3ProductConstant*(∑ n ∈ range (m+1), (6:ℝ)^n)` (`:86-87`).
Full unfolding to fixed data:

* `h3ProductConstant = 1 + 13*smoothEmbeddingConstant + 4*(1+3*(sobolevConstant:ℝ))^2`
  (`OrdinaryH3Products.lean:16-17`).
* `smoothEmbeddingConstant = embeddingConstant 3 2 _ * ((unitBumpCoefficient 0) + (2π)^(-2:ℤ)*3*unitBumpCoefficient 2)`
  (`EulerProof.lean:8227-8229`) — depends only on dimension 3 and order 2.
* `sobolevConstant = eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2`
  (`MeanCutoffCurlBound.lean:20-21`) — Mathlib's homogeneous Sobolev constant for `Space = ℝ³`, `p = 2`.

None of these mentions a field, `A`, `P`, `M`, `T`, or any solution. **No hidden solution
dependence**: the field arguments `A`, `P` and the bound `M` do not occur in the constant, and
`M` appears in the statement only as an explicit, universally quantified linear factor. Size:
`tameEnergyConstant m = 6·C·(6^{m+1}-1)/5 ≈ (6/5)·C·6^{m+1}` — exponential in `m`, but a numeral
function of `m` only. Positivity is genuine (`1 + …`, so `h3ProductConstant ≥ 1`), so the
constant is not degenerate/zero: the estimate is not "≤ 0" in disguise.

### 3. Where does the nonlinear estimate come from? COMMUTATOR + H²-pointwise + L² log-convex interpolation. Constant uniform in the field.

Chain, bottom-up:

1. **Exact transport cancellation** `advection_inner_zero` (`OrdinaryTransportCancellation.lean:42-64`):
   `divergence A.field = 0 → ⟪(advectionField A B).toLp, B.toLp⟫ = 0`. Proved by real integration
   by parts (`scalar_transport_pair` :29, `field_directional_inner`
   `OrdinaryL2Integration.lean:46`), **no compact-support assumption** — integrability comes from
   the `SmoothL2Field` structure fields (`LpSmoothField.lean:31-34`: `ContDiff ℝ ∞` + every
   `iteratedFDeriv` in L²).
2. **Pressure orthogonality** `word_pressure_pairing_zero` (`OrdinaryWordConstraints.lean:49-53`),
   via `word_gradient` :40 / `word_solenoidal` :32 (derivative words stay in
   `gradientSpace`/`solenoidalSpace`) and `pressure_pairing_zero`
   (`MeanSolenoidalSpace.lean:129`, literally `hu p hp` — orthogonal complement).
   `solenoidalSpace := gradientSpace.orthogonal` (:58).
3. Consequently `eulerRhs_pairing` (`OrdinaryTameEnergy.lean:70-84`) reduces the whole nonlinear
   production term to a **commutator only**:
   `⟪D^w u, D^w rhs⟫ = -⟪[D^w, u·∇]u, D^w u⟫`, with
   `transportCommutator A B w := fieldSub (wordField (advectionField A B) w) (advectionField A (wordField B w))`
   (`OrdinaryH3Commutator.lean:25`). This is a genuine commutator estimate, NOT a naive Leibniz
   bound on `D^w(u·∇u)`.
4. **Commutator bound** `tame_transportCommutator_word` (`:32-52`) / `tame_transportCommutator`
   (`:54-60`): `‖[D^a, u·∇]u‖_{L²} ≤ 3(2^n-1)·h3ProductConstant·M·N` by induction on `n` using
   `transportCommutator_snoc` (`OrdinaryH3Commutator.lean:32`) — each induction step peels off one
   derivative onto the advecting factor and calls
5. `tame_advection_outer` (`:16-30`) → `tame_outer_product` (`OrdinaryTameProduct.lean:83-100`):
   Leibniz recursion `word_coordinateProduct_recurrence` (`OrdinaryH3Products.lean:124`) giving the
   `2^n` factor, base case
6. `coordinateProduct_tame` (`OrdinaryTameProduct.lean:63-81`): for `m = 3` it uses the honest
   H¹×H¹→L² product `gradient_outer_product` (`OrdinaryH3Products.lean:133`, itself resting on
   `scalarProduct_h1_bound` :32 which uses `smooth_product_h1`, i.e. the **L⁶ Sobolev embedding
   with exponent 6**, `homogeneous_sobolev` `MeanCutoffCurlBound.lean:24-26`, `L²·L²→L¹` via
   Cauchy–Schwarz on `L⁶×L³`-type pairing packaged in `OrdinarySobolevL4.lean`); for `m ≥ 4` it
   puts the LOW factor in L^∞ by the **H²→L^∞ embedding** `real_pointwise_H2`
   (`OrdinaryWordBounds.lean:67`, from `smooth_pointwise_le_H2` `EulerProof.lean:8237`) through
   `wordPointBound` (`OrdinaryTameProduct.lean:17`, note `∑ j ∈ range 3` = 3 extra derivatives) and
   `wordPointBound_product` :24.
7. **The tameness itself** is `wordMaximum_product_le` (`OrdinaryWordInterpolation.lean:52-73`):
   `max_a·max_b ≤ M·N` whenever `a,b ≤ m` and `a+b ≤ m+3`, obtained from
   `EulerNonnegativeLogConvex.between` (`NonnegativeLogConvex.lean:46`: `x a·x b ≤ x s·x (a+b-s)`
   for `s ≤ a ≤ b`) applied at base index `s = 3`, where log-convexity
   `max_{n+1}^2 ≤ max_n·max_{n+2}` is `wordMaximum_logconvex` (:31-50), proved by the same L²
   integration by parts `field_directional_inner`. This is a real (Landau–Kolmogorov style)
   interpolation, purely algebraic on top of IBP — I re-derived `cross`/`pair`/`between` and they
   are correct, including the zero-entry case (:19-25).

Counting audit (I re-derived every `omega`): `tame_outer_product` needs `n+k+l ≤ m+1`;
`coordinateProduct_tame` needs `k+l ≤ m+1` and, in the branch `k ≤ l`, `k+2 ≤ m`, which does
follow from `2k ≤ k+l ≤ m+1` and `4 ≤ m`; `wordMaximum_product_le` then needs
`(k+j)+l ≤ m+3` with `j ≤ 2` ✓ and `k+j ≤ m` ✓. The derivative budget closes with no slack abuse.
**Uniformity in the field:** the only field-dependent quantities entering the constant chain are
`M` (given `WordBound 3 M A`) and `N` (instantiated to `√(wordEnergy m A)`); both appear as
explicit factors, and every multiplicative constant is `smoothEmbeddingConstant`,
`sobolevConstant`, `13`, `4`, `3^j`, `2^n`, `3^n` — all field-independent numerals or fixed
embedding constants.

### 4. Does the proof assume an energy differential inequality, or assume regularity of the object being estimated? NO.

Hypotheses of `integer_energy_tame` and who discharges them:

| hypothesis (`:123-125`) | nature | discharged by |
|---|---|---|
| `hm : 3 ≤ m` | order restriction | callers: `OrdinaryEulerHigherEnergy.lean:56`, `OrdinaryEulerCauchy.lean:75` (`by_cases hq : 3 ≤ q`; the `q < 3` case is handled separately at :87-91) |
| `hM : WordBound 3 M A` | **assumed H³ bound** (the whole point of a tame/conditional estimate) | NOT proved here; supplied as `∀ t, WordBound 3 M (U.velocity t)` at `OrdinaryEulerHigherEnergy.lean:57`, ultimately from `tensorNorm 3 (U.velocity t) ≤ M` (`higher_energy_of_h3` :101-107). Honest conditional. |
| `hdiv : ∀ x, divergence A.field x = 0` | pointwise incompressibility | `solenoidal_representative_divergence` from `U.solenoidal t` (`OrdinaryEulerHigherEnergy.lean:61-62`) |
| `hA : A.toLp ∈ solenoidalSpace` | Helmholtz | `Evolution.solenoidal` structure field (`OrdinaryEulerDifference.lean:26`) |
| `hP : P.toLp ∈ gradientSpace` | pressure is a gradient | `Evolution.gradient` structure field (`OrdinaryEulerDifference.lean:27`) |
| smoothness / integrability of `A`, `P` and of ALL their derivatives, and integrability of every pairing | structure fields | `SmoothL2Field` (`LpSmoothField.lean:31-34`) — `ContDiff ℝ ∞` + `∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume`; the pairings are then genuinely integrable by `field_inner_integrable` (`OrdinaryL2Integration.lean:20`). Nothing is postulated ad hoc inside the proof. |
| `X := √(wordEnergy m A)` is a valid `WordBound m X A` | needed for the high-order factor | PROVED, `wordBound_sqrt_energy` (`OrdinarySmoothWords.lean:109-113`) via `word_norm_sq_le_energy` :103. Used at `OrdinaryTameEnergy.lean:105`. |

No differential inequality is assumed anywhere in this file: `integerEnergyProduction` is a purely
algebraic pairing, and the identification `d/dt wordEnergy = integerEnergyProduction` is DERIVED,
not axiomatised — `wordEnergy_hasDerivWithinAt` (`OrdinaryWordTime.lean:86-97`) from
`ordinaryWord_hasDerivWithinAt` :78 and the pointwise `Evolution.time_law`
(`OrdinaryEulerDifference.lean:28-32`), then wired at `OrdinaryEulerHigherEnergy.lean:48-54`. The
docstring claim at `OrdinaryEulerHigherEnergy.lean:6` ("no postulated energy differential
inequality") is, unusually, backed by the code.
No circularity: the file's dependency cone (products → interpolation → IBP → Helmholtz) never
refers back to `integer_energy_tame` or to any energy bound.

### 5. Vacuity / triviality probes — all failed to break it

* **Constant zero?** No: `h3ProductConstant ≥ 1` by the `1+` in `OrdinaryH3Products.lean:17`
  (and `_left`/`_middle` at :24/:28 show it dominates both used constants). If it had been `0` the
  statement would be a false-looking strong claim, not a vacuous one.
* **`M` forced huge / hypothesis unsatisfiable?** No: `hM` is satisfiable for every field with the
  sharp choice `M = √(wordEnergy 3 A)` (`wordBound_sqrt_energy`), and `wordBound_nonneg` only
  forces `0 ≤ M`. `M = 0` forces `A = 0` in L² and both sides are 0, consistent.
* **Junk-value escape?** No `fderiv`/`integral` junk-value trick is used: differentiability comes
  from `A.smooth` (`OrdinaryL2Integration.lean:40-41`), integrability from `A.integrable`. The `L²`
  objects are `MemLp.toLp` of actual smooth functions with `toLp_ae` bridging (`LpSmoothField.lean:42-44`),
  so a "0 by junk" reading is impossible.
* **Trivially true side?** No. RHS `≥ 0` always, and the LHS is a signed quantity that is genuinely
  positive for generic fields, so the inequality has content; it is exactly the Grönwall input
  `E_m' ≤ C(m)·M·E_m` used at `OrdinaryEulerHigherEnergy.lean:64-92`.
* **Absolute value missing?** The proof bounds only the pairing from above (`neg_le_abs` at :117),
  not `|·|`. This is correct for a Grönwall UPPER bound; no over-claim in the statement.
* **Empty-domain / `Fin 0` degeneracy?** `n = 0` terms are the field itself
  (`wordField_zero` :35) and are included; `transportCommutator … (Fin 0)` is genuinely 0
  (`OrdinaryH3Commutator.lean:28-30`), matching the `2^0-1 = 0` coefficient.
* **Real limitations (not vacuity):** (i) `tameEnergyConstant m ~ 6^{m+1}`, so the Grönwall factor
  `exp(tameEnergyConstant m·M·T)` (`OrdinaryEulerHigherEnergy.lean:87`,
  `OrdinaryEulerCauchy.lean:78`) blows up double-exponentially in `m`; the downstream
  quantification is `∀ q, ∃ C` (`OrdinaryEulerCauchy.lean:70-73`), which is honest, but NOTHING
  here is uniform in `m`, so no analytic/Gevrey-type conclusion can be drawn from this file.
  (ii) the estimate is CONDITIONAL on an assumed uniform H³ bound `M`; it is a propagation lemma,
  not a regularity theorem. (iii) `P` is an arbitrary `gradientSpace` field: the pressure Poisson
  equation is never used (the pressure is annihilated by orthogonality), so no pressure estimate is
  claimed or needed — but that also means `Evolution.pressureForce` must be SUPPLIED as a
  `SmoothL2Field` with all jets in L², which is a nontrivial decay assumption discharged only at
  `evolutionOfClassical` (`OrdinaryEulerDifference.lean:34-54`).

### 6. Kernel-risk pass (13 files listed in Scope)

Machine scan of the 13 files (regex over the sources) plus manual reading:

| pattern | count | notes |
|---|---|---|
| `decide` / `native_decide` | **0** | — |
| `macro` / `elab` / `syntax` / `set_option` / `axiom` / `unsafe` / `partial` / `sorry` | **0** | confirms the repo-wide zero-finding; no metaprogramming in this cone |
| numeric literals with > 4 digits | **0** | largest literals: `13`, `40`, `399`, `1800`, `3600` (the last three are outside this file, `OrdinaryH3Energy.lean:113`, `OrdinaryH3Envelope.lean:17`) |
| explicit `.rec` / `recOn` / `Acc.rec` / `WellFounded` | **0** | — |
| `termination_by` / `decreasing_by` | **0** | — |
| `deriving` | **0** | — |
| `Nat.*` numeral ops | 7, all `Nat.add_zero` / `Nat.zero_add` rewrites (`OrdinaryTameEnergy.lean:60`, `OrdinaryH3Products.lean:105,107`, `OrdinarySmoothWords.lean:118`, `OrdinaryWordInterpolation.lean:85`, `NonnegativeLogConvex.lean:17`, `OrdinaryH3Commutator.lean:102`) | pure defeq index normalisation, no `Nat.pow/div/mod/gcd/beq/ble` anywhere |
| `rfl` on recursive data | 4 relevant: `OrdinarySmoothWords.lean:29,36` (`wordField A (w : Fin 0 → _) = A` — one `Nat.rec` iota step), `OrdinaryTransportCancellation.lean:54`, `OrdinaryFieldAlgebra.lean:28,54,116`, `OrdinaryWordConstraints.lean:47` | all single-step structure/`Nat.rec` iota or projection reductions on SYMBOLIC arguments; no numeral evaluation |
| `Finset.sum` over `range` with a concrete numeral | 8 sites, all `range 3` (`OrdinaryTameProduct.lean:18,28,34,36`, `OrdinaryWordInterpolation.lean:109`, `OrdinaryWordBounds.lean:68,79,81`) plus `range 4` in the sibling `OrdinaryH3Energy.lean:120` | expanded by `norm_num [sum_range_succ]` into 3 real summands (`OrdinaryTameProduct.lean:39`, `OrdinaryWordBounds.lean:83`); the kernel checks `13 = 1+3+9` style ℝ arithmetic at 2-digit size only |
| `Fintype`/card computations | `Fintype.card_fin` on `Fin 3` (`OrdinaryTameEnergy.lean:30`) and `card (Fin n → Fin 3) = 3^n` used symbolically at `:136` (`by simp`) | `n`, `m` stay SYMBOLIC (`range (m+1)`, `Fin n → Fin 3`); the kernel never enumerates a concrete `3^n`-element `Finset` |
| structural recursion the kernel must unfold | `wordField` (`OrdinarySmoothWords.lean:31-33`, match on `0 / _+1` ⇒ compiles to `Nat.rec`) | unfolded only symbolically via `wordField_zero`/`wordField_cons` simp lemmas and explicit `induction n` (`OrdinaryTameEnergy.lean:37`, `OrdinaryTameProduct.lean:89`, `OrdinaryWordInterpolation.lean:84`, `NonnegativeLogConvex.lean:16,39`); no nested/indexed inductive, no `Acc.rec`, no eta-heavy structure defeq beyond `SmoothL2Field` field projections |

**Verdict: the kernel is NOT asked to perform any risky computation in this cone.** All arithmetic
is symbolic `ℝ` ring/`linarith`/`nlinarith`/`positivity` reasoning plus `omega` on small ℕ index
constraints; the heaviest closed numeral facts are `∑_{j<3} 3^j = 13` and `6 = 3*2`.
Reservation: `simp`/`norm_num`-produced proof terms cannot be inspected without a build, so this is
a source-level (not kernel-level) clearance.

## Per-declaration findings

| # | declaration (`Euler/OrdinaryTameEnergy.lean`) | verdict | finding |
|---|---|---|---|
| 1 | `tame_advection_outer` :16-30 | OK | `‖D^a((D^w u)·∇ D^v u)‖ ≤ 3·2^n·C·M·N` for `1 ≤ k`, `n+k+l ≤ m`. Sums the 3 coordinate pieces; calls `tame_outer_product` with the shifted budget `n+k+(l+1) ≤ m+1`, which matches that lemma's `≤ m+1` convention (`OrdinaryTameProduct.lean:85`). `1 ≤ k` is essential: `k = 0` is exactly the term that must cancel, and it is excluded. |
| 2 | `tame_transportCommutator_word` :32-52 | OK | Induction on `n` via `transportCommutator_snoc`; coefficient bookkeeping `3(2^n-1) = 3(2^n-1-1)·…` closes by `pow_succ; ring` at :52. Base case genuinely 0 (`transportCommutator_zero`). Correct commutator structure, no missing term. |
| 3 | `tame_transportCommutator` :54-60 | OK | Specialisation `v = Fin.elim0`. |
| 4 | `eulerRhs` :62-63 + `eulerRhs_field` :65-68 | OK | `-(u·∇u) - ∇p`; `advectionField_field` (`OrdinaryFieldAlgebra.lean:121-128`) really is `fderiv B x (A x)`, i.e. `(A·∇)B`, proved not asserted. Name matches statement. |
| 5 | `eulerRhs_pairing` :70-84 | OK | The crucial identity `⟪D^w u, D^w rhs⟫ = -⟪[D^w,u·∇]u, D^w u⟫`. Top transport term killed by `advection_inner_zero` (needs `hdiv`), pressure killed by `word_pressure_pairing_zero` (needs `hP`,`hA`). Both are real theorems with real proofs; I checked signs (`inner_neg_right`, `real_inner_comm`) and they are consistent. |
| 6 | `tameEnergyConstant` :86-87 + `_nonneg` :89-91 | OK | Closed form in `m` only (question 2). `6·C·∑_{n≤m}6^n`. |
| 7 | `integerEnergyProduction` :93-95 | OK (name honest) | Purely algebraic `2Σ⟪D^w A, D^w Q⟫`. "Production" is justified only via `OrdinaryWordTime.lean:87-90` + `OrdinaryEulerHigherEnergy.lean:48-54`, where it is PROVED to be the derivative of `wordEnergy m`. Same summation range as `wordEnergy m` — no index mismatch. |
| 8 | `eulerRhs_word_tame` :97-121 | OK | Per-word bound `⟪D^w u, D^w rhs⟫ ≤ 3·2^n·C·M·E_m`. Instantiates the high-order bound at the SHARP self-referential value `X = √(wordEnergy m A)` — legitimate because `wordBound_sqrt_energy` proves it; `X² = E_m` by `Real.sq_sqrt` with `wordEnergy_nonneg`. Slack `3(2^n-1) → 3·2^n` at :110-114 needs `C,M,X ≥ 0`, all available. |
| 9 | `integer_energy_tame` :123-144 | OK | Sums item 8 over `3^n` words and `n ≤ m`, `3^n·2^n = 6^n` (:137-140), then `2·Σ6^n·(3C·M·E) = tameEnergyConstant m·M·E` by `unfold tameEnergyConstant; ring` (:144). I re-did this algebra by hand: `2·3 = 6` ✓ exactly, no hidden slack, no wrong constant. |
| — | `wordMaximum_product_le` (`OrdinaryWordInterpolation.lean:52-73`) | OK (the real engine) | Landau–Kolmogorov interpolation at base index 3 from IBP log-convexity. This, not a magic constant, is what makes the estimate tame. Verified `between`'s ℕ-subtraction side conditions (`3 ≤ c ≤ d`, `c+d ≤ m+3`). |
| — | `SmoothL2Field` (`LpSmoothField.lean:31-34`) | UNCLEAR (scope note, not a defect) | The class of fields is "smooth with EVERY iterated derivative in L²". This is what removes all compact-support/decay side conditions (`OrdinaryL2Integration.lean:5-7`). It is a strong but standard-for-this-setting hypothesis; the burden shifts to whoever constructs an `Evolution`. Not verifiable from this cone. |
| — | `Evolution` (`OrdinaryEulerDifference.lean:21-32`) | UNCLEAR (scope note) | The solution, its pressure force, jet continuity, both Helmholtz constraints and the pointwise time law are STRUCTURE FIELDS. Everything downstream is conditional on inhabiting this structure (`evolutionOfClassical` :34-54 reduces it to a classical smooth decaying solution). Whether a nonempty instance is ever produced is outside this sub-audit. |

Verdict counts (9 declarations in the target file): **OK 9, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0.**
Plus 2 UNCLEAR scope notes on out-of-file structures (`SmoothL2Field`, `Evolution`).
I tried hard to break items 5, 8, 9 and could not.

## Escalations (for the parent)

1. **NOT a defect but must not be mis-sold:** `integer_energy_tame` is a CONDITIONAL propagation
   estimate. Its `M` is an ASSUMED uniform H³-word bound (`:124`), and downstream
   (`OrdinaryEulerHigherEnergy.lean:56-107`, `OrdinaryEulerCauchy.lean:70-91`) it is used exactly
   that way (`∀ t, WordBound 3 M (U.velocity t)` as a hypothesis). Nothing here proves an H³ bound,
   hence nothing here bears on global regularity/blow-up. Any headline that reads it as more should
   be challenged.
2. **`m`-non-uniformity:** `tameEnergyConstant m ≈ (6/5)·h3ProductConstant·6^{m+1}` (`:86-87`), and
   consumers exponentiate it (`exp(tameEnergyConstant m·M·T)`, `OrdinaryEulerHigherEnergy.lean:87`,
   `OrdinaryEulerCauchy.lean:78`). If any part of the repo claims analyticity/Gevrey regularity or
   an `m`-uniform statement built on this constant, that step deserves its own audit — this file
   supplies nothing uniform in `m`. (`OrdinaryEulerCauchy.lean:70-73` is correctly `∀ q, ∃ C`.)
3. **Pressure is never estimated, only projected away** (`:80-82` via
   `OrdinaryWordConstraints.lean:49`). `P` is any `gradientSpace` field, so the pressure Poisson
   solvability/regularity is entirely relocated into the `Evolution.pressureForce` +
   `Evolution.gradient` structure fields (`OrdinaryEulerDifference.lean:23,27`). A consumer at
   `OrdinaryRegularizedEnergy.lean:42-49` instantiates `P := fieldSub B B` (i.e. ZERO pressure) —
   legitimate there because the mollified `S.rhs` already contains the projection
   (`rhs_pairing` :22-26) and `0 ∈ gradientSpace` (:36-38), but it is a place where a reader could
   be misled into thinking the Euler pressure was handled. Flagged, not condemned.
4. Kernel-side: this cone is clean (zero `decide`, zero big numerals, zero metaprogramming, zero
   well-founded recursion). If the swarm is triaging kernel risk, do NOT spend budget here.

## Residue (what I could not check)

* No build: I could not confirm the file elaborates, nor inspect the proof terms produced by
  `simp`/`norm_num`/`omega`/`positivity`/`nlinarith` (e.g. `:136 by simp`, `:144 ring`,
  `OrdinaryTameProduct.lean:39`). All arithmetic claims above were re-derived by hand instead.
* One-level-down only for: `smooth_product_h1` / `OrdinarySobolevL4.lean` internals (the L⁶
  Sobolev input), `embeddingConstant` / `unitBumpCoefficient` (finiteness of
  `smoothEmbeddingConstant` is only asserted by name plus `_nonneg`; a ZERO or absurd value would
  not create a false theorem here, but a *hidden* dependence would — I checked the definitions and
  saw none), `solenoidal_representative_divergence`, `sobolevPath_hasDerivWithinAt`
  (`OrdinaryWordTime.lean:82`), and Mathlib's
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable` (`OrdinaryL2Integration.lean:36`) —
  this last one is the single external analytic input carrying the no-compact-support IBP and is
  worth a targeted check by whoever audits `OrdinaryL2Integration.lean`.
* Whether `Evolution` is ever inhabited by a genuine nontrivial 3D Euler solution: out of scope.
