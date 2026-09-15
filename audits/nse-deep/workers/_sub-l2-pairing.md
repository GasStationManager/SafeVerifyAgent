# Worker report: L2 difference pairing (pressure + transport cancellation)

Repo: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5).
READ-ONLY. No `lake build` (no Mathlib on disk: `.lake/` absent, deps only in
`lake-manifest.json`). All claims below are from source text; every claim carries file:line.

## Scope

Read in full: `Euler/OrdinaryH3Energy.lean` (132 lines),
`Euler/OrdinaryEulerDifference.lean` (150), `Euler/OrdinaryEulerL2Stability.lean` (161),
`Euler/OrdinaryFieldAlgebra.lean` (130).
Read one level down (dependencies of the two cancellations):
`Euler/OrdinaryTransportCancellation.lean` (66), `Euler/OrdinaryWordConstraints.lean` (55),
`Euler/OrdinaryL2Integration.lean` (113), `Euler/OrdinaryH3Commutator.lean` (104),
`Euler/OrdinarySmoothWords.lean` (139), `Euler/LpSmoothField.lean` (125),
`Euler/MeanSolenoidalSpace.lean` (260), `Euler/OrdinaryPressureCancellation.lean` (120),
`Euler/MeanClassicalConstraints.lean` (51), `Euler/MeanSobolevBoundedField.lean` (125).
Read for the vacuity and non-circularity questions: `Euler/OrdinaryEulerUniqueness.lean`,
`Euler/OrdinaryGradientStability.lean`, `Euler/OrdinaryEulerGradientControl.lean`,
`Euler/OrdinaryEulerLocalExistence.lean`, `Euler/OrdinaryRegularizedFlow.lean`.

Two corrections to the brief:
* `differenceRhs_pairing` is at `Euler/OrdinaryH3Energy.lean:34`, not :33.
* `differenceRhs` is **not** in `OrdinaryEulerDifference.lean`; it is defined at
  `Euler/OrdinaryH3Energy.lean:25`. `OrdinaryEulerDifference.lean` only *uses* it
  (`differenceDerivative_eq`, :98).

## 1. Exact statements, and which lemma proves which cancellation

`differenceRhs` (Euler/OrdinaryH3Energy.lean:25-26):

    def differenceRhs (U W P : SmoothL2Field Space) : SmoothL2Field Space :=
      fieldNeg (addField (addField (advectionField (addField U W) W) (advectionField W U)) P)

Pointwise content, `differenceRhs_field` (H3Energy:28-32):
`(differenceRhs U W P).field x = -fderiv ℝ W.field x (U.field x + W.field x)
 - fderiv ℝ U.field x (W.field x) - P.field x`, i.e. `-(V·∇)W - (W·∇)U - ∇q` with `V = U+W`.
I re-derived this by hand against the true difference equation
`∂_t W = -(V·∇)V + (U·∇)U - ∇q = -(U·∇)W - (W·∇)V - ∇q`; the two expressions are
algebraically identical. **The sign convention and the pairing structure are correct.**
`advectionField A B` really is `(A·∇)B`: `advectionField_field` (OrdinaryFieldAlgebra.lean:118-128)
gives `(advectionField A B).field x = fderiv ℝ B.field x (A.field x)` — proved, not assumed.

`differenceRhs_pairing` (H3Energy:34-51), statement verbatim in substance:

    ⟪(wordField W w).toLp, (wordField (differenceRhs U W P) w).toLp⟫_ℝ
      = -⟪(transportCommutator (addField U W) W w).toLp, (wordField W w).toLp⟫_ℝ
        - ⟪(wordField (advectionField W U) w).toLp, (wordField W w).toLp⟫_ℝ

under `hdiv : ∀ x, divergence (addField U W).field x = 0`, `hW : W.toLp ∈ solenoidalSpace`,
`hP : P.toLp ∈ gradientSpace`, for any word `w : Fin n → Fin 3`.

Two terms are claimed to cancel; both cancellations are **proved**, not assumed:

* **Transport term** — `ht` (H3Energy:41-44). The word derivative of `(V·∇)W` is split by the
  definition of the commutator, `transportCommutator A B w :=
  fieldSub (wordField (advectionField A B) w) (advectionField A (wordField B w))`
  (Euler/OrdinaryH3Commutator.lean:25-26), and the *un-commuted* piece
  `⟪advectionField V (wordField W w), wordField W w⟫` is killed by
  **`advection_inner_zero`** (Euler/OrdinaryTransportCancellation.lean:42-64).
  That is the genuine skew-symmetry `⟪(V·∇)B, B⟫ = 0` for `div V = 0`. Its proof is real:
  coordinate split (`coordinateProduct`, FieldAlgebra:109), the 1-D pairing identity
  `scalar_transport_pair` (TransportCancellation:29-34) which is *integration by parts*
  via `field_directional_inner`, plus `divergence_eq_coordinate_sum` to make
  `∑_i ∂_i V_i = 0` (TransportCancellation:50-53). No compact support, no ad-hoc hypothesis.
* **Pressure term** — `hp` (H3Energy:45-47) via
  **`word_pressure_pairing_zero`** (Euler/OrdinaryWordConstraints.lean:49-53), which is
  `word_gradient` + `word_solenoidal` (WordConstraints:32-47, honest translation-orbit
  argument: every coordinate word derivative preserves membership in `gradientSpace` /
  `solenoidalSpace`) followed by
  **`pressure_pairing_zero`** (Euler/MeanSolenoidalSpace.lean:129-130), whose proof is
  literally `hu p hp` — because `solenoidalSpace := gradientSpace.orthogonal`
  (MeanSolenoidalSpace.lean:58). So this cancellation is *orthogonal decomposition by
  definition*, not integration by parts. That is legitimate but note where the real work
  sits: it sits in proving that an actual pressure force lies in `gradientSpace`
  (see §2/§3).

Integration by parts itself: `field_directional_inner` (Euler/OrdinaryL2Integration.lean:46-50)
`⟪∂_v A, B⟫ = -⟪A, ∂_v B⟫`, reduced to `field_directional_ibp` (:33-44), which calls the
Mathlib lemma `integral_bilinear_fderiv_right_eq_neg_left_of_integrable` with **only**
integrability of the three pairings plus everywhere-differentiability. **No compact support and
no explicit decay hypothesis** — the decay is supplied structurally by the `SmoothL2Field`
class (§3). I could not check that Mathlib lemma's exact statement (no Mathlib source on disk):
flagged UNCLEAR-external.

`differenceRhs_l2_bound` (Euler/OrdinaryEulerL2Stability.lean:27-44) is the `n = 0`
specialization: `differenceRhs_pairing ... (Fin.elim0 : Fin 0 → Fin 3)` (:32), then
`transportCommutator_zero` (H3Commutator:28-30) kills the commutator, leaving
`-⟪(W·∇)U, W⟫`, bounded by `advection_norm_gradient` (L2Stability:18-25) with the
*hypothesis* `hK : ∀ x, ‖fderiv ℝ U.field x‖ ≤ K`. This is the textbook estimate. Correct.

## Per-declaration findings

| # | Declaration (file:line) | Verdict | Note |
|---|---|---|---|
| 1 | `differenceRhs` H3Energy:25 | OK | matches the true difference equation (hand-checked) |
| 2 | `differenceRhs_field` H3Energy:28 | OK | `simp`+`abel`, unfolds real defs |
| 3 | `differenceRhs_pairing` H3Energy:34 | OK | both cancellations proved; see §1 |
| 4 | `advection_inner_zero` TransportCancellation:42 | OK | genuine skew-symmetry from IBP + `div = 0` |
| 5 | `word_pressure_pairing_zero` WordConstraints:49 | OK | reduces to orthogonality of the two submodules |
| 6 | `pressure_pairing_zero` MeanSolenoidalSpace:129 | OK-by-definition | `solenoidalSpace := gradientSpace.orthogonal` (:58); zero mathematical content here |
| 7 | `field_directional_inner` L2Integration:46 | UNCLEAR (external) | IBP with integrability only; Mathlib lemma not checkable offline |
| 8 | `differenceRhs_word_bound` H3Energy:53 | OK | 21+24=45, `2^n ≤ 8` for `n ≤ 3`, all arithmetic re-checked by hand |
| 9 | `energyProduction` / `difference_energy_bound` H3Energy:105/108 | SUSPICIOUS (honest but non-linear) | constant is `(M + √(wordEnergy 3 W))`, i.e. it **does** depend on the estimated difference; this is a quadratic/Riccati bound and yields **no** uniqueness by itself. `40 = 1+3+9+27`, `2*40*45 = 3600` ✓ |
| 10 | `differenceRhs_l2_bound` L2Stability:27 | OK | linear in `‖W‖²`; `K` bounds only the **reference** `U`, not `W` — not a tautology |
| 11 | `linear_stability_within` L2Stability:46 | OK | Mathlib Grönwall `le_gronwallBound_of_liminf_deriv_right_le`, ε = 0 |
| 12 | `Evolution` structure Difference:21-32 | UNCLEAR (assumption-carrying, expected) | see §2 |
| 13 | `differenceDerivative_eq` Difference:98 | OK | exact identity; I verified `-∇V(V)+∇U(U) = -∇W(V)-∇U(W)` by hand |
| 14 | `difference_time_law` Difference:111 | OK | subtraction of the two `time_law` fields; interior `Ioo` only |
| 15 | `energyDerivative_bound` Difference:132 | OK | `hdiv` for `U+W` discharged from `V.solenoidal` (:142) |
| 16 | `l2EnergyDerivative_bound` L2Stability:90 | OK | same discharge pattern (:100-105) |
| 17 | `l2_stability` / `l2_stability_of_h3` L2Stability:127/148 | OK | `K` from `tensorNorm 3 U` via a Sobolev embedding, derived (:154-158) |
| 18 | `velocityPath` L2Stability:61 + `velocityPath_apply` :64 | OK, **not vacuous** | see §5 |
| 19 | `Evolution.velocity_eq_of_initial` Uniqueness:24 | OK, notable | uniqueness with **no** extra size hypothesis; constant is `gradientIntegral`, a *derived* functional of `U` |

Verdict counts: **OK 14, OK-by-definition 1, UNCLEAR 3, SUSPICIOUS 1, KERNEL-RISK 0.**

## 2. Assumed vs derived: the `Evolution` fields (Euler/OrdinaryEulerDifference.lean:21-32)

| Field (line) | Kind | Comment |
|---|---|---|
| `velocity` :22 | data | `Icc 0 T → SmoothL2Field Space` |
| `pressureForce` :23 | data | the **force** `∇p`, not the scalar `p` |
| `velocity_continuous` :24 | ASSUMPTION | continuity in `t` of *every* L² jet `n`. Strong regularity, supplied by the producer |
| `pressure_continuous` :25 | ASSUMPTION | same for the pressure force |
| `solenoidal` :26 | ASSUMPTION | `(velocity t).toLp ∈ solenoidalSpace`. This is the divergence-free constraint |
| `gradient` :27 | ASSUMPTION | `(pressureForce t).toLp ∈ gradientSpace`. **This single field is exactly what makes the pressure term cancel** |
| `time_law` :28-32 | ASSUMPTION | pointwise `HasDerivAt` of `t ↦ velocity` equal to `-(u·∇)u - ∇p`, on the **open** `Ioo 0 T` only |

So: **the pressure cancellation is not derived inside the pairing lemma; it is imported from
the `Evolution.gradient` field** (plus `Evolution.solenoidal`), through
`gradientSpace.sub_mem` / `solenoidalSpace.sub_mem` (L2Stability:102-105).
This is not circular, because both fields are actually discharged where `Evolution`s are built:
`evolutionOfClassical` (Difference:34-54) discharges `solenoidal` by
`smooth_mem_solenoidal` (MeanSolenoidalSpace:187) from pointwise `div u = 0`, and `gradient`
by `gradient_mem` (Euler/OrdinaryPressureCancellation.lean:84-96) from
"`A = ∇p` pointwise, `p` smooth". `gradient_mem` is a real theorem: its engine
`gradient_mem_of_symmetric` (…:~40-82) shows the solenoidal part of a curl-free field is
harmonic and then **zero** by `field_zero_of_laplacian_zero`
(Euler/OrdinaryL2Integration.lean:72-111) — an L²-Liouville argument, not a hypothesis.
`regularizedEvolution` (Euler/OrdinaryEulerLocalExistence.lean:89-106) discharges it by
`pressureField_mem_gradient` (Euler/OrdinaryHelmholtzField.lean:74).

Is any field strong enough to trivialize L² stability or uniqueness? **No.**
* No field asserts an energy inequality, a Grönwall inequality, or any bound on `‖fderiv u‖`.
  The constant `K` is a *consumer* hypothesis (L2Stability:28, :91) and depends only on the
  reference `U`, never on the difference `W`. I looked specifically for the "constant that
  secretly depends on the solution being estimated" failure and did **not** find it in the L²
  chain.
* Best evidence of non-triviality: `Evolution.velocity_eq_of_initial`
  (Euler/OrdinaryEulerUniqueness.lean:24-30) needs **no** size hypothesis at all. Its constant
  is `U.gradientIntegral` (Euler/OrdinaryEulerGradientControl.lean:41), the time integral of
  `gradientNormPath` (:20-23), which is `‖finiteField (U.velocity t).derivative‖` — a sup-norm
  that is *constructed*, not assumed, by `finiteField`
  (Euler/MeanSobolevBoundedField.lean:104-113). So finiteness of the Grönwall constant is
  derived from the `SmoothL2Field` class itself. That is the honest, non-circular version.
* The one place where a constant *does* depend on the estimated object is the H³ bound
  `difference_energy_bound` (H3Energy:108-113): `3600·C·(M + √(wordEnergy 3 W))·wordEnergy 3 W`.
  The statement is honest (the dependence is visible), but **anyone reading this as "H³
  stability" is wrong**: it is a Riccati inequality, it gives no uniqueness and no global
  bound. Also note it needs `WordBound 4 M U` — H⁴ control of the reference to close an H³
  estimate (derivative loss on the `(W·∇)U` term, `source_advection_outer`, H3Energy:66).
  That makes the H³ estimate *not* self-contained. Flagging loudly.

## 3. `hdiv` / solenoidality placement, and decay

* `hdiv` is stated for `addField U W`, i.e. for `V = U + W`, the **other** solution
  (H3Energy:35, L2Stability:29). That is exactly the field which the transport operator
  advects with in `advectionField (addField U W) W`, so `advection_inner_zero` is applied to
  the right field. Correct placement. In the consumers it is discharged from `V.solenoidal`
  by `solenoidal_representative_divergence` (Difference:142, L2Stability:100,
  GradientStability:27), whose proof (Euler/MeanClassicalConstraints.lean:14-35) goes from
  weak orthogonality to pointwise `div = 0` by testing against compactly supported smooth
  `φ` (`weak_divergence_test`, MeanSolenoidalSpace:68-76, and
  `gradient_test_integration_by_parts`, :137-…) plus `ae_eq_zero_of_integral_contDiff_smul_eq_zero`
  and continuity. Genuine du Bois-Reymond, no shortcut.
* `hW ∈ solenoidalSpace` is used only for the pressure pairing, and it is the *difference*
  `W = V - U` that must be solenoidal — correct, since both are.
* **Decay / integrability**: not assumed lemma-by-lemma; it is built into the class.
  `structure SmoothL2Field` (Euler/LpSmoothField.lean:31-34) requires `field : Space → V`,
  `smooth : ContDiff ℝ ∞ field`, and `integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume`
  — i.e. **all** iterated derivatives in L². The IBP (`field_directional_ibp`,
  L2Integration:33-44) then needs no compact support: it consumes only
  `field_inner_integrable` (L2Integration:20-24), which follows from `MemLp … 2` by
  Cauchy-Schwarz. This is mathematically the right justification (`f, ∂f ∈ L¹ ⇒ ∫ ∂f = 0`),
  and it is honest. The price: `Evolution` describes only H^∞-type solutions; uniqueness
  proved here is uniqueness **within that very regular class**, not among weak solutions.
  Not a defect, but a scope limitation that a reader of the docstrings would miss.
* Residual external dependency: the exact hypotheses of the Mathlib lemma
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable` (called at L2Integration:36).
  Everything downstream of the two cancellations rests on it. Could not verify offline.

## 4. Vacuity: is `Evolution T hT` inhabited?

**Yes, and unconditionally so** — this is the good news, and it contradicts the "everything is
conditional" prior.
`Euler/OrdinaryEulerLocalExistence.lean:152-155`:

    theorem exists_local_evolution (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace) :
        ∃ (T : ℝ) (hT : 0 < T), ∃ U : Evolution T hT.le, U.velocity ⟨0,le_rfl,hT.le⟩ = A

built from `localEvolution` (:139-143) → `regularizedEvolution` (:89-106) → a limit of
regularized flows, whose existence comes from `SmoothingOperator.exists_smooth`
(Euler/OrdinaryRegularizedFlow.lean:75-…, a **theorem**, proved by a Duhamel/integral-equation
argument, not a structure field), with the concrete `regularizer n`
(Euler/OrdinaryRegularizer.lean:48) as a `def`. Additional constructors:
`evolutionOfClassical` (Difference:34), `restrictTime` (Euler/OrdinaryEulerRestriction.lean:18),
and a Cauchy-limit constructor (Euler/OrdinaryEulerCauchy.lean:100).
Caveat I did **not** discharge: I did not audit the interior of `exists_smooth`, the
`SmoothingOperator` fields, or the compactness/`smoothLimitData` chain. Non-vacuity of
`Evolution` therefore reduces to that chain, which is a real proof obligation and a good
target for another worker. But it is *not* an assumed structure field, and any
`A` that is solenoidal and in the class gives a nontrivial evolution — the theorems in this
audit are **not** vacuous.

## Kernel-risk

Scanned the 11 files listed under Scope with regexes for the whole threat list.

| pattern | count | file:line |
|---|---|---|
| `decide` / `native_decide` | **0** | — |
| numerals > 4 digits | **0** | largest literal in scope is `3600` (H3Energy:113/128), and `45`, `24`, `21`, `40`; all appear only inside `ring`/`norm_num`/`linarith` real-arithmetic steps, so the kernel sees small `ℝ`/`OfNat` literals, never big `Nat` GMP work |
| `.rec` / `recOn` / `Acc.rec` / `brecOn` (explicit) | **0** | — |
| `termination_by` / `decreasing_by` | **0** | — |
| `WellFounded` | **0** | — |
| `deriving` | **0** | — |
| `macro` / `elab` / `syntax` / `notation` / `macro_rules` | **0** | — |
| `set_option` | **0** | — |
| `axiom` / `sorry` / `unsafe` / `partial` | **0** | — |
| structural recursion | 4 | `wordField` OrdinarySmoothWords.lean:31-33 (structural on `ℕ` via `Fin.tail`, compiles to `Nat.rec`, no `termination_by`); inductions at OrdinarySmoothWords.lean:45,117, H3Commutator:80, LpSmoothField.lean:71. All plain `Nat` induction, depth-3 usage; no kernel-reduction hazard |
| structure eta / proof irrelevance | 1 | `field_ext` OrdinarySmoothWords.lean:25-29 (`cases A; cases B; cases h; rfl`). Safe: `SmoothL2Field` has exactly one data field plus two `Prop` fields (LpSmoothField.lean:31-34), so this is ordinary proof irrelevance, not eta abuse |
| `Fin.elim0` | 7 | L2Stability:32, :62, :71, :84; H3Commutator:72, :92, :102 |

**`Fin.elim0` vacuity check (asked specifically about L2Stability:32 and :62): NOT vacuous.**
The index type of a word is `Fin n → Fin 3`. At `n = 0` this type is **nonempty** (it has the
unique element `Fin.elim0`), so instantiating there is a specialization, not a quantification
over an empty domain. The concrete content is pinned down by
`@[simp] theorem wordField_zero (A) (w : Fin 0 → Fin 3) : wordField A w = A := rfl`
(Euler/OrdinarySmoothWords.lean:35-36) — proof is `rfl`, so the empty word is literally the
identity. Consequences:
* L2Stability:32-35 turns `differenceRhs_pairing` into a statement about `W` itself; the
  commutator drops out by `transportCommutator_zero` (H3Commutator:28-30, `wordField_zero`
  twice then `sub_self`), which is a *true* cancellation, not an empty-type artifact.
* L2Stability:62-66: `velocityPath_apply` proves `U.velocityPath t = (U.velocity t).toLp`,
  again by `wordField_zero`. So `velocityPath` is the honest L² velocity path.
* Similarly `l2EnergyPath` (:68-73) is genuinely `‖(difference).toLp‖²`, and
  `energyProduction` (H3Energy:105-106) sums `n ∈ range 4` over `Fin n → Fin 3` with
  `3^n` words, `1+3+9+27 = 40`, matching the `40` used at H3Energy:118.
No `Fin 3`/`Fin 0` trick makes any statement in scope vacuous.

## Escalations

1. **`difference_energy_bound` (H3Energy:108) is a Riccati bound, not an H³ stability
   estimate.** Its "constant" contains `√(wordEnergy 3 W)`, i.e. the estimated quantity, and
   it needs H⁴ control of the reference (`WordBound 4 M`) to close an H³ estimate. Anyone
   consuming it as linear H³ stability is misusing it. Recommend a follow-up worker check
   every consumer of `energyDerivative_bound` (Difference:132) and of the H³ chain
   (`OrdinaryEulerHigherEnergy`, `OrdinaryEulerContinuation`, `EulerFiniteLifespan`,
   `PacketStageContradiction`) for exactly that misuse. The L² chain does not have this
   defect.
2. **External Mathlib dependency, unverifiable offline:**
   `integral_bilinear_fderiv_right_eq_neg_left_of_integrable` (used at L2Integration:36,
   and also MeanCurlIntegration:41, R3CompactEnergy:111, R3/H3Comparison:59). The *whole*
   transport cancellation and the L²-Liouville step rest on it holding with
   integrability-only hypotheses. Verify its Mathlib statement at rev
   `85e3a25e006c35636f0e53b0e9296caca2685bc0` (v4.34.0-rc2).
3. **Non-vacuity is real but unaudited one level further:** `exists_local_evolution`
   (LocalExistence:152) depends on `SmoothingOperator.exists_smooth`
   (OrdinaryRegularizedFlow.lean:75) plus the `SmoothingOperator` structure
   (OrdinaryRegularizer.lean:48) and the `smoothLimitData` compactness chain. If a hidden
   assumption lives anywhere in this campaign, that chain — not the pairing lemma — is where
   to look.
4. **Scope caveat worth stating in any summary of the paper's claims:** `Evolution` is an
   H^∞-type class (`SmoothL2Field` requires *all* iterated derivatives in L²,
   LpSmoothField.lean:34). Uniqueness/stability proved here is within that class only. The
   docstrings ("no Sobolev regularity ... is postulated", OrdinarySmoothWords.lean:6-7) are
   misleading about this: the regularity is postulated, just packaged into the field type.

## Residue

* Did not read: interior of `exists_smooth`, `SmoothingOperator`, `smoothLimitData`,
  `pressureField`/`OrdinaryHelmholtzField`, `ordinaryWord_hasDerivWithinAt` and
  `wordEnergy_hasDerivWithinAt` (the interior-derivative → one-sided-endpoint-derivative
  upgrade used at Difference:126-130 and L2Stability:78-88), `variable_linear_stability`,
  `EulerSmoothSobolev.real_smooth_fderiv_le_H3`, `source_advection_outer`,
  `transportCommutator_bound`, `h3ProductConstant`.
* Could not check any `simp`/`abel`/`ring`/`abel_nf`/`nlinarith` step actually closes its
  goal (no build). Load-bearing closers in scope: H3Energy:32 (`abel`), :51 (`ring`),
  Difference:109 (`abel_nf`), L2Stability:134 (`nlinarith`), GradientStability:61 (`nlinarith`).
* `Evolution.time_law` only constrains `Ioo 0 T`; the endpoint one-sided derivatives claimed
  by the file docstring (L2Stability:4-7) are produced by the unread
  `ordinaryWord_hasDerivWithinAt`. That upgrade is the one remaining place in the L² chain
  where I would look for an unjustified step.
