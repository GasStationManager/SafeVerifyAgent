# Junk-value triage 3 — NSE @ f9e8bc5 (READ-ONLY)

Rule under test: flag only if denominator reaches a subterm on ONE side of the statement.

## 1. Euler/PacketPhysicalLowBounds.lean — 2 hits: C, C (both bounds; harmless)

* `Euler/PacketPhysicalLowBounds.lean:57` `shearTerm_norm_le` — CLAIMS a bound
  `‖shearTerm amp slope r w‖ ≤ (amp*(‖r‖*‖w‖))/δ`. Signature has `hamp : 0 ≤ amp`,
  `hslope : |slope| ≤ δ⁻¹` (:58) and NO `δ ≠ 0`.  **Class C.**
  At `δ = 0` the RHS is `.../0 = 0`; but the *hypothesis* also degenerates:
  `δ⁻¹ = 0` so `hslope` becomes `|slope| ≤ 0`, i.e. `slope = 0`, hence
  `shearTerm amp 0 r w = (amp*0) • rankOne … = 0` (def :16-17) and the LHS is
  ALSO 0. Statement collapses to `0 ≤ 0` — a bound, so nothing of value is lost.
  Callers exclude it anyway: `good_step_bounds` :141 `(hδ : 0 < δ)`, used at :154;
  `absolute_step_bounds` :173 `(hδ : 0 < δ)`, used at :186.

* `Euler/PacketPhysicalLowBounds.lean:65` `pressureTerm_norm_le` — CLAIMS a bound
  `‖pressureTerm amp slope M r w‖ ≤ 2*‖M‖*(amp*(‖r‖*‖w‖))/δ`. Same shape: only
  `hamp`, `hslope : |slope| ≤ δ⁻¹` (:66). **Class C.** At `δ = 0`, `hslope` forces
  `slope = 0`, and `pressureTerm` (def :19-20) has `slope` as a factor of its
  scalar, so LHS = 0; RHS = 0. Collapses to `0 ≤ 0`. Callers: :141/:155-158 and
  :173/:188-192, both with `0 < δ`.

NOTE (new FP kind, kind (iii)): here the denominator ALSO occurs in a hypothesis
(`|slope| ≤ δ⁻¹`) whose own degeneration pins the LHS to the same junk value. The
collapse is coordinated, not silent-in-one-direction. Worth adding to the tool.

## 2. Euler/PacketPressureFastHessian.lean — 2 hits (same theorem), both FALSE POSITIVES

* `Euler/PacketPressureFastHessian.lean:49` `fastHessianRemainder_norm_le` — CLAIMS a bound
  `‖fastHessianRemainder a k m Y J x‖ ≤ |k⁻¹| * (…)`. No `k ≠ 0` in the signature.
  **Class B (symmetric collapse; the ONE-SIDE rule filters it).**
  `k⁻¹` is the outer scalar of the definition (:19-23, `k⁻¹ • (…)`) and appears
  EXPLICITLY as the outer factor `|k⁻¹|` of the RHS (:52). At `k = 0` both sides are
  literally `0`, so the statement is `0 ≤ 0` and the inequality's shape is preserved
  by the same junk value on both sides — no asymmetric loss of content. It is a bound,
  not an exact value, so nothing was claimed there anyway.
  (The instrument reported this row twice: once as `denom k`, once as
  `denom k (via fastHessianRemainder)` — the same `k⁻¹` seen syntactically and
  through the definition. Dedupe those.)
  Caller also guards: `Euler/PacketPressureFastBounds.lean:28` `(hk : 0 < k)`, use at
  `PacketPressureFastBounds.lean:59-61` (`abs_of_pos (inv_pos.mpr hk)`).
  Note :25 `fastForce_hasFDerivAt` in the SAME file DOES carry `(hk : k ≠ 0)`, i.e. the
  author guards exactly where the identity would otherwise be exact — evidence the
  unguarded :49 is deliberate, not an oversight.

## 3. Euler/PacketScaledRay.lean — 2 hits (same theorem), both FALSE POSITIVES

* `Euler/PacketScaledRay.lean:14` `physicalTime_hasDerivAt` — CLAIMS the derivative of
  the time reparametrisation: `HasDerivAt (physicalTime t₀ a ε) (ε/a) τ`, where
  `physicalTime t₀ a ε τ = t₀ + (ε/a)*τ` (:12). **Class B (junk value is the TRUE value).**
  At `a = 0` the function becomes the CONSTANT `t₀ + 0*τ = t₀` and the claimed derivative
  becomes `ε/0 = 0`, which is the correct derivative of a constant. The theorem is true
  and non-vacuous for every `a`, including 0; nothing is lost because `ε/a` occurs both in
  the function and in the derivative slot (prompt FP kind (i), shared subterm).
  Both hit rows (`denom a` and `denom a (via physicalTime)`) are this one theorem.
  For contrast, the two real consumers in the same file DO carry `(ha : a ≠ 0)`:
  `scaledRay_hasDerivAt` :42 and `scaledRay_hasDerivWithinAt` :63 (needed by
  `scaledRayRate_algebra` :25, which is stated WITH `ha : a ≠ 0`).

## 4. NavierStokes/RadialModulation.lean — 2 hits, both FALSE POSITIVES (B)

* `NavierStokes/RadialModulation.lean:47` `modulatedE_contDiffAt` — CLAIMS smoothness:
  `ContDiffAt ℝ ∞ (uncurry (modulatedE n E A)) (X,η)` given `hE`, `hA`, `hX : X ≠ 0`.
  Denominator `n` enters via `modulatedE n E A X η = E X η * exp (A (phasePoint n X η) / n)` (:39-40).
  **Class B (no collapse to triviality).** At `n = 0`, `A(…)/0 = 0`, so the function becomes
  `E X η * exp 0 = E X η` and the conclusion becomes `ContDiffAt ℝ ∞ (uncurry E) (X,η)` — still a
  genuine, non-vacuous claim (and true from `hE`). The conclusion is a PREDICATE about a function,
  not an equation with `n` on one side; nothing degenerates into `0 = 0`.
* `NavierStokes/RadialModulation.lean:56` `modulatedU_contDiffAt` — same, with
  `modulatedU n U B X η = U X η + B (phasePoint n X η)/n` (:42-43); at `n = 0` it degenerates to
  `ContDiffAt ℝ ∞ (uncurry U) (X,η)`. **Class B.**
  Its caller `NavierStokes/ParametricModulation.lean:466-476` `realized_profiles_contDiffAt` also
  has no `n ≠ 0`, consistent with the guard being unnecessary here.
  Strong counter-evidence that the file's guard discipline is deliberate: every neighbouring
  theorem whose conclusion IS an exact derivative identity carries `hn : n ≠ 0` — :93, :106,
  :138, :154 — and the estimate lemmas carry `hn : 0 < n` (:169, :189).

