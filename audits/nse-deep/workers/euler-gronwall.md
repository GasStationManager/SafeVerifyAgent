# Worker report: the Euler ENERGY / GRÖNWALL core (L² stability, higher-order energy, uniqueness consumer)

Repo audited (READ-ONLY): `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`
(clone of `openai/NavierStokesAndEuler`). **Nothing under `NSE/` was modified.**
No Mathlib build on this box (disk full), and **no Mathlib source is vendored** (`ls NSE/.lake`
is empty) — so this is source-level reading of the repo only (grep + line-by-line).
Mathlib lemma *statements* could not be re-read on this box; see `## Residue`.

Predecessors skimmed as instructed: `workers/euler-interpolation.md`,
`workers/euler-spine-uniqueness.md`. **This report closes
`euler-interpolation.md` Escalation 1** (are the Grönwall constants uniform in the
approximation index `k`, and is the L²-stability exponent driven by a quantity the H³ bound
controls?) and **`euler-spine-uniqueness.md` Escalation 3** (the interior→endpoint derivative
upgrade feeding `velocity_eq_of_initial`).

**Headline: I found no circularity, no non-uniform constant, and no vacuity in this layer.**
The three estimates are the textbook ones, with explicit field-independent constants, applied
on the closed interval `Icc 0 T` of a *given* `Evolution T hT` — the blowup time never enters
here, because `T` is a parameter of the solution object, not a supremum of a lifespan. The
kernel-risk surface of this layer is essentially empty (zero `decide`, zero literal above
`3600`, zero `termination_by`/`WellFounded`, zero metaprogramming). The two places where I
would still send an expert are listed in `## Escalations`, and neither is a defect I can
demonstrate: they are (1) the *growth* of `tameEnergyConstant m ~ 6^m`, which is honest but
must be compatible with how the caller uses it, and (2) three Mathlib lemma signatures I
cannot re-read here.

---

## Scope

Assigned files, read **in full, line by line**:

| file | lines | theorem | def | total decls | read |
|---|---|---|---|---|---|
| `Euler/OrdinaryEulerL2Stability.lean` | 161 | 10 | 3 | 13 | full |
| `Euler/OrdinaryEulerHigherEnergy.lean` | 110 | 11 | 3 | 14 | full (note: the file is `OrdinaryEulerHigherEnergy.lean`; the brief's `Euler/HigherEnergy.lean` does not exist, and the brief's line hints `:64-70`, `:101` match this file exactly) |
| `Euler/OrdinaryEulerUniqueness.lean` | 47 | 4 | 0 | 4 | full |

Dependency files chased and read **in full** (the scope questions cannot be answered without
them; all counts from `audits/nse-deep/CONE.csv`):

| file | lines | decls | read |
|---|---|---|---|
| `Euler/OrdinaryVariableGronwall.lean` | 55 | 1 | full |
| `Euler/OrdinaryGradientStability.lean` | 74 | 4 | full |
| `Euler/OrdinaryEulerGradientControl.lean` | 143 | 16 | full |
| `Euler/OrdinaryEulerDifference.lean` | 150 | 13 | full |
| `Euler/OrdinaryWordTime.lean` | 99 | 6 | full |
| `Euler/SmoothFieldSobolevTime.lean` | 113 | 8 | full |
| `Euler/SeparatingTimeDerivative.lean` | 68 | 3 | full |
| `Euler/OrdinaryTameEnergy.lean` | 146 | (read `:55–146`) | decisive region |
| `Euler/OrdinaryH3Energy.lean` | 132 | (read `:1–60`) | decisive region |
| `Euler/OrdinaryTransportCancellation.lean` | (read `:1–60`) | | decisive region |
| `Euler/OrdinarySmoothWords.lean` | 139 | (read `:60–139`) | decisive region |
| `Euler/OrdinaryH3Norms.lean` | 57 | 8 | full |
| `Euler/OrdinaryWordBounds.lean` | 97 | (read `:25–60`) | decisive region |
| `Euler/OrdinaryH3Products.lean` | (read `:1–40`) | | decisive region |
| `Euler/MeanSobolevBoundedField.lean` | 125 | (read full) | full |
| `Euler/ContinuousTimeIntegral.lean` | 134 | (read `:1–80`) | decisive region |
| `Euler/VolterraConvolution.lean` | 147 | (read `:15–35`) | decisive region |
| `Euler/OrdinaryEulerCauchy.lean` | 123 | (read `:1–100`) | consumer, to close Escalation 1 |
| `Euler/OrdinaryEulerEndpoint.lean` / `Euler/ComparatorEvolutionIdentification.lean` | | (read the consumer sites `:60–105` / `:95–130`) | consumers of uniqueness |

Skimmed only (not audited): `Euler/EulerProof.lean` regions `8215–8250` and `8360–8400`
(`smoothEmbeddingConstant`, `real_smooth_fderiv_le_H3`) — statements read, proofs skimmed.

Two READ-ONLY sub-auditors were run in parallel on the two deepest dependencies
(`Euler/OrdinaryTameEnergy.lean`, and `differenceRhs_pairing` + the `Evolution` fields);
their reports land at `workers/_sub-tame-energy.md` and `workers/_sub-l2-pairing.md`. I
derived the answers below independently *before* their reports, so nothing here depends on
them; see `## Cross-checks delegated`.

---

## A. The three estimates, stated exactly

### A1. L² stability of the difference of two Euler solutions

`Evolution.l2_energy_bound` (`Euler/OrdinaryEulerL2Stability.lean:107`) and its square root
`Evolution.l2_stability` (`:127`):

> for `U V : Evolution T hT`, `K : ℝ` with `hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K`,
> and **every** `t : Icc 0 T`:
> `‖(U.difference V t).toLp‖ ≤ ‖(U.difference V 0).toLp‖ * Real.exp (K*t)`.

Controlled quantity: `X t = ‖(V.velocity t - U.velocity t)‖²_{L²(ℝ³)}` — the *L²* norm of the
difference of the two velocity fields (`difference` = `fieldSub (V.velocity t) (U.velocity t)`,
`Euler/OrdinaryEulerDifference.lean:81`; `l2EnergyPath` = its squared L² norm,
`OrdinaryEulerL2Stability.lean:68`).

Interval: the **closed** `Icc 0 T`, where `T` is the parameter of the `Evolution T hT` record
(`Euler/OrdinaryEulerDifference.lean:21`). **The blowup time is never reached**: an
`Evolution T hT` is a solution *given on* `[0,T]`, whose `time_law` (`:28`) holds on the open
`Ioo 0 T`; there is no `⨆`/`sSup` of a lifespan anywhere in this layer, and no limit `t → T⁻`.
The estimate does hold *at* `t = T`, but only because the energy path is continuous on the
closed interval and the Grönwall lemma is the closed-interval one (see B1).

The variable-coefficient version actually used downstream —
`Evolution.l2_stability_gradientIntegral` (`Euler/OrdinaryGradientStability.lean:54`) — has
**no hypothesis at all**:

> `‖(U.difference V t).toLp‖ ≤ ‖(U.difference V 0).toLp‖ * Real.exp (U.gradientIntegral t)`,
> where `U.gradientIntegral t = ∫₀ᵗ ‖∇u(s,·)‖_{L∞} ds` (`Euler/OrdinaryEulerGradientControl.lean:41`,
> `gradientNormPath` `:20`).

### A2. Higher-order (integer Sobolev) energy propagation

`Evolution.integer_energy_bound` (`Euler/OrdinaryEulerHigherEnergy.lean:64`), and the
`T`-uniform form `integer_energy_uniform` (`:84`) / `higher_energy_of_h3` (`:101`):

> for `m ≥ 3` (`hm : 3 ≤ m`), `M` with `hM : ∀ t, WordBound 3 M (U.velocity t)` (`:101` instead
> takes `hM : ∀ t, tensorNorm 3 (U.velocity t) ≤ M`), and every `t : Icc 0 T`:
> `wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity 0) * Real.exp (tameEnergyConstant m * M * t)`
> (resp. `... * Real.exp (tameEnergyConstant m * M * T)`).

Controlled quantity: `wordEnergy m A = ∑_{n≤m} ∑_{w : Fin n → Fin 3} ‖∂^w A‖²_{L²}`
(`Euler/OrdinarySmoothWords.lean:94`) — the genuine `Hᵐ` energy written over coordinate
"words" (all `3ⁿ` axis-derivative multi-indices of each length `n ≤ m`). Same closed interval
`Icc 0 T`, same `T`. Docstring claim "*no order-dependent shortening of time*"
(`OrdinaryEulerHigherEnergy.lean:4-6`) is **borne out by the statement**: the same `T` appears
for every `m`; only the *constant* `tameEnergyConstant m` depends on `m`.

### A3. The uniqueness consumer

`Evolution.velocity_eq_of_initial` (`Euler/OrdinaryEulerUniqueness.lean:24`):

> `U V : Evolution T hT`, `hinit : (V.velocity 0).toLp = (U.velocity 0).toLp` ⟹
> `∀ t : Icc 0 T, V.velocity t = U.velocity t` (equality of `SmoothL2Field`s, i.e. of the
> actual smooth fields, not merely a.e.).

and `pressure_eq_of_initial` (`:40`) upgrades it to the pressure force, for `0 < T`.

---

## B. Walking the proofs: mechanism, and where the constant comes from

### B1. The Grönwall steps themselves

* `linear_stability_within` (`Euler/OrdinaryEulerL2Stability.lean:46`) is a thin,
  **honest** wrapper of Mathlib's `le_gronwallBound_of_liminf_deriv_right_le` with `ε := 0`
  and `δ := X 0` (`:51-55`). The `liminf`-slope hypothesis is produced from the *actual*
  one-sided derivative: `(hder t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)` then
  `.liminf_right_slope_le` (`:52-53`). The final `simpa only [gronwallBound_ε0, sub_zero]`
  (`:55`) is what turns `gronwallBound δ K 0 (t-0)` into `X 0 * exp (C*t)`. Hypotheses are
  exactly: continuity on the **closed** `Icc 0 T`, one-sided derivative on `Ico 0 T`,
  differential inequality on `Ico 0 T`. Verdict OK. No hypothesis is dead and none is
  vacuous: with `Ico 0 T` empty (`T = 0`) the conclusion degenerates to `X 0 ≤ X 0`, which is
  true and harmless.
* `variable_linear_stability` (`Euler/OrdinaryVariableGronwall.lean:14`) is the
  integrating-factor argument done by hand and **correctly**: `Y r = X r * exp (-C * I r)`
  with `I = realIntegral T hT K` (`:21-23`), `Y' ≤ 0*Y` (`:38-42`, from the hypothesis
  `X' ≤ C*K(t)*X` and `exp > 0`), then `linear_stability_within Y Y' 0 T` (`:43`), then
  multiply the factor back (`:47-53`). `I 0 = 0` is `intervalIntegral.integral_same` (`:44`).
  `I` is differentiable *everywhere* because `K` is a continuous path and
  `realIntegral_hasDerivAt` (`Euler/ContinuousTimeIntegral.lean:57`) is FTC-1 for a continuous
  integrand (`:60`). Verdict OK.

### B2. Where the nonlinear term is estimated — L² case

This is the crux of A1, and it is the classical argument, term by term:

1. `d/dt ‖w‖² = 2⟪w, ẇ⟫` is *proved*, not postulated:
   `l2Energy_hasDerivWithinAt` (`OrdinaryEulerL2Stability.lean:78`) `= (…).norm_sq` applied to
   the strong L² time derivative of the difference path (`:81-84`).
2. `ẇ = differenceRhs U w q` (`Evolution.differenceDerivative_eq`,
   `Euler/OrdinaryEulerDifference.lean:98`), where
   `differenceRhs U W P = -[(U+W)·∇]W - (W·∇)U - P` (`Euler/OrdinaryH3Energy.lean:25,28`).
3. The pairing identity `differenceRhs_pairing` (`Euler/OrdinaryH3Energy.lean:34`) kills two
   of the three terms:
   * the **full transport term** `⟪w, ((U+W)·∇)w⟫ = 0` by `advection_inner_zero`
     (`Euler/OrdinaryTransportCancellation.lean:42`), which is a genuine integration by parts
     using **only** `divergence (U+W) = 0` — and which needs **no decay hypothesis** because
     it is done through `field_directional_inner` / `scalar_transport_pair`
     (`OrdinaryTransportCancellation.lean:29-34`), i.e. through L² translation unitarity of
     the *actual* L² objects, not through a boundary term on a large ball;
   * the **pressure term** `⟪w, ∇q⟫ = 0` by `word_pressure_pairing_zero`
     (`Euler/OrdinaryWordConstraints.lean:48`), i.e. orthogonality of `solenoidalSpace` and
     `gradientSpace`.
4. What is left is exactly `-⟪(w·∇)U, w⟫`, and it is bounded by Cauchy–Schwarz plus the
   **pointwise operator-norm bound on the reference gradient**:
   `advection_norm_gradient` (`OrdinaryEulerL2Stability.lean:18`) gives
   `‖(w·∇)U‖_{L²} ≤ K‖w‖_{L²}` from `hK : ∀ x, ‖fderiv ℝ U.field x‖ ≤ K`, via
   `Lp.norm_le_mul_norm_of_ae_le_mul` and `le_opNorm` (`:21-25`). Hence
   `2⟪w, differenceRhs⟫ ≤ 2K‖w‖²` (`differenceRhs_l2_bound`, `:27-44`).

   **No Sobolev embedding and no product estimate is used in the L² step at all** — only
   Cauchy–Schwarz and the operator norm. The embedding appears only when a caller wants to
   *produce* `K` from an H³ bound (`l2_stability_of_h3`, `:148`, and `gradient_le_h3`,
   `Euler/OrdinaryEulerCauchy.lean:41`), and there it is `real_smooth_fderiv_le_H3`
   (`Euler/EulerProof.lean:8375`): `‖∇f‖_{L∞} ≤ 9·smoothEmbeddingConstant·‖f‖_{H³}` on ℝ³,
   i.e. `H³ ↪ C¹` in dimension 3 (exponent 3 > 3/2 + 1, correct).

   **Uniformity of the constant.** `K` bounds `∇U` — the *reference* solution — while the
   estimated quantity is `‖V - U‖`. The inequality is linear in the estimated quantity, so it
   is **not** a tautology: nothing on the right depends on `‖V-U‖`. I specifically hunted for
   the failure mode "constant secretly containing the estimated norm" and it is absent here.
   Contrast `Evolution.energyDerivative_bound` (`Euler/OrdinaryEulerDifference.lean:132`),
   which *does* have `(M + Real.sqrt (U.energyPath V t))` on the right — that one is a
   quadratic (H³-difference) estimate and is **not** what the Grönwall chain in my scope uses;
   the L² chain uses `l2EnergyDerivative_bound` (`OrdinaryEulerL2Stability.lean:90`), which is
   strictly linear. Flagging the distinction because a reader could easily conflate them.
   In the version actually consumed (`l2_stability_gradientIntegral`) the coefficient is the
   *measured* quantity `‖∇u(t)‖_{L∞}` itself — a path, not a constant — which is the sharpest
   honest form.

### B3. Where the nonlinear term is estimated — higher-order case

`integerEnergyDerivative_bound` (`OrdinaryEulerHigherEnergy.lean:56`) delegates everything to
`integer_energy_tame` (`Euler/OrdinaryTameEnergy.lean:123`), which I read:

* the production term is `integerEnergyProduction m A Q = 2∑_{n≤m}∑_w ⟪∂^w A, ∂^w Q⟫`
  (`OrdinaryTameEnergy.lean:93`) — literally the `d/dt` of `wordEnergy m` (compare
  `wordEnergy_hasDerivWithinAt`, `Euler/OrdinaryWordTime.lean:87-90`, whose derivative value is
  the same double sum times 2; `integerEnergy_hasDerivWithinAt`
  (`OrdinaryEulerHigherEnergy.lean:48`) is what ties them);
* per word, `eulerRhs_pairing` (`OrdinaryTameEnergy.lean:70`) again kills the pressure term
  (`word_pressure_pairing_zero`) and the *pure* transport term (`advection_inner_zero`),
  leaving **only the commutator** `[∂^w, u·∇]u` (`transportCommutator`);
* the commutator is estimated by `tame_transportCommutator`
  (`OrdinaryTameEnergy.lean:53-59`): `‖[∂^w, u·∇]u‖_{L²} ≤ 3(2ⁿ-1)·h3ProductConstant·M·N`
  with `M` a `WordBound 3` (the **low** norm) and `N` a `WordBound m` (the **high** norm).
  This is the classical tame/Moser structure: low norm × high norm, one derivative never
  landing on the high factor. In `eulerRhs_word_tame` (`:97`) `N` is instantiated at
  `X = √(wordEnergy m A)` (`:103-105`), giving `≤ 3·2ⁿ·C·M·E_m` per word, and summing
  `3ⁿ` words of each length `n ≤ m` gives the `6ⁿ` sum (`:127-144`).
* **`tameEnergyConstant m = 6·h3ProductConstant·∑_{n≤m} 6ⁿ`** (`OrdinaryTameEnergy.lean:86`).
  `h3ProductConstant = 1 + 13·smoothEmbeddingConstant + 4(1+3·sobolevConstant)²`
  (`Euler/OrdinaryH3Products.lean:16`) — a **closed form in two fixed embedding constants**,
  with no field, no `M`, no `T`, no solution anywhere in it. So the constant is genuinely
  uniform over solutions; it depends only on `m`. **I could not break this.**
* Direction of the estimate: the constant multiplies `M` = the **H³/word-3** norm of `U`,
  while the controlled quantity is the **Hᵐ** energy of the *same* `U`. That is the standard
  "low norm controls high norm" a-priori estimate, not circularity: the right-hand side never
  contains `wordEnergy m` in the *coefficient*, only linearly as the estimated quantity.

  Honest caveat, not a defect: `tameEnergyConstant m ≈ 6^{m+1}/5·h3ProductConstant`, so the
  bound at order `m` is `E_m(0)·exp(C·6^m·M·T)` — doubly bad in `m`. That is fine for the
  consumer, which needs *one* constant per order `q` (`all_order_bounds_of_h3`,
  `Euler/OrdinaryEulerCauchy.lean:70-91`), and never a bound uniform in `q`. See Escalation 1.

### B4. Closing `euler-interpolation.md` Escalation 1 (uniformity in `k`)

At the consumer, `cauchyPath_of_initial` (`Euler/OrdinaryEulerCauchy.lean:50`) sets
`K := (9*smoothEmbeddingConstant)*M` (`:54`) where `hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M`
is the *k-independent* hypothesis; `hK` (`:57-58`) holds for every `k` with that same `K`, and
the Cauchy estimate uses the single factor `exp (K*T)` (`:61-68`). Likewise
`all_order_bounds_of_h3` (`:70`) exhibits, for each `q ≥ 3`, the explicit `k`-free constant
`wordCount q·√(wordCount q·R²·exp (tameEnergyConstant q·M·T))` (`:78`). **So: yes, the
constants are uniform in `k`, they are finite for the actual `T`, and the L²-stability
exponent is driven by `‖∇u‖_{L∞}`, which `real_smooth_fderiv_le_H3` genuinely controls by the
H³ bound `M`.** Escalation 1 of `euler-interpolation.md` is answered affirmatively, at
`Euler/OrdinaryEulerCauchy.lean:54` and `:78`.

---

## C. Hypotheses: assumed vs derived

| hypothesis | where it enters | assumed or derived |
|---|---|---|
| continuity of **all** spatial L² jets of the velocity in time | `Evolution.velocity_continuous` (`Euler/OrdinaryEulerDifference.lean:24`) | **ASSUMED** — a field of the solution class. This is the one substantive regularity assumption of the whole layer. It is what makes `sobolevPath` a `C(K, SobolevSpace 1 q)` and hence what makes every derivative statement below possible. Discharged for the constructed solutions elsewhere (`evolutionOfClassical` `:34`, `limitEvolutionOfH3`, `restrictTime`, `shiftTime`) — outside my scope. |
| same for the pressure force | `Evolution.pressure_continuous` (`:25`) | **ASSUMED** (same status). |
| continuity of the energy path on `Icc 0 T` (needed by Grönwall) | `l2EnergyPath` (`OrdinaryEulerL2Stability.lean:68-73`), `integerEnergyPath` (`OrdinaryEulerHigherEnergy.lean:36`) | **DERIVED** from the above, via `wordEnergy_continuous` (`Euler/OrdinaryWordTime.lean:58`) and `ordinaryWordPath` continuity. Not an extra hypothesis. |
| differentiability of the energy on `Ico 0 T`, **including the endpoint `t = 0`** | `l2Energy_hasDerivWithinAt` (`:78`), `integerEnergy_hasDerivWithinAt` (`OrdinaryEulerHigherEnergy.lean:48`) | **DERIVED.** Chain: `Evolution.time_law` (pointwise-in-`x` `HasDerivAt` on the **open** `Ioo 0 T`, `Euler/OrdinaryEulerDifference.lean:28`) → `EulerSeparatingTimeDerivative.hasDerivWithinAt` (`Euler/SeparatingTimeDerivative.lean:49`) → `sobolevPath_hasDerivWithinAt` (`Euler/SmoothFieldSobolevTime.lean:96`) → `ordinaryWord_hasDerivWithinAt` (`Euler/OrdinaryWordTime.lean:78`) → `.norm_sq`. **This closes `euler-spine-uniqueness.md` Escalation 3, and the mechanism is better than an MVT argument:** `eq_initial_add_integral` (`SeparatingTimeDerivative.lean:24`) *reconstructs the Bochner primitive* `f t = f 0 + ∫₀ᵗ g` by testing with the separating family and applying `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` on the interior (`:36-42`), and then the endpoint derivative is FTC-1 for a continuous integrand (`:53`). No pointwise→strong convergence step, no MVT, no one-sided subtlety. The separating family is the point-evaluation family `observation q hq x` (`Euler/SmoothFieldSobolevTime.lean:52`) and its injectivity is *proved* (`observation_injective`, `:68`) from a.e.-representative uniqueness. Verdict OK. |
| integrability of the Grönwall coefficient `‖∇u(t)‖_{L∞}` on `[0,t]` | `gradientIntegral` (`Euler/OrdinaryEulerGradientControl.lean:41`) | **DERIVED** — `gradientNormPath` is a `C(Icc 0 T, ℝ)` (`:20`), so `intervalIntegrable` on a compact interval is automatic. |
| finiteness of `sup_x ‖∇u(t,x)‖` | `gradientNormPath` (`:20`) | **DERIVED, and this is the subtle one.** It is `‖finiteField (U.velocity t).derivative‖`, the norm of a *bounded continuous function* `Space →ᵇ V` (`Euler/MeanSobolevBoundedField.lean:104`), built by finite-coordinate reconstruction from `spaceField` (`:52`), which is the image of the **genuine H³→L∞ Sobolev embedding** `sobolevMap` (`:49`) with explicit constant `sobolevEmbeddingConstant 1 3` (`:26-35`). Crucially `finiteField_apply` (`:108`) and `spaceField_apply` (`:55`) prove the bounded function is *equal to the actual field* **unconditionally** — so there is no junk-value fallback (`if bounded then … else 0`) hiding in the definition. Hence `pointwise_gradient_le` (`Euler/OrdinaryEulerGradientControl.lean:37`) is a real bound and `gradientNormPath t` is a real finite supremum. This is exactly the shape of trick I was told to hunt, and it is **not** present. |
| `divergence (U + w) = 0`, `w ∈ solenoidalSpace`, `q ∈ gradientSpace` (needed for the two cancellations) | `l2EnergyDerivative_bound` (`OrdinaryEulerL2Stability.lean:95-105`), `l2EnergyDerivative_gradient` (`OrdinaryGradientStability.lean:22-32`), `integerEnergyDerivative_bound` (`OrdinaryEulerHigherEnergy.lean:60-62`) | **DERIVED** from the class fields `solenoidal`/`gradient` (`Euler/OrdinaryEulerDifference.lean:26-27`) via `solenoidal_representative_divergence` and `solenoidalSpace.sub_mem`/`gradientSpace.sub_mem`. Not assumed on top. |
| `MemLp` of jets up to order 3, smoothness (for the embedding `real_smooth_fderiv_le_H3`) | `l2_stability_of_h3` (`OrdinaryEulerL2Stability.lean:154-156`), `gradient_le_h3` (`Euler/OrdinaryEulerCauchy.lean:44-45`) | **DERIVED** from the `SmoothL2Field` structure fields `smooth`/`integrable` (`Euler/LpSmoothField.lean:31-34`). |
| **no assumed energy (in)equality anywhere** | — | Confirmed: I grepped my scope for any hypothesis of the form `… ≤ …` on the energy or its derivative being *taken as input*; the only differential inequalities are the *conclusions* of `l2EnergyDerivative_bound`/`integerEnergyDerivative_bound`/`l2EnergyDerivative_gradient`, each proved from the pairing lemmas. The docstrings' claim "no postulated energy differential inequality" (`OrdinaryEulerHigherEnergy.lean:5-6`, `OrdinaryEulerUniqueness.lean:6`) is, unusually, accurate. |

---

## D. The uniqueness consumer

`velocity_eq_of_initial` (`Euler/OrdinaryEulerUniqueness.lean:24`):

* **Direction.** `hinit` says the two initial *data* agree in L² (`:25`); the conclusion says
  the two *solutions* agree at every time (`:26`). Same data ⟹ same solution. Correct
  direction; nothing is being run backwards.
* **Mechanism.** It instantiates `l2_stability_gradientIntegral` (`:27`), then
  `simp only [difference, toLp_fieldSub, hinit, sub_self, norm_zero, zero_mul]` (`:28`)
  collapses the right-hand side to `0`, so `‖V.velocity t - U.velocity t‖_{L²} ≤ 0`, hence
  `= 0` by `le_antisymm` with `norm_nonneg` (`:30`), hence the fields agree a.e., hence
  everywhere by continuity (`smoothField_eq_of_toLp_eq`, `:15-18`, using
  `Measure.eq_of_ae_eq` with both `.smooth.continuous`). Verdict OK — and note the upgrade
  from "a.e. equal" to "equal" is *proved*, not glossed.
* **Which estimate it uses — worth stating loudly.** It uses the **hypothesis-free**
  `l2_stability_gradientIntegral` (`Euler/OrdinaryGradientStability.lean:54`), **not** the
  `K`-uniform `l2_stability` (`OrdinaryEulerL2Stability.lean:127`) and **not**
  `l2_stability_of_h3` (`:148`). This is the strongest arrangement available: no gradient
  bound `K`, no H³ bound `M`, no positivity of `T`, no extra regularity is required —
  uniqueness holds for **any** two members of the bundled class on `[0,T]`, because
  `gradientIntegral` is automatically finite (see C, row 6). So the consumer does *not*
  narrow the class.
* **Class.** The class is the **bundled `Evolution T hT`** record itself
  (`Euler/OrdinaryEulerDifference.lean:21`), not a narrower ad-hoc predicate. Both arguments
  are arbitrary `Evolution T hT`. The real content of "which class" therefore sits entirely in
  the six fields of that record (velocity/pressureForce + jet-continuity of both + solenoidal
  + gradient + `time_law` on `Ioo 0 T`). Two observations:
  * the class is *not* empty-by-construction: `evolutionOfClassical`
    (`Euler/OrdinaryEulerDifference.lean:34`) builds one from a classical solution, and
    `limitEvolutionOfH3` (`Euler/OrdinaryEulerCauchy.lean:97`) builds one as a limit;
  * the consumers use it in the right way: `endpoint_matches_partial`
    (`Euler/OrdinaryEulerEndpoint.lean:75-87`) applies it to `W.restrictTime …` vs `U`, and
    `ComparatorEvolutionIdentification.lean:114` applies it to `W.restrictTime` vs
    `U.shiftTime` — i.e. to genuine `Evolution`s obtained by restriction/translation, both
    with `hinit` discharged by an *equality of fields* (`:106-113`). No circular use of the
    conclusion to build one of the inputs.
* `pressure_eq_of_initial` (`:40`) needs `0 < T`, inherited from `pressure_eq_projected`
  (`:32`), which identifies `U.pressureForce t` with the Leray projection
  `pressureField (U.velocity t)` from `derivative_toLp_projected`. Its `hpos` is a real
  hypothesis (at `T = 0` the interior `Ioo 0 T` is empty and nothing pins the pressure) —
  honestly carried, not hidden.

---

## E. Kernel-risk assessment

Machine census over the 11 files I read most closely (`OrdinaryEulerL2Stability`,
`OrdinaryEulerHigherEnergy`, `OrdinaryEulerUniqueness`, `OrdinaryVariableGronwall`,
`OrdinaryEulerGradientControl`, `OrdinaryGradientStability`, `OrdinaryWordTime`,
`SeparatingTimeDerivative`, `OrdinaryEulerDifference`, `OrdinaryH3Norms`,
`OrdinarySmoothWords`):

| pattern | count | sites |
|---|---|---|
| `decide` / `native_decide` / `Decidable` mention | **0** | — |
| `axiom` / `sorry` / `unsafe` / `partial` | **0** | — |
| `macro` / `elab` / `syntax` / `notation` / `set_option` | **0** | — |
| `termination_by` / `WellFounded` / `Acc.rec` | **0** | — |
| explicit `.rec` / `.recOn` / `.brecOn` | **0** | — |
| `deriving` | **0** | — |
| numeral with ≥5 digits | **0** | — |
| numerals with 2–4 digits | 4 | `OrdinaryEulerDifference.lean:134` (`3600`), `OrdinaryH3Norms.lean:27,34` (`40`), `:38` (`40`) |
| `norm_num` | 7 | `OrdinaryEulerL2Stability.lean:38,40,43,158`, `OrdinaryWordTime.lean:19`, `OrdinaryH3Norms.lean:31,47` |
| `omega` | 6 | `OrdinaryEulerHigherEnergy.lean:25`, `OrdinaryH3Norms.lean:24,30,46`, `OrdinarySmoothWords.lean:107,123` |
| bare `rfl` | 5 | `OrdinaryEulerHigherEnergy.lean:26`, `OrdinaryEulerGradientControl.lean:35`, `OrdinaryWordTime.lean:43`, `OrdinarySmoothWords.lean:29,36` |
| `induction` (⇒ `Nat.rec`) | 2 | `OrdinarySmoothWords.lean:45,117` |
| `Fin.elim0` | 4 | `OrdinaryEulerL2Stability.lean:32,62,71,84` |

**Vector (2) — Nat/GMP numeral work the kernel must redo.** Essentially nil. The largest
literal anywhere in my scope is `3600` (`OrdinaryEulerDifference.lean:134`) and it appears in
a *statement*, not in a computation the kernel must evaluate. The only arithmetic the kernel
actually performs is:
* `norm_num` on trivial sign goals like `(0:ℝ) ≤ 2` / `0 ≤ 9`
  (`OrdinaryEulerL2Stability.lean:38,40,43,158`) — one-step numeral comparisons;
* `norm_num [sum_range_succ]` on `∑_{n<4} 3ⁿ·M = 40·M` and
  `∑_{n<4} ∑_{w:Fin n→Fin 3} c = 40·c` (`OrdinaryH3Norms.lean:31,47`, and the analogous
  `Euler/OrdinaryEulerCauchy.lean:25-29`). These force `Fintype.card (Fin n → Fin 3) = 3ⁿ`
  for `n = 0,1,2,3`, i.e. numerals up to `27`, and a 4-term sum to `40`. Kernel cost: a handful
  of small `Nat` operations, far below any GMP-bignum concern. **No `Finset.univ` of a
  function type is ever enumerated by `decide`** — the card is obtained through
  `Fintype.card_fun`/`card_univ` simp lemmas (visible at `Euler/OrdinaryEulerCauchy.lean:26`),
  not by brute force. The remaining `∑ n ∈ range (m+1)` / `∑ w : Fin n → Fin 3` sums all carry
  a **variable** `m`/`n`, so nothing reduces.
* `omega` closes only `n ≤ m`-style linear `Nat` goals (6 sites) — linear-arithmetic
  certificates over small numerals.

**Vector (1) — recursors / inductive families.** Two `induction k` sites in
`Euler/OrdinarySmoothWords.lean:45` and `:117` (`wordBound_wordField`) build a `Nat.rec`
motive; the kernel type-checks the recursor application but **never reduces it at a literal**
(`k` stays a variable in every consumer in my scope). No nested or indexed inductive, no large
elimination (`Sort`-valued recursion), no `Acc.rec`, no well-founded definition, and no
`Fin`/`Vector` recursion in my scope. The `Evolution` and `SmoothL2Field` records are plain
non-recursive structures; the proofs *do* rely on structure projection/eta at
`OrdinaryEulerGradientControl.lean:35` (`rfl` identifying
`((U.velocity t).derivative).field x` with `fderiv ℝ (U.velocity t).field x`, i.e. one
projection-of-constructor step through `SmoothL2Field.derivative`,
`Euler/LpSmoothField.lean:49`) and at `OrdinaryEulerHigherEnergy.lean:26` (`rfl` unfolding the
`wordCount` `def`). Both are one-step delta/proj reductions on non-recursive data — the
cheapest, best-understood part of the kernel.

**Vector (3) — custom metaprogramming.** **Zero occurrences** in my scope, consistent with the
repo-wide scan. I re-ran the scan on my files specifically; nothing. The only non-`theorem`
oddity is `private local instance : Fact (0 < (1:ℝ))` (`Euler/OrdinaryWordTime.lean:19`,
`Euler/SmoothFieldSobolevTime.lean:20`, `Euler/OrdinaryEulerDifference.lean:18-19`), which the
predecessor `euler-interpolation.md` already settled as benign (it fixes the `L¹`/cylinder
weight, and `0 < 1` is true).

**`Fin.elim0` — checked specifically for vacuity, and it is NOT a vacuity trick.**
`OrdinaryEulerL2Stability.lean:32` instantiates the *general word* pairing identity
`differenceRhs_pairing` at the **empty word** `w : Fin 0 → Fin 3`. One might fear that
instantiating a family at an empty index type makes the statement content-free. It does not:
`wordField A (Fin.elim0) = A` (`wordField_zero`) and
`transportCommutator … (Fin.elim0) = 0` (`transportCommutator_zero`) — both used in the
`simp only` at `:33-34` — so the `n = 0` case is *precisely* the plain L² energy identity
`⟪w, RHS⟫ = -⟪(w·∇)U, w⟫` with the commutator genuinely absent (there is no derivative to
commute past the transport operator). The claim is about the actual field, not about an empty
family. Same for `:62,71,84`, where `Fin.elim0` selects the order-0 word path, i.e. the
velocity itself (`velocityPath_apply`, `:64`). Verdict OK.

**Bottom line for the kernel.** To accept these files the kernel must: type-check ordinary
`Nat.rec` motives (never reduce them), perform delta/proj steps on non-recursive structures,
and evaluate small-`Nat` arithmetic up to `40`. It never decides a `Decidable` instance, never
unfolds a well-founded recursion, and never touches a bignum. **This layer is not where a
kernel exploit could live.** If the artifact is unsound for kernel reasons, the reason is not
in the Grönwall core.

---

## Per-declaration findings

`cone` = `in_cone` column of `audits/nse-deep/CONE.csv` (all rows below have
`in_import_closure = True`).

### `Euler/OrdinaryEulerL2Stability.lean`

| decl | file:line | statement, in my words | how the proof establishes it | cone | verdict |
|---|---|---|---|---|---|
| `advection_norm_gradient` | `:18` | `‖(W·∇)U‖_{L²} ≤ K‖W‖_{L²}` given a pointwise bound `K` on `‖∇U‖_op` | `Lp.norm_le_mul_norm_of_ae_le_mul` + a.e. representatives + `le_opNorm`; no embedding, no integration by parts | True | **OK** |
| `differenceRhs_l2_bound` | `:27` | `2⟪W, differenceRhs U W P⟫ ≤ 2K‖W‖²` | `differenceRhs_pairing` at the empty word (pressure + full transport cancel exactly), then Cauchy–Schwarz + the previous lemma | True | **OK** |
| `linear_stability_within` | `:46` | closed-interval Grönwall: `X' ≤ C·X` on `Ico 0 T`, `X` continuous on `Icc 0 T` ⟹ `X t ≤ X 0 e^{Ct}` on `Icc 0 T` | Mathlib `le_gronwallBound_of_liminf_deriv_right_le` with `ε := 0`, `δ := X 0`; liminf-slope hypothesis produced from the real one-sided derivative | True | **OK** |
| `velocityPath` / `velocityPath_apply` | `:61`, `:64` | the velocity as a continuous `L²`-valued path; its value is `(velocity t).toLp` | order-0 `ordinaryWordPath`; `simp` | True | **OK** |
| `l2EnergyPath` | `:68` | `t ↦ ‖V-U‖²` as a *continuous* path | continuity of `ordinaryWordPath` of the difference (from the class's jet-continuity) composed with `‖·‖²` | True | **OK** |
| `l2EnergyDerivative` | `:75` | *defines* the candidate derivative as `2⟪w, ẇ⟫` | definition only — the identification with the actual derivative is the next lemma, not assumed | True | **OK** |
| `l2Energy_hasDerivWithinAt` | `:78` | that candidate really is the one-sided derivative on `Icc 0 T`, at every `t` including endpoints | strong L² derivative of the difference path (`ordinaryWord_hasDerivWithinAt`, ultimately the Bochner-primitive reconstruction) then `.norm_sq` | True | **OK** |
| `l2EnergyDerivative_bound` | `:90` | `2⟪w,ẇ⟫ ≤ 2K·‖w‖²` for the actual solutions | `differenceDerivative_eq` + `differenceRhs_l2_bound`; the three side conditions discharged from the class fields (`solenoidal`, `gradient`) | True | **OK** |
| `l2_energy_bound` | `:107` | `‖w(t)‖² ≤ ‖w(0)‖² e^{2Kt}` on `Icc 0 T` | the two previous lemmas fed to `linear_stability_within` with `C := 2K` | True | **OK** |
| `l2_stability` | `:127` | square root of the above | `exp_add` + `nlinarith` with `norm_nonneg` | True | **OK** |
| `velocityPath_norm_sub_le` | `:136` | the same bound in the **uniform-in-time** `C(Icc 0 T, L²)` norm, with `e^{KT}` | `ContinuousMap.norm_le` + monotonicity of `exp` in `t ≤ T` (needs `0 ≤ K`, which is a hypothesis `hK0`) | True | **OK** |
| `l2_stability_of_h3` | `:148` | same, with `K := 9·smoothEmbeddingConstant·M` from an H³ bound `M` on `U` | `real_smooth_fderiv_le_H3` (`H³ ↪ C¹` on ℝ³) + `tensorNorm_eq`; `MemLp`/smoothness discharged from the `SmoothL2Field` fields | **False** | **OK (dead code)** — used nowhere in the repo (grep: only its own definition site); the live path is `gradient_le_h3` at `Euler/OrdinaryEulerCauchy.lean:41`, which proves the same thing. Harmless duplication, worth noting only because `in_cone=False` here means the *main theorem does not need it*. |

### `Euler/OrdinaryEulerHigherEnergy.lean`

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `wordCount` | `:17` | `∑_{n≤m} 3ⁿ` = number of coordinate words of length ≤ m | definition | True | **OK** |
| `wordCount_nonneg` | `:19` | `0 ≤ wordCount m` | `sum_nonneg`+`positivity` | True | **OK** |
| `tensorNorm_le_wordCount` | `:21` | `Hᵐ` tensor norm ≤ `wordCount m · N` if all words up to `m` are ≤ `N` | `wordBound_jet_norm` (`‖jet n‖ ≤ 3ⁿ N`, itself from the coordinate-sum bound `multilinear_norm_le_coordinate_sum`) summed over `n ≤ m`; `rfl` only unfolds `wordCount` | True | **OK** |
| `tensorNorm_le_energy` | `:28` | `tensorNorm m A ≤ wordCount m·√(wordEnergy m A)` | previous + `wordBound_sqrt_energy` | True | **OK** |
| `integerEnergyPath` | `:36` | `t ↦ wordEnergy m (u(t))` continuous | `wordEnergy_continuous` from class jet-continuity | True | **OK** |
| `integerEnergyDerivative` | `:39` | candidate derivative `= integerEnergyProduction m u u̇` | definition | True | **OK** |
| `derivative_eq_eulerRhs` | `:42` | the class's `derivative` *is* `-u·∇u - ∇p` | `field_ext` + `derivative_field`/`eulerRhs_field`, both pointwise identities | True | **OK** |
| `integerEnergy_hasDerivWithinAt` | `:48` | the candidate is the real one-sided derivative on `Icc 0 T` | `wordEnergy_hasDerivWithinAt` (`Euler/OrdinaryWordTime.lean:87`) fed the class `time_law` | True | **OK** |
| `integerEnergyDerivative_bound` | `:56` | `d/dt E_m ≤ tameEnergyConstant m · M · E_m` when the word-3 norm is ≤ M | `integer_energy_tame` (`Euler/OrdinaryTameEnergy.lean:123`): pressure and pure transport cancel exactly; only the commutator survives, bounded tamely (low×high) | True | **OK** |
| `integer_energy_bound` | `:64` | `E_m(t) ≤ E_m(0)·e^{C_m M t}` on `Icc 0 T` | previous two + `linear_stability_within` | True | **OK** |
| `integer_energy_uniform` | `:84` | same with `T` in place of `t` | monotonicity of `exp`; needs `0 ≤ C_m` (`tameEnergyConstant_nonneg`) and `0 ≤ M` (`wordBound_nonneg`, derived from the bound itself) | True | **OK** |
| `tensorNorm_uniform` | `:94` | the `Hᵐ` tensor norm version | previous + `tensorNorm_le_energy` + `Real.sqrt_le_sqrt` | **False** | **OK** (used at `Euler/OrdinaryEulerGradientControl.lean:130`, itself out of cone) |
| `higher_energy_of_h3` | `:101` | same as `:84` but with the hypothesis phrased as `tensorNorm 3 ≤ M` | `wordBound_tensorNorm` converts the tensor-norm bound into a word bound | True | **OK** — this is the live consumer entry point (`Euler/OrdinaryEulerCauchy.lean:83`) |

### `Euler/OrdinaryEulerUniqueness.lean`

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `smoothField_eq_of_toLp_eq` | `:15` | equal in `L²` ⟹ equal as smooth fields | a.e. equality + `Measure.eq_of_ae_eq` with both fields continuous | True | **OK** |
| `velocity_eq_of_initial` | `:24` | equal initial data ⟹ equal velocity at all times, for any two `Evolution T hT` | `l2_stability_gradientIntegral` with the RHS collapsing to 0, then `norm_eq_zero`, then the previous lemma | True | **OK** |
| `pressure_eq_projected` | `:32` | for `0 < T`, the class's pressure force is the Leray projection of the velocity's advection | `derivative_toLp_projected` + `eulerRhs`, algebra | True | **OK** |
| `pressure_eq_of_initial` | `:40` | equal initial data ⟹ equal pressure force (for `0 < T`) | previous two | True | **OK** |

### Key dependencies I read and my verdicts on them

| decl | file:line | verdict | one-line reason |
|---|---|---|---|
| `variable_linear_stability` | `Euler/OrdinaryVariableGronwall.lean:14` | **OK** | textbook integrating factor, reduced to `linear_stability_within` with `C = 0`; `I 0 = 0` and `exp>0` handled explicitly |
| `l2EnergyDerivative_gradient` | `Euler/OrdinaryGradientStability.lean:18` | **OK** | same pairing lemma, coefficient = the measured `‖∇u(t)‖_{L∞}` |
| `l2_energy_gradientIntegral` / `l2_stability_gradientIntegral` | `:34` / `:54` | **OK** | hypothesis-free L² stability with exponent `∫₀ᵗ‖∇u‖_{L∞}` |
| `gradientNormPath` / `gradientNormPath_le_iff` / `pointwise_gradient_le` | `Euler/OrdinaryEulerGradientControl.lean:20,30,37` | **OK** | genuine finite sup via the proved `H³ ↪ L∞` bounded-continuous-function construction; `finiteField_apply` is unconditional, so no junk fallback |
| `h3_energy_gradientIntegral` | `:68` | **OK** | H³ energy propagates with exponent `C·∫‖∇u‖_{L∞}` — the honest Beale–Kato–Majda-shaped statement |
| `wordBound_of_gradientIntegral` | `:103` | **OK** | converts the H³ bound into a word bound with the explicit `gradientH3Bound` |
| `Evolution` (structure) | `Euler/OrdinaryEulerDifference.lean:21` | **OK, but see C** | six fields; `time_law` on the open `Ioo 0 T`; jet-continuity in time is the substantive assumption |
| `differenceDerivative_eq` | `:98` | **OK** | pointwise identity, `fderiv_sub` with differentiability from `.smooth` |
| `difference_time_law` | `:111` | **OK** | difference of the two `time_law`s |
| `energyDerivative_bound` | `:132` | **OK but easily misread** | this H³-difference estimate *does* carry `(M + √(energy))` on the right, i.e. it is quadratic; it is **not** in the L² Grönwall chain. Do not confuse it with `:90`. |
| `ordinaryWord_hasDerivWithinAt` / `wordEnergy_hasDerivWithinAt` | `Euler/OrdinaryWordTime.lean:78`, `:87` | **OK** | bounded linear word operator composed with the strong Sobolev-path derivative; then `HasDerivWithinAt.fun_sum` over the finitely many words |
| `sobolevPath_hasDerivWithinAt` | `Euler/SmoothFieldSobolevTime.lean:96` | **OK** | reduces order `q` to `q+3` and uses `restrictOperator`; the separating family is point evaluation, injectivity proved at `:68` |
| `EulerSeparatingTimeDerivative.eq_initial_add_integral` / `hasDerivWithinAt` | `Euler/SeparatingTimeDerivative.lean:24`, `:49` | **OK** | reconstructs the Bochner primitive by testing with a separating family, then FTC-1; **this is the correct route and closes spine-uniqueness Escalation 3** |
| `advection_inner_zero` | `Euler/OrdinaryTransportCancellation.lean:42` | **OK** | exact transport cancellation from `div = 0` via L² translation-unitarity integration by parts; no decay hypothesis needed |
| `differenceRhs_pairing` | `Euler/OrdinaryH3Energy.lean:34` | **OK** | pressure term killed by solenoidal⊥gradient, transport term by `advection_inner_zero`; only `(w·∇)U` and the commutator survive |
| `integer_energy_tame` | `Euler/OrdinaryTameEnergy.lean:123` | **OK** | commutator-only production, tame low×high bound, explicit constant |
| `tameEnergyConstant` | `Euler/OrdinaryTameEnergy.lean:86` | **OK** | `6·h3ProductConstant·∑_{n≤m}6ⁿ` — closed form in `m` and two fixed embedding constants; **no dependence on the solution** |
| `h3ProductConstant` | `Euler/OrdinaryH3Products.lean:16` | **OK** | `1+13·smoothEmbeddingConstant+4(1+3·sobolevConstant)²`, field-independent |
| `finiteField` / `finiteField_apply` / `sobolevField` | `Euler/MeanSobolevBoundedField.lean:104,108,26` | **OK** | the `H³→L∞` embedding with an explicit constant; the bounded function is *provably equal* to the field, so no junk value |
| `realIntegral_hasDerivAt` | `Euler/ContinuousTimeIntegral.lean:57` | **OK** | Mathlib FTC-1 for a continuous integrand, at every real `t` |
| `cauchyPath_of_initial` / `all_order_bounds_of_h3` | `Euler/OrdinaryEulerCauchy.lean:50`, `:70` | **OK** | constants `k`-free; this is what closes interpolation Escalation 1 |

Verdict counts over the 31 declarations of the three assigned files plus the 24 dependency
declarations tabulated above: **OK 55, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0**, with two
"OK-but-note" annotations (`l2_stability_of_h3` is dead code; `energyDerivative_bound` is a
quadratic estimate that a reader could mistake for the linear one).

---

## Escalations

Ranked. **None is a demonstrated defect.** Each is a place where my OK is conditional on
something outside my scope or outside this box.

1. **`tameEnergyConstant m = 6·h3ProductConstant·∑_{n≤m}6ⁿ` grows like `6^m`
   (`Euler/OrdinaryTameEnergy.lean:86`), so `higher_energy_of_h3`
   (`Euler/OrdinaryEulerHigherEnergy.lean:101`) gives `E_m(T) ≤ E_m(0)·exp(C·6^m·M·T)`.**
   *Question for an expert:* does any consumer need a bound **uniform in the order `m`** — e.g.
   an analytic/Gevrey estimate, a `∀ m` smoothness statement with a single constant, or a
   diagonal argument over `m` and `k` simultaneously? If yes, this constant cannot supply it
   and the chain has a real gap.
   *What would settle it:* the statement of `limitEvolutionOfH3`
   (`Euler/OrdinaryEulerCauchy.lean:97`) and of the smooth-limit construction it feeds — my
   reading of `all_order_bounds_of_h3` (`:70-91`) says the consumer only ever asks for
   *"for each `q`, some constant `C_q`"* (`:73`), which this estimate does supply, but I did
   not read the *packet/blowup* side that ultimately consumes those `C_q`.
2. **The `Evolution` class assumes continuity in time of *all* spatial `L²` jets
   (`Euler/OrdinaryEulerDifference.lean:24-25`), not just of the velocity in `L²`.**
   Everything in this layer — the strong time derivative, the energy path, the Grönwall input —
   rests on it.
   *Question:* for the constructed blowup solution, is that continuity *proved*, and proved
   without assuming the very regularity the blowup is supposed to destroy? *What would settle
   it:* the construction sites `evolutionOfClassical` (`:34`), `limitEvolutionOfH3`
   (`Euler/OrdinaryEulerCauchy.lean:97`), `restrictTime`/`shiftTime`, and the packet files.
   (This is an existence question, not a soundness question: if the class turned out to be
   empty, my theorems would be vacuous but still true.)
3. **Three Mathlib signatures I could not re-read on this box** (no Mathlib source vendored):
   `le_gronwallBound_of_liminf_deriv_right_le` + `gronwallBound_ε0`
   (used `Euler/OrdinaryEulerL2Stability.lean:51,55`), `HasDerivWithinAt.norm_sq`
   (used `:84`, `Euler/OrdinaryWordTime.lean:92`), and
   `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
   (used `Euler/SeparatingTimeDerivative.lean:36`).
   *Question:* does `le_gronwallBound_of_liminf_deriv_right_le` really conclude on the closed
   `Icc a b` from the differential inequality on `Ico a b` only, and is `norm_sq`'s derivative
   `2⟪f, f'⟫` (real inner product, no factor `½`)? *What would settle it:* `git show`ing
   `Mathlib/Analysis/ODE/Gronwall.lean` and `Mathlib/Analysis/InnerProductSpace/Calculus.lean`
   at the pinned rev (the spine-uniqueness worker did exactly this by fetching raw sources at
   rev `85e3a25e`; the same trick would settle it here). Note the factor question is
   *load-bearing*: a missing `2` would make `l2_energy_bound` off by a factor in the exponent,
   though not false in a way that helps the claimant.
4. **`l2_stability_of_h3` (`Euler/OrdinaryEulerL2Stability.lean:148`) is `in_cone = False` and
   is referenced nowhere in the repo.** Not a defect; recorded because a reader auditing "the
   L² stability theorem" may audit this one and think it is the one being used. The live ones
   are `l2_stability_gradientIntegral` (`Euler/OrdinaryGradientStability.lean:54`, uniqueness)
   and `velocityPath_norm_sub_le` (`OrdinaryEulerL2Stability.lean:136`, the Cauchy-sequence
   argument). Same status for `tensorNorm_uniform` (`:94`),
   `h3_energy_gradient_bound`/`higher_energy_of_gradientIntegral`/
   `higher_tensorNorm_of_gradientIntegral`/`higher_tensorNorm_of_gradientBound`
   (`Euler/OrdinaryEulerGradientControl.lean:90,119,125,132`) and
   `velocityPath_norm_sub_le_gradientIntegral` (`Euler/OrdinaryGradientStability.lean:63`,
   though that one *is* used at `Euler/OrdinaryGradientLimit.lean:43`).

---

## Residue — what I could not check, and why

* **No Mathlib.** No build (disk full) and no vendored source (`NSE/.lake` is empty), so
  (a) I could not run `lake build` to confirm the files elaborate — I rely on the audit's
  premise that Comparator already passed; (b) I could not read the three Mathlib statements in
  Escalation 3; (c) I could not measure actual kernel work (e.g. `set_option profiler`), so my
  vector-(2) assessment is a *source-level upper bound* on what the kernel could be asked to
  compute, not a measurement.
* **`Euler/EulerProof.lean` (≈8.4k lines) was only spot-read** at `8215-8250` and `8360-8400`.
  I read the *statements* of `smoothEmbeddingConstant` (`:8227`) and
  `real_smooth_fderiv_le_H3` (`:8375`) and the top of `smooth_pointwise_le_H2` (`:8237`), but
  I did **not** verify the `H² ↪ L∞` / `H³ ↪ C¹` proofs. If `smoothEmbeddingConstant` were
  somehow infinite/ill-defined the constants above would be meaningless — but it is a
  `noncomputable def` of a product of two proved-nonnegative quantities, so the risk is that
  the *inequality* is wrong, not that the constant is fake. Delegated to no one; flagged here.
* **`sobolevConstant`, `sobolevEmbeddingConstant 1 3`, `unitBumpCoefficient`** — used inside
  `h3ProductConstant` and `sobolevField`; I confirmed they are field-independent *definitions*
  but did not audit their defining files.
* **`transportCommutator` and `tame_transportCommutator`'s own proof**
  (`Euler/OrdinaryTameEnergy.lean:53`, and the `Euler/OrdinaryH3Products.lean` product
  estimates it rests on) I read at the statement level and one level of proof; the full
  Leibniz-expansion bookkeeping (`OrdinaryH3Products.lean:101-146`) was delegated (see below)
  rather than read by me line by line.
* **The pressure side** (`pressureField`, `derivative_toLp_projected`, `projectedRhs_toLp`,
  used at `Euler/OrdinaryEulerUniqueness.lean:35-38`) is asserted-by-name in my report; I read
  how they are *used* but not their proofs. The Leray projection's correctness is the
  spine/Helmholtz workers' territory.
* **Existence.** I checked that the `Evolution` class is *constructible in principle*
  (`evolutionOfClassical`, `limitEvolutionOfH3`) but I did not verify that the blowup
  construction actually produces one. Every theorem in my scope is a conditional statement
  about members of that class.

## Cross-checks delegated

Two READ-ONLY sub-auditors were spawned in parallel with independent briefs, so that the two
deepest dependencies are read by someone who did not already believe my conclusion:

* `workers/_sub-tame-energy.md` — `Euler/OrdinaryTameEnergy.lean` in full: is
  `tameEnergyConstant` solution-free, where exactly does the commutator estimate come from, is
  the estimate vacuous.
* `workers/_sub-l2-pairing.md` — `differenceRhs_pairing`, the `Evolution` fields one by one
  (derived vs assumed), the `Fin.elim0` vacuity question, and whether anything constructs an
  `Evolution`.

My conclusions above were reached **before** those reports and do not depend on them; if either
sub-report contradicts me, the contradiction should be resolved in favour of re-reading the
source, and I flag it to the parent.

### Result of cross-check 1: `workers/_sub-l2-pairing.md` (landed) — **agrees, and adds three things**

No contradiction with anything above. Its counts: OK 14, OK-by-definition 1, UNCLEAR 3,
SUSPICIOUS 1, KERNEL-RISK 0; `decide`/`sorry`/`axiom`/`macro`/`termination_by`/`deriving`/
numerals-over-4-digits all **0**, matching my census. Three additions I am folding in:

1. **The pressure cancellation is orthogonality *by definition*.**
   `word_pressure_pairing_zero` (`Euler/OrdinaryWordConstraints.lean:49`) →
   `pressure_pairing_zero` (`…MeanSolenoidalSpace…:129`) is literally `hu p hp`, because
   `solenoidalSpace := gradientSpace.orthogonal` (`:58`). So *that* step is free; the real
   content is pushed into (a) the `Evolution.gradient` field, discharged at construction by
   `gradient_mem` (`…PressureCancellation…:84`), and (b) the fact that `solenoidalSpace`
   membership really is div-freeness, which is what `smooth_mem_solenoidal` /
   `solenoidal_representative_divergence` supply (used
   `Euler/OrdinaryEulerDifference.lean:50`, `OrdinaryEulerL2Stability.lean:100`). Not a defect
   — but an expert reading "the pressure term vanishes exactly" should know it vanishes by the
   *definition of the space*, and should audit the two membership facts instead.
2. **The `Evolution` class is provably nonempty**: `exists_local_evolution`
   (`…LocalExistence…:152`) is unconditional. This softens my Escalation 2 to an
   existence-quality question rather than a vacuity question.
3. **One more unverifiable Mathlib dependency for Escalation 3**: the integration by parts under
   `advection_inner_zero` bottoms out in
   `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`
   (used `Euler/OrdinaryL2Integration.lean:36`). Add it to the list of signatures to check at
   the pinned Mathlib rev.

It also confirms independently my "easily misread" note: `difference_energy_bound`
(`Euler/OrdinaryH3Energy.lean:108`) carries `√(wordEnergy 3 W)` in its constant, so it is a
**Riccati** inequality (no uniqueness from it) and additionally needs `H⁴` on the reference —
a derivative loss. That estimate is *not* in the L² Grönwall chain audited here, and the L²
chain's `K` bounds only the reference `U`. Its verdict tag there is SUSPICIOUS-by-name; mine
for the L² chain stays OK.
