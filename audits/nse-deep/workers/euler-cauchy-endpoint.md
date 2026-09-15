# Worker report: Euler ordinary-Sobolev Cauchy limit & smooth endpoint

Repo audited (READ-ONLY): `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`
(clone of `openai/NavierStokesAndEuler`). No Mathlib build on this box; this is
source-level reading (grep + line-by-line). Nothing under `NSE/` was modified.

## Scope

Assigned files (read IN FULL, line by line, both of them):

| file | lines | `theorem` | `def` | `structure`/`inductive` | read | skimmed |
|---|---|---|---|---|---|---|
| `Euler/OrdinaryEulerCauchy.lean` | 123 | 6 | 1 (`limitEvolutionOfH3`) | 0 | 7/7 | 0 |
| `Euler/OrdinaryEulerEndpoint.lean` | 102 | 6 | 1 (`endpointScale`) | 0 | 7/7 | 0 |

Total in scope: **14 declarations, all 14 read line-by-line.**
Verdicts: **15 in-scope rows all OK** (the table below numbers 15 because
`limitEvolutionOfH3` is listed once as `def` and its two companion theorems
separately), **0 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS**; among the out-of-scope
chain rows, 13 OK and **1 UNCLEAR** (`pointwise_derivative_of_l2`'s exponent
normalisation, Escalation 3). Delegated children: 26 OK / 27 OK, 0 adverse.

Because `limitEvolutionOfH3` (`OrdinaryEulerCauchy.lean:97`) is a **one-line
wrapper** whose entire content is delegated, answering the assigned question
required reading the callee chain as well. Read IN FULL (line-by-line) outside
the nominal scope:

* `Euler/OrdinaryEulerDifference.lean:1-130` (the `Evolution` structure + `evolutionOfClassical`),
* `Euler/OrdinaryEulerLimit.lean` (125 lines, all 12 decls) — `SmoothLimitData.toEvolution`, `limitEvolution`,
* `Euler/OrdinaryHelmholtzField.lean` (156 lines, all 20 decls) — `projectedRhs`, `pressureField`, `derivative_mem_solenoidal`, `velocity_integral_equation`,
* `Euler/OrdinaryStrongTime.lean` (62 lines, 2 decls) — `sobolev_derivative_of_l2`, `pointwise_derivative_of_l2`,
* `Euler/InjectivePathDerivative.lean` (42) and `Euler/InjectivePathDerivativeWithin.lean` (31) — all 4 decls,
* spot-read (targeted line ranges, not whole files): `OrdinaryEulerL2Stability.lean:125-158`,
  `OrdinaryEulerHigherEnergy.lean:17-31,95-108`, `OrdinaryH3Norms.lean:1-25`,
  `OrdinarySmoothWords.lean:88-100`, `OrdinaryEulerLifespan.lean:55-85`,
  `OrdinaryEulerContinuation.lean:1-90`, `OrdinaryEulerNontriviality.lean:35-55`,
  `OrdinaryBKMReduction.lean:25-48`, `EulerSingularity.lean:40-70,120-150`,
  `ComparatorMaximalSolution.lean:95-115`, `EulerC1Breakdown.lean:50-70,125-155`.

Two sub-chains were delegated to read-only child auditors and are cross-referenced
below (their reports are separate files, see `## Delegated sub-chains`):
`OrdinarySmoothLimit.lean` + `OrdinaryAdvectionLimit.lean` (the compactness /
nonlinear-limit machinery) and `OrdinaryEulerRescaling.lean` +
`OrdinaryGradientLimit.lean` + `OrdinaryEulerGradientControl.lean`.

## A. The `Evolution` structure — exact fields

`Euler/OrdinaryEulerDifference.lean:21-32`, verbatim:

```lean
structure Evolution (T : ℝ) (hT : 0 ≤ T) where
  velocity : Icc (0 : ℝ) T → SmoothL2Field Space
  pressureForce : Icc (0 : ℝ) T → SmoothL2Field Space
  velocity_continuous : ∀ n, Continuous (fun t => (velocity t).jetLp n)
  pressure_continuous : ∀ n, Continuous (fun t => (pressureForce t).jetLp n)
  solenoidal : ∀ t, (velocity t).toLp ∈ solenoidalSpace
  gradient : ∀ t, (pressureForce t).toLp ∈ gradientSpace
  time_law : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r => (velocity (projIcc 0 T hT r)).field x)
      (-fderiv ℝ (velocity ⟨t,ht.1.le,ht.2.le⟩).field x
        ((velocity ⟨t,ht.1.le,ht.2.le⟩).field x)-
          (pressureForce ⟨t,ht.1.le,ht.2.le⟩).field x) t
```

Seven fields; the PDE field is named **`time_law`** (`:28`). It is a genuine
classical statement: for every interior time and every point `x`,
`t ↦ u(t,x)` has derivative `-(Du)(u) - g` where `g = pressureForce`. Two
observations that matter for the threat model:

* `time_law` is **not vacuous** when `T > 0`: `Ioo 0 T` is then nonempty, and for
  `t ∈ Ioo 0 T` the `projIcc` reparametrisation is the identity on a neighbourhood
  of `t`, so `HasDerivAt` is a real two-sided derivative of the real function.
* No junk-value escape hatch in `time_law`: `fderiv` is applied to
  `(velocity t).field`, and `SmoothL2Field` carries a `smooth : ContDiff ℝ ∞ …`
  field (used e.g. at `OrdinaryEulerDifference.lean:105-106`,
  `OrdinaryEulerCauchy.lean:44`), so the `fderiv` is a real derivative, not the
  `0` junk value of a non-differentiable function. Likewise `solenoidal` and
  `gradient` are genuine subspace memberships, so the Helmholtz split is real.

## B. `limitEvolutionOfH3` — is `time_law` PROVED for the limit?

**Verdict: PROVED, not inherited and not assumed** — the passage to the limit is
done through an integral (Duhamel) equation, and the limit's pressure is *not*
carried over from the sequence but *reconstructed* from the limit velocity by the
Helmholtz projection. Detail:

### B.1 The wrapper (`OrdinaryEulerCauchy.lean:97-102`)

```lean
def limitEvolutionOfH3 (V : ℕ → Evolution T hT) (hpos : 0 < T) (M : ℝ)
    (hM : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M)
    (hinit : ∀ q, ∃ R : ℝ, ∀ k, tensorNorm q ((V k).velocity ⟨0,le_rfl,hT⟩) ≤ R)
    (hcauchy : CauchySeq (fun k => ((V k).velocity ⟨0,le_rfl,hT⟩).toLp)) : Evolution T hT :=
  limitEvolution V hpos (Evolution.all_order_bounds_of_h3 V M hM hinit)
    (Evolution.cauchyPath_of_initial V M hM hcauchy)
```

It contributes **no** field of `Evolution` itself. It only converts the two
hypotheses into the shape `limitEvolution` wants:

* `all_order_bounds_of_h3` (`:70-91`): from one uniform H³ bound `M` on all
  `V k` at all times plus uniform bounds on the *initial* `H^q` norms, produce a
  uniform-in-`k`-and-`t` bound at every order `q`. Mechanism for `q ≥ 3`: the tame
  energy estimate `higher_energy_of_h3` (`OrdinaryEulerHigherEnergy.lean:101`,
  a Grönwall bound `wordEnergy q (u t) ≤ wordEnergy q (u 0) · exp(c_q M T)`),
  composed with the two elementary norm comparisons `tensorNorm_le_energy` and
  `wordEnergy_le_tensorNorm`. For `q < 3` it just re-uses the H³ bound
  (`tensorNorm_le_wordCount` + `wordBound_tensorNorm 3`, `:87-91`). This is a real
  argument: the H³ bound is genuinely what drives the higher-order Grönwall.
* `cauchyPath_of_initial` (`:50-68`): the sup-in-time L² Cauchy property of the
  velocity paths, from L² Cauchyness of the *initial* data. Mechanism: the Euler
  L²-stability estimate `velocityPath_norm_sub_le`
  (`OrdinaryEulerL2Stability.lean:136`, itself `l2_stability`:
  `‖v-u‖_{L²}(t) ≤ ‖v-u‖_{L²}(0)·exp(K t)` with `K` a bound on `‖∇u‖_∞`),
  with `K = 9·smoothEmbeddingConstant·M` supplied by the Sobolev embedding
  `gradient_le_h3` (`:41-48`, from `real_smooth_fderiv_le_H3`). Correct
  ε/exp(KT) bookkeeping at `:61-68`. This is the standard Grönwall
  well-posedness estimate, honestly used.

`hM`'s role is therefore real, not decorative: it supplies both the higher-order
Grönwall constant and the stability exponent.

### B.2 Where `time_law` is actually discharged

`limitEvolution` (`OrdinaryEulerLimit.lean:85-88`) = `(eulerLimitData V hb h0).toEvolution …`,
and `SmoothLimitData.toEvolution` (`OrdinaryEulerLimit.lean:55-73`) is the only
place any field is produced:

```lean
def toEvolution (hpos : 0 < T) (M : ℝ) (hb : ∀ k t, tensorNorm 3 ((V k).velocity t) ≤ M) :
    Evolution T hT where
  velocity := L.field
  pressureForce t := pressureField (L.field t)          -- :58  RECONSTRUCTED
  velocity_continuous := L.field_continuous              -- :59
  pressure_continuous := pressureField_continuous …      -- :60
  solenoidal := L.field_mem_solenoidal                   -- :61
  gradient t := pressureField_mem_gradient (L.field t)   -- :62
  time_law t ht x := by …                                -- :63-73  PROVED
```

Field by field:

1. `velocity := L.field` — the limit field packaged by `SmoothLimitData`
   (delegated: does `smoothLimitData` really construct it? see
   `## Delegated sub-chains`).
2. `pressureForce t := pressureField (L.field t)` (`:58`). **Not** inherited from
   the sequence. `pressureField A := fieldSub (solenoidalField (advectionField A A)) (advectionField A A)`
   (`OrdinaryHelmholtzField.lean:60-61`), i.e. `(P-I)(u·∇u)` — the Helmholtz
   *gradient* part of the advection term. So the limit's pressure is a function of
   the limit velocity; there is nothing to pass to the limit, and no unproved
   hypothesis is re-used.
3. `gradient` (`:62`) = `pressureField_mem_gradient` (`OrdinaryHelmholtzField.lean:74-76`):
   `P(w) - w ∈ gradientSpace` for the orthogonal projection onto `solenoidalSpace`.
   Real, one-line, from `sub_solenoidalProjection_mem_gradient`.
4. `solenoidal` (`:61`) = `field_mem_solenoidal` (`OrdinaryEulerLimit.lean:23-25`):
   `gradientSpace.isClosed_orthogonal.mem_of_tendsto` applied to
   `L.toLp_convergence t` with `Eventually.of_forall (fun k => (V k).solenoidal t)`.
   This is the correct argument (a *closed* subspace is stable under limits) and
   the hypotheses are actually supplied: the convergence used is the limit
   field's own L² convergence, and the members' solenoidality is the `V k`'s own
   field. **OK.**
5. `time_law` (`:63-73`). The mechanism, in order:
   * `hd` (`:64-69`): for every `r ∈ Ioo 0 T`, `HasDerivAt` **in L²** of
     `s ↦ (L.field (projIcc … s)).toLp` with derivative `(projectedRhs (L.field r)).toLp`.
     Obtained from `L.field_hasDerivWithinAt hpos M hb` (`:43-53`) by
     `.hasDerivAt (Icc_mem_nhds hr.1 hr.2)` — legitimate: on the *interior* a
     within-`Icc` derivative is a genuine derivative.
   * `field_hasDerivWithinAt` (`:43-53`) is proved by **rewriting the path as
     initial value + time integral** (`he`, `:47-51`, which is exactly
     `L.field_integral_equation`) and then differentiating the integral
     (`integral_hasDerivWithinAt … |>.const_add`). So the limit derivative comes
     from the *integral equation for the limit*, i.e. from FTC applied to a
     continuous integrand — not from any attempt to pass a derivative to the limit.
     This is the mathematically correct way to do it.
   * `field_integral_equation` (`:27-41`) is the actual passage to the limit:
     each member satisfies `u_k(t) = u_k(0) + ∫₀ᵗ projectedRhs(u_k)`
     (`he`, `:36-40`, = `(V k).velocity_integral_equation hpos`), the LHS
     converges by `L.toLp_convergence t`, the RHS converges by
     `L.toLp_convergence ⟨0,…⟩` plus **`L.projectedRhsPath_convergence hT M hb`**
     (`:31`) pushed through the (continuous, linear) integral operator and
     evaluation map (`:32-34`), and `tendsto_nhds_unique` (`:41`) identifies the
     two limits. The *only* nontrivial analytic input is
     `projectedRhsPath_convergence` (`OrdinaryAdvectionLimit.lean:135`) — the
     convergence of the **nonlinear term**, which is where the uniform Sobolev
     bound `hb` is consumed. **This is the single load-bearing lemma of the whole
     construction** (delegated, see below).
   * `pointwise_derivative_of_l2` (`OrdinaryStrongTime.lean:48`) upgrades the L²
     time-derivative to the *pointwise* derivative demanded by `time_law`. I read
     this chain in full and it is honest, not a junk step:
     `sobolev_derivative_of_l2` (`:28-45`) lifts the L² derivative to the order-`q`
     Sobolev path via `hasDerivWithinAt_of_injective_map`
     (`InjectivePathDerivativeWithin.lean:15`), which does **not** illegitimately
     pull a derivative back through an injective embedding: it goes
     `L(u(t)) = L(u(0)) + ∫L(f)` → (CLM commutes with the Bochner integral,
     `InjectivePathDerivative.lean:16-20`) → `L(u(t)) = L(u(0) + ∫f)` →
     (injectivity, `:23-31`) → `u(t) = u(0) + ∫f` in the *stronger* space →
     (FTC for the continuous `f`, `InjectivePathDerivativeWithin.lean:21-29`)
     → `u' = f` in the stronger space. The continuity hypotheses `hA`/`hB` are
     exactly what makes this valid, and they are supplied
     (`OrdinaryEulerLimit.lean:70-71`: `L.field_continuous` and
     `projectedRhs_continuous`). Then `pointwise_derivative_of_l2` composes with
     `observation 3 (le_refl 3) (x, 0)` — a **bounded linear** evaluation
     functional on the order-3 Sobolev space (Sobolev embedding H³ ↪ C⁰) — via
     `L.hasFDerivAt.comp_hasDerivWithinAt`, which is the correct direction
     (push forward through a CLM). **OK.**
   * Final `simpa only [projectedRhs_field]` (`:73`) turns
     `(projectedRhs u).field x` into `-fderiv u x (u x) - (pressureField u).field x`
     — `projectedRhs_field` (`OrdinaryHelmholtzField.lean:78-81`) is a two-line
     `simp`+`abel` identity that is *definitionally* true from the definitions of
     `projectedRhs` and `pressureField` (`:60-64`). So the shape delivered matches
     `time_law` exactly with `pressureForce = pressureField (L.field t)`. **No
     definitional trick that would weaken the PDE**: the identity is a genuine
     rearrangement `-(P a) = -a - ((P a) - a)` with `a = advectionField u u`.

   One consistency point worth stating loudly, because it is what makes the
   limit's PDE equivalent to the members': the *canonical* right-hand side
   `projectedRhs u = -P(u·∇u)` used in the integral equation is proved to equal
   each member's own right-hand side, i.e. each `V k`'s own `pressureForce` is
   *determined* by its velocity. `derivative_mem_solenoidal`
   (`OrdinaryHelmholtzField.lean:110-123`) differentiates the identity
   `P(u(t)) = u(t)` to get `∂ₜu ∈ solenoidalSpace`, and
   `derivative_toLp_projected` (`:125-134`) then applies `P` to
   `∂ₜu = -(u·∇u + g)` and uses `solenoidalProjection_eq_zero_iff` on
   `g ∈ gradientSpace` to conclude `∂ₜu = projectedRhs u`. That is the correct
   Helmholtz/uniqueness argument, and it means **no information about the
   pressure is lost or smuggled** when passing to the limit. **OK.**

### B.3 What I did NOT find (checked explicitly)

* No `sorry` / `admit` / `axiom` / `native_decide` in either scope file or in any
  file of the chain I read (`grep` counts 0; see `## Kernel-risk assessment`).
* No field of `Evolution` in `toEvolution` is discharged by `trivial`,
  `Classical.choice` of the *property*, or by re-using an unestablished hypothesis.
  The only choice-like step in my scope is `choose U hinit hgrad using hsol`
  (`OrdinaryEulerEndpoint.lean:50`), which skolemises an `∃` that was *proved*
  on the previous line from the hypothesis `hpartial` — legitimate use of AC.
* No junk-value exploitation: every `fderiv` in scope is applied to a
  `SmoothL2Field.field`, which carries `ContDiff ℝ ∞`.

## C. `exists_smooth_endpoint` (`OrdinaryEulerEndpoint.lean:39-73`)

Statement (verbatim `:39-43`):

```lean
theorem exists_smooth_endpoint (T : ℝ) (hT : 0 < T) (A : SmoothL2Field Space) (G : ℝ)
    (hpartial : ∀ S (hS : 0 < S), S < T →
      ∃ U : Evolution S hS.le, U.velocity ⟨0,le_rfl,hS.le⟩=A ∧
        ∀ t, U.gradientIntegral t ≤ G) :
    ∃ U : Evolution T hT.le, U.velocity ⟨0,le_rfl,hT.le⟩=A
```

"If for every shorter time `S < T` there is a genuine Euler evolution on `[0,S]`
starting at `A` whose gradient integral is `≤ G` (one `G` uniform in `S`), then
there is a genuine Euler evolution on the *closed* interval `[0,T]` starting at
`A`." Note the produced object is a full `Evolution T hT.le`, i.e. it carries
`time_law` on `Ioo 0 T` — the endpoint is genuinely reached.

Proof walk:

1. `hsol` (`:44-49`): instantiate `hpartial` at `S = endpointScale n * T` with
   `endpointScale n = 1 - 1/(n+2) ∈ (0,1)` (`:18`, positivity `:20-24`,
   `< 1` at `:26-29`). `S < T` from `mul_lt_mul_of_pos_right (endpointScale_lt_one n) hT`.
   Elementary and correct.
2. `choose U hinit hgrad using hsol` (`:50`) — skolemisation of a *proved* `∃`.
3. `V n := (U n).rescale T hT.le (endpointScale n) …` (`:51-52`): each shorter
   solution is rescaled to the **common** interval `[0,T]` by the Euler scaling
   symmetry. This is the step where a fake `Evolution` could be manufactured, so
   it was delegated for an independent read (`Evolution.rescale`,
   `OrdinaryEulerRescaling.lean:29`); see `## Delegated sub-chains`.
   Note `rescale` returns an `Evolution T hT.le`, so Lean *did* check its
   `time_law` field — the risk is a wrong scaling (chain-rule factor) making the
   *statement* provable but about the wrong object, not a missing proof.
4. `hv0` (`:53-55`): the rescaled initial datum is `scaleField (endpointScale n) A`
   `= (endpointScale n) • A` — i.e. the initial data are **perturbed** by the
   rescaling; they are *not* `A`. This is honest, is stated in the proof, and is
   repaired only in the limit (step 6). It is also the reason
   `exists_smooth_endpoint` cannot lean on any single `U n`: its entire content
   rests on the limit object of part B.
5. Uniform H³ bound `hb` (`:57-61`): `tensorNorm 3 ((V n).velocity t) ≤ M` with
   `M := gradientTensorBound (tensorNorm 3 A) G` (`:56`), via
   `tensorNorm_scaleField_le` (the norm is homogeneous, so amplitude scaling by
   `c ≤ 1` cannot increase it) and
   `(U n).h3_tensorNorm_gradient_uniform` — the H³-from-finite-gradient-integral
   Grönwall bound (`OrdinaryGradientLimit.lean:23`). **Crucially `M` does not
   depend on `n`**, which is exactly what compactness needs; this is where
   `hpartial`'s uniform `G` is consumed. Delegated for independent check.
6. `hb0` (`:62-67`): uniform bound on *all* initial Sobolev orders, `tensorNorm q A`,
   again by homogeneity. `hc` (`:68-70`): the initial data converge in
   L² to `A.toLp`, because `scaleField σ A ↦ σ • A.toLp` (`scaleField_toLp`) and
   `endpointScale n → 1` (`endpointScale_tendsto`, `:31-37`, a clean
   `tendsto_inv_atTop_zero` argument). Correct.
7. `W := limitEvolutionOfH3 V hT M hb hb0 hc.cauchySeq` (`:71`) — the object of
   part B. Its `time_law` is proved, per B.2.
8. `refine ⟨W, smoothField_eq_of_toLp_eq _ A ?_⟩` (`:72-73`): the initial value is
   identified with `A` via `limitEvolutionOfH3_initial` (uniqueness of limits) and
   `smoothField_eq_of_toLp_eq` (`OrdinaryEulerUniqueness.lean:15`: two smooth L²
   fields with equal L² classes are equal — this needs the a.e.-to-everywhere
   upgrade for continuous representatives, and it is a stated lemma, not an
   assumption).

**Verdict: OK.** No `sorry`-shaped discharge, no junk value, no re-use of an
unestablished hypothesis. The *only* two places where the truth of the theorem
is not fully visible inside this file are the two delegated sub-chains
(`rescale`'s scaling algebra and `projectedRhsPath_convergence`'s nonlinear
limit) — both of which are Lean-checked proofs of *stated* lemmas, so the
residual risk is "correct proof of a subtly mis-stated lemma", not a gap.

`endpoint_matches_partial` (`:75-87`) and `exists_smooth_endpoint_extension`
(`:89-100`): restriction of `W` to `[0,S]` (`W.restrictTime`) plus L²-based
uniqueness (`velocity_eq_of_initial`, `pressure_eq_of_initial`) identify the
endpoint solution with every shorter one. The hypothesis actually used is only
equality of the *initial L² classes* (`hi`, `:83-86`), which is genuinely
established from `hW`/`hU`. **OK** (the uniqueness lemmas themselves were audited
by the sibling `euler-spine-uniqueness` report, not re-derived here).

## D. Why it matters — dependency chain, verified by grep

I re-derived the chain myself rather than trusting the hand-off, and **two of the
three claimed consumers are wrong**:

* **(a) is wrong as stated.** `FiniteLifespan.no_endpoint`
  (`OrdinaryEulerContinuation.lean:53-56`) does **not** use
  `exists_smooth_endpoint`. Its proof is
  `intro h; obtain ⟨S,hS,hE⟩ := h.extend; exact L.maximal S hS hE`, i.e. it uses
  `HasEulerEvolution.extend` (`:45`, from local existence + concatenation,
  `Evolution.exists_extension`, `:20-34`) and maximality. It *is* the `T = T*`
  exclusion feeding clause 8 (`hasEulerEvolution_iff`, `EulerSingularity.lean:48-59`,
  → `hasScalarEulerEvolution_iff`, `:61` → `maximal_sobolev_existence_iff`,
  `ComparatorMaximalSolution.lean:107`), but that route is independent of my scope.
* **(b) is wrong.** `FiniteLifespan.initial_nonzero`
  (`OrdinaryEulerNontriviality.lean:47-52`) uses `L.no_endpoint` plus
  `zeroEvolution` (`:21`), not `exists_smooth_endpoint`.
* **(c) is right, and it is the real reason this file is load-bearing.** The one
  consumer of `exists_smooth_endpoint` is
  `FiniteLifespan.endpoint_of_bounded_gradient` (`OrdinaryEulerLifespan.lean:77-83`),
  and that is used **contrapositively** by:
  - `FiniteLifespan.gradientIntegral_unbounded` (`OrdinaryEulerContinuation.lean:57-63`),
  - `FiniteLifespan.gradient_unbounded` (`:65-74`) → `gradient_unbounded_near_endpoint` (`:86`)
    → `EulerC1Breakdown.lean:58,135` → `maximalC1Norm_limsup`,
  - `FiniteLifespan.vorticity_unbounded_of_logarithmic` (`OrdinaryBKMReduction.lean:34-46`)
    → `maximalVorticity_integral_infinite`.
  Both `maximalC1Norm_limsup` and `maximalVorticity_integral_infinite` are among
  the deliverable clauses of `Euler.exists_compact_smooth_euler_singularity`
  (`EulerSingularity.lean:133-150`; the two `= ⊤` clauses).

  **Direction of danger, stated precisely.** `exists_smooth_endpoint` is used in
  the *positive* direction: it manufactures an `Evolution` which then contradicts
  maximality. So if it manufactured an object that need not satisfy the PDE, the
  derived clauses ("limsup C¹ norm at `T*` is `⊤`", "vorticity integral is `⊤`")
  would be **false theorems**, i.e. a refutation of the artifact rather than a
  vacuity. I therefore held this to the standard requested. **My finding is that
  it does not manufacture such an object**: `Evolution` bundles `time_law`, Lean
  checked that field, `time_law` is non-vacuous for `T > 0` (see A), and the
  proof of the limit's `time_law` is a genuine Duhamel + Helmholtz argument with
  its hypotheses supplied (see B.2). The residual risk is concentrated in exactly
  two delegated lemmas, and in the deeper `SmoothL2Field`/Sobolev-embedding
  infrastructure that is outside this worker's scope.

### D.1 Instrument finding: `CONE.csv` has systematic false negatives

`audits/nse-deep/CONE.csv` marks `in_cone=False` for
`Euler/OrdinaryEulerEndpoint.lean:39 exists_smooth_endpoint`,
`OrdinaryEulerLifespan.lean:77 endpoint_of_bounded_gradient`,
`OrdinaryEulerContinuation.lean:53 no_endpoint`,
`OrdinaryEulerLimit.lean:27 field_integral_equation`,
`OrdinaryHelmholtzField.lean:125 derivative_toLp_projected` and `:139
velocity_integral_equation`, `OrdinaryAdvectionLimit.lean:135 projectedRhsPath_convergence`.
That is provably wrong: `OrdinaryEulerLimit.lean:43 field_hasDerivWithinAt` is
`in_cone=True` and its proof body *calls* `L.field_integral_equation` at `:51`;
`toEvolution` (`:55`) is `True` and calls `L.field_hasDerivWithinAt` at `:68`.
The common feature of the false negatives is that they are only ever invoked with
**dot notation** (`L.field_integral_equation`, `L.no_endpoint`,
`U.gradientIntegral`). So: **do not read `in_cone=False` as "not load-bearing"
for any lemma whose call sites are dot-notation.** Cone statuses of the
declarations I audited are listed in the table below with this caveat attached.

## Per-declaration findings

`cone` = `in_cone` column of `audits/nse-deep/CONE.csv` (see D.1 for its
unreliability on dot-notation callees).

| # | declaration | file:line | what the statement says | how the proof establishes it | cone | verdict |
|---|---|---|---|---|---|---|
| 1 | `wordEnergy_le_tensorNorm` | `OrdinaryEulerCauchy.lean:15` | `wordEnergy m A ≤ wordCount m · (tensorNorm m A)²`, i.e. the sum of squares of the ≤`3^n` word-derivative L² norms is bounded by the count times the squared H^m norm | `sum_le_sum` twice, each term bounded by `wordBound_tensorNorm` (`OrdinaryH3Norms.lean:21`, itself `single_le_sum`), then `sum_const`+`Fintype.card_fun` gives `3^n` and `rfl` closes `∑_{n≤m}(3:ℝ)^n = wordCount m` by delta-unfolding `wordCount` (`OrdinaryEulerHigherEnergy.lean:17`) | True | OK |
| 2 | `Evolution.fieldPath_eq_velocityPath` | `:35` | the generic `fieldPath` of the velocity equals the bundled `velocityPath` | `ContinuousMap.ext` + `velocityPath_apply` | True | OK |
| 3 | `Evolution.gradient_le_h3` | `:41` | a uniform H³ bound `M` gives the pointwise gradient bound `‖∇u(t,x)‖ ≤ 9·c_S·M` | Sobolev embedding `real_smooth_fderiv_le_H3` (`EulerProof.lean:8375`) rewritten by `tensorNorm_eq`, then monotonicity. Uses `(U.velocity t).smooth` and `.integrable`, so no junk `fderiv` | True | OK |
| 4 | `Evolution.cauchyPath_of_initial` | `:50` | L² Cauchy initial data + uniform H³ bound ⟹ the velocity paths are Cauchy in `C([0,T],L²)` | `Metric.cauchySeq_iff`, ε/exp(KT) split, and the Euler L² stability estimate `velocityPath_norm_sub_le` (`OrdinaryEulerL2Stability.lean:136`, Grönwall with `K` from #3) | True | OK |
| 5 | `Evolution.all_order_bounds_of_h3` | `:70` | uniform H³ bound + uniform bounds on all initial `H^q` norms ⟹ uniform-in-`k,t` bound at every order `q` | `q ≥ 3`: tame-energy Grönwall `higher_energy_of_h3` (`OrdinaryEulerHigherEnergy.lean:101`) + `tensorNorm_le_energy` + #1. `q < 3`: `tensorNorm_le_wordCount` + `wordBound_tensorNorm 3` + `omega` | True | OK |
| 6 | `limitEvolutionOfH3` | `:97` | **def**: from a sequence of genuine Euler evolutions with a common H³ bound, uniform initial Sobolev bounds and L² Cauchy initial data, produce a genuine Euler evolution on the same `[0,T]` | pure delegation to `limitEvolution` (`OrdinaryEulerLimit.lean:85`) with #5 and #4 as the two hypotheses; contributes no field itself. All 7 fields, incl. `time_law`, discharged in `SmoothLimitData.toEvolution` (`OrdinaryEulerLimit.lean:55-73`) — see B.2 | True | OK |
| 7 | `limitEvolutionOfH3_convergence` | `:104` | the order-`q` jet paths of the sequence converge to those of the limit | delegation to `limitEvolution_jet_convergence` → `SmoothLimitData.jetPath_convergence` | False (unused here) | OK |
| 8 | `limitEvolutionOfH3_initial` | `:114` | if the initial data converge in L² to `u₀`, the limit's initial datum *is* `u₀` | delegation to `limitEvolution_initial` = `tendsto_nhds_unique` on the two convergences. Honest: uniqueness of limits, no assumption | True | OK |
| 9 | `endpointScale` | `OrdinaryEulerEndpoint.lean:18` | **def** `1 - 1/(n+2)` | — | False | OK |
| 10 | `endpointScale_pos` | `:20` | `0 < 1-1/(n+2)` | `div_lt_one` + `linarith`; `Nat.cast_nonneg` | False | OK |
| 11 | `endpointScale_lt_one` | `:26` | `1-1/(n+2) < 1` | `positivity` + `linarith` | False | OK |
| 12 | `endpointScale_tendsto` | `:31` | `endpointScale n → 1` | `tendsto_inv_atTop_zero.comp (… add_const …)` then `simpa`. Genuine | False | OK |
| 13 | `exists_smooth_endpoint` | `:39` | solutions on all `[0,S]`, `S<T`, with a *uniform* gradient-integral bound `G` ⟹ a solution on the closed `[0,T]` with the same initial datum | rescale each shorter solution to `[0,T]` (`Evolution.rescale`), uniform H³ bound from `G` via `h3_tensorNorm_gradient_uniform` + `gradientTensorBound`, initial data `scaleField σₙ A → A` in L², then #6 and #8. See C | False (**false negative**, see D.1: it is the source of two `= ⊤` deliverable clauses) | OK |
| 14 | `endpoint_matches_partial` | `:75` | the endpoint solution agrees with every shorter solution with the same initial datum, in velocity *and* pressure | `W.restrictTime`, then L²-initial-data uniqueness `velocity_eq_of_initial` / `pressure_eq_of_initial`. Only the initial L² equality is used, and it is established | False (false negative: used at `OrdinaryEulerLifespan.lean:71`) | OK |
| 15 | `exists_smooth_endpoint_extension` | `:89` | #13 and #14 packaged together | `obtain` from #13, then #14 | False | OK |

Out-of-scope declarations I read line-by-line and judged (relevant to the question):

| declaration | file:line | mechanism | verdict |
|---|---|---|---|
| `Evolution` (structure) | `OrdinaryEulerDifference.lean:21` | 7 fields, PDE field `time_law` at `:28`; non-vacuous for `T>0`, no junk-`fderiv` escape | OK |
| `SmoothLimitData.field_mem_solenoidal` | `OrdinaryEulerLimit.lean:23` | closed subspace stable under the limit | OK |
| `SmoothLimitData.field_integral_equation` | `:27` | **the passage to the limit**: member Duhamel equations + `projectedRhsPath_convergence` + `tendsto_nhds_unique` | OK, conditional on the delegated `projectedRhsPath_convergence` |
| `SmoothLimitData.field_hasDerivWithinAt` | `:43` | differentiate the integral equation (FTC), not the sequence | OK |
| `SmoothLimitData.toEvolution` | `:55` | all 7 fields; pressure *reconstructed* by Helmholtz; `time_law` proved | OK |
| `limitEvolution` | `:85` | `toEvolution` with `Classical.choose (hb 3)` as the H³ constant | OK (choice of a *constant*, not of a proof) |
| `Evolution.derivative_mem_solenoidal` | `OrdinaryHelmholtzField.lean:110` | differentiate `P u = u`; needs `0 < T` and `uniqueDiffOn_Icc` | OK |
| `Evolution.derivative_toLp_projected` | `:125` | apply `P` to the Euler RHS, `P g = 0` for `g ∈ gradientSpace` ⟹ pressure is determined by velocity | OK — this is why the limit PDE is the same PDE |
| `Evolution.velocity_integral_equation` | `:139` | Duhamel form of `time_law` for every genuine evolution | OK |
| `projectedRhs_field` | `:78` | `-(P a) = -a - ((P a) - a)`; matches `time_law`'s shape exactly | OK |
| `pointwise_derivative_of_l2` | `OrdinaryStrongTime.lean:48` | H³ derivative composed with the *bounded* evaluation functional `observation 3` (Sobolev embedding) — correct direction | OK on mechanism, **UNCLEAR** on normalisation: I could not reconcile the cylinder point `(x, (0 : AddCircle 1))` and the local `Fact (0 < (1:ℝ))` instance (`:18`) with the `L2` used elsewhere — Escalation 3 |
| `sobolev_derivative_of_l2` | `:28` | L² → H^q derivative via `hasDerivWithinAt_of_injective_map` | OK — see next row |
| `hasDerivWithinAt_of_injective_map` | `InjectivePathDerivativeWithin.lean:15` | **not** an illegitimate pullback: CLM commutes with the Bochner integral → injectivity gives the integral equation in the strong space → FTC with a *continuous* integrand | OK |
| `integral_equation_of_injective_map` | `InjectivePathDerivative.lean:23` | `apply hL` then `map_pathIntegral` + `integral_equation_of_hasDerivAt` | OK |

## Kernel-risk assessment

Vector (3) — **custom metaprogramming: ZERO in scope.** `grep` over both scope
files for `macro`, `elab`, `syntax`, `set_option`, `native_decide`, `axiom`,
`unsafe`, `partial`, `attribute`, `deriving`: 0 real hits (the only textual
matches in `OrdinaryEulerEndpoint.lean` are the substring `partial` inside the
hypothesis name `hpartial` at `:40,42,48,91,93` and inside
`endpoint_matches_partial`; not the `partial` keyword). Also 0 `sorry`, 0
`admit`, 0 `axiom`. The two files declare no instances; the two
`private local instance` lines in the chain (`OrdinaryEulerDifference.lean:18-19`,
`OrdinaryStrongTime.lean:18`) are `inferInstance`/`⟨by norm_num⟩` restatements,
which are diamond-hygiene noise rather than kernel risk, though
`OrdinaryStrongTime.lean:18` (`Fact (0 < (1:ℝ))`) is the kind of local `Fact`
instance that can silently pick a different `Lp` exponent instance — see
Escalation 3.

Vector (2) — **Nat/GMP numeral arithmetic: essentially absent.**
* `OrdinaryEulerCauchy.lean`: no `decide`, no `Nat.pow` on literals, no literal
  with ≥4 digits, no `norm_num` extension certificate that the kernel must
  recompute. The only arithmetic tactics are `omega` at `:24` and `:91` (goals
  `n ≤ m` / `n ≤ 3` from `n < m+1`, tiny linear-integer certificates) and
  `norm_num` at `:48,:56` (goal `0 ≤ (9:ℝ)`). `Fintype.card_fun` at `:26`
  produces the symbolic `3^n` with `n` a *bound variable* — the kernel never
  enumerates `Fin n → Fin 3`.
* `OrdinaryEulerEndpoint.lean`: no `decide`, no `omega`; `positivity` at `:22,:27`
  and `linarith` at `:22,:24,:29` on `1/((n:ℝ)+2)`. All numerals are `1`, `2`;
  all live in `ℝ` (`Real` literals are `OfNat` applications the kernel does not
  evaluate). Nothing for GMP to do.
* The one `rfl` in scope (`OrdinaryEulerCauchy.lean:29`) closes
  `∑ n ∈ range (m+1), (3:ℝ)^n = wordCount m` where `wordCount` is *defined* as
  that sum (`OrdinaryEulerHigherEnergy.lean:17`). The kernel work is one delta
  unfolding plus `Eq.refl`; `m` is symbolic, so no `Finset.sum` / `List.foldr`
  recursor reduction is forced. **Cheap and safe.**
* Nowhere in scope does the kernel have to decide a `Decidable` instance. Count
  of `decide`/`Decidable.decide`/`by decide` in both files: **0**.

Vector (1) — **recursive inductive types / recursors.**
* Both scope files declare **no** `inductive`, `structure`, or `def` by pattern
  matching / recursion. Count of `termination_by`, `WellFounded.fix`, `Acc.rec`,
  `.rec`, `.recOn`, `.brecOn` in both files: **0**.
* The recursive data that *is* present is only used through Mathlib's API:
  `Finset.range (m+1)` and `Finset.sum` (`Multiset`/`List.foldr` under the hood)
  in `wordEnergy`/`tensorNorm`/`wordCount`, and `Fin n → Fin 3` with
  `Pi.fintype`. Every manipulation goes through `sum_le_sum`, `sum_const`,
  `sum_mul`, `single_le_sum`, `Fintype.card_fun` — *lemmas*, whose kernel cost is
  proof-term checking, not recursor reduction on a concrete `List`. The one place
  a reduction happens is the `rfl` above, and it is a delta step only.
* `Icc (0:ℝ) T` is a subtype, and `Subtype`/structure eta is used pervasively
  (anonymous constructors `⟨0,le_rfl,hT⟩`, `⟨t,ht.1.le,ht.2.le⟩`). Structure eta
  *is* a kernel feature (Lean 4 has definitional eta for structures), so it is
  formally in vector (1); but these are non-recursive single-constructor
  structures (`Subtype`, `And`) where eta is well-trodden and used by essentially
  all of Mathlib. I flag it for completeness, not as a suspicion.
* `Classical.choose (hb 3)` (`OrdinaryEulerLimit.lean:88`) and `choose … using`
  (`OrdinaryEulerEndpoint.lean:50`) introduce `Classical.choice`, which is an
  *axiom* in Lean's core (as in all of Mathlib) but not a kernel-computation risk.

**Bottom line on kernel risk in scope: nothing. The kernel accepts these two
files by type-checking proof terms built from Mathlib lemmas; it is never asked
to evaluate a numeral, decide a proposition, or reduce a recursor on concrete
data.** If the artifact is exploiting a kernel bug, it is not doing it here.

## Delegated sub-chains

Two read-only child auditors were given the two lemmas on which my verdict is
conditional. Their reports:

* `audits/nse-deep/workers/_sub-smoothlimit-advection.md` —
  `structure SmoothLimitData` / `smoothLimitData` (`OrdinarySmoothLimit.lean:27,62`)
  and `projectedRhsPath_convergence` (`OrdinaryAdvectionLimit.lean:135`).
* `audits/nse-deep/workers/_sub-rescale-gradient.md` — `Evolution.rescale`
  (`OrdinaryEulerRescaling.lean:29`), `h3_tensorNorm_gradient_uniform` /
  `gradientTensorBound` (`OrdinaryGradientLimit.lean:16,23`),
  `Evolution.gradientIntegral` (`OrdinaryEulerGradientControl.lean:41`).

### Result of the first sub-chain (`smoothlimit-advection`, 26 decls read, 26 OK)

**Escalation 1 is resolved in the artifact's favour.** The child reports, with
file:line:

* `structure SmoothLimitData` (`OrdinarySmoothLimit.lean:27-32`) has one DATA
  field (`tower`) and two PROOF fields (`value_convergence` `:30`,
  `sobolev_convergence` `:31`). They are *bundled but discharged*, not assumed:
  `nonempty_smoothLimitData` (`:34-60`) builds the limit field from
  `cauchySeq_tendsto_of_complete h0` (`:39`) and the tower realisation from
  `exists_sobolevPath_limit` (`:40`), whose engine is a Sobolev **interpolation**
  lemma (`OrdinaryCauchyInterpolation.lean:91` / `SobolevCauchyInterpolation.lean:78`:
  a uniform bound at order `q+1` plus L² Cauchyness gives Cauchyness at order `q`),
  and proves `value_eq` by `tendsto_nhds_unique` (`:55`). `smoothLimitData`
  (`:62-67`) is then `Classical.choice` of a **proved** `Nonempty` — noncomputable,
  but no new axiom and no unproved field.
* `projectedRhsPath_convergence` (`OrdinaryAdvectionLimit.lean:135`) is a **real
  nonlinear passage to the limit**: the bounded Leray projection
  (`EulerMeanSolenoidal:104`) composed with `advectionPath_convergence`
  (`:108-133`), which is a Leibniz split (`:28-37`) plus the product estimate
  `‖A·∇A − B·∇B‖ ≤ G‖A−B‖ + K‖∇A−∇B‖` (`:48,:89`), with `G` from the uniform H³
  sup-gradient bound (`EulerProof.lean:8375`) and `K` obtained for the *limit* via
  `tensorNorm_bound` (`le_of_tendsto`), closed by `squeeze_zero` using both the
  `fieldPath` and the order-1 `jetPath` convergence. It is convergence of the
  genuine advection term in a strong (L² with L² gradient control) sense — not a
  self-conversion, and not weaker than its name.
* Child's own top remark, which I endorse: the compactness engine here is
  **interpolation, not Rellich**, and both inputs (`h0` L² Cauchy, `hb` at every
  order) are *assumed* at this level — so the burden sits on the producers, which
  are precisely `OrdinaryEulerCauchy.lean` (#4, #5 above, audited OK) and
  `OrdinaryEulerLocalExistence.lean` (not my scope).
* Kernel: zero `decide` / recursors / `termination_by` / bignums / macros /
  `unsafe` / `sorry` in those two files; only `Classical.choice` at `:67`.

Consequently the conditional in B.2 is discharged: the limit's `time_law` rests on
a genuine nonlinear convergence lemma, not on a definitional trick.

### Result of the second sub-chain (`rescale-gradient`, 27 decls read, 27 OK)

**Escalation 2 is resolved in the artifact's favour, and my own guess about the
scaling was wrong — the correction matters, so I record it.** The child reports:

* `Evolution.rescale` (`OrdinaryEulerRescaling.lean:29`, fields `:31-32`) uses an
  **amplitude + time** rescaling with **no spatial dilation**:
  `u_c(t,x) = c·u(c·t, x)` and `P_c(t,x) = c²·P(c·t, x)`
  (`scaleField` is a `c •` scalar multiple, `FieldScaling.lean:18-22`). I checked
  by hand that this *is* an exact symmetry of the pointwise law as encoded in
  `time_law` (`OrdinaryEulerDifference.lean:28-32`): with `v(t,x) = c·u(ct,x)`,
  `∂ₜv = c²(∂ₜu)(ct,x)` and `(v·∇v) = c²(u·∇u)(ct,x)`, so the residual is
  `c²` times the original residual and the pressure force must be scaled by
  exactly `c²` — which is what `:32` does. My Escalation 2 had guessed the
  *self-similar* symmetry `c·u(ct,cx)`; the file does not use it, and the
  simpler symmetry it does use is equally exact and avoids any spatial
  chain-rule factor.
* `time_law` for the rescaled object is genuinely proved (`:43-74`): both
  chain-rule factors `c` come from `HasDerivAt.scomp` + `const_smul` (`:48`), the
  target is rewritten to `c·(c·…)` via `scaleField_fderiv` (`:58-72`), and the
  `projIcc` clamping is removed by an eventual-equality argument on `Ioo`
  (`:49-57`). Domain correctness: `hc` gives `c·t ∈ Ioo 0 S` (`:44`), `hct` gives
  `c·t ≤ S`. `exists_smooth_endpoint` instantiates it with `c·T = S` exactly
  (`OrdinaryEulerEndpoint.lean:52`, where `S = endpointScale n * T`).
* `h3_tensorNorm_gradient_uniform` / `gradientTensorBound`
  (`OrdinaryGradientLimit.lean:23,16`): a **real Grönwall** chain,
  `time_law → energy derivative` (`OrdinaryEulerHigherEnergy.lean:48,42`)
  `→ commutator estimate` (`OrdinaryGradientEnergy.lean:92`)
  `→ variable_linear_stability` (`OrdinaryVariableGronwall.lean:14`), and
  `gradientTensorBound R G` does **not** mention `T` — so the H³ bound really is
  uniform in the interval length, which is exactly what step 5 of C needs.
* `Evolution.gradientIntegral` (`OrdinaryEulerGradientControl.lean:41`) is a real
  BKM-type quantity `∫₀ᵗ supₓ‖∇u(s,x)‖ ds`: the sup is genuine
  (`norm_le` iff at `:30-35`, finiteness of the sup from a *proved* H³→L^∞
  embedding), and **integrability is established** (`:52,:55`), so the
  `∫ = 0`-for-non-integrable junk-value escape is not being exploited. This
  matters because `hpartial`'s `∀ t, U.gradientIntegral t ≤ G` would otherwise be
  a trivially satisfiable hypothesis, which would make
  `exists_smooth_endpoint` far too strong.
* Kernel: 0 `decide` / recursors / `termination_by` / metaprogramming / bignums
  across the three files; 5 `rfl`, all structure/`Subtype` defeq.
* Child's residual, which I promote to Escalation 6 below: the H³ Grönwall
  arguments want a within-`Icc` derivative *at* `t = 0`, while `time_law` only
  provides `Ioo 0 T`; the upgrade lives at `SmoothFieldSobolevTime.lean:96` and
  is unaudited.

Their conclusions are summarised in `## Escalations` below.

## Escalations

Ranked. None of these is a demonstrated defect; they are the places where my
"OK" verdict is conditional on something I could not settle from my scope.

1. **[RESOLVED by the delegated read — kept for the record]
   `projectedRhsPath_convergence` (`Euler/OrdinaryAdvectionLimit.lean:135`) is
   the single load-bearing analytic lemma of the whole limit construction.**
   Everything in B.2 reduces to it: if the *nonlinear* term of the approximating
   solutions does not really converge to the nonlinear term of the limit, then
   `field_integral_equation` (`OrdinaryEulerLimit.lean:27`) is about the wrong
   object and the limit's `time_law` — although Lean-checked — would be a
   correctly proved statement about a mis-specified right-hand side.
   *Question for an expert:* does the lemma establish convergence of
   `t ↦ P(u_k·∇u_k)` to `t ↦ P(u·∇u)` in `C([0,T],L²)` (or a topology strong
   enough for the integral operator used at `OrdinaryEulerLimit.lean:32-34`), and
   is the uniform H³ bound `hb` genuinely what supplies the compactness (product
   estimate `‖u_k·∇u_k - u·∇u‖ ≤ C(M)‖u_k-u‖`)?
   *What would settle it:* the verbatim statement plus the norm in which the
   convergence holds, and a check that the constant depends only on `M`.
   *Settled:* yes to both — Leray projection ∘ `advectionPath_convergence`
   (`:108-133`), product estimate `‖A·∇A−B·∇B‖ ≤ G‖A−B‖+K‖∇A−∇B‖` (`:48,:89`)
   with `G` from the uniform H³ sup-gradient bound and `K` from `tensorNorm_bound`
   for the limit; convergence in `C([0,T],L²)` with order-1 jet control. The
   residual question moves *down* one level, to
   `OrdinaryCauchyInterpolation.lean:91` / `SobolevCauchyInterpolation.lean:78`
   (the interpolation lemma that replaces Rellich compactness).
2. **[RESOLVED by the delegated read — kept for the record, and my guess was wrong]
   `Evolution.rescale` (`Euler/OrdinaryEulerRescaling.lean:29`) is the one place
   in `exists_smooth_endpoint` where an `Evolution` is *constructed* rather than
   received.** Lean checked its `time_law` field, so there is no gap; the risk is
   a wrong Euler scaling normalisation (`u_c(t,x) = c·u(ct,cx)` vs `c·u(c²t,cx)`
   etc.), which would make `rescale` a correct theorem about a *non-Euler* object.
   *Question:* is the implemented scaling an exact symmetry of the incompressible
   Euler system as encoded in `time_law`, with the chain-rule factors matching,
   and does `c·t` stay in `[0,S]` for `t ∈ [0,T]` given `hct`?
   *What would settle it:* the definition of `rescale`'s `time_law` field and the
   lemma it cites, checked factor by factor against `time_law`'s statement.
   *Settled:* the implemented symmetry is `u_c(t,x) = c·u(ct,x)`,
   `P_c = c²·P(ct)` — amplitude + time only, no spatial dilation — which I
   verified by hand to be an exact symmetry of `time_law`; both `c` factors are
   produced by `HasDerivAt.scomp`/`const_smul` and the domain conditions come
   from `hc`/`hct`. See the second sub-chain block above.
3. **`private local instance : Fact (0 < (1:ℝ))` at `Euler/OrdinaryStrongTime.lean:18`.**
   This is a *local* `Fact` instance used to make `Lp … 1` typecheck in the
   Sobolev-lift machinery (`valueOperator 1 q`, `value_injective 1`). A `Fact`
   instance is exactly the mechanism by which a file can silently select a
   different `Lp` exponent or a different `NormedSpace` structure than the rest of
   the development, which would break the intended reading of
   `pointwise_derivative_of_l2` without breaking elaboration.
   *Question:* is the `1` in `valueOperator 1 q` / `observation 3` the same
   normalisation as the `L2` used in `Evolution.velocityPath` and
   `SmoothL2Field.toLp`? *What would settle it:* the definitions of
   `valueOperator`, `value_injective`, `observation`, `ordinaryLift` and their
   ambient exponent, plus a check that `observation 3 (le_refl 3) (x, 0 : AddCircle 1)`
   really is the Sobolev evaluation functional at `x` (note the second
   coordinate is a point of `AddCircle 1` — a cylinder domain — which I could not
   reconcile with `Space` from my scope).
4. **`smoothField_eq_of_toLp_eq` (`Euler/OrdinaryEulerUniqueness.lean:15`)** is
   used at `OrdinaryEulerEndpoint.lean:72` to turn an L²-class equality into an
   equality of smooth fields; that is the step that upgrades "the limit's initial
   datum equals `A` a.e." to "equals `A`". *Question:* does it use continuity of
   both representatives (a.e.-equal continuous functions are equal), and is the
   measure `volume` on `Space` genuinely such that a.e. determines continuous
   representatives? *What would settle it:* the 15-line proof and the
   `toLp_ae`/`smooth` fields of `SmoothL2Field`.
5. **`CONE.csv` false negatives (see D.1)** — an audit-instrument bug, not an
   artifact defect, but it can cause other workers to skip load-bearing lemmas.
   *What would settle it:* regenerate the cone with dot-notation resolution
   (resolve `X.f` against the namespace of `X`'s type), or treat `in_cone=False`
   as "unknown" for any declaration in a `namespace` matching its first argument's
   type.

## Residue — what I could NOT check, and why

* **No build.** There is no compiled Mathlib on this box (disk full), so I could
  not run `lake build`, `#print axioms`, or `set_option pp.all` on anything.
  Every statement above is from reading source text. In particular I cannot rule
  out that a name I read resolves to a *different* declaration than the one I
  found by `grep` (namespace shadowing, `export`, `open` aliasing). The scope
  files open 8-10 namespaces each (`OrdinaryEulerCauchy.lean:11-13`,
  `OrdinaryEulerEndpoint.lean:14-16`), so this risk is real but unquantified.
* **`SmoothL2Field` internals.** I took `field`, `smooth`, `toLp`, `jetLp`,
  `integrable`, `toLp_ae` on faith as the fields of a real structure. If
  `SmoothL2Field` were degenerate (e.g. `field` not actually tied to `toLp`), the
  whole reading changes. Not in my scope; flagged for whoever audits
  `EulerLpTranslation`.
* **The Sobolev-embedding constants.** `smoothEmbeddingConstant`
  (`EulerProof.lean:8227`) and `tameEnergyConstant` (`OrdinaryTameEnergy.lean:86`)
  were not opened; I only checked that they are used with a nonnegativity lemma
  and never need to be evaluated.
* **`higher_energy_of_h3` / `l2_stability` interiors.** I read their statements
  and top-level proofs (`OrdinaryEulerHigherEnergy.lean:101-107`,
  `OrdinaryEulerL2Stability.lean:127-146`) but not the energy-identity chain
  below them (`integer_energy_uniform`, `l2_energy_bound`). Those are Grönwall
  arguments whose failure would break `all_order_bounds_of_h3` and
  `cauchyPath_of_initial`; the sibling reports `euler-spine.md` /
  `euler-spine-bkm.md` cover part of that territory.
* **`restrictTime`, `velocity_eq_of_initial`, `pressure_eq_of_initial`** (used by
  `endpoint_matches_partial`) were not re-derived; they belong to the
  `euler-spine-uniqueness` worker.
* **The `Icc`-endpoint upgrade of `time_law`** (`SmoothFieldSobolevTime.lean:96`)
  and **the Sobolev interpolation lemmas** that replace Rellich compactness
  (`OrdinaryCauchyInterpolation.lean:91`, `SobolevCauchyInterpolation.lean:78`)
  are unaudited by me and by both children. They are Escalations 6 and 7 and are
  now the two lowest unexamined load-bearing points under this construction.
* **Numerical/kernel behaviour of `Fin n → Fin 3` sums at concrete `n`.** In my
  scope `n` is always symbolic. Elsewhere (`wordEnergy 3`, `tensorNorm 3`) a
  literal `3` appears; if some *other* file closes such a goal by `decide` or
  `rfl`, the kernel would enumerate up to 27 functions. That is cheap, but I did
  not survey it repo-wide — that is the `decide-bignum` workers' territory.

6. **The `Ioo`-vs-`Icc` endpoint of `time_law` (`OrdinaryEulerDifference.lean:28`,
   upgrade at `Euler/SmoothFieldSobolevTime.lean:96`).** `time_law` only asserts a
   derivative on the *open* interval, but the H³ Grönwall arguments that produce
   the uniform bound `M` (and hence the compactness) integrate from `t = 0` and
   therefore need a within-`Icc` derivative at the left endpoint. Some lemma must
   bridge that, and it was not audited by either me or the children.
   *Question:* does the bridge use continuity of the jets on the closed interval
   plus the mean-value/`hasDerivWithinAt_of_tendsto` route (valid), or does it
   quietly assume the endpoint derivative? *What would settle it:*
   `SmoothFieldSobolevTime.lean:96` and its callers in
   `OrdinaryEulerHigherEnergy.lean:42,48`.

7. **The interpolation lemma that replaces Rellich compactness**
   (`Euler/OrdinaryCauchyInterpolation.lean:91`,
   `Euler/SobolevCauchyInterpolation.lean:78`). Per the first sub-chain, the whole
   compactness engine is "uniform bound at order `q+1` + L² Cauchy ⟹ Cauchy at
   order `q`". That is true for a *fixed* function via interpolation
   (`‖v‖_{H^q} ≤ ‖v‖_{L²}^θ‖v‖_{H^{q+1}}^{1-θ}`), and it is genuinely what makes
   this development avoid Rellich — but the exponent bookkeeping is where such an
   argument usually goes wrong. *Question:* is the interpolation inequality stated
   with correct exponents and applied to the *differences* `u_j − u_k`?
   *What would settle it:* the two lemma statements plus the θ arithmetic.
