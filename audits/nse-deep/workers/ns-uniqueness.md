# NS uniqueness — the load-bearing step of the Navier–Stokes half (worker: ns-uniqueness)

Target: `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5` (clone of
openai/NavierStokesAndEuler). **Nothing under that path was modified.** No `lake build`
(no built Mathlib on this box): this is **source-level reading** of actual statements and
actual proof terms/tactics. Every line citation below was re-read in the original file.

Question set from the parent: (A) exact statement + competitor class of
`candidate_global_agrees_before_one`; (B) the energy/Grönwall argument line by line;
(C) the pressure recovery; (D) kernel-risk pass; (E) `CONE.csv` cross-check.

---

## Scope

**The uniqueness subtree is exactly 67 local modules / 13,049 lines / 939 declarations.**
Computed as the transitive `import` closure of `NavierStokes.R3.WholeSpaceUniqueness`
(recomputed from source; the closure of `NavierStokes.R3.CandidateBreakdown` adds only itself,
68). Declaration count = comment-stripped
`theorem|lemma|def|abbrev|structure|inductive|instance|class` matches, and it agrees
exactly with `CONE.csv`'s row count for the same 67 files (939).

Read **line by line, in full** by me (15 files, **161 declarations**):

| file | decls | note |
|---|---|---|
| `NavierStokes/R3/WholeSpaceUniqueness.lean` | 3 | the answer to (A) |
| `NavierStokes/R3/WholeSpaceComparisonClosure.lean` | 2 | the energy closure, (B) |
| `NavierStokes/R3/WholeSpaceEnergyLimit.lean` | 4 | Grönwall + `R→∞`, (B) |
| `NavierStokes/R3/ComparisonGronwall.lean` | 7 | the scalar Grönwall, (B) |
| `NavierStokes/R3/ComparisonRateBound.lean` | 3 | the Young absorption, (B) |
| `NavierStokes/R3/LocalizedDifferenceEnergy.lean` | 12 | the energy identity, (B) |
| `NavierStokes/R3/LocalizedTransport.lean` | 5 | the two integrations by parts |
| `NavierStokes/R3/ComparisonSetup.lean` | 11 | all the energy/norm definitions |
| `NavierStokes/R3/ComparisonCutoffs.lean` | 51 | the weight `χ_R`, all its estimates |
| `NavierStokes/R3/CompactComparisonBounds.lean` | 9 | candidate-side constants |
| `NavierStokes/R3/CandidateBreakdown.lean` | 4 | the consumer of (A) |
| `NavierStokes/R3/ProblemStatement.lean` | 25 | the competitor class |
| `NavierStokes/R3/ComparatorBridge.lean` | 3 | challenge structure → competitor class |
| `NavierStokes/R3/Theorem.lean` | 6 | the ν-general reduction |
| `NavierStokes/ComparatorDefinitions.lean` | 16 | the challenge structures themselves |

Read **partially** (statement + the specific proof I needed): `LocalizedLaplacian.lean:100-153`,
`PeriodicUniqueness.lean:40-140` and `:307-330`, `CompactEnergy.lean:94-150`,
`ViscosityScaling.lean:24-32,141-196`, `SpatialEnergyScaling.lean:19-51`,
`PressureRecovery.lean:1-80` (the `Hypotheses` structure), `ComparatorR3Bridge.lean` (full, 4).

Delegated to three read-only children (their reports are separate files; findings folded into
"Corroboration" below): `ns-uniqueness-pressure.md` (`PressureRecovery` /
`HarmonicTestFunctionals` / Riesz, question C), `ns-uniqueness-flux.md` (`PressureFlux.lean`,
600 lines, the `hpressure` hypothesis), `ns-uniqueness-estimates.md`
(`LocalizedFluxEstimates` / `WeightedSobolev` / `ComparisonYoung` / `ComparisonFiniteEnergy`).

Instrument work (grep/python over all 67 files): kernel-risk census (D) and the `CONE.csv`
cross-check (E), both below.

---

## The chain, in the order the kernel would check it

```
R3/ComparatorBridge.lean:77  comparator_of_breakdown          -- exhibits u₀ ≡ 0, force toComparator f
  :88   hglobal ⟨globalSolutionOfComparator hv⟩               -- challenge structure -> competitor class
R3/Theorem.lean:26  theorem_1_1_with_initial_rest
  :36   hc.no_global_solution_one ⟨normalized_global_solution hν v⟩   -- ν -> 1 by SPACE-only rescale
R3/CandidateBreakdown.lean:43  no_global_solution_one
  :49   h.not_global_agreement v.velocity_smooth (WholeSpaceUniqueness.candidate_global_agrees_before_one h v)
R3/WholeSpaceUniqueness.lean:104 candidate_global_agrees_before_one   <-- THE step
  :113  candidate_unique_on_Icc (:72)  with T := t < 1
  :86   classical_uniqueness_on_Icc (:30)
  :64   WholeSpaceComparisonClosure.eq_of_pressure_flux_bound (:32)
          :68  WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound (:70)
                 ComparisonGronwall.le_div_radius_of_deriv_le (:105)   -- Grönwall on [0,T]
                 WholeSpaceEnergyLimit.eq_zero_of_radius_bound (:53)   -- R -> ∞, dominated convergence
          :140 ComparisonRateBound.exists_uniform_rate_bound (:127)    -- Young absorption of the flux
          :135 LocalizedDifferenceEnergy.difference_energy_balance (:102)  -- the energy identity
          :49  hpressure  <- PressureFlux.exists_uniform_actual_pressure_flux_bound (:576)
                             <- PressureRecovery (Riesz + H⁻³ Liouville)
```

---

## (A) `candidate_global_agrees_before_one` — exact statement, and the competitor class

`NavierStokes/R3/WholeSpaceUniqueness.lean:104-107`, verbatim:

```lean
theorem candidate_global_agrees_before_one {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties 1 u p f K)
    (v : GlobalFiniteEnergySolution 1 f) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v.velocity (t, x)
```

Two hypotheses, no more: the candidate's own `CandidateProperties 1 u p f K`
(`R3/ProblemStatement.lean:92-109`) and **one bundled competitor**
`GlobalFiniteEnergySolution 1 f` (`R3/ProblemStatement.lean:125-135`). Conclusion is
agreement at **every** `t ∈ [0,1)` and **every** `x`. Viscosity is literally `1` — the
general-ν case is reduced to ν = 1 elsewhere (see below).

**The competitor class, field by field** (`R3/ProblemStatement.lean:125-135`):
`velocity`, `pressure`; `velocity_smooth`/`pressure_smooth : ContDiffOn ℝ ∞ · futureDomain`
(`futureDomain = Ici 0 ×ˢ univ`); `zero_initial_velocity : ∀ x, velocity (0,x) = 0`;
`divergence_free : ∀ t ∈ Ici 0`; `navier_stokes : ∀ t ∈ Ioi 0, residual 1 v q t x = f (t,x)`;
`energy_bounded : UniformFiniteEnergy (Ici 0) velocity`, i.e. (`:81-83`)
`∃ E ≥ 0, ∀ t ≥ 0, SquareIntegrableAtTime v t ∧ (1/2)∫‖v(t,x)‖² ≤ E`.
**There is no support, decay, periodicity, pressure-growth, derivative-growth, mild-solution,
energy-inequality or Leray-class hypothesis.** The docstring at `:119-124` claims exactly this
and, unusually, the claim is TRUE of the structure as written.

**Is that class the challenge's class? Yes — the bridge adds nothing.**
`NavierStokes/R3/ComparatorBridge.lean:48-74` `globalSolutionOfComparator` takes
`Comparator.NavierStokesExistenceAndSmoothnessRn ν (fun _ => 0) (toComparator f) v p`
and produces `GlobalFiniteEnergySolution ν f`, field by field:
* `velocity_smooth`/`pressure_smooth` from `h.velocity_smooth`/`h.pressure_smooth` via
  `fromComparator_smooth` (only a coordinate swap `(x,t) ↦ (t,x)`; challenge smoothness is on
  `univ ×ˢ Ici 0`, `ComparatorDefinitions.lean:76,79`);
* `zero_initial_velocity` **is literally `h.initial_condition`** (`:56`) — u₀ ≡ 0;
* `divergence_free` from `h.div_free` through `divergence_eq` (`:57-60`);
* `navier_stokes` from `comparator_equation_Rn` (`ComparatorR3Bridge.lean:34-47`), which
  rewrites `derivWithin _ (Ici 0)` → `deriv` for `t>0`, `Δ` → coordinate Laplacian using the
  competitor's OWN `velocity_smooth`, and `gradient` → `pressureGradient`. Note the direction
  of loss is safe: the challenge gives the PDE for all `t ≥ 0`, the competitor class only asks
  `t > 0`;
* `energy_bounded` from `h.integrable` + `h.globally_bounded_energy`
  (`ComparatorDefinitions.lean:94,97`: `∀ t ≥ 0, MemLp (‖v · t‖) 2` and
  `∃ E, ∀ t ≥ 0, ∫‖v x t‖² < E`) — `:64-74`, with `E ↦ max 0 (E/2)`.

So **the competitor class is exactly the Clay/challenge (C) solution class, not a subclass.**
The `MemLp`/`SquareIntegrableAtTime` field is the one that could have been a smuggled extra
hypothesis, and it is not: it is condition 7 of the challenge structure, present in
`ComparatorChallenges/NavierStokes.lean` too (byte-identical region, three independent diffs
by prior workers). **Verdict [OK]** on the class question — this is *not* a
"non-existence in a subclass" claim. That is a genuinely strong architectural result and the
single most important positive finding of this report.

**General ν.** `R3/Theorem.lean:26-36` exhibits the ν-candidate `scaledVelocity ν u` and
kills a ν-competitor by `hc.no_global_solution_one ⟨normalized_global_solution hν v⟩`.
`ViscosityScaling.lean:182-195` `normalized_global_solution` maps a
`GlobalFiniteEnergySolution ν (scaledVelocity ν f)` to a `GlobalFiniteEnergySolution 1 f`
through `rescale_global_solution` (`:141-160`), where `rescale a b g z = a • g (z.1, b • z.2)`
(`:24-25`) is **space-only** — time is untouched, so the singular time stays exactly 1. The
energy field survives by `UniformFiniteEnergy.spatial_smul`
(`SpatialEnergyScaling.lean:40-50`) with the exact Jacobian factor
`‖a‖² * |(b³)⁻¹|` proved in `kineticEnergy_spatial_smul` (`:27-36`, via
`Measure.integral_comp_smul` and `finrank ℝ Space = 3`). No hypothesis is added or dropped.
**[OK]**

**How agreement becomes non-existence.** `R3/CandidateBreakdown.lean:18-40`
`not_global_agreement`: bound the competitor on the compact set `Icc 0 1 ×ˢ K` by
`exists_bound_of_continuousOn` (`:26-27`), pick `(t,x)` with `t ∈ Ioo 0 1` and
`‖u(t,x)‖ > max M 1` from `speed_unbounded` (`:31`), show `x ∈ K` from `velocity_support`
(`:32-38`), rewrite by the agreement and contradict. Airtight, and note it needs the
agreement only on `[0,1)` — never at `t = 1`. **[OK]**

---

## (B) The energy comparison, line by line

**Norm and functional.** `ComparisonSetup.lean:37-51`: `weightedEnergy χ w t = ∫ χ(x)‖w(t,x)‖²`,
`weightedEnergyRate χ w t = ∫ χ(x)·2⟪w,∂ₜw⟫`, `weightedDissipation χ w t = ∫ χ·Σᵢ‖∂ᵢw‖²`,
`dissipationRoot φ w t = √(weightedDissipation (φ⁸) w t)`,
`cutoffL6 φ w t = ‖φ⁴w‖_{L⁶}`. The comparison is in **localized L²** of the difference
`w = u - v`, with weight `χ_R = cutoff R ^ 8` (`ComparisonCutoffs.lean:35`).

**Why nothing is junk-valued.** `cutoff R` is a `ContDiffBump` dilate: smooth, `0 ≤ · ≤ 1`,
`= 1` on `‖x‖ ≤ R`, `= 0` for `‖x‖ ≥ 2R`, compact support
(`ComparisonCutoffs.lean:25-107`). Therefore every integral above is an integral of a
**continuous, compactly supported** function, hence honestly integrable
(`LocalizedDifferenceEnergy.lean:34-50`), and the `ENNReal.toReal` in `comparisonLpNorm`
(`ComparisonSetup.lean:28-29`) cannot silently be `0`-from-`∞` for `cutoffL6`. The
`R`-uniformity of the derivative constants is proved, not assumed:
`cutoff_iteratedFDeriv_le` (`:170-188`) gives `‖∇ⁿχ‖ ≤ derivativeConstant n / Rⁿ` by
`iteratedFDeriv_comp_right` on the dilation, and `derivativeConstant n`
(`:143-158`) is `Classical.choose` of an existence statement proved from compact support +
continuity of `iteratedFDeriv`. **[OK]** — a real constant with a real bounding property, not
a postulate.

**The identity** (`LocalizedDifferenceEnergy.lean:102-121`, `difference_energy_balance`):
```
(1/2)·rate(χ,w,t) + dissipation(χ,w,t)
  = -∫ χ ⟪w, (∇u)·w⟫  +  (1/2)∫ ‖w‖² Δχ  +  (1/2)∫ ‖w‖² ⟨∇χ, v⟩  +  ∫ (p-q) ⟨∇χ, w⟩
```
Its hypotheses are only: `χ` smooth with compact support; `u,v,p,q` smooth **spatial slices**
at the single time `t`; time-differentiability of `u,v` at `t`; both fields divergence-free at
`t`; and the residuals equal at `t`. **No integrability and no support hypothesis on `u,v,p,q`**
— the docstring at `:100-101` says so and it is true, because every integrand carries `χ`.
Mechanism, checked term by term:
* the pointwise difference equation `∂ₜw = Δw - (∇u)w - (∇w)v - ∇(p-q)` is
  `PeriodicUniqueness.lean:112-138 difference_equation`, which is honest algebra on the two
  residuals plus `advection_difference` (`:62-70`), i.e. the *favourable* splitting
  `(u·∇)u - (v·∇)v = (∇u)w + (∇w)v`; **[OK]**
* Laplacian term: `LocalizedLaplacian.lean:125-151` `integral_weighted_laplacian`, two
  integrations by parts, result `-∫χΣ‖∂ᵢw‖² + (1/2)∫‖w‖²Δχ`. Sign of the dissipation is
  **negative**, i.e. it is retained on the good side. **[OK]**
* transport term: `LocalizedTransport.lean:66-79` `integral_weighted_transport` gives
  `∫χ⟪w,(∇w)v⟫ = -(1/2)∫‖w‖²⟨∇χ,v⟩` using **only** `div v = 0` and compact support of `χ`
  (via `CompactEnergy.integral_fderiv_apply`, `CompactEnergy.lean:94-117`, itself a
  compact-support divergence theorem). **[OK]**
* pressure term: `LocalizedTransport.lean:83-89` `integral_weighted_pressure`,
  `∫χ⟨∇(p-q),w⟩ = -∫(p-q)⟨∇χ,w⟩`, using `div w = 0` and compact `χ`. The docstring's claim
  "the pressure need not have compact support or satisfy any bound at infinity" is **true as
  stated**: the boundary term is killed by `χ`, not by decay of `q`. **[OK]** This is exactly
  the place where a fake uniqueness proof would have assumed pressure decay, and it does not.
* differentiation under the integral sign: `weightedEnergy_hasDerivAt` (`:74-85`) via
  `CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt` with the compact
  support of `χ` supplying the dominating function. **[OK]**

**The estimate and the absorption.** `WholeSpaceComparisonClosure.lean:32-53`
`eq_of_pressure_flux_bound` assembles: the coupling term `-∫χ⟪w,(∇u)w⟫ ≤ G·(weighted energy)`
with `G` an **L∞ bound on the CANDIDATE's gradient** (`hG`), the `Δχ` term `≤ C·M²/R²`, the
`∇χ·v` term `≤ 8·c₁M^{3/2}/R · B^{3/2}`, and the pressure flux `≤ CP·pressureEnvelope R A B`
with `pressureEnvelope R A B = (B^{1/2}+1)(A/R + 1/R²) + R^{-7/4}B^{3/4}` (`:25-27`).
Then `ComparisonRateBound.exists_uniform_rate_bound` (`ComparisonRateBound.lean:127-148`)
converts `(1/2)E' + A² ≤ G·E + C₀/R² + C₁/R·B^{3/2} + C₂·envelope` into
`E' ≤ 2G·E + D/R`, with **`δ = 1/2` of the dissipation `A²` used for absorption** and the
Sobolev link `B ≤ S(A + M/R)` (`:34`) as a hypothesis of the absorption lemma. I checked the
arithmetic by hand: `(1/2)E' ≤ G·E + C₀/R + D/R - A² + (1/2)A²`, so the dissipation is absorbed
**with the right sign and with half of it to spare**. The `Q := max 1 (S·max 1 M)` device
(`:38-54`) makes the constant independent of `R`, and every `rpow` step is a real
`Real.rpow_le_rpow` monotonicity, `p ≤ 2` (`rpow_le_square_mul_rpow`, `:17-27`). **[OK]**

**Grönwall.** `ComparisonGronwall.lean:24-61` `exp_neg_mul_le_of_deriv_le` is a real
integrating-factor argument: `G(t) = e^{-Kt}E(t) - εt` is shown `AntitoneOn (Icc 0 T)` by
`antitoneOn_of_hasDerivWithinAt_nonpos`, with the derivative needed only on `interior = Ioo 0 T`
and continuity on the closed `Icc 0 T`. `le_div_radius_of_deriv_le` (`:105-115`) then gives
`E(t) ≤ (C·T·e^{KT})/R` for all `t ∈ Icc 0 T`, from `E 0 = 0`.
**Answer to the parent's (B) question:** the Grönwall inequality is applied on the **closed**
interval `[0,T]` with `T = t < 1` chosen by the caller
(`WholeSpaceUniqueness.lean:113`, `candidate_unique_on_Icc … hT : T < 1`), i.e. **never up to
the blow-up time**, and never at `T = 1`. Since agreement is only needed on `[0,1)`
(`R3/CandidateBreakdown.lean:18`), no uniformity as `T → 1⁻` is required — the constants
`G(T)`, `D(T)` may blow up as `T → 1` and the argument is unaffected. This is the correct
architecture, and I re-derived it rather than taking the docstring's word. **[OK]**

**Removing the cutoff.** `WholeSpaceEnergyLimit.lean:70-91` `eq_zero_of_weighted_rate_bound`
feeds Grönwall and then `eq_zero_of_radius_bound` (`:53-66`): `∫ χ_R‖w‖² ≤ D/R` for all large
`R`, `∫ χ_R‖w‖² → ∫‖w‖²` by **dominated convergence** with dominating function `‖w‖²`
(`integral_weight_tendsto`, `:25-38` — legitimate exactly because `w(t,·) ∈ L²`, which for the
competitor is `energy_bounded`/`SquareIntegrableAtTime` and for the candidate follows from
compact support), so `∫‖w‖² ≤ 0`, hence `w(t,·) ≡ 0` by continuity
(`eq_zero_of_l2Sq_eq_zero`, `:40-49`). **[OK]**

**Is any integrability of the competitor ASSUMED rather than derived?** Only
`SquareIntegrableAtTime v t` + one uniform bound — and that is a *field of the challenge
structure* (condition 7), so it is given, not smuggled. Everything else about the competitor
that the argument uses is derived: `MemLp` of `u-v` (`ComparisonFiniteEnergy`), the `L²` bound
`M`, the `L¹` bound on the tensor difference `G₀`. The **candidate's** side
(`CompactComparisonBounds.lean`) is entirely derived from compact support + continuity:
`uniformFiniteEnergy_of_compact_slab` (`:133-155`), `exists_lpNorm_three_bound` (`:85-99`),
`exists_gradient_bound` (`:33-46`), `exists_radius_weight_derivative_zero` (`:112-129`, and it
correctly needs `R ≥ max 1 (C+1)` with `K ⊆ B_C` — it is *not* a for-all-`R` vanishing trick).
**[OK]**

---

## (C) The pressure

The competitor's pressure `q` enters the identity **only** through the flux term
`∫ (p-q)⟨∇χ_R, w⟩` (`LocalizedDifferenceEnergy.lean:121`), and `∇χ_R` is supported in the
annulus `R ≤ ‖x‖ ≤ 2R` with `‖∇χ_R‖ ≲ 1/R`. So the argument never needs the *value* of `q`,
only that the difference `p - q` is controlled on the annulus in a way that decays in `R` —
which is what `PressureFlux.exists_uniform_actual_pressure_flux_bound`
(`R3/PressureFlux.lean:576`) provides as the `hpressure` hypothesis
(`WholeSpaceComparisonClosure.lean:49-52`, quantified `∀ R ≥ 1, ∀ t ∈ Ioo 0 T`, with `CP`
produced **before** `R` and `t` — the quantifier order is right).

What I verified myself: the hypothesis bundle handed to the pressure machinery,
`PressureRecovery.Hypotheses` (`R3/PressureRecovery.lean:33-44`), has exactly ten fields —
`positive : 0 < T`, four `ContDiffOn ℝ ∞ · (slab 0 T)`, `div_u`, `div_v`, `equation`,
`energy_u`, `energy_v` — and at `WholeSpaceUniqueness.lean:46-47` every one of them comes from
the hypotheses of `classical_uniqueness_on_Icc`, with the candidate's `energy_u` **derived**
from compact support (`heu`, `:45`) and the competitor's `energy_v` being the challenge's own
condition 7. **So the pressure recovery is handed no extra decay/growth/regularity hypothesis
about the competitor.** The `H⁻³`/Liouville step therefore has to pin the pressure gauge using
only these — see the delegated report `ns-uniqueness-pressure.md` for whether it really does,
and `ns-uniqueness-flux.md` for the decay-in-`R` of the three envelope terms.

---

## (D) Kernel-risk pass over the whole 67-file uniqueness closure

Method: comment-stripped line scan (block and line comments removed) of all 67 files.

| vector | count | verdict |
|---|---|---|
| custom metaprogramming: `macro`/`elab`/`syntax`/`notation`/`set_option`/`axiom`/`unsafe`/`partial`/`sorry`/`deriving`/`native_decide` | **0** | vector (3) absent |
| `inductive` | **0** | — |
| `structure` (all non-recursive, fields are functions/Props) | 5: `ProblemStatement.lean:101`, `R3/ProblemStatement.lean:92,112,125`, `R3/PressureRecovery.lean:33` | vector (1) absent |
| `.rec` / `.recOn` / `motive` | **0** | no recursor reduction |
| `termination_by` / `decreasing_by` / `WellFounded` / `Acc.` / `.fix` | **0** | no WF unfolding |
| `Nat.pow/div/mod/gcd/beq/ble` | **0** | no GMP delegation |
| numerals: **largest literal anywhere in the 67 files is `40`** (`R3/PressureFluxTest.lean:193`); next `24` (`:192`), `12`, `9`, `8` | — | vector (2) effectively absent |
| `decide` | **6**, all of the form `zero_pow (by decide : (2:ℕ) ≠ 0)` / `(3:ℕ) ≠ 0` / one exponent comparison: `PeriodicUniqueness.lean:610`, `R3/CompactComparisonBounds.lean:68,145`, `R3/CompactForceBound.lean:39,50`, `R3/FourierSobolevWeights.lean:107` | trivial |
| `omega` | 2 (`R3/SmoothSobolevL6.lean:106`, `R3/WeightedSobolev.lean:45`), both discharging a small exponent side-goal `2 ≤ 6`-style | trivial |
| `norm_num` | 152 sites, all on small rational/`rpow` arithmetic (largest operand seen: `40`) | trivial |
| `Classical.choose` | 6 (`R3/ComparisonCutoffs.lean:151,154,158`, `R3/LocalizedFluxEstimates.lean:184,187,191`) | see below |
| `rfl` (tactic or term) | 83 sites, all on `EuclideanSpace`/`PiLp`/`ContinuousLinearMap` projection defeq (e.g. `LocalizedTransport.lean:40`, `CandidateBreakdown` none) — **no recursive data, no `Nat` arithmetic** | OK |

**Concretely: to accept this subtree the kernel must not reduce a single recursor application
of a recursive type, must not unfold a well-founded fixpoint, and must not evaluate any numeral
larger than 40.** The six `decide` sites each decide `(2 : ℕ) ≠ 0` or `(3 : ℕ) ≠ 0`, i.e. one
`Nat.beq` step on a literal below 4 — no GMP path of any interest. `Classical.choose` is used
only to *name* constants whose bounding property is proved immediately after
(`derivativeConstant`, `weightSecondDerivativeConstant`); it is not an axiom smuggle and it
carries no computation. Vectors (1) and (3) are **absent** from this scope; vector (2) is
present only in the degenerate sense that `norm_num` closes `(0:ℝ) < 1/2`-style goals.

---

## (E) `CONE.csv` cross-check — a framework-level finding, stated loudly

Of the **939** declarations in the 67-file uniqueness closure, `audits/nse-deep/CONE.csv`
marks only **243 in-cone and 696 out-of-cone** — and among the out-of-cone ones are:

| decl | file:line | CONE.csv `in_cone` |
|---|---|---|
| `…WholeSpaceUniqueness.candidate_global_agrees_before_one` | `R3/WholeSpaceUniqueness.lean:104` | **False** |
| `…WholeSpaceUniqueness.candidate_unique_on_Icc` | `:72` | **False** |
| `…WholeSpaceUniqueness.classical_uniqueness_on_Icc` | `:30` | **False** |
| `…CandidateProperties.no_global_solution_one` | `R3/CandidateBreakdown.lean:43` | **False** |
| `…CandidateProperties.not_global_agreement` | `R3/CandidateBreakdown.lean:18` | **False** |
| `…WholeSpaceComparisonClosure.eq_of_pressure_flux_bound` | `R3/WholeSpaceComparisonClosure.lean:32` | **False** |
| `…WholeSpaceEnergyLimit.eq_zero_of_weighted_rate_bound` | `R3/WholeSpaceEnergyLimit.lean:70` | **False** |
| `…PressureFlux.exists_uniform_actual_pressure_flux_bound` | `R3/PressureFlux.lean:576` | **False** |
| `…LocalizedDifferenceEnergy.difference_energy_balance` | `R3/LocalizedDifferenceEnergy.lean:102` | **False** |

**This is a false negative of `audits/cone.py`, not dead code.** Root cause, at
`audits/cone.py` in the reference resolver: a token is resolved by exact match in `byfull` or
by SUFFIX match, but Lean **dot notation on a hypothesis** produces the token
`hc.no_global_solution_one` (`R3/Theorem.lean:36`) / `h.not_global_agreement`
(`R3/CandidateBreakdown.lean:49`) / `v.velocity_smooth`, and `hc.no_global_solution_one` is
neither a declared name nor a *suffix* of one, so the edge is dropped. The uniqueness subtree
hangs off the graph at **one** such edge (`R3/Theorem.lean:36`).

I verified this by re-running a patched resolver (which additionally tries every suffix of a
dotted token) over the same repo with three headline seeds
(`NavierStokes.Comparator.navier_stokes_breakdown_R3`, `…_periodic`, `Euler.euler_breakdown_R3`):

* repo-wide cone: **33,163 → 40,414 of 52,516** (63.1% → 77.0%), **+7,251** declarations;
* the 67-file uniqueness closure: **243 → 813 in-cone** of 939;
* every row of the table above flips `False → True`.

Recipe to reproduce: copy `audits/cone.py`, and in the resolver replace
`r = {t} if t in byfull else suffix.get(t, frozenset())` by a version that also unions
`suffix.get(".".join(t.split(".")[j:]))` for `j = 1 …`; run with the three seeds above.
(I ran exactly this as a scratch script and deleted it; it wrote `/tmp/CONE_dot.csv`.)

**Consequence for the whole audit:** `in_cone = False` in the current `CONE.csv` must NOT be
used to deprioritise anything, and the published denominator "22,643 in-cone theorems" is an
**under**-count (the patched run gives 28,959 in-cone theorems). The suffix
over-approximation the tool documents does not compensate for this, because the dropped token
never reaches the suffix map at all. `FINDINGS.md:220-238` documents the instance-synthesis
blind spot but not this one.

The remaining 126 still-out-of-cone declarations in the closure do look like genuine spares
(`ComparisonCutoffs.multiplier_*`, `cutoff_laplacian_le`, `ComparisonGronwall.
eq_zero_of_forall_radius_bound`, `l2Sq_nonneg`, …) — i.e. after the fix the triage signal
becomes informative again.

---

## Per-declaration findings

| # | declaration | file:line | statement (my words) | mechanism | verdict |
|---|---|---|---|---|---|
| 1 | `candidate_global_agrees_before_one` | `R3/WholeSpaceUniqueness.lean:104` | candidate = any global finite-energy competitor at every `t<1`, all `x` | for each `t<1` apply `candidate_unique_on_Icc` with `T := t`; restrict competitor's `Ici 0` energy bound to `Icc 0 t` (`.mono`), restrict smoothness `slab 0 t ⊆ futureDomain` | OK |
| 2 | `candidate_unique_on_Icc` | `:72` | same on a closed `[0,T]`, `T<1` | feeds `classical_uniqueness_on_Icc`; candidate's fields restricted from `Ico 0 1` via `ht.2.trans_lt hT`; handles `T ≤ 0` separately by the shared zero datum (`:98-100`) | OK |
| 3 | `classical_uniqueness_on_Icc` | `:30` | smooth + compactly-supported `u` vs smooth uniform-finite-energy `v`, same residual, same datum ⇒ equal on `[0,T]` | builds `PressureRecovery.Hypotheses` (`:46-47`), derives `M`,`U`,`G₀`,`CP`,`G`,`R₀`, then `eq_of_pressure_flux_bound` | OK |
| 4 | `eq_of_pressure_flux_bound` | `R3/WholeSpaceComparisonClosure.lean:32` | with the pressure flux bounded by `CP·envelope`, the localized energy vanishes | energy identity + 4 flux bounds + Young absorption + Grönwall + `R→∞`; `convert! hsum using 1; ring` for the final algebra | OK |
| 5 | `pressureEnvelope` | `:25` | `(B^½+1)(A/R+1/R²)+R^{-7/4}B^{3/4}` | definition | OK |
| 6 | `eq_zero_of_weighted_rate_bound` | `R3/WholeSpaceEnergyLimit.lean:70` | differential inequality `E' ≤ K·E + C/R` + `E(0)=0` + `w(t,·) ∈ L²` ⇒ `w ≡ 0` on `[0,T]` | Grönwall then dominated convergence in `R` | OK |
| 7 | `eq_zero_of_radius_bound` | `:53` | `∫χ_R‖w‖² ≤ D/R` for all large `R`, `w` continuous and `L²` ⇒ `w ≡ 0` | `integral_weight_tendsto` + `le_of_tendsto_of_tendsto` + `integral_eq_zero_iff_of_nonneg` | OK |
| 8 | `integral_weight_tendsto` | `:25` | `∫χ_R‖w‖² → ∫‖w‖²` | `tendsto_integral_filter_of_dominated_convergence`, dominator `‖w‖²` (needs `w ∈ L²`: supplied) | OK |
| 9 | `exp_neg_mul_le_of_deriv_le` / `le_div_radius_of_deriv_le` | `R3/ComparisonGronwall.lean:24,105` | perturbed Grönwall with interior-only derivative | integrating factor `e^{-Kt}E - εt` antitone on `Icc 0 T` | OK |
| 10 | `exists_uniform_rate_bound` | `R3/ComparisonRateBound.lean:127` | `(1/2)E' + A² ≤ G·E + flux ⇒ E' ≤ 2G·E + D/R` | Young absorption with `δ = 1/2`; `D` independent of `R,t` | OK |
| 11 | `exists_uniform_flux_absorption` | `:31` | all three envelope terms `≤ δA² + D/R` given `B ≤ S(A+M/R)` | monotone `rpow` reduction to `x = A + 1/R`, then `ComparisonYoung.exists_cutoff_absorption` | OK (Young step delegated) |
| 12 | `difference_energy_balance` | `R3/LocalizedDifferenceEnergy.lean:102` | the localized energy identity (see (B)) | pointwise difference equation + 3 integrations by parts, all integrands cut off by `χ` | OK |
| 13 | `weightedEnergy_hasDerivAt` / `_continuousOn` | `:74,62` | differentiate/continuity of `t ↦ ∫χ‖w‖²` | `CompactTimeIntegral` differentiation under the integral, compact `χ` as dominator | OK |
| 14 | `integral_weighted_transport` | `R3/LocalizedTransport.lean:66` | `∫χ⟪w,(∇w)v⟫ = -(1/2)∫‖w‖²⟨∇χ,v⟩` | compact-support divergence theorem + `div v = 0` | OK |
| 15 | `integral_weighted_pressure` | `:83` | `∫χ⟨∇π,w⟩ = -∫π⟨∇χ,w⟩` | same, with `div w = 0`; **no decay of `π` used** | OK |
| 16 | `integral_weighted_laplacian` | `R3/LocalizedLaplacian.lean:125` | `∫χ⟪w,Δw⟫ = -∫χΣ‖∂ᵢw‖² + ½∫‖w‖²Δχ` | two integrations by parts per coordinate | OK |
| 17 | `difference_equation` | `PeriodicUniqueness.lean:112` | `∂ₜw = Δw - (∇u)w - (∇w)v - ∇π` | subtraction of residuals + `advection_difference` | OK |
| 18 | `cutoff`/`weight` + 49 estimates | `R3/ComparisonCutoffs.lean:25-271` | dilated `ContDiffBump`, `‖∇ⁿχ‖ ≤ cₙ/Rⁿ` | `iteratedFDeriv_comp_right` on the dilation; `cₙ` from compact support | OK |
| 19 | `uniformFiniteEnergy_of_compact_slab` | `R3/CompactComparisonBounds.lean:133` | candidate has uniform finite energy on `[0,T]` | continuity of `t ↦ ∫‖u‖²` on a compact interval + compact-support `MemLp` | OK |
| 20 | `exists_gradient_bound` | `:33` | `‖∇u‖ ≤ G` on `[0,T]×ℝ³` | compactness inside `K`, `fderiv_of_notMem_tsupport = 0` outside | OK |
| 21 | `exists_radius_weight_derivative_zero` | `:112` | for `R ≥ max 1 (C+1)`, `⟨∇χ_R, u(t,x)⟩ = 0` ∀x | inside `K`: `χ_R ≡ 1` near `x` so `∇χ_R = 0`; outside: `u = 0` | OK |
| 22 | `exists_lpNorm_three_bound` | `:85` | one `L³` bound for the candidate on `[0,T]` | continuity of `t ↦ ∫‖u‖³` + compact support | OK |
| 23 | `GlobalFiniteEnergySolution` | `R3/ProblemStatement.lean:125` | the competitor class | structure; **no decay/support/periodicity fields** | OK |
| 24 | `CandidateProperties` | `:92` | the candidate's 12 fields | structure | OK |
| 25 | `zero_force_has_global_solution` | `:189` | the competitor class is inhabited (zero fields, zero force) | explicit witness, `simp` on each field | OK (anti-vacuity certificate) |
| 26 | `no_global_solution_one` | `R3/CandidateBreakdown.lean:43` | candidate at ν=1 ⇒ no global finite-energy solution for its force | `not_global_agreement ∘ candidate_global_agrees_before_one` | OK |
| 27 | `not_global_agreement` | `:18` | candidate cannot agree with a competitor on `[0,1)` | compactness bound on `Icc 0 1 ×ˢ K` vs `speed_unbounded` | OK |
| 28 | `force_nonzero_of_no_global_solution` | `:53` | the exhibited force is not `≡ 0` | contradiction with `zero_force_has_global_solution` | OK (anti-vacuity) |
| 29 | `uniform_l2_sq_bound` | `:66` | restates the candidate's energy bound without the ½ | `linarith` | OK |
| 30 | `globalSolutionOfComparator` | `R3/ComparatorBridge.lean:48` | challenge structure ⇒ competitor class, same ν, same `f` | field-by-field, no added hypothesis | OK |
| 31 | `comparator_of_breakdown` | `:77` | exhibits `u₀ ≡ 0`, `toComparator f`, negates the challenge existential | `rintro` a comparator solution, feed it to #30 | OK |
| 32 | `forceConditionDecay_of_compact` | `:22` | compact support ⇒ the challenge's force decay condition | `CompactSpatialForceDecay.forceConditionDecay` | OK |
| 33 | `comparator_equation_Rn` | `ComparatorR3Bridge.lean:34` | the challenge PDE ⇒ the project's residual equation for `t>0` | `temporalDerivative_eq`, `laplacian_eq` (uses the competitor's own smoothness), `gradient_eq` | OK |
| 34 | `theorem_1_1_with_initial_rest` | `R3/Theorem.lean:26` | for every ν>0 a candidate + no global solution + rest before `3/8` | `ActualCandidate.selected_candidate_one_with_initial_rest` + `candidate_at_viscosity` + `normalized_global_solution` | OK (construction itself out of my scope) |
| 35 | `normalized_global_solution` / `rescale_global_solution` | `ViscosityScaling.lean:182,141` | a ν-competitor rescales to a 1-competitor | space-only dilation `rescale a b`, energy factor `‖a‖²|b³|⁻¹` proved | OK |
| 36 | `UniformFiniteEnergy.spatial_smul` / `kineticEnergy_spatial_smul` | `SpatialEnergyScaling.lean:40,27` | uniform finite energy survives dilation with the exact factor | `Measure.integral_comp_smul`, `finrank = 3` | OK |
| 37 | `PressureRecovery.Hypotheses` | `R3/PressureRecovery.lean:33` | the 10 hypotheses the pressure machinery gets | structure; nothing beyond smooth+div+equation+energy | OK |
| 38 | `NavierStokesExistenceAndSmoothnessRn` | `ComparatorDefinitions.lean:89` | the challenge's (C) solution class | structure, extends the base one; `integrable`, `globally_bounded_energy` | OK |

Verdict counts (my own 38 rows): **OK 38, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0.**
The one non-OK item in my scope is not a declaration but the framework's `CONE.csv`
(section (E)), and the three delegated sub-scopes are reported separately.

---

## Escalations

**U-1 (rank 1) — `CONE.csv` drops Lean dot-notation edges; the entire NS uniqueness spine is
mislabelled out-of-cone.** `audits/cone.py` resolver vs `R3/Theorem.lean:36`
(`hc.no_global_solution_one`). Repo-wide effect measured: cone 33,163 → 40,414 of 52,516.
*Question for an expert / maintainer:* should `cone.py` resolve dotted tokens by trying every
suffix of the token (safe over-approximation, consistent with the tool's stated philosophy)?
*What would settle it:* the patched run above, plus regenerating `CONE.csv` and re-checking
every "out of cone, therefore deprioritised" statement in `FINDINGS.md`.

**U-2 (rank 2) — the pressure gauge.** `R3/PressureFlux.lean:576` +
`R3/PressureRecovery.lean:407`. The competitor's `q` is only determined up to `c(t)`, and the
flux term `∫(p-q)⟨∇χ_R,w⟩` is NOT gauge-invariant term-by-term (it is, in exact arithmetic,
because `∫ c(t)⟨∇χ_R,w⟩ = c(t)∫⟨∇χ_R,w⟩ = -c(t)∫χ_R div w = 0` for `div w = 0` — so the gauge
freedom should cancel, and that cancellation is exactly `integral_weighted_pressure`).
*Question:* does `PressureRecovery` pin a canonical representative by Riesz + `H⁻³` Liouville
using ONLY the ten `Hypotheses` fields, or does some step require `q` (or `∇q`) to decay /
be `L²`? *ANSWERED by `ns-uniqueness-pressure.md`:* only the ten fields are used; the singular operator
is applied to the compact test function, the `H⁻³` Liouville step runs on the velocity side
with `L²`/`L¹` masses only (`PressureFunctionals.lean:169,279`,
`WeakFourierUniqueness.lean:75`), and the Poisson equation is derived by integration by parts
(`ConservativeDifference.lean:431`). **Downgraded to rank 4.** Residual for a build: an
`example` that adds `c(t)` to `q` and re-derives the same flux bound.

**U-3 (rank 3) — decay in `R` of the three `pressureEnvelope` terms.**
`WholeSpaceComparisonClosure.lean:25-27` and `PressureFlux.lean:397`. The middle term
`(B^{1/2}+1)·1/R²` and `R^{-7/4}B^{3/4}` must survive Young against `A²` uniformly in `t`.
I checked the absorption algebra (`ComparisonRateBound.lean:31-123`) and it is valid **given**
`B ≤ S(A + M/R)`; the risk is entirely in whether `PressureFlux` really proves the envelope
with an `R`-free and `t`-free `CP`. *ANSWERED by `ns-uniqueness-flux.md`:* `CP = 9·uniformCoefficient(M₀,U₀,G₀)` is `R`-free and
`t`-free and quantified before `R`,`t`; `R^{-7/4} = R^{-3/4}·1/R` exactly
(`PressureFlux.lean:445`). **Closed.**

**U-4 (rank 4) — `ComparisonYoung.exists_cutoff_absorption`** (`R3/ComparisonYoung.lean`, the
one step of the absorption I did not read myself). Exponents `3/2, 3/4, 1/2` against `A²` with
`x = A + 1/R` — a real Young computation with several `rpow` cases. *Question:* is any case
closed by an inequality that is false for small `A` (e.g. `x^{3/4} ≤ x^2 + 1` needs care at
`x < 1`)? *ANSWERED by `ns-uniqueness-estimates.md`:* valid for all `R ≥ 1` and all `A,B ≥ 0`; the
Sobolev constant is Mathlib's, not a postulate (`WeightedSobolev.lean:39,210`). **Closed.**

**U-5 (rank 5, low) — `speed_unbounded` is the only non-vacuity link.** My scope proves
"candidate = competitor on `[0,1)`"; the contradiction needs `SpeedUnboundedAtOne u`
(`ProblemStatement.lean:94-96`, consumed at `R3/CandidateBreakdown.lean:31`). That field's
proof lives in the construction (`ActualCandidate` / `FinalSlowBase.lean:361` per the
`ns-spine` reports), i.e. **outside** my scope. If that single field is wrong, the uniqueness
theorem is still true and the non-existence claim is empty. *What would settle it:* the
construction-side worker's verification of the divergent profile
`u(t,0) = (1-t)^{-A h}·j·e₂`.

---

## Corroboration from the delegated children

**`ns-uniqueness-estimates.md` (estimate layer, non-pressure) — 78 declarations read
line-by-line; OK 78, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0.** Independently confirms three
things I flagged as load-bearing:
* **The Sobolev inequality is DERIVED from Mathlib, not postulated.**
  `R3/WeightedSobolev.lean:39` applies Mathlib's
  `eLpNorm_le_eLpNorm_fderiv_of_eq_inner` with `p = 2, p' = 6` and `finrank ℝ Space = 3`
  (`:43`); `weightedSobolevConstant := 4 * sobolevConstant + 1` (`:210`) where
  `sobolevConstant` is Mathlib's `eLpNormLESNormFDerivOfEqInnerConst` (`:25`). So the constant
  `S` in `B ≤ S(A + M/R)` is a real Sobolev constant, closing the "postulated `0 < C`" worry.
* **`transport_flux_bound` exponents are exactly what Hölder + Sobolev give**
  (`R3/LocalizedFluxEstimates.lean:90`): `φ⁶‖w‖³ = ‖φ²w‖³`, split `1/3 = 1/4 + 1/12`, giving
  `‖w‖₂^{3/2}‖φ⁴w‖₆^{3/2}`, and `L = derivativeConstant 1 / R` — i.e. the
  `M^{3/2}B^{3/2}/R` of `WholeSpaceComparisonClosure.lean:125` is real, not fitted.
* **The Young absorption is valid for all `R ≥ 1` and all `A,B ≥ 0`**, `A²` enters with `+` on
  the left, `δ = 1/2`, and the leftover `-(1/2)A²` is dropped (a valid weakening) — matching my
  own hand-check of `ComparisonRateBound.lean:127-148`.
* `exists_radius_weight_derivative_zero` is threshold-quantified, not all-`R` (agrees with my
  row 21), and the difference's integrability is **derived** (`MemLp.sub`,
  `ComparisonFiniteEnergy.lean:53,80`) with `MemLp` returned alongside every norm bound
  (`:197,:214`) — so no `ENNReal.toReal ∞ = 0` junk path.
* Kernel risk in that sub-scope: 2 trivial `decide`, zero metaprogramming — consistent with my
  census.
* Its top escalation coincides with my **U-3**: the envelope's shape and `CP`'s `R`-uniformity
  are *hypotheses* at `WholeSpaceComparisonClosure.lean:25-52`; `PressureFlux` must deliver
  exactly them.

**`ns-uniqueness-flux.md` (`PressureFlux.lean` → the `hpressure` hypothesis) — OK 47,
UNCLEAR 1, KERNEL-RISK 0, SUSPICIOUS 0.** This closes my **U-3** and most of **U-2**:
* `PressureRecovery.Hypotheses` is confirmed to be exactly the ten fields I read
  (`R3/PressureRecovery.lean:33-44`) with **nothing about `q` at infinity**; the extra arguments
  of `exists_uniform_actual_pressure_flux_bound` (`R3/PressureFlux.lean:576-589`) — `M`, `U`,
  `G₀` — are **derived** at `WholeSpaceUniqueness.lean:54-59`
  (`ComparisonFiniteEnergy.lean:197,214` for the competitor's `L²`/tensor bounds; the
  candidate's `L³` bound from compact support). The competitor's pressure `q` enters only
  through (i) its smoothness, (ii) the PDE, which pins `∇(p-q)` pointwise, and (iii) pairings
  against **compactly supported** test functions (`PressureFluxIdentity.lean:41,114`).
* **The `R`-decay is real:** `1/R` and `1/R²` come from `cutoff_fderiv_le` /
  `cutoff_second_fderiv_le`, and `R^{-7/4} = R^{-3/4} · 1/R` exactly
  (`PressureFlux.lean:445`). `CP = 9 · uniformCoefficient(M₀,U₀,G₀)` is **`R`-free and
  `t`-free** and is quantified **before** `R` and `t` — exactly the quantifier order
  `WholeSpaceComparisonClosure.lean:49` needs. (The envelope alone is not `o(1)`: `A` and `B`
  themselves may grow with `R`, which is why the Sobolev link `hSob`
  (`WholeSpaceComparisonClosure.lean:90-103`) plus the Young absorption is required — and that
  absorption is the step the estimates child verified.)
* Integrability of every pairing is **derived** (`PressureFlux.lean:221-232,129,238`,
  `RieszPairing.lean:31`), so no bound holds vacuously through a `0`-valued Bochner integral of
  a non-integrable function.
* Its one UNCLEAR is cosmetic-but-worth-knowing: the exported statement drops the `Integrable`
  conjunct that is proved internally at `PressureFlux.lean:221`.
* Its remaining escalations: **the harmonic/Liouville step in `gradient_recovery`
  (`R3/PressureRecovery.lean:391-405`) is the only black box** in the pressure chain (this is my
  **U-2**, now sharpened to a 15-line target), and the heat-kernel commutator's `R^{-3/4}`
  (`R3/HeatKernelCommutator.lean:97`).

**`ns-uniqueness-pressure.md` (`PressureRecovery` + Riesz + Liouville, question C) — ~62
declarations; OK 61, UNCLEAR 1, KERNEL-RISK 0, SUSPICIOUS 0.** This **answers my U-2**:
* The theorem at `R3/PressureRecovery.lean:407` is `gradient_recovery` (C¹-twin at `:391`,
  export at `:419`). Its hypotheses are **only** the `Hypotheses` bundle (`:33-44`). For a
  compactly supported test `ψ` and interior `t` it proves
  `∫ ∂ₖ(p-q)·ψ = -Σ Re pressurePair(tensorDiff)(∂ₖψ)`, where `pressurePair` is
  `(-Δ)⁻¹∂ᵢ∂ⱼ` with symbol `-ξᵢξⱼ/|ξ|²` (`R3/ComparisonFourierSetup.lean:17-25`) and the
  singular operator is **always applied to the test function**, never to `q`.
* **The Liouville/`H⁻³` kill runs on the VELOCITY side, not the pressure side**: the functional
  built from time averages of `u-v` and `uᵢuⱼ-vᵢvⱼ` has its `H⁻³` bound from the `L²`/`L¹`
  masses alone (`R3/PressureFunctionals.lean:169,279`), giving an `L²` Fourier representative,
  then `q̂·(1+|ξ|²)²|ξ|² = 0` a.e. ⇒ `q̂ = 0` because `{0}` is null
  (`R3/WeakFourierUniqueness.lean:75`). Since `p-q` is only ever paired with compact `ψ`,
  **no term at spatial infinity appears and no decay hypothesis on `q` is needed**. The one
  extra `L³` bound (`PressureFlux.lean:581`) is on the **candidate** `u` and comes from its
  compact support (`WholeSpaceUniqueness.lean:57`) — allowed.
* The pressure Poisson equation is **derived, not assumed**: `weak_pressure_poisson`
  (`R3/ConservativeDifference.lean:431`) is an integration by parts from the residual equality.
* Minor items it raises: a bare `_` at `R3/RieszLinearityDecay.lean:81` that should be
  Riemann–Lebesgue's integrability side condition (mathematically true, unverifiable without a
  build); `ν = 1` is hard-wired in `PressureRecovery.lean:41` and consumed at
  `WholeSpaceUniqueness.lean:41` (harmless — the general-ν case is reduced to `ν = 1` in
  `R3/Theorem.lean:36`, which I verified, row 35); and the `ξ = 0` junk value `0/0 = 0`
  (`R3/RieszSymbolRegularity.lean:50`) used pointwise, harmless because a single point is null.

**Net effect of the three children on my verdicts:** nothing in the 67-file uniqueness closure
was found SUSPICIOUS or KERNEL-RISK by anyone. Aggregate across the four reports:
**OK 224, UNCLEAR 2, SUSPICIOUS 0, KERNEL-RISK 0** (my 38 + estimates 78 + flux 48 + pressure
62), with the two UNCLEARs both cosmetic (`PressureFlux.lean:221` export drops a proved
`Integrable` conjunct; `RieszLinearityDecay.lean:81` bare `_`).


---

## Residue — what I could NOT check

* **No build.** Everything here is source reading; I cannot rule out an elaboration-level
  surprise (implicit-argument capture, an ambient `simp` lemma changing a statement's meaning,
  a `change`/`convert!` that succeeds for a reason other than the one I read). Six `convert!`
  and eleven `change` sites in my scope were read as syntactic re-statements; a build would
  confirm.
* **4 of the 67 files' internals I delegated** (`PressureFlux.lean`, `PressureRecovery.lean`
  + helpers, `LocalizedFluxEstimates.lean`, `WeightedSobolev.lean`, `ComparisonYoung.lean`,
  `ComparisonFiniteEnergy.lean`, `ComparisonTimeAverages.lean` and the Riesz/HeatKernel
  cluster — roughly 5,500 of the 13,049 lines). Their verdicts are in the three sibling
  reports; where they disagree with me, believe them, since they read the lines.
* **The construction side** (`ActualCandidate`, `CandidateFromLimits`, `FinalSlowBase`, …) is
  out of scope by construction: I audited that *if* the candidate has its 12 properties, no
  challenge-class competitor exists. Whether the candidate exists and really blows up is the
  other half of the audit.
* **Statement fidelity to Clay** is not mine either; I only verified that the *challenge
  structure* maps into the competitor class without loss (`ComparatorDefinitions.lean:89-97`
  → `R3/ProblemStatement.lean:125`). Whether `ComparatorChallenges/NavierStokes.lean` faithfully
  encodes Fefferman's conditions 6-7 is the upstream question already raised as `ns-spine` E-1.
