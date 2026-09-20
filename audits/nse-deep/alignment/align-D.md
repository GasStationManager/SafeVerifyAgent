# align-D — paper §9, §10, Theorem 1.1 vs the Lean formalization

Auditor slice D. Read-only pass over `/home/user/openai/navierstokesandeuler`
(no writes) against `ns-paper.txt` (published PDF text, page markers).
Lean cites are `file:line`; paper cites are `p<page>`.

**Headline verdict.** For Theorem 1.1, Proposition 10.1, Lemmas 10.2–10.5 and
Corollary 10.6 I found **no case where the Lean statement is materially weaker
than the paper's**, and several where it is strictly stronger. The two clauses
the brief flagged as suspicious — `u₀ ≡ 0` and a time-compact force — are **the
paper's own claims**, in Theorem 1.1's own display and in its abstract, not a
Lean specialization. The genuine (small) divergences are listed in §4.

---

## 1. Summary table

| number | kind | page | Lean counterpart(s) `file:line` | class | one-line how |
|---|---|---|---|---|---|
| **1.1** | Theorem | p1 | `NavierStokes/R3/ProblemStatement.lean:92` (`CandidateProperties`), `:125` (`GlobalFiniteEnergySolution`), `:150` (`breakdownStatement`); `NavierStokes/R3/Theorem.lean:26,46` | **EXACT** (Lean stronger in 3 places) | every clause present; Lean adds initial-rest interval, dissipation bound, maximal H³ lifespan |
| **10.1** | Proposition | p117 | `NavierStokes/SpatialLocalization.lean:49,72,134,165-174` + `NavierStokes/TimeLocalization.lean:27,30,57,61,110-125` + `NavierStokes/R3/ActualCandidate.lean:40,51,59` + `NavierStokes/LocalAngularGrowth.lean:60` | **EXACT — split** | no single Lean theorem; the four conclusions are four theorems; cutoffs are fixed explicit choices (paper: "there are…", so instantiation is legal) |
| **10.2** | Lemma | p118 | `NavierStokes/JointResidualLimits.lean:81,84,120,126,130,148,156,220,227` | **EXACT — split, one wording gap** | `boundaryLimits_zero:126` is `∂ᵅF_j(0)=0`; convergence is stated **locally uniformly** (`:148`) / uniformly on compacts (`:156`), not "uniformly on ℝ³" |
| **10.3** | Lemma | p120 | `NavierStokes/CandidateFromLimits.lean:82,86,114,119,124,128`; `NavierStokes/R3/ActualCandidate.lean:67,78` (`PositiveTimeForce.force`) | **LEAN STRONGER** | `force_zero_from:114` gives support in `t ≤ 2` (= paper's `K×[0,2]`); Lean additionally proves `tsupport f ⊆ Ioi 0 ×ˢ univ`, which the paper *asserts* (`C∞_c(ℝ³×(0,∞))`) but whose literal Lemma 10.3 display (`K × [0,2]`) does not give |
| **10.4** | Lemma | p121 | `NavierStokes/R3/IntegratedDissipation.lean:143,183,203,248,279`; used at `NavierStokes/R3/Theorem.lean:66` | **LEAN STRONGER** | paper states (10.13) at viscosity one; Lean proves it for every `ν>0` with `2ν` in front of the dissipation; `F(1)<∞`, integrability and the total-dissipation bound are separate theorems |
| **10.5** | Lemma | p121 | `NavierStokes/R3/WholeSpaceUniqueness.lean:30,72,104` | **LEAN STRONGER** | `candidate_unique_on_Icc:72` is the paper's statement for an *arbitrary* compactly-supported candidate; `classical_uniqueness_on_Icc:30` is more general still (two solutions with equal residual) |
| **10.6** | Corollary | p125 | `NavierStokes/PeriodicPaperTheorem.lean:26,51,148,155`; `NavierStokes/PeriodicPaperSupport.lean:22,25` | **EXACT** | every clause present; support clauses correctly read modulo the fundamental cube |
| **9.1** | Proposition | p101 | `NavierStokes/LinearWaveBounds.lean:898` (`constructed_linear_wave_with_flat_error`) | **EXACT (partial)** | `WaveClass … (α + 1/2 − 3κ)` plus an all-order flat error, exactly the display; the trailing clause `π_m ∈ W_{α+1/2}` I did not locate |
| **9.2** | Lemma | p102–103 | `NavierStokes/WaveInteractionBounds.lean:153` (`MeanVector`), `:374` (`wave_mean_bound`), `:640`, `:1157`; `NavierStokes/CurlClassBounds.lean:758` | **EXACT** | `MeanVector s μ` = radial in `M_{μ+1}`, tangential in `M_μ` — literally the paper's hypothesis; conclusions `W_{α+μ−1/2}` and `W_{α+β−κ}` / `M_{α+β−κ}` match |
| **9.3** | Proposition | p103 | `NavierStokes/LinearWaveBounds.lean:898` (part i + flat remainder); `NavierStokes/ActualCyclePreservation.lean:826-920` | **UNRESOLVED (partial)** | the residual decomposition `R = G + F` with a per-stage flat `F` exists as the `excludedSlotError` / `RawStageBounds` pair, but I did not match parts (ii) and (iii) clause by clause |
| **9.4** | Definition | p106 | `NavierStokes/ActualParticularCycleData.lean:41` (`Data x σ`); `NavierStokes/ActualIterationLedger.lean:22,29`; `NavierStokes/ExponentLedger.lean:24,27,286` | **EXACT on (9.8); UNRESOLVED on (9.9)–(9.10)** | `Data`'s `amplitude` is `W_{1/2+σ}` and `pressure` is `M_{1+σ}` = paper's `B_j`, `C*_j`; `stageParameter n = 1/5 + n/10` = `σ_j` exactly. The cumulative bounds (9.9) and the two exact moments (9.10) I did not locate |
| **9.5** | Proposition | p106 | `NavierStokes/ActualInitialization.lean` + `NavierStokes/ActualCycleCoherence.lean:87` (`initial`), `NavierStokes/ExponentLedger.lean:288` | **EXACT on the numbers; UNRESOLVED analytically** | `stage_parameter_zero : stageParameter 0 = 1/5` gives `B₀ = 0.7`, `C*₀ = 1.2` exactly; the analytic stage-0 construction I did not read |
| **9.6** | Proposition | p107 | `NavierStokes/ActualCandidateConstruction.lean:40` (`cycle` = iterate of `step`), `NavierStokes/ActualCyclePreservation.lean:826,835,850`; arithmetic in `NavierStokes/ExponentLedger.lean:63,68,291,304` | **EXACT in shape** | the `+1/10` per cycle is `ExponentLedger.stage_parameter_succ`; the *chaining* is `state_particularData … (sigma j)` for **every** `j`, proved by induction (`state_runInvariant:826`) |
| **9.7** | Lemma | p111 | `NavierStokes/ActualCandidateConstruction.lean:155,157,159,189` (`qbig`, `qbig_pos`, `physicalDomain`) | **EXACT by instantiation** | Lean *defines* `qbig B N0 := ChartScales.Q (firstBand B N0)` instead of asserting `∃ qbig`; independence of stage and derivative order is structural (no `j`, no `m` in the definition). The "finitely many input amplitude derivatives" clause has no separate statement |
| **9.8** | Lemma | p113 | `NavierStokes/CutStageEstimates.lean:199` (`RawStageBounds`), `NavierStokes/MixedCandidateAssembly.lean:29` (`StageEstimates`), `NavierStokes/ActualIterationLedger.lean:29` (`gain h j = h*j/10`) | **EXACT on (9.17); LEAN WEAKER on (9.18)** | see §4.3 — the uniformity structure is exactly the paper's; the residual exponent is `gain j = hj/10` where the paper has `hσ_j = h(1/5 + j/10)` |
| **9.9** | Proposition | p114 | `NavierStokes/LocalPaperTheorem.lean:53` (`Properties`), `:179` (`local_theorem`); summation in `NavierStokes/SolenoidalDiagonal.lean` (`potentialSum`) + `NavierStokes/DiagonalScale.lean:57,156` | **EXACT / LEAN STRONGER** | `local_theorem` is unconditional and bundles every Theorem 3.1 conclusion including `divergence_free` and `AngularRayGrowth`; smoothness is asserted on all of `t<1`, a **larger** set than the paper's `Ω* = {τ>0, q<q*}` |

---

## 2. The headline, clause by clause

### 2.1 Paper Theorem 1.1 (p1), verbatim

> For every `ν > 0` there exist a force `f ∈ C∞_c(R³ × (0,∞); R³)`, a compact set
> `K ⊂ R³`, and smooth velocity and pressure fields `u, p` on `R³ × [0,1)` satisfying
> `∂ₜu + (u·∇)u − ν∆u + ∇p = f`, `∇·u = 0`, `u(·,0) = 0`, (1.1)
> such that `supp u(·,t) ∪ supp p(·,t) ⊂ K` for every `0 ≤ t < 1`,
> `sup_{0≤t<1} ‖u(t)‖_{L²(R³)} < ∞`, `limsup_{t↑1} ‖u(t)‖_{L∞(R³)} = ∞`.
> Consequently, there is no smooth solution `(u,P)` on `R³ × [0,∞)` with the same
> force and initial datum whose kinetic energy is uniformly bounded
> `sup_{t≥0} ½∫|u|² dx < ∞`.

### 2.2 Lean: `NavierStokesR3.theorem_1_1 : ProblemStatement.breakdownStatement`
(`NavierStokes/R3/Theorem.lean:46`, unfolding `NavierStokes/R3/ProblemStatement.lean:150`)

```
∀ ν : ℝ, 0 < ν →
  ∃ u p f K, CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalFiniteEnergySolution ν f)
```

| paper clause | Lean field (`R3/ProblemStatement.lean`) | verdict |
|---|---|---|
| `∀ ν > 0` | `∀ ν, 0 < ν → …` (`:150`) | **EXACT** |
| `f ∈ C∞_c(R³×(0,∞); R³)` | `force_smooth : ContDiff ℝ ∞ f` (`:98`) **and** `force_support : CompactPositiveTimeSupport f` = `HasCompactSupport f ∧ tsupport f ⊆ Ioi 0 ×ˢ univ` (`:66`, `:99`) | **EXACT.** Compact in ℝ⁴ *and* support bounded away from `t=0` — precisely `C∞_c` on `ℝ³×(0,∞)` |
| `K ⊂ R³` compact | `∃ K : Set Space`, `support_compact : IsCompact K` (`:95`) | **EXACT** |
| `u, p` smooth on `R³×[0,1)` | `velocity_smooth/pressure_smooth : ContDiffOn ℝ ∞ · preSingularDomain`, `preSingularDomain = Ico 0 1 ×ˢ univ` (`:93,94`; `ProblemStatement.lean:42`) | **EXACT.** `∞` in the `ContDiff` scope is "all finite orders", i.e. genuine `C^∞` (the module says `⊤` would be the stronger analytic order) |
| `∂ₜu + (u·∇)u − ν∆u + ∇p = f` | `navier_stokes : ∀ t ∈ Ioo 0 1, ∀ x, navierStokesResidual ν u p t x = f (t,x)` (`:104`), with the residual at `R3/ProblemStatement.lean:57` and its four operators at `ProblemStatement.lean:55–80` | **LEAN WEAKER by one endpoint** — imposed on the *open* interval, not on `[0,1)`. See §4.1 |
| `∇·u = 0` | `divergence_free : ∀ t ∈ Ico 0 1, ∀ x, spatialDivergence u t x = 0` (`:102`) | **EXACT** (includes `t=0`) |
| `u(·,0) = 0` | `zero_initial_velocity : ∀ x, u (0,x) = 0` (`:101`) | **EXACT.** This is the *paper's* clause; the abstract says "starting from rest" |
| `supp u(·,t) ∪ supp p(·,t) ⊂ K`, `0 ≤ t < 1` | `velocity_support` / `pressure_support : ∀ t ∈ Ico 0 1, tsupport (fun x => ·(t,x)) ⊆ K` (`:96,97`) | **EXACT**, one `K` for all `t` |
| `sup_{0≤t<1}‖u(t)‖_{L²} < ∞` | `energy_bounded : UniformFiniteEnergy (Ico 0 1) u` = `∃ E ≥ 0, ∀ t ∈ Ico 0 1, SquareIntegrableAtTime u t ∧ kineticEnergy u t ≤ E` (`:71,76,81,105`) | **EXACT.** Integrability is an explicit conjunct, so the totalized Bochner integral cannot hide infinite energy |
| `limsup_{t↑1}‖u(t)‖_{L∞} = ∞` | `speed_unbounded : SpeedUnboundedAtOne u` = `∀ M>0, ∀ δ>0, ∃ t ∈ Ioo 0 1, 1−δ<t ∧ ∃ x, M < ‖u(t,x)‖` (`ProblemStatement.lean:94`) | **EXACT** (continuous compactly-supported slices make the two equivalent) |
| "no smooth solution `(u,P)` on `R³×[0,∞)` with the same force and initial datum whose kinetic energy is uniformly bounded" | `¬ Nonempty (GlobalFiniteEnergySolution ν f)` with the **same** `f` (`:125–136,150`): smooth on `Ici 0 ×ˢ univ`, `zero_initial_velocity`, div-free on `Ici 0`, PDE on `Ioi 0`, `UniformFiniteEnergy (Ici 0)` | **EXACT / marginally LEAN STRONGER** — no support, decay, pressure-growth or energy-inequality hypothesis is imposed on the competitor (the module docstring says so at `:128–131`, and the code bears it out), and the PDE is demanded only at `t>0`, so the excluded class is *larger* |

Lean additionally proves, for the same fields:

* `theorem_1_1_with_initial_rest` (`R3/Theorem.lean:26`) — `u(t,x) = p(t,x) = 0` for `|t| ≤ 3/8`.
  (The paper's Prop 10.1 (10.2) only says "for all sufficiently small `t ≥ 0`".)
* `theorem_1_1_with_dissipation` (`R3/Theorem.lean:66`) — the full Lemma 10.4 package,
  at every `ν`.
* `theorem_1_1_with_maximalH3` (`R3/H3MaximalLifespan.lean:109`) —
  `admissibleH3Lifespans ν f 0 = Ioc 0 1`, i.e. the paper's proof-body sentence
  "the maximal classical existence interval is `[0,1)`" (p124) promoted to a theorem.
* `LocalAngularGrowth.selected_candidate_one_with_angular_growth`
  (`NavierStokes/LocalAngularGrowth.lean:238`) — the quantitative rate; see §2.4.

### 2.3 Paper Proposition 10.1 (p117) vs Lean

> There are a compact set `K ⊂ R³`, a smooth vector field `u` and a smooth scalar field
> `p` on `R³ × [0,1)`, with `supp u(·,t) ∪ supp p(·,t) ⊂ K` for every `0 ≤ t < 1`,
> satisfying `div u = 0`, `u(·,t) = p(·,t) = 0` for all sufficiently small `t ≥ 0`. (10.2)
> They agree with `u_loc, p_loc` on a spatial neighborhood of the origin for all times
> sufficiently close to 1.

There is **no single Lean theorem named for Prop 10.1**; its content is four theorems.

| clause | Lean | verdict |
|---|---|---|
| compact `K`, supports in `K` | `SpatialLocalization.supportCylinder` (`:72`), `isCompact_supportCylinder` (`:79`), `R3/ActualCandidate.lean:51,59` | **EXACT** |
| smooth on `R³×[0,1)` | `R3/ActualCandidate.lean:78` field `velocity_smooth`/`pressure_smooth` | **EXACT** |
| `div u = 0` | same, field `divergence_free` | **EXACT** |
| `u(·,t)=p(·,t)=0` for small `t` | `TimeLocalization.activatedVelocity_zero_early:57`, `activatedPressure_zero_early:61` (`|t| ≤ 3/8`) | **LEAN STRONGER** — an explicit interval |
| agreement with `u_loc,p_loc` near `(0,1)` | `LocalAngularGrowth.localized_eq_raw:60`: for `3/4 ≤ t` and `x ∈ SpatialLocalization.plateau` (an **open** neighbourhood of `0` — `isOpen_plateau:136`, `zero_mem_plateau:140`), `R3CompactCandidate.velocity A D (t,x) = MixedPeriodicAssembly.velocity A D (t,x)` | **EXACT** |

Two instantiation differences, both legal because Prop 10.1 is an existence claim:

* the paper takes "any fixed `r₀ > 0`" and `0 < τ₀ < 1/2`, `z₀ > 0` chosen small
  relative to `q*`; Lean **fixes** the cutoff — `spatialCutoff:49` built from
  `cutoff(16 r²)·cutoff(4 z)`, support cylinder `r² ≤ 1/16, |z| ≤ 1/4` (`:72`),
  plateau `r² < 1/32, |z| < 1/8` (`:134`), and the time switch vanishing on
  `|t| ≤ 3/8`. Lean's effective `τ₀ = 5/8` exceeds the paper's `τ₀ < 1/2`; the
  `q < q*` margin is instead secured by `ActualCandidateConstruction.qbig` and
  `LocalAngularGrowth.exists_ray_interval:81`. This is a construction choice, not
  a statement difference.
* Lean's Prop-10.1 analogue is stated about the **periodic lift first** and the
  compactly-supported `R³` field second (`SpatialLocalization.periodicVelocity:213`
  → `R3CompactCandidate` → `R3/ActualCandidate.of_localized_fields:78`), the reverse
  of the paper's §10.1 → §10.5 order. The end statements are unaffected.

### 2.4 The blow-up rate

The paper never states a rate in Theorem 1.1. Its rate is Theorem 3.1(iv)/(3.6) (p16),
transported to (10.21) (p124):

> For some fixed `X_in ∈ (0, X_a)` and `e₀ > 0`,
> `uθ(√(2X_in τ), 0, 0, 1−τ) = τ^{−A}(e₀ + O(τ^{2h}))` as `τ ↓ 0`,
> with `A = 1/2 + h`, `0 < h < 1/100` (p9, p22).

Lean:
* `CoordinateAlgebra.A h = 1/2 + h` (`NavierStokes/CoordinateAlgebra.lean:18`) — **EXACT**.
* `LocalAngularGrowth.selected_exponent_small:230` : `0 < h ∧ h < 1/100` — **EXACT**.
* `LocalPaperTheorem.AngularRayGrowth:42`:
  `∃ X_in, 0 < X_in ∧ X_in < X_a ∧ ∃ e₀ C δ, … ∀ τ ∈ (0,δ), |τ^A · u(1−τ, ray X_in τ) 1 − e₀| ≤ C τ^{2h}`
  — the existential over `X_in ∈ (0,X_a)` is the paper's "for some fixed `X_in`", and
  component `1` at the point `(√(2X_in τ),0,0)` is exactly `uθ`. **EXACT.**
* `LocalAngularGrowth.AngularGrowth:180` is the same statement with `X_in` pinned to
  `innerRadius := activeLeft/2` (`:71`) — a witness for that existential.

**Lean also asserts something the paper does not:** `FinalSlowBase.origin`
(`NavierStokes/FinalSlowBase.lean:361`) gives, in closed form,
`velocity (t,0) = ((1−t)^{−A} · j) • e₂` with `j > 0`, so the candidate's speed is
unbounded **at the fixed spatial origin along the axis**, and `speed_unbounded` is
realised there (`FinalSlowBase.axis_tendsto:372`, `speedUnbounded:380`,
`MixedAxisPreservation.final_origin_blowup`). The paper's proof instead uses the
*moving* path `x_τ = (√(2X_in τ),0,0)` and says only that those points converge to
the origin. This is stronger, and consistent with §2.1's axial-outflow picture, but
it is the one place where Lean claims more about the flow than the paper states.

### 2.5 Paper Corollary 10.6 (p125) vs Lean

> For every `ν > 0`, there is a smooth force on `T³ × [0,∞)`, compactly supported in
> time, for which the solution `(U, P_per)` … with viscosity `ν` and zero initial
> velocity is smooth on `[0,1)` and satisfies `limsup_{t↑1}‖U(t)‖_{L∞(T³)} = ∞`.
> Its velocity and pressure have support in a fixed compact subset of the interior of
> `Q₀` at every time before one. There is no global smooth periodic solution for the
> same datum and force.

Lean: `NavierStokes.PeriodicPaper.periodic_corollary : breakdownStatement`
(`NavierStokes/PeriodicPaperTheorem.lean:155`, statement at `:148`):
`∀ ν>0, ∃ u p f K, CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalSmoothSolution ν f)`.

| paper clause | Lean field (`PeriodicPaperTheorem.lean:26–49`) | verdict |
|---|---|---|
| smooth force on `T³×[0,∞)` | `force_smooth : ContDiff ℝ ∞ f` + `force_periodic : UnitSpatialPeriodsOn (Ici 0) f` | **LEAN STRONGER** (globally smooth on ℝ⁴) |
| compactly supported in time | `force_time_support : CompactFutureTimeSupport f` + `force_zero_nonpos : ∀ t ≤ 0, f(t,·)=0` | **EXACT** (support in `[0,T]`); Lean does not pin the paper's `[t₀, 1+λ⁻²]` |
| zero initial velocity | `zero_initial_velocity` | **EXACT** |
| smooth on `[0,1)` | `velocity_smooth`/`pressure_smooth` on `preSingularDomain` | **EXACT** |
| periodic NS at viscosity `ν` | `navier_stokes : ∀ t ∈ Ioo 0 1, navierStokesResidual ν u p = f` + `divergence_free` on `Ico 0 1` | **EXACT** (same open-interval caveat as §4.1) |
| `limsup_{t↑1}‖U(t)‖_{L∞(T³)} = ∞` | `speed_unbounded : SpeedUnboundedAtOne u` on the periodic lift | **EXACT** |
| support in a fixed compact subset of `int Q₀` | `support_compact : IsCompact K`, `support_interior : K ⊆ fundamentalInterior` (`= {x : ∀ i, |xᵢ| < 1/2}`, `PeriodicPaperSupport.lean:22`), `velocity_support`/`pressure_support : tsupport(·(t,·)) ∩ fundamentalCube ⊆ K` | **EXACT** — the `∩ fundamentalCube` is the correct torus reading (a nonzero periodic lift cannot have compact support in ℝ³); the module says so at `:20–22` |
| no global smooth periodic solution, same datum and force | `¬ Nonempty (GlobalSmoothSolution ν f)` (`:51–63`): smooth on `futureDomain`, `velocity_periodic`, `pressure_periodic`, zero datum, div-free on `Ici 0`, NS on `Ioi 0`. **No energy condition** | **EXACT** — correctly omits any energy bound (automatic on T³); `pressure_periodic` matches the Clay erratum and the paper's "two smooth periodic solutions" (see §4.5) |

Paper: "The pressure is periodic as well, as required in the erratum to the problem
statement [13]" (p125). Lean carries it on both sides. **EXACT.**

### 2.6 The Comparator challenge

`ComparatorChallenges/NavierStokes.lean:296,304` are DeepMind's `formal-conjectures`
statements verbatim (with `sorry`). The submission's theorems are
`NavierStokes/ComparatorSolution.lean:16,23`, forwarding to
`NavierStokes/ComparatorR3Theorem.lean:38` and `NavierStokes/ComparatorTheorem.lean:47`.

* **(C)** `navier_stokes_breakdown_R3` is obtained **directly** from `theorem_1_1`:
  `obtain ⟨u,p,f,K,h,hglobal⟩ := NavierStokesR3.theorem_1_1 ν hν;
   exact NavierStokesR3.comparator_of_breakdown h hglobal`
  (`ComparatorR3Theorem.lean:43-44`). `comparator_of_breakdown`
  (`R3/ComparatorBridge.lean:77`) supplies `u₀ = fun _ => 0` and `toComparator f`
  — **the same force**, untouched. `forceConditionDecay_of_compact:22` derives
  Fefferman's condition (5) from compact spacetime support, exactly as the paper's
  Lemma 10.3 proof does in its last display (p120).
* `globalSolutionOfComparator` (`R3/ComparatorBridge.lean:48-74`) builds the
  competitor record from the challenge structure's own fields only. Confirmed: **not
  a subclass claim**; the earlier kernel-trust audit's reading holds.
* **(D)** `navier_stokes_breakdown_periodic` comes from `periodic_corollary`
  via `option_D_of_paper_candidate` (`PeriodicPaperComparator.lean:44`).

Alignment paper ↔ Comparator:

| Fefferman/Comparator requirement | paper Theorem 1.1 / Cor 10.6 | Lean |
|---|---|---|
| `u₀` smooth, div-free, rapidly decaying (`InitialVelocityConditionDecay`) | `u(·,0) = 0` | `fun _ => 0` — trivially satisfies all three |
| `f` smooth on `ℝ³×[0,∞)` with rapid space–time decay (`ForceConditionDecay`) | `f ∈ C∞_c(ℝ³×(0,∞))` | from compact support |
| no `(v,p)` with (1),(2),(3),(6),(7) (`NavierStokesExistenceAndSmoothnessRn`, incl. `integrable` and `globally_bounded_energy`) | "no smooth solution … whose kinetic energy is uniformly bounded" | `¬ Nonempty (GlobalFiniteEnergySolution ν f)` |

The Comparator class demands *more* of a competitor (decay of `u₀`, and the PDE also
at `t = 0` via `derivWithin` on `Ici 0`) than Lean's own `GlobalFiniteEnergySolution`
does, so the Lean Theorem 1.1 clause is the **stronger** of the two, and (C) follows
from it rather than the reverse. Nothing in the Comparator route is weaker than the
paper.

### 2.7 Linkage to the §3–4 slice: does the headline use the §4 leading profile? (coordinator question)

**Yes, and it is settled by `rfl`-level definitions, not by a chain of coincidences.**

The headline's profile is reached as
`NavierStokes/R3/Theorem.lean:27` → `ActualCandidate.selected_candidate_one_with_initial_rest`
(`R3/ActualCandidate.lean:143`) → `ActualCandidateAssembly.selected_witness`
(`ActualCandidateAssembly.lean:1177`) → `witness:1153` →
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages` applied to
`certificate`, `modulation`, `upper`. Those three are
`CorrectionInitialization.lean:3886-3891`:

```
abbrev profile     := FinalSlowBase.actualProfile
abbrev outgoing    := profile.outgoing
abbrev nominal     := profile.nominal
abbrev h           := outgoing.data.h
abbrev certificate := profile.certificate
abbrev modulation  := profile.modulation
```

and `FinalSlowBase.actualProfile` (`NavierStokes/FinalSlowBase.lean:634`) is

```
structure ProfileData where
  outgoing      : OutgoingProfile.Profile
  nominal       : NominalProfile.Witness outgoing
  certificate   : NominalConeAssembly.Certificate nominal
  loop          : ModulatedProfileAssembly.LoopData nominal
  modulation    : ModulatedProfileAssembly.Witness loop
  fullTrueCone  : LeadingStressWeights.FullTrueCone modulation

theorem profileData_nonempty : Nonempty ProfileData := by
  obtain ⟨F, W, H⟩  := NominalConeAssembly.exists_nominal_cone
  obtain ⟨ld, v, hc⟩ := ModulatedProfileAssembly.exists_of_certificate W H
  exact ⟨⟨F, W, H, ld, v, hc⟩⟩

noncomputable def actualProfile : ProfileData := Classical.choice profileData_nonempty
```
(`FinalSlowBase.lean:619-634`; `ActualPrimary.profile = FinalSlowBase.actualProfile` is
also recorded as `rfl` at `NavierStokes/BaseWitnessClosure.lean:22`.)

Compare the §4 declaration the other auditor found:

```
theorem ModulatedProfileAssembly.exists_modulated_profile :=  -- :1126
  obtain ⟨F, W, hW⟩   := NominalConeAssembly.exists_nominal_cone
  obtain ⟨d, v, hv⟩   := exists_of_certificate W hW
  exact ⟨F, W, d, v, hv⟩
```
(`ModulatedProfileAssembly.lean:1126-1139`) and

```
theorem LeadingStressWeights.exists_weighted_profile := -- :1154
  obtain ⟨F, W, d, v, hv⟩ := ModulatedProfileAssembly.exists_modulated_profile
  exact ⟨F, W, d, v, hv, weighted_bounds v hv,
         inner_direction_positive v hv, outer_direction_positive v⟩
```
(`LeadingStressWeights.lean:1154-1176`).

So `profileData_nonempty` makes **exactly the same two calls** —
`NominalConeAssembly.exists_nominal_cone` and
`ModulatedProfileAssembly.exists_of_certificate` — that `exists_modulated_profile`
makes, and it stores the third component under the name
`LeadingStressWeights.FullTrueCone modulation`, which is *definitionally* the
`∀ p, … InTrueCone …` proposition that `exists_of_certificate` returns
(`LeadingStressWeights.lean:453-460` vs `ModulatedProfileAssembly.lean:1103-1110` —
the two displays are character-identical). **The headline's leading profile and the
§4 leading profile are the same object, produced by the same existence theorems.**

Three qualifications, all worth stating:

1. `actualProfile` is `Classical.choice profileData_nonempty`, so it is *a* profile
   satisfying those existence theorems, fixed once at `FinalSlowBase.lean:634`, and
   every downstream reference is to that single choice. It is not literally the tuple
   `exists_weighted_profile` returns; the two are interchangeable only through the
   existence statement. Nothing downstream depends on which witness was chosen, so
   this is harmless.
2. **`LeadingStressWeights.exists_weighted_profile:1154` is used nowhere.**
   `grep -rn "exists_weighted_profile" NavierStokes/` returns only its own declaration
   line. It is a terminal packaging theorem for §4's statement, not a link in the
   headline chain. The headline reaches `weighted_bounds` and the two edge collars
   *directly* instead: `FinalSlowBase.lean:147` applies
   `LeadingStressWeights.weighted_bounds v hcone`, and
   `AlignedProfileSpectralCone.lean:443-444` applies
   `inner_direction_positive v hcone` / `outer_direction_positive v` — to
   `actualProfile.modulation` and `actualProfile.fullTrueCone`. So every conclusion
   `exists_weighted_profile` bundles is in the headline cone; only the bundle is not.
3. `ProfileData` stores `fullTrueCone` but not `WeightedBounds` or the collars; those
   are re-derived on demand from `modulation` + `fullTrueCone`, which is why the
   bundle is unnecessary.

**Theorem 4.6(vi) — the two reserved intervals.** Paper (p33–34):

> (vi) Two fixed disjoint intervals `I_pos` and `I_mean` remain available … with
> `sup I_pos < inf I_mean`. Both intervals lie in `(X_a, X_v)`. For every `X` in either
> interval, `U = 0`, `E = c_patch(1+η²)^{-1} X^{-1/2-λ}`, (4.30) with a positive constant
> `c_patch` independent of `X, η`. The construction of the leading profile leaves both
> intervals unchanged.

The §3–4 auditor was reading a *consumer's* signature. `hpatchU`/`hpatchE` at
`ModulatedProfileJetRates.lean:347` (fields at `:375-377`) are hypotheses **of the
moment-repair theorem** `exists_with_moment_repair_all_jets`, and likewise at
`ModulatedHistories.lean:994-995,1405-1406` and `ModulatedCone.lean:1444-1445`. The
**supplier is `NavierStokes/ReservedPatches.lean`**, and there the shape is a stated
conclusion:

| paper (4.30) clause | Lean |
|---|---|
| four reservations, the last two kept pure | `inductive Slot := modulation \| heat \| positive \| mean` (`ReservedPatches.lean:22`) with log offsets `(-25,-20)`, `(-20,-15)`, `(-14,-9)`, `(-8,-3)` (`:29-39`) — the paper's `I₁…I₄`, so `I_pos = .positive`, `I_mean = .mean`, exactly the paper's "`I_pos = I₃` and `I_mean = I₄`" (p33) |
| disjoint, `sup I_pos < inf I_mean` | `offsets_separated:48`, `windows_disjoint:90`, `closedPatches_disjoint:254` |
| both lie in `(X_a, X_v)` | `window_inside_wait:120`, `clock_inside_wait:114`, `right_before_switch:157` |
| `U = 0` and `E = c_patch(1+η²)^{-1} X^{-1/2-λ}` | **`heated_fields:333`** — `∀ s ≠ .heat`, on `window F XR s`: `HeatedOutgoing.U F XR (X,η) = 0 ∧ HeatedOutgoing.E F XR c (X,η) = xAmplitude F XR η * X ^ (-(1/2 + F.data.core.lam))`; also `heated_fields_on_closedPatch:342`, and the `R`-coordinate form `radial_heated_fields:546`, `radial_heated_fields_on_closedPatch:566` |
| `c_patch(1+η²)^{-1}` | **`xAmplitude_shape:282`** — `xAmplitude F XR η = xAmplitude F XR 0 / (1 + η^2)`, with `xAmplitude_pos:274`. So `c_patch = xAmplitude F XR 0 > 0`, independent of `X` and `η` |
| exponent `-1/2 - λ` | literally `-(1/2 + F.data.core.lam)`; and `FiveProfileMoments.good_outgoing:267` certifies `GoodExponent (-1/2 - lam)` |
| "the construction of the leading profile leaves both intervals unchanged" | **`supported_updates_preserve_fields:634`** — if `vU, vE` are `Supported` in slot `s ≠ t` and `t ≠ .heat`, then on `window F XR t` the updated fields still satisfy `U + vU = 0` and `E + vE = xAmplitude · X^{-(1/2+λ)}`; plus `supported_vanishes:600`, `supported_update_eqOn:607`, `supported_update_germ:616`, `supported_update_jets:625`, the finite-sum version `finite_updates_eqOn:648`, and the radial analogues `radial_supported_vanishes:664`, `radial_supported_updates_preserve_fields:679`. The file's own section header is "Supported perturbations preserve the other complete open windows" (`:574`) |
| the perturbations really are slot-supported | `heat_increment_supported:579` (the heat patch increment) and `five_row_updates_supported:586` (the five-row moment bumps) |

So **(vi) is a conclusion, not a hypothesis** — but it is stated slotwise in
`ReservedPatches.lean` about `HeatedOutgoing.U/E`, not as a clause of the finished
profile's structure. Two nearby instances confirm the pattern is the real one:
`ModulatedProfileAssembly.nominal_patch_fields:207` *proves*
`W.profiles.U (X,η) = 0 ∧ W.profiles.E (X,η) = xAmplitude F W.controls.radius η * X^(-1/2 - λ)`
on the `.modulation` window for the **nominal** profile `W`, and that is precisely
what discharges `hpatchU`/`hpatchE` at `ModulatedProfileAssembly.lean:477-487,516` —
with `G := fun _ => 0` and `b := -1/2 - F.data.core.lam` passed at `:511-513`, i.e.
the paper's `U = 0` and `X^{-1/2-λ}` verbatim. And
`OutgoingDilation.patch_fields:529` is the same conclusion for the `.heat`
(compensation) patch, carried as the structure field `shaped_patch`
(`OutgoingDilation.lean:602,632`). `MeanRankUpdate.reserved_five_rows:1398` is §8's
consumer of `I_mean` and it *derives* the shape from
`ReservedPatches.radial_heated_fields` rather than assuming it (`:1420`).

**What I did not close.** I did not verify that *every* modification performed between
`HeatedOutgoing` and the finished `ModulatedProfileAssembly.Witness.profiles` is
routed through `Supported`/`RadialSupported` at the `.modulation` or `.heat` slot —
i.e. that `supported_updates_preserve_fields`'s hypothesis is discharged for the whole
chain. And I found **no single declaration** stating (4.30) for `I_pos` and `I_mean`
about the finished `modulation.profiles` (the analogue of `nominal_patch_fields:207`
exists only for the `.modulation` slot). All the ingredients are present as
conclusions; the assembly into one 4.6(vi) statement is what I could not locate. That
is the residual question for §5's `Lemma 5.2` consumer and §8's `Lemma 8.7` consumer,
and `MeanRankUpdate.lean:1398-1420` suggests §8 at least does the assembly itself.

---

## 3. Per-statement notes (non-EXACT rows)

### 10.2 — locally uniform, not uniform on ℝ³

Paper (p118): "`∂ᵅₓ∂ʲₜ f` converges **uniformly on R³** as `t ↑ 1`. There are functions
`F_j ∈ C∞_c(R³;R³)`, all supported in `K`, such that `lim_{t↑1} ∂ᵅₓ∂ʲₜ f(x,t) = ∂ᵅₓF_j(x)`,
`∂ᵅₓF_j(0) = 0`."

Lean takes a different but equivalent-in-effect route. `JointResidualLimits`
(`NavierStokes/JointResidualLimits.lean`) assumes
`VanishingJointJets f` (`:84` — all jets `→ 0` at `(1,0)`, i.e. the paper's flatness
(3.4)/(10.9)) and `AwayExtensions f` (`:81` — a one-sided smooth extension near every
`x ≠ 0`, i.e. the paper's two "away from the origin" regions), and produces
`boundaryLimits f hext x : FormalMultilinearSeries` (`:120`) with

* `boundaryLimits_joint:130` — `iteratedFDeriv ℝ n f → boundaryLimits … x n` along `𝓝[past] (1,x)`;
* `boundaryLimits_locallyUniform:148`, `boundaryLimits_uniformOn_compact:156` — the convergence;
* **`boundaryLimits_zero:126`** — `boundaryLimits f hext 0 n = 0`, which is the paper's
  `∂ᵅₓ F_j(0) = 0` clause, verbatim;
* `boundaryLimits_smooth:220`, `extendedJets_compatible:227` — compatibility under
  spatial and time differentiation, the paper's (10.10).

So the conclusion is present clause for clause **except** that Lean says "locally
uniformly / uniformly on compacts" where the paper says "uniformly on ℝ³". Given the
fixed compact support `K` the two coincide, but the paper's stronger wording has no
Lean statement. It is also not needed: Lean's Borel realization
(`CandidateFromLimits.force:82`, `SpacetimeGluing.smoothExtension`) consumes the
boundary **jets**, not a global modulus of convergence.

### 10.3 — Lean is stronger than the literal display

Paper: "The force in (10.5) extends to `f ∈ C∞_c(R³ × (0,∞); R³)`, with support
contained in `K × [0,2]`." The two halves are in mild tension as written: `K × [0,2]`
includes `t = 0`, which `C∞_c(R³×(0,∞))` forbids. The paper's proof closes the gap in
one sentence — "Finally, the original force is zero near `t = 0`, by (10.2) and the
construction of `p`" (p120).

Lean proves both halves explicitly and separately:
`CandidateFromLimits.force_zero_from:114` (`t ≥ 2 ⇒ f = 0`),
`force_zero_nonpos:119` (`t ≤ 0 ⇒ f = 0`),
`force_time_support:124`, and then the *strict* positivity of the support is obtained
by a further cutoff, `PositiveTimeForce.force`, giving
`force_support : CompactPositiveTimeSupport` with
`tsupport f ⊆ Ioi 0 ×ˢ univ` (`R3/ActualCandidate.lean:78`, fields `force_smooth`,
`force_support`). Also `force_eq_activated_residual:108` is the paper's (10.5)
(`f = R(u,p)` for `0 ≤ t < 1`), and `R3/ActualCandidate.lean:87-105` checks that the
extra positive-time cutoff does not break it.

**Class: LEAN STRONGER.** No downstream use of the paper's stronger form is at risk.

### 10.4 — Lean generalizes in `ν`, and one half is carried rather than re-derived

Paper: `F(t) = ∫₀ᵗ‖f(s)‖₂ ds`; `F(1) < ∞` and
`‖u(t)‖²₂ + 2∫₀ᵗ‖∇u(s)‖²₂ ds ≤ F(t)²` for `0 ≤ t < 1`, at viscosity one.

Lean, for every `ν > 0`:
* `candidate_l2Norm_le_cumulativeForceNorm:143` — `‖u(T)‖₂ ≤ F(T)`, derived from the
  differential inequality (`SharpEnergyBound.sqrt_energy_le_integral`), **not** from
  the candidate's `energy_bounded` field. This is the paper's route.
* `candidate_energy_dissipation_le:203` —
  `l2Sq u T + 2ν∫₀ᵀ dissipation ≤ (cumulativeForceNorm f T)²`, i.e. (10.13) with the
  viscosity restored.
* `candidate_integrable_dissipation:73`, `candidate_total_dissipation_le:248` — genuine
  `IntegrableOn … (Ico 0 1)` plus the endpoint bound, i.e. "the total dissipation on
  `[0,1)` is finite" stated as integrability rather than as a totalized integral.
* `l2Norm_intervalIntegrable … 0 1` inside `candidate_energy_estimates:279` — `F(1) < ∞`.

One asymmetry worth noting: `candidate_uniform_kineticEnergy_le:183` obtains the
*square-integrability* half from `hc.energy_bounded` (line 190, `obtain ⟨E,hE,hb⟩`),
i.e. from the `CandidateProperties` field, rather than re-deriving it. That field is
itself proved for the actual construction by exactly Lemma 10.4's argument
(`R3/ActualCandidate.lean:126-129`, `CompactEnergy.uniform_finite_energy` applied to
the force, the equation and the zero datum), so the chain is closed — but a reader
auditing the Lemma-10.4 file alone will see the energy bound both assumed (as a
field) and concluded.

### 10.5 — Lean is strictly more general

Paper: "Fix `T < 1`. If `v, P` is a smooth solution of (1.1) at viscosity one on
`R³ × [0,T]`, with the force `f` of Lemma 10.3, zero initial velocity, and
`v ∈ L∞([0,T];L²(R³))`, then `v = u` on that interval, where `u` is the localized
velocity of Proposition 10.1."

`WholeSpaceUniqueness.candidate_unique_on_Icc:72`:

```
(h : CandidateProperties 1 u p f K) (hT : T < 1)
(hv : ContDiffOn ℝ ∞ v (slab 0 T)) (hq : ContDiffOn ℝ ∞ q (slab 0 T))
(hev : UniformFiniteEnergy (Icc 0 T) v)
(hdv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0)
(hNSv : ∀ t ∈ Ioo 0 T, ∀ x, navierStokesResidual 1 v q t x = f (t,x))
(hvzero : ∀ x, v (0,x) = 0)
→ ∀ t ∈ Icc 0 T, ∀ x, u (t,x) = v (t,x)
```

Three ways it is stronger: the reference is *any* candidate with compact spatial
support, not the one specific localized field; the competitor's equation and
divergence condition are required only on the open `(0,T)`; and
`classical_uniqueness_on_Icc:30` underneath is the fully symmetric statement (two
smooth fields with equal residual, one compactly supported, equal at `t=0` ⇒ equal),
with no reference to the force at all. The module docstring's claim — "No growth,
decay, support or derivative bound is assumed for the competing pressure or
velocity" — is borne out by the signature; `hq : ContDiffOn ℝ ∞ q (slab 0 T)` is the
only condition on the competing pressure, matching the paper's "These hypotheses
leave the growth of spatial derivatives at infinity unrestricted" (p121).

### 9.1 — matched except for the pressure-amplitude clause

`LinearWaveBounds.constructed_linear_wave_with_flat_error:898` concludes

```
WaveClass s P (α + 1/2 - 3*κ) (a.constructedGood s d g.cutoff) ∧
  (∀ N : ℝ, UnweightedClass s N (excludedSlotError d g.cutoff a.amplitude source)) ∧
  <exact residual identity>
```

which is the paper's "belongs to `W_{α+1/2−3κs}`, apart from additive pulse-cutoff
tails whose Cartesian space–time derivatives vanish to infinite order as `q ↓ 0`"
(p101) — the `∀ N, UnweightedClass s N` is exactly the flatness. The hypothesis
`hsolve : a.principal s d n x = -source n x` is the paper's `L_m(t_m,π_m) = −f_m`.
I did not find a Lean statement for the last sentence, `π_m ∈ W_{α+1/2}`.

### 9.2 — exact, including the asymmetric mean hypothesis

The paper's hypothesis is subtle: "`v` a mean field with **tangential** components in
`M_μ` and **radial** component in `M_{μ+1}`". Lean encodes it literally:

```
def MeanVector (s : StripData D) (μ : ℝ) (a : Family D) : Prop :=
  MeanClass s (μ + 1) (fun n x => a n x 0) ∧
    MeanClass s μ (fun n x => a n x 1) ∧ MeanClass s μ (fun n x => a n x 2)
```
(`NavierStokes/WaveInteractionBounds.lean:153` — index `0` is radial.)

`wave_mean_bound:374` concludes `WaveVector s P (α + μ - 1/2) (waveMeanCoefficient …)`
— the paper's `W_{α+μ−1/2}` — and `waveMeanCoefficient:367` is literally both cross
advections plus the phase term. The two-wave half is `same_label_harmonic_bound:640`
and `same_label_curl_interaction:1157` (`WaveVector s P (α+β−κ)`) with the zero
harmonic in `MeanClass s (α+β−κ)` (`:509,611,625,859`); "distinct labels have zero
products on their closed supports" is `slot_transport_zero:746`,
`transport_zero_of_products:673`, `slot_curl_transport_zero:1012`.

The Lean versions carry side hypotheses the paper leaves in its class setup
(`hζ : zeta ≤ 1`, `hP : 0 ≤ P`, `hκ1 : κ ≤ 1/2`, boundedness of the phase normal).
These are properties of the fixed geometry, not restrictions on the lemma's reach.

### 9.4 / 9.6 — the exponent ledger is exact; the chaining exists for every `j`

Paper Definition 9.4 (9.8): `B_j = 1/2 + σ_j`, `C*_j = 1 + σ_j`, `σ_j = 1/5 + j/10`.

Lean:
* `ExponentLedger.waveExponent σ = 1/2 + σ` (`:24`), `meanExponent σ = 1 + σ` (`:27`),
  `stageParameter n = 1/5 + n/10` (`:286`), `stage_parameter_succ` (`:291`) — **EXACT**.
* `ActualIterationLedger.sigma J = stageParameter J` (`:22`).
* `ActualParticularCycleData.Data x σ` (`:41`) carries
  `amplitude : UniformWaveClass … (1/2+σ)` and `pressure : UniformWaveClass … (1+σ)`
  — the two exponents of (9.8) — plus `linear : … (1+σ-3κ)`.
* `ActualCyclePreservation.state_particularData B N0 hN j :
   Data (state B N0 j) (ActualIterationLedger.sigma j)` (`:850`), for **every** `j`,
  proved from `state_runInvariant:826` by induction over the cycle
  `ActualCandidateConstruction.cycle:40 = CycleState.iterate step`.

So Proposition 9.6's "there is a state at stage `j+1` with `B_{j+1} = B_j + 1/10`,
`C*_{j+1} = C*_j + 1/10`" is present as an `∀ j` invariant with the paper's exact
exponents. `ExponentLedger.lean`'s own docstring is careful that it "checks the
arithmetic of those assignments, **conditional on the estimates being valid**"; the
analytic half is the `state_*` invariant bundle (`:826–920`), which I did **not** read
field by field. The paper's (9.9) cumulative bounds (`w ∈ W_{1/2}`, `w − w₀^tan ∈
W_{0.68}`, `v,γ,p_m ∈ M_{0.9}`, `β ∈ M_{1.9}`) and the two exact moments (9.10) I did
not locate; that is the largest §9 residue.

### 9.7 — a definition where the paper has an existential

Paper: "There **exists** `q_big > 0`, independent of the correction stage and
derivative order, such that every finite partial sum above, before applying summation
cutoffs, is well defined on `0 < q < q_big`."

Lean: `ActualCandidateConstruction.qbig (B N0 : ℕ) : ℝ := ChartScales.Q (firstBand B N0)`
(`:155`), `qbig_pos:157`, `qbig_le_choice:159`, domain `physicalDomain B N0` (`:189`).
The independence claims are structural — the definition mentions neither the stage
index `j` nor a derivative order `m` — rather than being a stated quantifier fact.
The second sentence ("for every fixed stage and output amplitude derivative, its
construction and estimate require finitely many input amplitude derivatives") has no
separate Lean statement; it is absorbed into the finitely-many-fields shape of
`CycleState` and the per-stage estimate structures.

### 9.8 — the uniformity structure matches exactly; one exponent is weaker

This is the row the brief asked about directly. Paper (9.17)/(9.18), p113:

> `|Z_j|_m + |∆u_j|_m ≤ C_{j,m} q^{g_j − ℓ_m} (1 + |log q|)^{P_{j,m}}`, `g_j = (h/10) j → ∞`,
> where `ℓ_m` is **independent of `j`**. … `|(u^[j],p^[j])|_m ≤ C_{j,m} q^{−K_m}(1+|log q|)^{P_{j,m}}`
> with `K_m` independent of `j`. Their residuals satisfy
> `|R(u^[j],p^[j])|_m ≤ C_{j,m} q^{hσ_j − K_m}(1+|log q|)^{P_{j,m}} + E_{j,m}`, `E_{j,m} ≤ C_{j,m,N} q^N`.

Lean, `NavierStokes/CutStageEstimates.lean:199`:

```
def RawStageBounds (q : E → ℝ) (A : ℕ → E → V) (g L : ℕ → ℝ) (C p : ℕ → ℕ → ℝ) (S : Set E) : Prop :=
  ∀ j, 1 ≤ j → ∀ m x, x ∈ S → q x ≤ 1 →
    ‖iteratedFDeriv ℝ m (A j) x‖ ≤ C j m * (1 + |Real.log (q x)|) ^ (p j m) * q x ^ (g j - L m)
```

**Answer to the brief's question: yes, exactly.** `C j m` and `p j m` depend on both
indices, matching `C_{j,m}` and `P_{j,m}`; `L m` depends on `m` only, matching
"`ℓ_m` is independent of `j`"; the exponent is literally `g j − L m`. And the concrete
supplier is `ActualIterationLedger.gain h j = h * j / 10` (`:29`) — the paper's
`g_j = (h/10)j`, confirmed to be the one actually used by
`GluedStageEstimates.actualStageEstimates_ledger:727` (`E.gain = ActualIterationLedger.gain h`, by `rfl`).

Two differences:

1. **`StageEstimates` (`NavierStokes/MixedCandidateAssembly.lean:29`) requires only
   `gain_pos`, `gain_mono`, `gain_top : Tendsto gain atTop atTop`**, not the paper's
   specific `hj/10`. The abstract interface is therefore *weaker in hypothesis*, i.e.
   the summation machinery is more general; the concrete instance matches the paper.
   No issue.
2. **`finite_residual` uses `gain J`, where the paper's (9.18) uses `hσ_j`.**
   `MixedCandidateAssembly.lean:62-65`:
   `JetRate … (residual of the J-th prefix) m (gain J - residualLoss m)`.
   Since `gain J = hJ/10` and `hσ_J = h(1/5 + J/10) = hJ/10 + h/5`, Lean's residual
   exponent is **smaller by the constant `h/5`**, i.e. the Lean statement of (9.18)
   asserts strictly less decay than the paper's. The `ActualIterationLedger` docstring
   makes this deliberate: "One common physical gain for all increment types and finite
   residuals" (`:28`). Classify **LEAN WEAKER (immaterial)**: every downstream use goes
   through `DiagonalScale.exists_diagonal_scales:156`, which needs only
   `∀ j ≥ 1, 0 < g j` and `g → ∞`. The paper's stronger form is not used at full
   strength anywhere I could find, and there is no reason to doubt it.

The `(1 + |log q|)^p` shape is `DiagonalScale.logPowerWeight:25`, and
`absorb_logarithmic_weight:57` is the "absorb half the positive power" step —
`|C(1+|log q|)^p q^{g−L}| ≤ ε q^{g/2−L}` — which is (9.17) used the way the paper's
§9.5 summation uses it.

### 9.9 — Lean's `local_theorem` is the bundled Theorem 3.1, on a larger domain

Paper: "There are smooth fields `(u_loc, p_loc)` on `Ω*`, obtained by summing the
finite corrections above, such that `div u_loc = 0` and all conclusions of Theorem 3.1
hold."

Lean: `NavierStokes.LocalPaper.local_theorem` (`NavierStokes/LocalPaperTheorem.lean:179`)

```
∃ h qstar Xa Xext heatNormalization, ∃ A D u p, Properties h qstar Xa Xext heatNormalization A D u p
```

unconditional (no schedule or finite-stage hypothesis). `Properties` (`:53`) bundles
`exponent_small : 0 < h ∧ h < 1/100`, `decomposition : u = curl A + D` (the paper's
`u_loc = curl A + B eθ`), `divergence_free`, the away-extensions and uniform jet
bounds (Theorem 3.1(i)–(ii)), `residual_flatness` (3.4), `exterior` (3.5, including
`A = 0`, `D = K eθ`, the normalized pressure and **zero residual**), and
`angular_growth : AngularRayGrowth h Xa u` (3.6). The literal radial heat formulas of
(3.5)/(A.34) are `NavierStokes/LocalPaperHeat.lean:19-59`
(`exterior_amplitude_formula`, `exterior_heat_equation`, `exterior_radial_form`,
including the genuinely integrable pressure tail `−∫_r^∞ K²/ρ dρ`).

Smoothness is asserted on `PhysicalWaveSum.preterminal` (all `t < 1`), a **larger**
set than the paper's `Ω* = {τ>0, q<q*}` — the module says so explicitly
(`:49-52`). **LEAN STRONGER** on the domain, EXACT on the clauses I checked.

---

## 4. Findings worth an expert — ranked

**F1 (highest value, and a negative result). The headline is not weaker than the
paper, and the two clauses that look like weakenings are the paper's own.**
`u₀ ≡ 0` is the paper's `u(·,0) = 0` in Theorem 1.1's display (p1) and its abstract's
"starting from rest"; a force compactly supported in space *and* time is the paper's
`f ∈ C∞_c(R³ × (0,∞); R³)`. The prior audit's sentence ("the exhibited initial
velocity is identically zero and the force is compactly supported in space and time")
is accurate as a description of the Lean, and **is not a divergence from the paper**.
Anyone reading that sentence as a specification gap should be told this explicitly.

**F2. The PDE is imposed only on the open time interval `(0,1)`, on both sides.**
`R3/ProblemStatement.lean:104` (`navier_stokes : ∀ t ∈ Ioo 0 1`) and `:135`
(`GlobalFiniteEnergySolution.navier_stokes : ∀ t ∈ Ioi 0`). The paper writes (1.1)
for fields "on `R³ × [0,1)`" and for a competitor "on `R³ × [0,∞)`". The design
reason is stated and is sound — the operators are ordinary `fderiv`s, and at `t=0`
one would be differentiating an arbitrary extension to negative time
(`ProblemStatement.lean:13-17`) — and for the candidate the point is moot, since
`u = p = 0` for `|t| ≤ 3/8`. But the effect is asymmetric and should be named: it
makes the **positive** half of Theorem 1.1 marginally weaker (the equation at `t=0`
is not asserted) and the **negative** half marginally stronger (more fields qualify
as competitors, so ruling all of them out is a stronger claim). Net: not a defect;
the stronger direction is the one that matters for (C)/(D).

**F3. Lean's realized blow-up is stronger than anything the paper states.**
`FinalSlowBase.origin` (`NavierStokes/FinalSlowBase.lean:361`) gives the closed form
`u(t,0) = ((1−t)^{−(1/2+h)} · j) • e₂` with `j > 0` — blow-up at the **fixed spatial
origin**, along the axis, with an exact rate. The paper's proof of Theorem 1.1 uses
the *moving* path `x_τ = (√(2X_in τ),0,0)` and says only that those points converge
to the origin (p124); it never asserts that `‖u(t,0)‖ → ∞`. This is consistent with
§2.1's axial-outflow picture, but it is the single place where the Lean asserts more
about the flow than the manuscript does, and an expert should confirm the axial
closed form is the intended leading behaviour rather than an artifact of the
particular base profile chosen.

**F4. Lemma 9.8's residual exponent in Lean is `hj/10`, not the paper's `h(1/5+j/10)`.**
`MixedCandidateAssembly.lean:62-65` reuses the single `gain` for both (9.17) and
(9.18). Strictly weaker by `h/5` in the exponent. Only `gain → ∞` is used downstream
(`DiagonalScale.exists_diagonal_scales:156`), so nothing breaks — but the Lean
statement of (9.18) is not the paper's, and if anyone ever wants the paper's
`hσ_j` decay from the formalization, it is not there.

**F5. Lemma 10.2's "uniformly on R³" has no Lean counterpart; the Lean says locally
uniformly / uniformly on compacts** (`JointResidualLimits.lean:148,156`). Harmless,
because the force has fixed compact support and because Lean's Borel/Whitney route
(`CandidateFromLimits.force:82`) consumes boundary *jets* rather than a global
modulus — but it is a real gap between the paper's wording and the formal statement,
and it is the only place in §10 where I found one.

**F6. `energy_bounded` is a field of `CandidateProperties`, not a derived fact of the
consuming lemmas.** Every Lemma-10.4 and Lemma-10.5 statement takes
`hc : CandidateProperties ν u p f K` and thus receives the uniform energy bound as a
hypothesis. It *is* discharged for the actual construction by Lemma 10.4's own
argument (`R3/ActualCandidate.lean:126-129`, `CompactEnergy.uniform_finite_energy`
from the force + equation + zero datum), so nothing is circular and the top-level
`theorem_1_1` is unconditional — but the bundling means a file-local reader of
`IntegratedDissipation.lean` sees the energy bound both assumed and concluded.
`candidate_l2Norm_le_cumulativeForceNorm:143` is the one that genuinely re-derives it
and does **not** use the field; `candidate_uniform_kineticEnergy_le:183` does use it
(for integrability only).

**F7. Corollary 10.6's competitor class requires a periodic pressure.**
`PeriodicPaperTheorem.lean:56` (`pressure_periodic`). The paper's Cor 10.6 proof
("Periodic integration removes both the transport and pressure terms", p126) needs it,
Fefferman's erratum requires it, and the Comparator challenge's
`NavierStokesExistenceAndSmoothnessPeriodic` has `isOnePeriodic_pressure`
(`ComparatorChallenges/NavierStokes.lean:275`), so this is the standard formulation and
matches (D). Flagged only because it is the one hypothesis on a competitor that a
maximally general reading of "there is no global smooth periodic solution" would not
carry.

**F8. Propositions 10.1, 9.3 and 9.9 are not single Lean theorems.** 10.1 is four
theorems across three files (§2.3); 9.3 is split between `LinearWaveBounds` and the
`state_*` invariant bundle; 9.9 is `local_theorem` plus the summation machinery. This
is a navigability finding, not a strength finding, but it is why the docstring
cross-references are the only index and they are (F9) unreliable.

**F9. The Lean's paper cross-references are a mixture of two numbering systems, and
one of them is not the published PDF's.** See §6. Anyone using docstring citations as
a map will be wrong roughly half the time.

**F10. The §3–4 linkage is clean, and `exists_weighted_profile` is dead code.**
The headline's leading profile is `FinalSlowBase.actualProfile`
(`NavierStokes/FinalSlowBase.lean:634`), whose nonemptiness proof
(`:627-630`) makes exactly the two calls `NominalConeAssembly.exists_nominal_cone`
and `ModulatedProfileAssembly.exists_of_certificate` that
`ModulatedProfileAssembly.exists_modulated_profile:1126` makes — so the headline and
the §4 declarations meet (§2.7). But `LeadingStressWeights.exists_weighted_profile:1154`
has **zero references** in the repository; the headline reaches its three extra
conclusions individually (`FinalSlowBase.lean:147`,
`AlignedProfileSpectralCone.lean:443-444`) instead. Anyone auditing §4 by following
that theorem's name will believe it is load-bearing when it is a display wrapper.

**F11. Theorem 4.6(vi) is a conclusion, in `ReservedPatches.lean`, but never assembled
into one statement about the finished profile.** `heated_fields:333` +
`xAmplitude_shape:282` give `U = 0`, `E = c_patch(1+η²)^{-1}X^{-1/2-λ}` on every
non-`.heat` slot window (so on `I_pos = .positive` and `I_mean = .mean`), and
`supported_updates_preserve_fields:634` / `finite_updates_eqOn:648` are the paper's
"the construction of the leading profile leaves both intervals unchanged". The
`hpatchU`/`hpatchE` at `ModulatedProfileJetRates.lean:347` are the *repair theorem's*
hypotheses, discharged at `ModulatedProfileAssembly.lean:477-487` from
`nominal_patch_fields:207`. What is missing is a single declaration asserting (4.30)
for `I_pos`/`I_mean` about `modulation.profiles` (the `.modulation`-slot analogue
exists; the `.positive`/`.mean` one does not), and a check that every intermediate
modification is slot-supported. An expert should confirm that §5's Lemma 5.2 consumer
does what §8's does — `MeanRankUpdate.reserved_five_rows:1398` derives the shape from
`ReservedPatches.radial_heated_fields` rather than assuming it (`:1420`), which is the
right pattern; I did not find the `I_pos` side's analogue.

**No `LEAN WEAKER` finding in this slice has a "paper lemma false as stated" flavour.**
F4 is the only genuine strength gap in §9–§10 and the paper's stronger form is the
plausible one (the residual after `j` cycles has accuracy `σ_j`, which starts at
`1/5`, not `0`); Lean simply chose one common gain function.

---

## 5. What I did not check

* **Proof correctness anywhere** (by instruction), and no kernel-trust re-derivation.
* **Definition 9.4's (9.9) and (9.10)**: the cumulative bounds `w ∈ W_{1/2}`,
  `w − w₀^tan ∈ W_{0.68}`, `v, γ, p_m ∈ M_{0.9}`, `β ∈ M_{1.9}`, and the two exact
  moment constraints `∫R²⟨v⟩_Y dR = 0`, `∫R⟨γ⟩_Y dR = 0`. I read
  `ActualParticularCycleData.Data:41` (which gives (9.8)) but not the companion
  invariants (`ActualSignedCoherence`, `ActualMeanStageData`,
  `ActualIntermediateDebtBounds`, `ActualCycleResidualBounds`) that would carry these.
* **Proposition 9.5** analytically (only its arithmetic, `B₀ = 0.7`, `C*₀ = 1.2`, via
  `ExponentLedger.stage_parameter_zero:288`).
* **Proposition 9.3 parts (ii) and (iii)** — the flat remainder `|F^[j]|_m ≤ C_{j,m,N} q^N`
  uniform over bands/labels/points, and the exact mean equations (9.6). The
  `excludedSlotError` / `UnweightedClass s N` pair in `LinearWaveBounds` is the
  obvious candidate for (ii) but I did not verify the uniformity quantifiers.
* **Proposition 9.1's trailing clause** `π_m ∈ W_{α+1/2}`.
* **Lemma 9.7's derivative-counting sentence** (the DAG argument, p111–112).
* Whether the Lean's fixed spatial cutoff (radius `1/4`, height `1/4`) and time switch
  (`τ₀ = 5/8`) actually satisfy the paper's `q < q*/2` margin — that is a proof
  question about `ActualCandidateConstruction.qbig`, not a statement question.
* Whether every modification between `HeatedOutgoing` and the finished
  `ModulatedProfileAssembly.Witness.profiles` is routed through
  `ReservedPatches.Supported`/`RadialSupported` at a slot other than `.positive`/`.mean`
  (the hypothesis of `supported_updates_preserve_fields:634`). I checked the
  `.modulation` repair (`ModulatedProfileAssembly.lean:477-520`) and the heat increment
  (`heat_increment_supported:579`), not the rest.
* The §5 `Lemma 5.2` consumer of `I_pos` — whether it derives (4.30) from
  `ReservedPatches` the way `MeanRankUpdate.reserved_five_rows:1398` does for `I_mean`,
  or assumes it.
* The `Euler/` half of the repository, and the Euler comparator.
* I did **not** elaborate or compile anything; all conclusions are from reading
  statements.

**Greps and reads performed** (so "I couldn't find it" is scoped):
`grep -rn` over `NavierStokes/` and `NavierStokes/R3/` for
`Theorem 1\.1`, `Lemma 10\.`, `Proposition 10\.`, `Corollary 10\.`, `Lemma 11\.`,
`Proposition 11\.`, `Lemma 9\.`, `Proposition 9\.`, `Definition 9\.`, `Lemma 8\.`,
`(9\.`, `MeanVector`, `WaveVector`, `RawStageBounds`, `StageEstimates`,
`fundamentalCube`, `fundamentalInterior`, `SupportedInCube`, `axis_tendsto`,
`selected_witness`, `exists_candidate_witness_of_finite_stages`,
`candidate_l2Norm_le_cumulativeForceNorm`, `AwayExtensions`, `α + μ - 1 / 2`,
`α + β - κ`, `InitialVelocityConditionDecay`, `def gain`, `def A `, `state_`.
Full reads: `R3/ProblemStatement.lean`, `R3/Theorem.lean`, `R3/CandidateBreakdown.lean`,
`R3/WholeSpaceUniqueness.lean`, `R3/ComparatorBridge.lean`, `R3/ActualCandidate.lean`,
`ProblemStatement.lean`, `PeriodicPaperTheorem.lean`, `PeriodicPaperComparator.lean`,
`ComparatorTheorem.lean`, `ComparatorSolution.lean`, `ComparatorChallenges/NavierStokes.lean`,
`LocalAngularGrowth.lean`, `LocalPaperHeat.lean`, `ExponentLedger.lean` (index),
`ActualIterationLedger.lean` (head), `TimeLocalization.lean` (head + index).
Partial reads: `R3/IntegratedDissipation.lean`, `R3/H3MaximalLifespan.lean`,
`CandidateFromLimits.lean`, `JointResidualLimits.lean`, `DiagonalScale.lean`,
`SpatialLocalization.lean`, `WaveInteractionBounds.lean`, `LinearWaveBounds.lean`,
`CurlClassBounds.lean`, `CutStageEstimates.lean`, `MixedCandidateAssembly.lean`,
`ActualCandidateConstruction.lean`, `ActualCandidateAssembly.lean`,
`ActualCyclePreservation.lean`, `ActualCycleCoherence.lean`,
`ActualParticularCycleData.lean`, `GermCandidateAssembly.lean`, `LocalPaperTheorem.lean`,
`FinalSlowBase.lean`, `BlowupImplication.lean`, `PeriodicLocalization.lean`,
`PeriodicPaperSupport.lean`, `CoordinateAlgebra.lean`.
Paper: full reads of pp. 1–3, 100–126, plus pp. 15–16 (Theorem 3.1(iv)), p9 and p22
(the definition of `A`).

---

## 6. Draft → published numbering, established by content

The Lean's docstring citations use **two** systems. Files under `NavierStokes/R3/`
appear to have been written against the published (or near-final) numbering; the
core `NavierStokes/` construction files were written against a draft that had a §11
where the published paper has §10.

| Lean docstring cite | file | what the Lean actually contains | published counterpart | basis |
|---|---|---|---|---|
| "Lemma 11.3" | `DiagonalScale.lean:11,152,207` | `logPowerWeight C p r q = C(1+|log q|)^p q^r`, the diagonal cutoff schedule, the dyadic tail bound | the **summation cutoff selection of §9.5 / Lemma 5.4**, used with Lemma 9.8's (9.17) shape — **not** Lemma 10.2 | the expression is literally (9.17)'s majorant; nothing about `∂ᵅ∂ᵗf` limits |
| "Proposition 11.4" | `TimeLocalization.lean:15` | the time switch `χ_t`, giving zero initial datum | **Proposition 10.1** (its temporal-cutoff half, (10.4)) — **not** Lemma 10.3 | "the temporal cutoff gives zero initial datum", p118 |
| "Proposition 11.7" | `BlowupImplication.lean:9,124` | `q^{−A}(E+error) → ∞`, `arbitrarily_large_near_time`, `controlling_quantity_tendsto_atTop` | the **§10.4 growth/lifespan step inside the proof of Theorem 1.1** (p124: (10.21) and "The embedding `H³ ↪ L∞` excludes a classical `H³` continuation") — arguably not Lemma 10.5 | `controlling_quantity_tendsto_atTop` is literally the `H³ ↪ L∞` step |
| "Proposition 10.3" | `ExponentLedger.lean:9`, and "§8.1 and again in §10.2" at `:14` | `waveExponent σ = 1/2+σ`, `meanExponent σ = 1+σ`, `stageParameter n = 1/5+n/10`, `κ = 10⁻⁵` | **Definition 9.4 (9.8)** plus the gains in **Proposition 9.6**; `κ_s = 10⁻⁵` is fixed "throughout this section" in published **§9** (p100) | exponent-for-exponent identity |
| "Lemma 9.2" | `CurlClassBounds.lean:757` | the **curl remainder** `r_m ∈ W_{α+1/2−κ}` | published **Lemma 7.7**, as cited in published §9.1 (p101: "If `t_m ∈ W_α`, then Lemma 7.7 gives `r_m ∈ W_{α+1/2−κs}`") — **not** published Lemma 9.2 | the theorem is `curlRemainder_waveClass`, about the curl correction only |
| "Proposition 9.3" | `LinearWaveBounds.lean:896` | linear harmonic residual in `W_{α+1/2−3κ}` + all-order flat error | published **Proposition 9.1** (p101) | the `α+1/2−3κ_s` exponent and the flat pulse-cutoff tails are Prop 9.1's exact conclusion |
| "Lemma 10.4" | `R3/IntegratedDissipation.lean:72,201,276` | `‖u(T)‖²₂ + 2ν∫ dissipation ≤ F(T)²`, integrability, `F(1)<∞` | published **Lemma 10.4** — the numbers coincide | content identity |
| "Theorem 1.1" | `R3/ProblemStatement.lean`, `R3/Theorem.lean`, `LocalAngularGrowth.lean`, `ProblemStatement.lean` | as in §2 | published **Theorem 1.1** | content identity |
| "Lemma 8.3 / 8.4 / 8.5 / 8.7 / 8.8" | `SlotGeometry`, `TangentProjection`, `PulseGrowth`, `TorusAverages`/`Covariance`, `CurlGeometry` | slot centres, tangent projection algebra, scalar growth, the finite-dimensional covariance algebra, the curl realization | **published §7** items (draft §8 ≈ published §7), by the same one-section shift; I did not verify these individually — outside my slice | pattern only |

**Net rule established:** for the core construction files, **draft §N ≈ published §(N−1)**
for `N ≥ 8` (draft 11 → published 10, draft 10 → published 9, draft 9 → published 8/7,
draft 8 → published 7), with item numbers *not* preserved inside a section. The
`R3/` files use published numbering directly. The brief's three guesses
(draft 11.3 ≈ published 10.2; draft 11.4 ≈ published 10.3; draft 11.7 ≈ published 10.5)
are **not** what the content supports; the corrected map is in the table above.
