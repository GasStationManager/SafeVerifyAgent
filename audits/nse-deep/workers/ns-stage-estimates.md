# Worker report: NS stage estimates, `VanishingJointJets` / `AwayExtensions`, and the `gain J -> infinity` discharge

Audit target: `/home/gsm/.openclaw/workspace/repos/NSE` @ f9e8bc5 (read-only).
Method: source-level reading of actual statements and actual proof terms/tactics. No `lake build`
(no Mathlib on this box). Every claim below carries `file:line` (paths relative to the NSE repo root).

Headline verdict up front, because it is the answer the parent wants:
**this cluster is NOT the "unproved `hres`" pattern the sibling worker found elsewhere.**
`StageEstimates.finite_residual` is a structure FIELD (a hypothesis) at
`NavierStokes/MixedCandidateAssembly.lean:62`, but on the live path it is *discharged by a real
theorem* — `ActualCycleResidualBounds.finite_residual_rates`
(`NavierStokes/ActualCycleResidualBounds.lean:1190`) — which is itself fed by a genuine
induction on the correction cycle (`ActualCyclePreservation.state_runInvariant`,
`NavierStokes/ActualCyclePreservation.lean:826`). I looked hard for a dangling hypothesis and
did not find one in this cluster. The remaining risk is *quantitative* and sits one level deeper
(`CorrectionAnalyticStep.step`), not structural.

---

## Scope

Files touched, declaration counts from `SafeVerifyAgent/audits/nse-deep/CONE.csv` (mark-4
regenerated cone), and how much I actually read:

| file | decls | `in_cone=False` | how read |
|---|---|---|---|
| `NavierStokes/JointResidualLimits.lean` | 34 | 19 | **all 324 lines, line-by-line** |
| `NavierStokes/MixedCandidateAssembly.lean` | 7 | 1 | **all 213 lines, line-by-line** |
| `NavierStokes/MixedDiagonalResidual.lean` | 13 | 2 | **all 268 lines, line-by-line** |
| `NavierStokes/MixedDiagonalExtensions.lean` | 14 | 0 | **all 211 lines, line-by-line** |
| `NavierStokes/ActualCycleResidualBounds.lean` | 89 | 3 | **all 1208 lines, line-by-line (two passes)** |
| `NavierStokes/ActualCyclePreservation.lean` | 80 | 10 | **all 932 lines, line-by-line** |
| `NavierStokes/GluedStageEstimates.lean` | 52 | 5 | lines 1-60, 330-520, 620-748 read; rest skimmed |
| `NavierStokes/DiagonalResidual.lean` | 21 | 4 | lines 1-60 and 150-300 read (incl. `residual_jetRate_of_stages`); rest skimmed |
| `NavierStokes/SolenoidalDiagonal.lean` | 28 | 12 | lines 1-200 read; 200-319 skimmed |
| `NavierStokes/GermCandidateAssembly.lean` | 14 | 4 | lines 160-308 read (the live discharge) |
| `NavierStokes/ActualCandidateAssembly.lean` | 103 | 12 | lines 460-500 and 1020-1187 read; rest skimmed |
| `NavierStokes/ActualStageEstimates.lean` | 28 | 8 | `RunData` (97-140) read; rest grep-only |
| `NavierStokes/ActualIterationLedger.lean` | 68 | 35 | `sigma`/`gain` block read by targeted grep only |
| `NavierStokes/CorrectionAnalyticStep.lean` | 23 | 3 | `StepResult` + `step` *signature* only (~40 lines of 690) |
| `NavierStokes/SmoothCutoffs.lean` | 47 | 7 | cutoff lemmas 134-200 read |
| `NavierStokes/SimilarityApproach.lean` | 8 | 1 | `jet_tendsto_zero` read |
| `NavierStokes/ActualCandidateConstruction.lean` | 127 | 47 | `firstBand`/`qbig`/`residualBand`/`selected*` (142-220) read |
| **total** | **756** | **173** | ~4300 lines read line-by-line, ~2000 skimmed |

Kinds in the 12 primary files: 420 theorem, 91 def, 12 abbrev, 12 structure, 2 instance.

---

## A. The two predicates, stated exactly

`NavierStokes/JointResidualLimits.lean:81-86`:

```lean
def AwayExtensions (f : SpaceTime → V) : Prop :=
  ∀ x : Space, x ≠ 0 → Nonempty (OneSidedExtension f x)

def VanishingJointJets (f : SpaceTime → V) : Prop :=
  ∀ n : ℕ, Tendsto (iteratedFDeriv ℝ n f)
    (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))) (𝓝 0)
```

with (`:73-79`)

```lean
structure OneSidedExtension (f : SpaceTime → V) (x : Space) where
  value : SpaceTime → V
  domain : Set SpaceTime
  isOpen : IsOpen domain
  mem : (1, x) ∈ domain
  smooth : ContDiffOn ℝ ∞ value domain
  agrees : EqOn value f (domain ∩ SpacetimeEndpoint.openPast 1)
```

**Answer to A: it is the STRONG version — every jet tends to ZERO, and jointly in `(t,x)`.**
Not "tends to a limit". Two things make it strong rather than weak:

1. The target is the literal `𝓝 0`, not `𝓝 (L x)`.
2. The filter is a *joint* filter. `past_filter` (`:88-91`) proves
   `𝓝[SpacetimeEndpoint.openPast 1] ((1:ℝ), x) = (𝓝[<] (1:ℝ)) ×ˢ 𝓝 x`, and
   `openPast T = Iio T ×ˢ univ` (`NavierStokes/SpacetimeEndpoint.lean:25`). So the assertion
   unpacks to: for every `n` and `ε>0` there are `δ,η>0` with
   `‖iteratedFDeriv ℝ n f (t,x)‖ < ε` whenever `1-δ < t < 1` and `‖x‖ < η`. That is uniform on
   shrinking spatial balls around the blow-up point, not a one-parameter limit along `x = 0`.

This strength is *load-bearing and not decorative*: `continuous_of_joint_limits` (`:30-52`) uses
exactly the joint filter to get continuity of the boundary trace, and `boundaryLimits_continuous`
(`:141`) instantiates it at `p := 𝓝[<] 1`. A weaker "for each fixed `x`" hypothesis would not
close that argument. I checked this by reading the proof: it extracts
`U ∈ p, W ∈ 𝓝 x` from `Filter.mem_prod_iff` and needs both factors.

Note the asymmetry, which is the honest mathematical shape of a one-point blow-up:
`VanishingJointJets` constrains the residual **only at the origin** `x = 0`; away from the origin
the only requirement is `AwayExtensions`, i.e. a genuinely smooth local extension across `t = 1`
whose jets are *unconstrained*. The boundary family is then assembled by
`boundaryLimits` (`:120-124`)

```lean
exact if hx : x = 0 then 0 else ftaylorSeries ℝ (Classical.choice (hext x hx)).value (1, x)
```

The `x = 0` branch is *defined* to be `0`. This is the one place a junk-value trick could hide,
so I checked it: `boundaryLimits_joint` (`:130-140`) has to prove
`Tendsto (iteratedFDeriv ℝ n f) … (𝓝 (boundaryLimits f hext x n))` and in the `x = 0` case it
discharges it with `simpa only [boundaryLimits_zero] using hzero n` — i.e. the definitional zero
is *matched by* `VanishingJointJets`, not substituted for it. **Not junk exploitation.**

---

## B. `StageEstimates.finite_residual` and the `gain J -> infinity` mechanism

### B1. Where the obligation lives

`NavierStokes/MixedCandidateAssembly.lean:29-65` — `StageEstimates` is a bundle of hypotheses,
with the two endpoint fields

```lean
  gain : ℕ → ℝ
  gain_top : Tendsto gain atTop atTop            -- :37
  residualLoss : ℕ → ℝ                            -- :58
  finite_residual : ∀ J m,                        -- :62
    JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
      (fun z => navierStokesResidual (MixedDiagonalResidual.uncutVelocity A B J)
        (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (gain J - residualLoss m)
```

`JetRate l q f m r := ∃ C ≥ 0, ∀ᶠ x in l, ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r`
(`NavierStokes/DiagonalResidual.lean:33-34`). Two uniformities matter and both hold:
`residualLoss` depends on `m` only (never on `J`), and `C` is allowed to depend on `J` and `m`.
The module docstring is candid that it is only a consumer
(`MixedCandidateAssembly.lean:11-13`: "This is a conditional consumer. It does not construct the
complete correction iteration or supply the finite-stage estimates it requires.").

### B2. Who supplies it (the sibling's `hres` question)

There are exactly three constructors of `MixedCandidateAssembly.StageEstimates` in the repo
(`grep`): `GluedStageEstimates.lean:379` and `:684`, and `ActualStageEstimates.lean:347`. The
one on the live path (see C) is `GluedStageEstimates.actualStageEstimates:684`, which wraps
`stageEstimates_of_component_bounds:379`. In that constructor, `GluedStageEstimates.lean:422`
leaves `finite_residual := ?_` and discharges it at `:436-440`:

```lean
· exact ActualCycleResidualBounds.finite_residual_rates hGeom (by omega)
    (fun _ => ActualCycleParameters.fixedParameters B N0)
    (fun J => MixedDiagonalResidual.uncutVelocity A Bdirect J)
    (fun J => DiagonalJetBounds.uncutPrefix P (J + 1))
    (fun J => ActualCyclePreservation.broad_invariant (R.invariant J)) d
```

`finite_residual_rates` (`ActualCycleResidualBounds.lean:1190-1206`) is a real theorem. Its two
substantive inputs are:

* `H : ∀ J, Invariant (ActualIterationLedger.sigma J) (CycleState.iterate p c seed J)` — the
  analytic cycle invariant at *every* stage, with the stage exponent `sigma J`;
* `d : ∀ J, PhysicalData B N (…).state (u J) (P J)` — an *identification* record (the docstring
  at `:1156-1157` says "The local physical fields are only identified, never bounded, by `d`",
  and reading `PhysicalFields` at `:1015-1037` confirms it: its fields are smoothness/germ
  equalities and an exterior equality, no size estimate).

and the proof body is

```lean
  have he := (H J).residual_jetRate hGeom hN (actual_iterate_base_error p J) (d J) m
  have hgain := ActualIterationLedger.gain_le_residualWave ActualPrimary.outgoing.data.h_pos.le J
  exact he.weaken origin_positive_small (sub_le_sub_right hgain _)
```

`Invariant.residual_jetRate` (`:1158-1171`) proves the per-stage decay
`h * (1/2 + σ) - fixedLoss m` from `native_residual` (`:845-877`, a genuine term-by-term
decomposition of the literal state residual: oscillation sum + mean + base/gaussian/alias errors)
pushed through `selected_residual_jetRate` (`:956-988`) and the polar/band geometry.

So `hres` here is **proved, not assumed**. Concretely the chain is closed:

```
finite_residual (hypothesis field)
  <- ActualCycleResidualBounds.finite_residual_rates            (ActualCycleResidualBounds.lean:1190)
     <- Invariant.residual_jetRate                              (:1158)
        <- Invariant.native_residual + selected_residual_jetRate (:845, :956)
     <- H := ActualCyclePreservation.broad_invariant (R.invariant J)   (ActualCyclePreservation.lean:301)
        <- RunData.invariant := ActualCyclePreservation.state_invariant (ActualCandidateAssembly.lean:479)
           <- state_runInvariant, by induction                   (ActualCyclePreservation.lean:826-833)
              base: initial_runInvariant                         (:773)
              step: next_runInvariant -> CorrectionAnalyticStep.step (:817, CorrectionAnalyticStep.lean:~500)
     <- d := ActualCandidateAssembly.physicalData                (ActualCandidateAssembly.lean:1079)
```

### B3. `gain J -> infinity` is arithmetic, not an assumption

`ActualIterationLedger.lean:22-38`: `sigma 0 = 1/5`, `sigma (J+1) = sigma J + 1/10`,
`sigma_admissible : 1/5 ≤ sigma J`. `gain h j = h * j / 10` (`:29`), so
`gain_tendsto_atTop` is genuine for `h > 0`, and `gain_le_residualWave` gives
`gain h J ≤ h * (1/2 + sigma J)` — exactly the per-stage exponent proved by the invariant.
The `+1/10` per cycle comes from `next_runInvariant_of_particular`
(`ActualCyclePreservation.lean:800-809`), whose `analytic` field is
`(stepResult_of_particular …).invariant` where
`StepResult.invariant : CycleAnalyticInvariant … (σ+1/10) (CycleState.step p c x)`
(`CorrectionAnalyticStep.lean`, `structure StepResult`). The induction
(`ActualCyclePreservation.lean:826-833`) is a plain `Nat` induction with `rw [sigma_succ, state_succ]`.

**This is the real substance of the whole NS construction and it is present.**

---

## C. The call sites `ActualCandidateAssembly.lean:1090` and `:1100`

`:1090-1098` (`estimates`) and `:1100-1113` (`endpoints`) — both are `in_cone=True` in
`CONE.csv`, i.e. live.

```lean
noncomputable def estimates (B N0 : ℕ) (hN : geometricThreshold ≤ N0) :
    MixedCandidateAssembly.StageEstimates h (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) :=
  GluedStageEstimates.actualStageEstimates (runData B N0 hN) (meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0) (ActualSignedWaveData.signedInputs B N0 hN)
    (ActualCyclePreservation.state_coherent B N0 hN) le_rfl
    (ActualCandidateConstruction.qbig_pos B N0) hN _ _ _
    (representations B N0 hN) (physicalData B N0 hN)
```

Hypothesis-by-hypothesis availability check (this was the specific vacuity hunt):

| slot | supplied by | genuinely available? |
|---|---|---|
| `R : RunData B N0` | `runData B N0 hN` (`:476-481`), fields = `state_invariant`, `state_stepData`, `state_particularInputs` | yes, all three are theorems/defs proved in `ActualCyclePreservation` |
| `hN : 4 ≤ N` with `N := firstBand B N0` | `firstBand_four` = `le_max_left`, since `firstBand = max 4 (bandFloor …)` (`ActualCandidateConstruction.lean:142-144`) | yes |
| `hq : qbig ≤ ChartScales.Q N` | `le_rfl` | **yes, and not a cheat**: `qbig B N0 := ChartScales.Q (firstBand B N0)` (`:155`), so this is literally reflexivity, not an instantiation that trivializes anything |
| `hqbig : 0 < qbig` | `qbig_pos = ChartScales.Q_pos _` (`:157`) | yes, `qbig = 2^(-firstBand) > 0`, **not zero**, so the sublevel domain is nonempty |
| `hGeom : geometricThreshold ≤ N0` | passed through; finally discharged by `selectedThreshold_geometry` (`:209`) with `N0 := startingThreshold 0 = max 0 geometricThreshold` | yes |
| `d : ∀ J, PhysicalData B (N+1) …` | `physicalData B N0 hN` at `:1079-1088`, typed at `residualBand B N0` | yes, and `residualBand = firstBand + 1` (`:165`) so `N+1` matches exactly |

No instantiation collapses anything. `B := selectedBudget = 0` and
`N0 := selectedThreshold = startingThreshold 0` (`ActualCandidateConstruction.lean:205-210`) are
concrete, and `qbig > 0` is a positive real, so the "physical sublevel" region on which every
stage estimate lives is a genuine nonempty open set.

`:1100` (`endpoints`) calls `GermEndpointInputs.actual_germ_stage_endpoints_of_estimates` with
`estimates B N0 hN` plus three side goals discharged by `rfl` / `rw [directStages_zero]; rfl` —
these are stage-zero identifications, definitional, and they are the *right* three (potential,
direct, pressure at `j = 0`).

**One finding worth recording, though it is a cleanliness point rather than a hole.** The parent
named `MixedCandidateAssembly.candidate_of_finite_stages`
(`MixedCandidateAssembly.lean:130`) as the consumer. In the regenerated cone that declaration is
`in_cone=False` — **dead code**. The live discharge is
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages`
(`GermCandidateAssembly.lean:164-304`, used at `ActualCandidateAssembly.lean:1153` = `witness`,
which `selected_witness:1177` instantiates and which is what `R3/ActualCandidate.lean:132,149`
consumes). I read the live one in full: it is the same argument shape as the dead one, so the
substance of the parent's question transfers unchanged. Also dead: `selected_candidate:1183`
(the `candidateStatement` wrapper) — the live consumers use `selected_witness` directly.

`AwayExtensions` discharge, checked for a coverage gap (this was my main vacuity suspicion, since
the supplied hypotheses `eA/eB/eP` are guarded by `x 2 ≠ 0 ∧ endpointRoot (2h) (x 2) < qbig`):
`MixedDiagonalExtensions.diagonal_awayExtensions_local` (`MixedDiagonalExtensions.lean:195-211`)
does a complete case split on `x ≠ 0`:

* `x 2 = 0`: `central_extension_local` (`:183`), which needs `sum_eventually_eq_initial` (`:158`)
  — all positive stages vanish near `(1,x)` by the shrinking-support hypothesis and the
  stage-0 cutoff is identically `1` there, so the sum equals `F 0` and the base extension transfers;
* `x 2 ≠ 0` and `endpointRoot < qbig`: `offplane_extension_local` (`:83`) uses the supplied `eA`;
* `x 2 ≠ 0` and `endpointRoot ≥ qbig`: the *same* lemma's other branch,
  `sum_eventually_zero_of_scale_large` (`:66`) — every cutoff is `0` on a common past
  neighborhood since `1/a 0 < qbig ≤ endpointRoot`, so the sum is locally zero and
  `extension_of_eventually_zero` applies.

All three branches are real. **No coverage gap, nothing vacuous.**

---

## D. The failure mode I was told to hunt: interchange of limits, assumed summability

I hunted both. **I did not find either, and I want to be explicit about why, because these are the
two places where this proof would most naturally be wrong.**

### D1. `J -> infinity` versus `t -> 1^-` versus derivative order

The interchange is *avoided by construction*: `J` is chosen **after** `(m, r)`, inside
`DiagonalResidual.residual_jetRate_of_stages` (`DiagonalResidual.lean:196-270`). The mechanism,
quoting the actual proof:

```lean
  let b := maxJetLoss Lbg (m + 1)
  let t := maxJetLoss Ltail (m + 2)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (hg.eventually (eventually_ge_atTop (max (n + b + t) (n + Lres m))))
  let J := max (m + 2) J₀
```

then the *exact algebraic identity*

```lean
  have hidentity :
      (fun z => navierStokesResidual (uStage J) (pStage J) z.1 z.2 +
        residualDifference (uStage J) (fun y => u y - uStage J y)
          (pStage J) (fun y => p y - pStage J y) z) =
      (fun z => navierStokesResidual u p z.1 z.2) := by
    funext z; simp only [residualDifference, huadd, hpadd]; abel
```

so the full-sum residual is *identically* (stage residual) + (perturbation), with the
perturbation bounded by `perturbation_majorant_le` (`:~120`) — a six-term algebraic inequality
`q^(-b) * q^(n+b) ≤ q^n` etc. No limit is exchanged: for each requested `(m, n)` there is one
`J`, one constant, and one eventual neighborhood. The `Lbg`/`Ltail`/`Lres` losses are functions
of the derivative order only, never of `J`, and I verified that the instantiation honours this
(`ActualCycleResidualBounds.fixedLoss:1145`, `residualLoss h beta m` at
`ActualIterationLedger.lean:~289` — both `J`-free).

The final step from "all powers" to "jets vanish" is a squeeze, not an interchange:
`SimilarityApproach.jet_tendsto_zero` (`NavierStokes/SimilarityApproach.lean:93-103`) takes
`JetRate l q f m 1` (exponent exactly `1`) plus `Tendsto q l (𝓝 0)` and applies
`squeeze_zero'`. `MixedDiagonalResidual.physical_vanishingJointJets:168-198` calls it with
`r := 1`, and `AnnularEndpoint.physicalQ_tendsto_zero`
(`NavierStokes/AnnularEndpoint.lean:49-61`) supplies `q → 0` along
`𝓝[openPast 1] (1, x)` for `x 2 = 0` (so in particular at `x = 0`). Honest.

**Where an expert should still push (see Escalations):** the *uniformity in `m` of the constants*
is never needed, and correspondingly never proved — which is fine for `VanishingJointJets` as
stated, since that predicate is `∀ n, Tendsto …` and each `n` gets its own `C` and its own
neighborhood. If any downstream consumer needed a *uniform-in-`n`* statement (e.g. a Gevrey or
analyticity claim), it would not follow from what is proved here. I checked the direct consumers
(`boundaryLimits_joint`, `boundaryLimits_locallyUniform`) and they are per-`n`, so this is
consistent — but it is the seam to watch.

### D2. The sum of corrections

`SolenoidalDiagonal.potentialSum` is a literal `tsum`
(`NavierStokes/SolenoidalDiagonal.lean:37-38`):

```lean
def potentialSum (a : ℕ → ℝ) (q : X → ℝ) (A : ℕ → X → V) (x : X) : V :=
  ∑' j : ℕ, cutStage a q A j x
```

A `tsum` of a non-summable family is `0` in Lean, so this is a textbook junk-value hazard, and
I treated it as my prime suspect. **It is not exploited.** `cutStage a q A j x =
scaledCutoff (a j) (q x) • A j x` (`:33`) and `SmoothCutoffs.scaledCutoff_zero_of_inv_le`
(`NavierStokes/SmoothCutoffs.lean:148`) gives `scaledCutoff a q = 0` once `1/a ≤ q`. Hence
`scaledCutoffs_zero_on_common_neighborhood` (`SmoothCutoffs.lean:190-200`, explicit neighborhood
`q > q₀/2`) yields `eventually_zero_tail` (`SolenoidalDiagonal.lean:46-53`): at any point with
`q x > 0` there is `N` and a *neighborhood* on which every stage `j ≥ N` is identically zero.
Consequences, all proved:

* `summable_cutStage:69` via `summable_of_ne_finset_zero` — summability is **proved**, not assumed;
* `potentialSum_eventuallyEq_partial:58` — the `tsum` equals the finite prefix
  `partialPotential … N` on a neighborhood, so it is not merely pointwise-equal-to-a-limit;
* `potentialSum_allJets_eventuallyEq_sum:165` — the *same* `N` works for **every** derivative
  order `k` ("The prefix length is independent of the derivative order", and the proof confirms
  it: `⟨N, fun k => …⟩` with `N` bound before `k`).

So near the endpoint (where `q > 0`, i.e. on `preterminal = {w | w.1 < 1}`,
`NavierStokes/PhysicalWaveSum.lean:386`) the "infinite sum" is *locally a finite sum*, and every
jet identity is a finite-sum identity. At the singular point `(1,0)` itself `q = 0` and the
`tsum` may indeed be junk — but the point is never used: `openPast 1 = Iio 1 ×ˢ univ` excludes
`t = 1`, so `𝓝[openPast 1] (1,0)` only sees `t < 1`, and all the smoothness statements are
`ContDiffOn … (openPast 1)` or on `preterminal`. **No assumed convergence; no junk value in the
live argument.** I am stating this loudly in the negative direction because it is the one place I
expected to catch something and did not.

### D3. Things I did NOT manage to falsify but that are the actual load
The per-cycle gain `+1/10` (with per-cycle losses `κ ≤ 1/100000`) is asserted by
`CorrectionAnalyticStep.step`'s conclusion and proved in ~600 lines I did not read. That is
where the mathematics could still be wrong. See Escalations #1.

---

## Per-declaration findings

Verdict tags: OK / UNCLEAR / KERNEL-RISK / SUSPICIOUS.
"cone" = `in_cone` from `SafeVerifyAgent/audits/nse-deep/CONE.csv`.

### `NavierStokes/JointResidualLimits.lean`

| decl | file:line | statement (my words) | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `continuous_of_joint_limits` | `:30` | joint convergence `F → L x` along `p ×ˢ 𝓝 x` for all `x` forces `Continuous L` | `Metric.tendsto_nhds`, `Filter.mem_prod_iff` to split the product filter, then an `ε/2 + ε/2` triangle inequality through an intermediate `F (i,y)`. Uses `[p.NeBot]` to get the witness `i`. Genuine and non-trivial | T | OK |
| `locallyUniform_of_joint_limits` | `:55` | same hypothesis gives `TendstoLocallyUniformly` | `tendstoLocallyUniformly_iff_forall_tendsto`, then composes the uniformity filter facts with the continuity just proved | T | OK |
| `OneSidedExtension` | `:73` | structure: open nbhd of `(1,x)`, a smooth function on it, agreeing with `f` on the *past* part only | — | T | OK — the "one-sided" weakening is correct and not a hidden strengthening |
| `AwayExtensions` | `:81` | such an extension exists at every `x ≠ 0` | def | T | OK |
| `VanishingJointJets` | `:84` | all jets `→ 0` jointly at `(1,0)` from the past | def | T | OK (strong form; see A) |
| `past_filter` | `:88` | `𝓝[openPast 1] (1,x) = 𝓝[<]1 ×ˢ 𝓝 x` | `simp [openPast, nhdsWithin_prod_eq, nhdsWithin_univ]` | T | OK — this is the identity that makes the joint reading provable, I re-derived it by hand from `openPast = Iio 1 ×ˢ univ` |
| `OneSidedExtension.eventuallyEq` | `:92` | `f = e.value` near `(1,x)` within the past | `filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds …]` | T | OK |
| `.jets_eventuallyEq` | `:100` | all iterated derivatives agree there | `EventuallyEq.iteratedFDerivWithin` + `iteratedFDerivWithin_of_isOpen` (legitimate, since `openPast` is open) | T | OK |
| `.jet_tendsto` | `:108` | `iteratedFDeriv n f → iteratedFDeriv n e.value (1,x)` | `ContDiffAt.iteratedFDeriv_right` then `continuousAt.tendsto.mono_left nhdsWithin_le_nhds`, transferred by `.congr'` | T | OK |
| `boundaryLimits` | `:120` | the boundary jet family: `0` at the origin, `ftaylorSeries` of a chosen extension elsewhere | `Classical.choice` on `hext` | T | OK (choice is fine; independence is proved at `:175`, albeit off-cone) |
| `boundaryLimits_zero` | `:126` | family is `0` at `x = 0` | `simp [boundaryLimits]` — definitional | T | OK, **but** see the note in A: this is only sound because `:130` re-proves the *limit* from `hzero` |
| `boundaryLimits_joint` | `:130` | the family really is the joint limit at every `x` | case split; `x=0` uses `hzero n`, else `jet_tendsto` | T | OK — this is the load-bearing one |
| `boundaryLimits_continuous` | `:141` | the trace is continuous | `continuous_of_joint_limits` at `p := 𝓝[<]1` | **F** | OK (dead code) |
| `boundaryLimits_locallyUniform` | `:148` | locally uniform convergence of each jet to the trace | `locallyUniform_of_joint_limits` | T | OK |
| `boundaryLimits_uniformOn_compact` | `:156` | upgrade to compacts | `tendstoLocallyUniformly_iff_forall_isCompact` | F | OK (dead) |
| `past_filter_neBot` | `:162` | the past filter is `NeBot` | `rw [past_filter]; infer_instance` | F | OK (dead) — needed only by the off-cone uniqueness lemmas |
| `boundaryLimits_eq_extension` / `_independent` / `_eq_of_eqOn_past` | `:169,:175,:191` | the family is choice-independent and depends only on past values | `tendsto_nhds_unique` | F | OK (dead). Worth noting: the *live* path therefore never needs choice-independence |
| `iteratedFDeriv_eqOn_past` | `:181` | jets agree if functions agree on the open past | `iteratedFDerivWithin_congr` + open-set transfer | F | OK (dead) |
| `actual_derivative_recurrence` | `:207` | `d/dz (∇^n f) = (∇^{n+1} f).curryLeft` on `t<1` | `fderiv_iteratedFDeriv` | F | OK (dead) |
| `boundaryLimits_smooth`, `extendedJets_compatible`, `boundaryLimits_hasFDerivAt` | `:220,:227,:240` | the boundary tensors are smooth and Whitney-compatible | delegate to `SpacetimeEndpoint.*` | F | OK (dead here — the live path uses `MixedPeriodicAssembly.boundaryLimits`) |
| `extendedResidual*` (6 decls) | `:257-293` | zero-order extension of `f` past `t=1` by the trace, smooth on `closedPast`, flat at the origin, unit-periodic | delegate to `SpacetimeEndpoint.extendTrace`/`contDiffOn_joint_extension` | F | OK (dead) |
| `exists_residual_limits`, `exists_smooth_compatible_limits` | `:295,:308` | packaging theorems | anonymous constructor | F | OK (dead) |

19 of 34 decls in this file are off-cone. That is a lot of unused scaffolding, but nothing in the
live 15 is weakened by it.

### `NavierStokes/MixedCandidateAssembly.lean`

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `StageEstimates` | `:29` | bundle: stage smoothness, a `gain` sequence with `gain_top`, raw stage bounds, and the two `finite_*` jet-rate families | structure (hypotheses) | T | OK as a *specification*; the honesty question is entirely about who builds it (answered in B2) |
| `StageEstimates.exists_schedule` | `:67` | from a `StageEstimates` produce a scale schedule `a` (`2 a j ≤ a (j+1)`, strict mono, `→ ∞`, `1/a j < qbig`) with three smooth sums and `VanishingJointJets` of the residual | forwards every field of `E` into `MixedDiagonalResidual.exists_physical_schedule_residual_zero`; the only extra work is `hS : ∀ᶠ z in 𝓝[openPast 1] (1,0), z ∈ preterminal` proved by `filter_upwards [self_mem_nhdsWithin]` + `hz.1` | T | OK |
| `potentialStages` / `pressureStages` | `:100,:110` | splice the anchored base + initialization into stage `0`, shift the rest | `MixedAxisPreservation.initializedSeries`; `fun j w => if j = 0 then base + initial else stages (j-1)` | T | OK — the `if`/`j-1` shift is matched by `pressureStages_zero:115` and `pressureStages_succ:121`, both proved, so no off-by-one |
| `candidate_of_finite_stages` | `:130` | the whole candidate statement from finite-stage data | assembles schedule, away-extensions, cut divergence, axis blow-up, then `MixedPeriodicAssembly.exists_candidate_force` | **F** | OK but **DEAD CODE**; the live twin is `GermCandidateAssembly.lean:164` |

### `NavierStokes/MixedDiagonalResidual.lean`

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `velocity`, `uncutVelocity`, `pressure`, `residual` | `:26,:32,:36,:39` | cut sums; `uncutVelocity A B J = curl (prefix A (J+1)) + prefix B (J+1)`; `residual := navierStokesResidual (velocity) (pressure)` | defs | T | OK. Note the prefix length is `J+1`, so stage `0` is always retained — consistent with `finite_residual`'s use |
| `residual_eq_originalResidual` | `:45` | `residual a q A B P = MixedPeriodicAssembly.originalResidual …` | `rfl` | F | OK — off-cone precisely because it is definitional; the live typing at `CandidateConsequences.lean:190` succeeds by defeq |
| `velocity_smooth` | `:52` | the mixed sum is `C^∞` where `q>0` | `velocitySum_contDiffOn.add potentialSum_contDiffOn` | T | OK |
| `uncutVelocity_smooth` | `:72` | finite prefix is `C^∞` | `ContDiffOn.sum` + `contDiffAt_spatialCurl` | T | OK |
| `velocityLoss` | `:87` | `max (LA (m+1)) (LB m)` — one derivative charged to the potential branch only | def | T | OK, and the `m+1` is right: the potential enters through a curl |
| `velocity_tail_jetRate` | `:89` | tail `velocity − uncutVelocity J` decays like `q^(g(J+1) − velocityLoss m)` | two `jetRate_diagonal_*_tail` lemmas, `weaken`, then `abel` to identify the algebraic difference | T | OK |
| `residual_jetRate` | `:125` | **for every `m` and every `r ≥ 0`**, the full-sum residual has jet rate `r` | `DiagonalResidual.residual_jetRate_of_stages` (the `J`-after-`(m,r)` argument) | T | OK — this is the crux of D1 |
| `physical_vanishingJointJets` | `:168` | the above + `q → 0` gives `VanishingJointJets` | `SimilarityApproach.jet_tendsto_zero` at `r := 1` | T | OK |
| `exists_physical_schedule_residual_zero` | `:200` | one schedule `a` serving all three families, with `VanishingJointJets` | `MixedDiagonalSchedule.exists_three_component_local_schedule` then the previous theorem; halves the gain (`g j / 2`) and re-weakens `hres` by `linarith [hnonneg J]` | T | OK. I checked the `g/2` bookkeeping: `hhalftop` proves `g/2 → ∞` from `g → ∞`, and the `hres` weakening needs only `0 ≤ g J`, which `hg0`+`hgmono` give |

### `NavierStokes/MixedDiagonalExtensions.lean` (14 decls, **0 off-cone** — all live)

| decl | file:line | statement | mechanism | verdict |
|---|---|---|---|---|
| `extension_of_eventuallyEq` | `:29` | transfer an extension along past-only agreement | shrinks `e.domain` by the `mem_nhdsWithin` witness `U`; `agrees` re-proved by composing the two equalities | OK |
| `extension_of_eventually_zero` | `:42` | locally-zero fields have extensions | `AnnularEndpoint.zeroExtension` | OK |
| `physicalQ_tendsto_endpoint` | `:50` | for `x 2 ≠ 0`, `q → endpointRoot (2h) (x 2) > 0` | continuity of a smooth Cartesian extension of `q`, transferred by `.congr'` | OK — **positive** limit, which is what makes the off-axis branch work |
| `sum_eventually_zero_of_scale_large` | `:66` | if `1/a 0 < endpointRoot`, the whole sum is `0` near `(1,x)` | monotonicity `1/a j ≤ 1/a 0` + `scaledCutoff_zero_of_inv_le`, then `tsum_zero` | OK |
| `offplane_extension_local` | `:83` | off-axis extensions from raw models below `qbig`, else from the zero germ | `by_cases` on `endpointRoot < qbig` | OK — complete dichotomy |
| `SublevelShrinkingSupport` | `:99` | support condition only where `q < qbig` | def | OK |
| `.eventually_zero` | `:109` | on the axis (`x 2 = 0`, `x ≠ 0`) such fields vanish near `(1,x)` | `exists_separating_neighborhood` + `outerRadius → 0` while `radius > 0` | OK — geometric, honest |
| `initial_add_extension` | `:123` | base + supported delta keeps the base's extension | `extension_of_eventuallyEq` with `add_zero` | OK |
| `localCopy_sum_support`, `localCopy_vector_support` | `:134,:146` | copy-family sums have shrinking support | `sum_nonzero_term` + mask/geometry support | OK |
| `sum_eventually_eq_initial` | `:158` | on the axis the sum collapses to `F 0` with cutoff `= 1` | `tsum_eq_single 0` + `scaledCutoff_eventually_one_at_zero` | OK — the `tsum_eq_single` is licensed by the proved vanishing of all `j ≠ 0` |
| `central_extension_local` | `:183` | axis extensions | previous + transfer | OK |
| `diagonal_awayExtensions_local` | `:195` | **`AwayExtensions` of the full sum** | `by_cases x 2 = 0` → the two branches above | OK — see C for the coverage argument |

### `NavierStokes/DiagonalResidual.lean` (read selectively)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `JetRate` | `:33` | `∃ C ≥ 0, ∀ᶠ x in l, ‖∇^m f x‖ ≤ C q^r` | def | T | OK — note `q^r` is `rpow`; `r < 0` is *permitted*, so a `JetRate` with negative `r` asserts almost nothing. The proofs are careful to only *consume* negative-`r` bounds as background (`hbg`) and to *produce* positive-`r` conclusions |
| `JetRate.weaken` | `:41` | lower the exponent when `0 < q ≤ 1` | `Real.rpow_le_rpow_of_exponent_ge` | T | OK, and the `q ≤ 1` side condition is genuinely carried everywhere (`hlq`) |
| `perturbation_majorant_le` | `:~120` | the six-term residual majorant absorbs `q^(-b)` | `power_product_le` + `rpow_add` | T | OK — I checked the three quadratic cross terms are all present (`A·W`, `W·A`, `W·W`) |
| `residualDifference_jetRate` | `:~155` | perturbation of the residual is `O(q^n)` | `residualDifference_jet_bound` + the majorant | T | OK |
| `residual_jetRate_of_stages` | `:196` | **`J` chosen per `(m,n)`; full residual gets every rate** | see D1 (`maxJetLoss`, `hg.eventually`, exact `abel` identity) | T | OK — this is the honest replacement for an interchange of limits |
| `allJetsFlat_residual_of_stages`, `allJetsFlat_diagonal_residual` | `:272,:395` | packaged flatness | as above | F | OK (dead) |
| two anonymous `instance`s | `:20,:23` | `NormedAddCommGroup`/`NormedSpace` on a nested CLM type | `inferInstance`, `private local` | F | OK — local instance shortcuts, not a metaprogramming finding |

### `NavierStokes/SolenoidalDiagonal.lean` (read 1-200)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `cutStage`, `potentialSum`, `partialPotential` | `:33,:37,:40` | `tsum` of cut stages, and its finite prefix | defs | T | OK **only because of `:46-72`** — see D2. In isolation this is the repo's most exposed junk-value surface |
| `eventually_zero_tail` | `:46` | a *common neighborhood* kills all `j ≥ N` | `scaledCutoffs_zero_on_common_neighborhood` + continuity of `q` | T | OK — "common neighborhood, not merely a pointwise support bound" is exactly the right strengthening and the proof delivers it |
| `potentialSum_eventuallyEq_partial` | `:58` | `tsum = finite prefix` near any `q>0` point | `tsum_eq_sum` | T | OK |
| `summable_cutStage` | `:69` | summability **proved** | `summable_of_ne_finset_zero` | T | OK — kills the "assumed convergence" hypothesis outright |
| `locallyFinite_cutStage_support(_on)` | `:79,:93` | local finiteness of supports | as above | F | OK (dead) |
| `cutStage_contDiffAt`, `potentialSum_contDiffAt/On` | `:117,:126,:140` | smoothness of the sum where `q>0` | congr with the finite prefix | T | OK — smoothness is *derived from* local finiteness, not assumed |
| `potentialSum_allJets_eventuallyEq_*` | `:140,:165` | one prefix length `N` works for **all** derivative orders | `⟨N, fun k => …⟩` — `N` bound before `k` | F/F | OK; I flag that these are off-cone yet the *statement* they encode (order-independence of `N`) is what the live `residual_jetRate` needs. It gets it instead through `iteratedFDeriv_eventuallyEq` applied per-order, which is equivalent. Not a gap, but it is why these look dead |
| `velocitySum` and its smoothness/divergence lemmas | `:188-260` | the constructed velocity is a genuine spatial curl, hence divergence-free | `SpatialCurl` lemmas | mixed | OK |

### `NavierStokes/ActualCycleResidualBounds.lean` (read in full, 89 decls; highlights)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `Invariant` | `:36` | abbreviation for `CycleAnalyticInvariant` at the actual geometry/carriers | abbrev | T | OK |
| `Invariant.source_support` | `:59` | residual source modes live in a finite band | `mem_modes` from `H.sourceBand` | T | OK — finiteness of the mode set is *from the invariant*, not assumed here |
| `source_zero` | `:65` | the zero Fourier mode of the source vanishes | `HarmonicResidual.residualBlock_zero_mode` | T | OK |
| `actual_slow_le` | `:97` | `slow n ≤ 1 * S n ^ 1` | `max_eq_right` + `S_ge_one` | T | OK — small explicit constant, no numeral risk |
| `actual_wave_weight` | `:108` | `sqrt(zeta) * envelope ≤ zeta^(1/2)` | `envelope_le_one` + `sqrt_eq_rpow` | T | OK |
| `current_pressureAlias_class` | `:175` | the pressure alias has *every* power | `GaugeExcludedBounds.pressureAliasState_mean_bounds` (external, unread) | T | UNCLEAR (delegated) |
| `radial_mean_class` | `:217` | the missing radial mean component has class `1+σ` | reconstructs it from the measured pressure debt `H.debt 0`, the literal pressure, and the alias; ends in an explicit `ring` identity | T | OK — this is the "no free lunch on the radial component" step and it does route through a real debt hypothesis of the invariant |
| `mean_component_class` | `:248` | all three mean components have class `1+σ` | `fin_cases i` → radial (above), `H.mean.angular`, `H.mean.axial` | T | OK |
| `fullResidual_decomposition` | `:310` | literal residual = Σ oscillations + mean + total error | `representation.fullResidual_reconstructed_local`, `angularAverage` identities | T | OK — an *identity*, so the subsequent term-by-term bounding is legitimate |
| `native_residual` | `:845` | every term of the state residual has gain `h(1/2+σ)` with loss `2h·m` | `.add`/`.congr` of the five term bounds, then `fullResidual_decomposition` | T | OK — the decomposition and the bounds match term for term |
| `graphResidual_smooth` | `:397` | smoothness of the cylindrical graph residual | long explicit `ContDiffOn` algebra | T | OK |
| `realization_native_smooth` | `:446` | the full native residual is smooth across radial edges *from the realization*, "not an output-jet premise" | swaps coordinates, uses `r.base_equation` | T | OK — I checked the docstring's claim: the smoothness really is derived from `StateRealization` fields, not assumed |
| `base_exterior_jetRate` | `:555` | outside the active cone the base residual has every rate | `GlobalBaseError.error_joint_jetRate` + a germ argument | T | OK |
| `SelectedGeometry` | `:903` | the geometric facts about the one selected dyadic band | structure | T | OK |
| `selected_residual_jet_bound` | `:915` | transfer a native band bound to a Cartesian jet bound | picks a comparable band `exists_comparable_band`, a polar chart, then `cartesianPull_jet_bound`; the exponent bookkeeping ends in `unfold physicalLoss; ring` | T | OK |
| `selected_residual_jetRate` | `:956` | glue interior (band) and exterior (base) estimates | `by_cases w ∈ S`; outside uses `residual_eventuallyEq` from `houtside` | T | OK — the two-region split is complete because `hsmall` forces `q < Q N` eventually |
| `PhysicalFields` / `PhysicalData` | `:1015,:1141` | *identification* of the physical velocity/pressure with the graph pullback, plus an exterior equality | structure | T | OK — I verified there is **no size estimate** among its fields, so `d` cannot smuggle in the decay |
| `PhysicalFields.exterior_germs` | `:1041` | pointwise exterior equality upgrades to germs | openness of `preterminal ∩ activeᶜ` + continuity of `q` | T | OK |
| `Invariant.stateRealization` | `:1088` | the invariant + `d` give a full `StateRealization` | 11-field `refine`, each from a named base/invariant lemma | T | OK |
| `fixedLoss` | `:1145` | `physicalLoss h (2h) m` — **independent of `J`** | def | T | OK, and this independence is exactly what `residual_jetRate_of_stages` requires |
| `Invariant.residual_jetRate` | `:1158` | per-stage residual rate `h(1/2+σ) − fixedLoss m` | `stateRealization` + `selected_residual_jetRate` + `native_residual` | T | OK |
| `iterate_base_error` | `:882` | the base error is unchanged by every cycle | `induction J`, `CycleParameters.next_base_error` | T | OK (structural `Nat` induction) |
| `finite_residual_rates` | `:1190` | **`∀ J m`, the finite-prefix residual has rate `gain h J − fixedLoss m`** | `(H J).residual_jetRate` + `gain_le_residualWave` + `weaken` | T | OK — **the answer to B** |

### `NavierStokes/ActualCyclePreservation.lean` (read in full, 80 decls; highlights)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `staticData` | `:42` | one fixed similarity geometry works at every stage | 20-odd fields, most `rfl`/`HEq.rfl` | T | OK — the `rfl`s are geometry-identification, not proof avoidance |
| `kappa_small` | `:74` | `κ ≤ 1/100000` | `norm_num [ChartScales.kappa]` with `kappa := 1/100000` | T | OK; the only 6-digit literal in scope (see kernel section) |
| `state` | `:149` | the run is `CycleState.iterate (fixedParameters) c (initialCycleState)` | def | T | OK — a *fixed* parameter sequence, so no per-stage tuning is hidden in `p` |
| `state_zero` / `state_succ` | `:153,:155` | `rfl` unfoldings of the iterate | `rfl` | F/T | OK; `state_zero` off-cone |
| `state_labels` | `:159` | the label set never changes | `induction n` with `zero => rfl`, `succ => exact ih` | T | OK — see kernel note: this is a definitional-equality claim discharged by `rfl`/`ih`, i.e. the kernel must whnf `CycleState.iterate` and a `.coefficients.labels` projection. Cheap, but it *is* a recursor reduction |
| `broad_invariant` | `:301` | weaken the refined carrier support to the broad one | `refine { H with inputSupport := ?_ }` + 4 inclusion arguments via `refinedCarrier_subset_broad` | T | OK — a real weakening, in the safe direction |
| `initial_invariant` | `:323` | the literal initial state satisfies the invariant at `σ = 1/5` | `ActualCoreSupport.initial_invariant` | T | UNCLEAR (delegated, unread) |
| `core_active` | `:384` | every supported label is in the finite active set, *including at the closed radial edges* | closure argument `closed_radius_mem_closure:326` + grid membership | T | OK — the edge case is handled explicitly, which is the sort of thing usually fudged |
| `signed_*` (`:410-527`) | 12 decls | the signed-wave outputs of one cycle satisfy the class bounds with exponent `1/2+σ−κ` etc. | each delegates to `ActualSignedOutputBounds` / `ActualWaveRegularityData` with an exponent normalisation `simp only [show (1+σ-κ)-1/2 = 1/2+σ-κ by ring]` | T | OK mechanically; the *content* is delegated (UNCLEAR at the delegate) |
| `particular_inputs` | `:538` | assemble `ActualParticularMeanGain.Inputs` | structure literal from four hypotheses + two support lemmas | T | OK |
| `stepData_of_waves` | `:556` | assemble the generic step's input record | 20-field `refine`, `cells := refinedCarrier` | T | OK |
| `waveData_of_particular` | `:689` | assemble `WaveData` from `ActualParticularCycleData.Data` | 30-field structure literal | T | OK |
| `stepResult_of_particular` | `:742` | run the generic analytic step | `CorrectionAnalyticStep.step _ … (staticData B) H hσ kappa_small (stepData_of_particular …)` | T | OK structurally; the mathematics is inside `step` |
| `RunInvariant` | `:768` | analytic ∧ coherent ∧ periodic | structure | T | OK — three genuinely separate invariants, which is the right way to avoid circularity between them |
| `initial_runInvariant` | `:773` | base case at `sigma 0 = 1/5` | `simpa only [sigma_zero]` + two initial lemmas | T | OK |
| `next_runInvariant_of_particular` / `next_runInvariant` | `:800,:817` | **one cycle raises `σ` by exactly `1/10`** | `analytic := (stepResult_of_particular …).invariant` | T | OK structurally — the `+1/10` is the conclusion of `step`, so all the quantitative risk is there |
| `particularData` | `:812` | the per-cycle particular data exists | `ActualParticularCycleData.actual_data` | T | UNCLEAR (delegated) |
| `state_runInvariant` | `:826` | **`∀ j, RunInvariant (sigma j) (state B N0 j)`** | `induction j`; `zero => initial_runInvariant`; `succ => rw [sigma_succ, state_succ]; exact next_runInvariant ih hN (sigma_admissible j)` | T | OK — **this is the honest induction the sibling's cluster was missing** |
| `state_invariant`/`_coherent`/`_periodic`/`_particularData`/`_stepData`/`_result` | `:835-892` | projections at each stage | `.analytic` etc. | mixed | OK |

### `NavierStokes/GluedStageEstimates.lean` (selected)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `Bound` | `:26` | `∃ C ≥ 0, ∀ w ∈ sublevel, q w ≤ 1 → ‖∇^m f w‖ ≤ C q^r` | abbrev | T | OK |
| `SignedInputs` | `:34` | native signed-wave data with exponent floors | structure | T | OK |
| `glued_bound_of_local` | `:453` | band-local bounds transfer to the glued field "with no factor counting charts" | `ValidDyadicBandCover.field_jet_bound_at` | T | OK — the absence of a chart-count factor is a real claim; it rests on the delegate |
| `localPotential_bound_of_modes` / `localPressure_bound_of_modes` | `:488,:511` | finite harmonic sums, constant `2250 * Σ_k C k` | `choose_mode_constants` then `Finset.sum_mul` | T | OK. The constant is summed **before** the band and point are chosen (`Σ_k C k` outside the `intro n … w`), which is the correct quantifier order and is easy to get wrong |
| `current_potential_bound` / `current_pressure_bound` | `:626,:646` | the current-band particular fields have gain `gain h (j+1) − loss m` | mode bounds + `gain_le_current_exponent` + `linarith` | T | OK — exponent arithmetic is explicit `linarith`, not `sorry`-adjacent |
| `represented_raw_bounds` | `:349` | package the three families' raw stage bounds | `raw_of_positive_bounds` + `bound_congr` | T | OK |
| `stageEstimates_of_component_bounds` | `:379` | **build `StageEstimates`**, with `finite_background := ?_`, `finite_residual := ?_` | `refine { … }`; residual goal closed at `:436` by `finite_residual_rates`; background goal at `:423-435` by `MixedFiniteBackground.mixed_background_from_initial` | T | OK — **the discharge point**; `gain := ActualIterationLedger.gain h`, `residualLoss := fixedLoss` |
| `actualStageEstimates` | `:684` | the live constructor; normalises three loss functions | `refine { E with … }` and three `rw [← h…]` where each `h…` is a `funext`+`max_self` identity | T | OK — the `max_self` rewrites are cosmetic normalisations, they do not weaken any bound |
| `actualStageEstimates_ledger` | `:727` | the six loss/gain fields are the ledger ones | `⟨rfl, rfl, rfl, rfl, rfl, rfl⟩` | F | OK (dead, but a useful sanity witness that the fields are definitionally the ledger's) |

### `NavierStokes/ActualCandidateAssembly.lean` (selected; see C)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `runData` | `:476` | the `RunData` record | three `ActualCyclePreservation.state_*` theorems | T | OK |
| `stageRealizations` | `:1059` | each stage equals its chart representation | `cases k` → zeroth/positive chart lemmas | T | OK |
| `physicalData` | `:1079` | `∀ J`, the finite prefix is the physical realization at band `residualBand` | `ActualPhysicalPrefixFields.physicalFields_all` + `twice_residual_scale.le` | T | OK |
| `estimates` | `:1090` | **`StageEstimates` for the actual stages** | `GluedStageEstimates.actualStageEstimates …` | T | OK (all args available; `hq := le_rfl` is genuine reflexivity) |
| `endpoints` | `:1100` | `EndpointInputs`: the away-extension inputs `eA/eB/eP` | `GermEndpointInputs.actual_germ_stage_endpoints_of_estimates` + three stage-zero `rfl`s | T | OK |
| `Witness` | `:1121` | the full conclusion: candidate properties, smooth force, consequences, `H^3` blow-up, force decay, and the force's boundary jets = `boundaryLimits` | def | T | OK |
| `witness` | `:1153` | `Witness B N0 hN` | `GermCandidateAssembly.exists_candidate_witness_of_finite_stages` with `estimates`, `endpoints`, five support lemmas, two axis lemmas | T | OK |
| `selected_witness` | `:1177` | instantiated at `selectedBudget = 0`, `selectedThreshold` | direct | T | OK — concrete instantiation exists, nothing vacuous |
| `selected_candidate` | `:1183` | `candidateStatement` | destructure + `⟨_,_,forcing,hc⟩` | F | OK (dead; `R3/ActualCandidate.lean` uses `selected_witness`) |

### `NavierStokes/GermCandidateAssembly.lean` (live discharge)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `exists_candidate_witness_of_finite_stages` | `:164` | from `StageEstimates` + supports + off-axis extension models + axis-zero germs, produce the schedule, the three `AwayExtensions`, and the force with all consequences | `E.exists_schedule` → `hz`; `diagonal_awayExtensions_local` ×3 → `ea/eb/ep`; `spatialCut_angularSum_divergence` → `hd`; `origin_blowup` → `haxis`; then `CandidateConsequences.mixed_exists_force_with_consequences` | T | OK |
| `candidate_of_finite_stages` | `:180` | wrapper to `candidateStatement` | destructure | F | OK (dead) |

### `NavierStokes/CorrectionAnalyticStep.lean` (signature only)

| decl | file:line | statement | mechanism | cone | verdict |
|---|---|---|---|---|---|
| `StepResult` | `~:460` | `invariant : CycleAnalyticInvariant … (σ+1/10) (CycleState.step p c x)` plus 7 increment/class bounds | structure | T | OK as a specification |
| `step` | `~:480` | `StaticData → Invariant σ → 1/5 ≤ σ → κ ≤ 1/100000 → StepData → StepResult` | ~200 lines of covariance/defect/reconstruction algebra (**NOT read**) | T | **UNCLEAR — this is where the mathematics lives; see Escalations #1** |

---

## Kernel-risk assessment

Vectors as defined in the brief, applied to the 17 files above (12 primary read in full or in
large part).

### (1) Recursive inductive types, recursor reduction, `Acc.rec`, well-founded unfolding, structure eta

* **`termination_by`: 0 occurrences. `WellFounded`: 0. `Acc.rec`: 0. Explicit `.rec`: 0.**
  Verified by regex over all 12 primary files.
* **New `inductive` declarations: 0.** All 12 `structure` declarations in scope are non-recursive
  records of `Prop`/function fields (`StageEstimates`, `OneSidedExtension`, `RunData`,
  `PhysicalFields`, `SelectedGeometry`, `SignedInputs`, `StepResult`, `RunInvariant`,
  `Offsets`, `StageMetadata`, `Invariant`-abbrevs). No indexed families, no large elimination
  (nothing eliminates a `Prop` into `Type`).
* **Structural `Nat` induction: exactly 4 sites** —
  `DiagonalResidual.lean:53` (`finiteJetRate_of_jetRate` helper region),
  `ActualCycleResidualBounds.lean:885` (`iterate_base_error`),
  `ActualCyclePreservation.lean:161` (`state_labels`) and `:829` (`state_runInvariant`).
  All are `induction n with | zero | succ n ih` over `ℕ`, i.e. `Nat.rec` at a `Prop` motive.
  **Does the kernel have to *reduce* these recursors?** For `:829` and `:885`, no: the proof term
  is a `Nat.rec` application whose type-correctness is checked without iterating it. For
  `ActualCyclePreservation.lean:161-163` the answer is *slightly* yes: `zero => rfl` and
  `succ n ih => exact ih` force the kernel to whnf `CycleState.iterate p c seed 0` and
  `CycleState.iterate p c seed (n+1)` and then a `.coefficients.labels` projection. Same for
  `state_zero:153` and `state_succ:155-157`, both literally `:= rfl`. These are single-step
  `Nat.rec` unfoldings plus structure projections — bounded work, no iteration, no `Acc`.
  **Assessment: LOW.** Depth is 1, not `n`.
* Structure eta is used pervasively and benignly (`refine { H with … }` at
  `ActualCyclePreservation.lean:306`, `refine { E with … }` at `GluedStageEstimates.lean:678`).
  Eta for structures is a kernel feature, not a bug surface, and these are single-level.
* `Finset.induction_on` at `SmoothCutoffs.lean:179` (`finite_scaledCutoffs_eventually_one`) —
  recursion on a `Finset` (a quotient-free `Multiset`/`List` wrapper). Also LOW: the induction is
  over an abstract `s`, never a literal, so nothing is reduced.

### (2) Nat operations delegated to GMP: `decide`, `Nat.pow/div/mod/gcd/beq/ble`, huge literals, `norm_num` certificates

* **`decide`: 0 occurrences. `native_decide`: 0.** Verified by regex over all 12 primary files.
* **Largest literal in scope: `100000`** — `ActualIterationLedger.lean:32`
  (`def kappa : ℝ := 1 / 100000`) and the many `κ ≤ 1/100000` side conditions
  (`:115,:119,:183,:188,:193,:198,:215,:351,:383,:419`),
  plus `ActualCyclePreservation.lean:74` (`kappa_small … := by norm_num [ChartScales.kappa]`,
  where `ChartScales.kappa := 1/100000` at `NavierStokes/ChartScales.lean:24`).
  Second largest: **`2250`** at `GluedStageEstimates.lean:502` and `:525`
  (a harmonic-sum geometric factor, used as an `ℝ` coefficient with nonnegativity by `norm_num`).
  These are `ℝ` literals; the kernel work is `Nat`/`Int` literal comparison inside `norm_num`
  certificates (`Nat.ble`-style), on 4-to-6-digit numerals. **Assessment: NEGLIGIBLE.**
  For reference, a GMP-stress attack would need thousands of digits or `Nat.pow` with a large
  exponent; there is none. No `Nat.pow`, `Nat.gcd`, `Nat.div`, `Nat.mod` anywhere in scope.
* `norm_num` sites in scope: 20 in `ActualCycleResidualBounds.lean` (`:112,:131,:182,:183,:259,
  :382,:519,:565,:718,:719,:778,:780,:853,:856,:864,:870,:871,:873,:1183`), 3 in
  `GluedStageEstimates.lean` (`:503,:526,:600`), 1 in `ActualCyclePreservation.lean:74`, several
  in `MixedDiagonalResidual.lean`/`DiagonalResidual.lean` (`(0:ℝ)<1`, `1 ≤ 4`, `0 ≤ 1/2`).
  Every one of them is on a tiny rational or a `1 ≤ 4`-style `Nat` fact. The heaviest is
  `ActualCycleResidualBounds.lean:518-519`
  (`Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans (by norm_num)`
  proving `exp (1/5) ≤ 2`) — a fixed-precision rational bound, still small.
* `omega` sites: e.g. `ActualCycleResidualBounds.lean:51,:999,:1005`,
  `GluedStageEstimates.lean:436` (`by omega` for `4 ≤ N+1` from `4 ≤ N`),
  `MixedDiagonalResidual.lean:112,:120,:163,:166`. `omega` emits linear-arithmetic certificates
  over small `Int`/`Nat` literals. **NEGLIGIBLE.**
* `fin_cases i` on `Fin 3` — `ActualCycleResidualBounds.lean:251,:278,:283,:288,:421,:437`,
  `ActualCyclePreservation.lean:354` — expands to 3 explicit cases. This *does* use decidability
  of `Fin 3` equality at elaboration, but the emitted term is three branches; the kernel checks
  three branches. **NEGLIGIBLE.**
* **So: does the kernel have to perform any risky computation to accept these files? No.** The
  only literal arithmetic it recomputes is `norm_num`/`omega` certificates on ≤6-digit numerals.
  Nothing here is exploitable by a GMP or `Nat.pow` bug.

### (3) Custom metaprogramming

* **`macro`: 0. `elab`: 0. `syntax`: 0. `set_option`: 0. `axiom`: 0. `unsafe`: 0.
  `partial`: 0 real hits** (the 7 apparent hits in `SolenoidalDiagonal.lean` are the identifier
  `partialPotential`). **`sorry`: 0. `deriving`: 0.**
* Two `private local instance` declarations at `DiagonalResidual.lean:20,:23`
  (`NormedAddCommGroup`/`NormedSpace` on `SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space`, both
  `inferInstance`). These are instance-resolution shortcuts, both `in_cone=False`. Not
  metaprogramming, not a finding, but I record them because they are the only non-standard
  elaboration-affecting declarations in scope.
* `local notation` for `G`, `κ`, `p`, `c`, `v`, `u`, `post`, `request`
  (`ActualCyclePreservation.lean:37-38,403-408,533-536,620-625,684-687`) and
  `ActualCycleResidualBounds`'s `abbrev Point/Cylinder/Index`. Notation only — no new elaborator.
  It does make the file substantially harder to audit (a reader must expand `p`, `v`, `u`
  mentally), which I note as an auditability cost, not a soundness finding.
* One thing I want to flag as *not* a finding but worth a second pair of eyes:
  `CorrectionAnalyticStep.lean` uses a French-quoted binder name `(«κ» := κ)` at
  `ActualCyclePreservation.lean:751` and `:889`. That is a legal Lean identifier escape, not
  metaprogramming, and it is consistent with `κ` being an ordinary implicit argument name.

### Cone status of everything I audited

Of the 756 decls across the 17 files, 173 are `in_cone=False`. In my *primary* 12 files
(526 decls) 116 are off-cone. Notable off-cone declarations that a reader might mistake for load-
bearing:
`MixedCandidateAssembly.candidate_of_finite_stages:130`,
`ActualCandidateAssembly.selected_candidate:1183`,
the entire `JointResidualLimits.extendedResidual*` block (`:257-293`),
`JointResidualLimits.exists_smooth_compatible_limits:308`,
`JointResidualLimits.boundaryLimits_eq_extension:169` / `_independent:175`,
`ActualStageEstimates.stageEstimates_of_representations:347`,
`DiagonalResidual.allJetsFlat_residual_of_stages:272`,
`SolenoidalDiagonal.potentialSum_allJets_eventuallyEq_sum:165`.
Live and load-bearing: `VanishingJointJets:84`, `AwayExtensions:81`, `boundaryLimits:120`,
`boundaryLimits_joint:130`, `boundaryLimits_locallyUniform:148`, `StageEstimates:29`,
`StageEstimates.exists_schedule:67`, `MixedDiagonalResidual.residual_jetRate:125`,
`physical_vanishingJointJets:168`, `exists_physical_schedule_residual_zero:200`,
all 14 of `MixedDiagonalExtensions`, `DiagonalResidual.residual_jetRate_of_stages:196`,
`ActualCycleResidualBounds.finite_residual_rates:1190`,
`ActualCyclePreservation.state_runInvariant:826`,
`GluedStageEstimates.stageEstimates_of_component_bounds:379` and `actualStageEstimates:684`,
`ActualCandidateAssembly.estimates:1090`, `endpoints:1100`, `witness:1153`, `selected_witness:1177`,
`GermCandidateAssembly.exists_candidate_witness_of_finite_stages:164`.

---

## Escalations

Ranked by how much of the claim rests on them.

**1. `CorrectionAnalyticStep.step` — the `+1/10` per cycle.**
`NavierStokes/CorrectionAnalyticStep.lean`, `structure StepResult` field
`invariant : CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x)`, proved by
`theorem step (D : StaticData …) (H : … σ x) (hσ : 1/5 ≤ σ) (hκsmall : κ ≤ 1/100000)
(d : StepData …) : StepResult …`.
*Question for an expert:* is the claimed gain of `1/10` in the residual exponent per correction
cycle actually achieved, given the stated losses (`κ` multiples, `2κ`, `4κ` appear in
`ActualCyclePreservation.lean:428-444` as `1+σ-2κ`, `1+σ-4κ`), and is the *nonlinear*
self-interaction of the new correction accounted for — not just its linearisation? Everything in
my scope is bookkeeping around this one number; if the true gain were `0` or negative, the whole
`gain J → ∞` mechanism collapses while every file I read stays literally true.
*What would settle it:* read `CorrectionAnalyticStep.lean:~480-690` line by line against a
written-out estimate of the new residual after one cycle, checking (a) the quadratic
self-interaction term, (b) the pressure/divergence correction, (c) that `σ` appears with the
claimed sign in every one of the 8 `StepResult` fields. Cross-check against
`ActualIterationLedger.all_cycle_margins:119` (`… + min (17/100) (1 - 4κ) …`) — the `17/100`
margin versus the `1/10` step is the number to verify.

**2. `ActualCycleResidualBounds.Invariant.native_residual:845` — completeness of the term list.**
The residual is decomposed as `Σ_l (source x l).oscillation + meanGoodResidual + errors.total`
(`fullResidual_decomposition:310`) and each piece is separately bounded.
*Question:* is `errors.total` (base + gaussian + alias, via `excluded_nativeBounds:871`) really
the *whole* remaining error, i.e. does `CorrectionStep.fullResidual` have no fourth term? And is
`H.gaussianMean` (used at `gaussian_modes_sum:791` to cancel the zero Fourier mode) a *proved*
field of the invariant rather than a definition that makes the cancellation automatic?
*What would settle it:* read `CorrectionStep.fullResidual` and `State.errors` field-by-field and
confirm the decomposition is an exhaustive `ring`/`abel` identity, plus check
`CycleAnalyticInvariant.gaussianMean`'s provenance in the initial state and in `step`.

**3. `ActualCycleResidualBounds.Invariant.radial_mean_class:217` — the radial component.**
The radial mean residual is not bounded directly; it is *reconstructed* from the pressure debt
`H.debt 0`, the literal reconstructed pressure (`H.reconstructed`), and the current compact
alias, ending in an explicit `ring`.
*Question:* is `H.debt 0 : UnweightedClass G.slowStrip (1+σ) (pressureDefect …)` an honest
invariant field (i.e. re-established by `step` each cycle) or does it get weaker with `j` in a way
that eventually breaks the `1+σ` class?
*What would settle it:* locate the `debt` field's re-proof inside `step` and check its exponent
against `ActualStageEstimates.RunData.rank_class:116` (`1+σ-2κ`) — note the `-2κ` there versus
`1+σ` here.

**4. `MixedPeriodicAssembly.exists_candidate_force` — the periodization/localization bridge.**
My `hz` is `VanishingJointJets (MixedPeriodicAssembly.originalResidual A v p)` for the *raw* sums;
the conclusion is about `TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v)`
and `SpatialLocalization.periodicPressure p` (`CandidateConsequences.lean:185-211`).
*Question:* does periodization + time localization preserve flatness of *all* residual jets at
`(1,0)`, and does the periodized field still blow up at exactly one point (not on a lattice of
points, which would break the challenge's "smooth force, finite-energy data" reading)?
*What would settle it:* this is `ns-force-and-blowup.md`'s territory; I flag it only because the
`hz` I validated is about the pre-periodization object and the type-checking is by `rfl`-level
defeq (`MixedDiagonalResidual.residual_eq_originalResidual:45`, off-cone), which is easy to miss.

**5. `ActualCoreSupport.initial_invariant` and `ActualParticularCycleData.actual_data`.**
`ActualCyclePreservation.lean:323` and `:812-815`. These are the base case of the induction and
the per-cycle particular data. Unread.
*Question:* is the initial invariant at `σ = 1/5` genuinely established for the *literal* initial
state (`ActualInitialization.initialCycleState`), including the `sourceBand` finiteness and the
`inputSupport` localisation, or does some field hold vacuously because the initial state is zero?
*What would settle it:* check whether `initialCycleState`'s coefficient blocks are nonzero; if the
initial state were identically zero the invariant would hold trivially and the *interesting*
content would be entirely in `step`.

**6. Off-cone scaffolding as a review hazard (low severity, high nuisance).**
19 of 34 `JointResidualLimits` decls, and the entire `extendedResidual` block, are dead. A
reviewer reading that file top-to-bottom would reasonably conclude that the artifact proves the
extension is smooth *through* `t = 1` with matching jets — but on the live path those theorems are
never used; the live analogue lives in `MixedPeriodicAssembly`.
*What would settle it:* confirm `MixedPeriodicAssembly.boundaryLimits` (the family the force's
jets are equated to at `CandidateConsequences.lean:210-211`) has its own smoothness/compatibility
proofs, and that they are in-cone.

---

## Residue: what I could not check, and why

1. **`CorrectionAnalyticStep.step`'s body** (~200 of 690 lines in that file). Read the signature
   and `StepResult` only. This is the single largest unchecked object in the chain and it carries
   the entire quantitative claim. Reason: size, and it pulls in `SignedMeanGain`,
   `assembledCovarianceIncrement`, `LocalRankDefect`, `VariableGaugeMean` — a multi-thousand-line
   subtree.
2. **All delegates named but not opened**: `ActualCoreSupport.initial_invariant`,
   `ActualParticularCycleData.actual_data`, `ActualSignedOutputBounds.*`,
   `ActualWaveRegularityData.*`, `GaugeExcludedBounds.pressureAliasState_mean_bounds`,
   `GaugeRadialResidualBounds.radialMinusAlias_class`, `CurrentParticularLabelBounds.*`,
   `ActualCurrentParticularBounds.*`, `ValidDyadicBandCover.field_jet_bound_at`,
   `cartesianPull_jet_bound`, `PhysicalMeanJetBounds.exists_comparable_band`,
   `ActualPolarCoverage.*`, `ActualCarrierGeometry.labelCarrier_*`,
   `MixedFiniteBackground.mixed_background_from_initial`,
   `MixedDiagonalSchedule.exists_three_component_local_schedule`,
   `ActualPhysicalPrefixFields.physicalFields_all`,
   `GermEndpointInputs.actual_germ_stage_endpoints_of_estimates`,
   `SpacetimeEndpoint.extendTrace`/`contDiffOn_joint_extension`,
   `MixedPeriodicAssembly.exists_candidate_force`, `TailGaugePotential.finalPotential_awayExtensions`,
   `SlowBaseEndpoint.final_fields_awayExtensions`, `LocalAngularDiagonal.*`,
   `MixedAxisPreservation.local_initialized_final_origin_blowup`, `ExponentLedger.stageParameter`.
   For each I verified only the *shape* of what it must supply and that the call type-checks
   syntactically.
3. **`MixedDiagonalSchedule.exists_three_component_local_schedule`** — the actual construction of
   the schedule `a` with `2 a j ≤ a (j+1)` and `1/a j < qbig`. I verified the *interface* is used
   correctly (in particular that `hgap 0 : 1/a 0 < qbig` is what
   `diagonal_awayExtensions_local` needs) but not that such an `a` exists. If it did not, the
   whole thing would be vacuous in the harmless direction (an unprovable lemma, not a false one).
4. **No elaboration or kernel check was performed at all.** Everything above is source reading.
   In particular I cannot rule out that some `rfl`, `simp only`, `linarith`, `positivity`, or
   `omega` in the files I read *fails* — I can only report what the source claims. Conversely I
   cannot rule out that an `exact?`-style term elaborates to something other than what its name
   suggests. The parent's premise (Comparator passed) is what licenses ignoring this.
5. **`ActualIterationLedger.lean` was grep-read, not line-read.** I confirmed
   `sigma 0 = 1/5`, `sigma (J+1) = sigma J + 1/10`, `gain h j = h j/10`, `gain_le_residualWave`,
   `kappa = 1/100000`, and that 35 of its 68 decls are off-cone; I did not verify the internal
   consistency of the ~15 `gain_le_*` inequalities or `all_cycle_margins:119`
   (`min (17/100) (1-4κ)`), which is exactly the arithmetic Escalation #1 depends on.
6. **`ActualStageEstimates.lean`** was read only for `RunData:97-103`. Its
   `stageEstimates_of_representations:347` is off-cone so I did not pursue it.
7. **Uniformity questions I did not need to answer and therefore did not**: whether constants in
   `JetRate` can be taken uniform in `m` (they cannot, as stated, and nothing live needs it);
   whether `boundaryLimits` is real-analytic; whether the boundary trace is nonzero anywhere.
