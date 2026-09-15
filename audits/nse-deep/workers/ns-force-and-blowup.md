# NS data conditions, force decay, gluing through t=1, and the blowup — read-only audit
Worker: `ns-force-and-blowup`

Target: `/home/gsm/.openclaw/workspace/repos/NSE` @ f9e8bc5 (clone of openai/NavierStokesAndEuler).
**Nothing under that path was modified.** No `lake build` was run (no built Mathlib on this box);
this is **source-level reading** of actual statements and actual proof terms/tactics. Every line
citation below was read in the original file.

Three read-only children were spawned for the heaviest sub-files; their reports are
`workers/_scratch-ns-gluing.md`, `workers/_scratch-ns-forcedecay.md`,
`workers/_scratch-ns-endpoint.md`. Their conclusions are marked `[child: name]` and I re-derived
every claim I reuse in the primary role (statement + call site) myself.

---

## Scope

### Files I read myself

| file | decls (CONE.csv count) | how much I read |
|---|---|---|
| `NavierStokes/CandidateFromLimits.lean` | 18 | **full, line by line** (223 lines) |
| `NavierStokes/R3/PositiveTimeForce.lean` | 10 | **full** (83 lines) |
| `NavierStokes/R3/ComparatorBridge.lean` | 3 | **full** (91 lines) |
| `NavierStokes/R3/ActualCandidate.lean` | 9 | **full** (155 lines) |
| `NavierStokes/R3CompactCandidate.lean` | 26 | **full** (282 lines) |
| `NavierStokes/GermCandidateAssembly.lean` | 10 | **full** (309 lines) |
| `NavierStokes/JointResidualLimits.lean` | 26 | lines 1–140 full; 141–325 statements read, proofs skimmed |
| `NavierStokes/MixedCandidateAssembly.lean` | 12 | `:20–110` full (`StageEstimates`, `exists_schedule`) |
| `NavierStokes/MixedCandidateWitness.lean` | 4 | `:1–110` full |
| `NavierStokes/MixedDiagonalResidual.lean` | 21 | `:120–250` full |
| `NavierStokes/MixedPeriodicAssembly.lean` | 33 | `:20–100`, `:300–350` full |
| `NavierStokes/ProblemStatement.lean` | 25 | `:30–170` full |
| `NavierStokes/R3/ProblemStatement.lean` | 25 | `:30–205` full |
| `NavierStokes/BaseResidual.lean` | 137 | `:55–130` full (the axis blow-up block) |
| `NavierStokes/NaturalCore.lean` | 43 | `:400–460` full |
| `NavierStokes/FinalSlowBase.lean` | 96 | `:350–400`, `:595–705` full |
| `NavierStokes/SpatialLocalization.lean` | 51 | `:525–585` full |
| `NavierStokes/TimeLocalization.lean` | 20 | `:160–200` full |
| `NavierStokes/DiagonalResidual.lean` | 34 | `:15–50` full (`JetRate`) |
| `NavierStokes/ActualCandidateAssembly.lean` | 80 | skimmed in full; `:1090–1188` read line by line |
| `ComparatorChallenges/NavierStokes.lean` | 18 | `:100–260` full (the challenge structures) |

Read-count: **21 files**; I read **line by line** roughly 1 900 lines of them and skimmed the rest.

### Files read by my children (statements independently re-derived by me at the call sites)

`NavierStokes/SpacetimeGluing.lean` (40 decls), `NavierStokes/GenericEndpointExtension.lean`
(91), `NavierStokes/SpatialBorelExtension.lean` (partial) — child `ns-gluing`;
`NavierStokes/SpacetimeEndpoint.lean` (35), `NavierStokes/PastExtension.lean` (38) — child
`ns-endpoint`; `NavierStokes/CompactSpatialForceDecay.lean` (6),
`NavierStokes/CompactForceDecay.lean` (14), `NavierStokes/SmoothCutoffs.lean`,
`NavierStokes/SpatialLocalization.lean` cutoff block — child `ns-forcedecay`.

### Correction to the brief (important, verified)

The brief says the live (C) path exhibits `toComparator (rescaledForce nu f)`
(`ComparatorR3Theorem.lean:33-35`). That is the **dead** viscosity-rescaling route.
The live path is `ComparatorR3Theorem.lean:38-44 navier_stokes_breakdown_R3`, which calls
`NavierStokesR3.comparator_of_breakdown` (`R3/ComparatorBridge.lean:77`), and that theorem
exhibits `toComparator f` — **the candidate's own force, unrescaled, same `nu`**
(`R3/ComparatorBridge.lean:85-86`, read verbatim). `option_C_of_compact_candidate`
(`ComparatorR3Theorem.lean:21`) is not used by `navier_stokes_breakdown_R3`. Viscosity `nu` is
absorbed instead by rescaling the **candidate** (`R3/Theorem.lean:26-44` via
`ViscosityScaling.candidate_at_viscosity`), not the force. So no `rescaledForce` obligation
exists on the live path, and I did not audit it.

Both other parent claims are confirmed: **the exhibited initial velocity is literally
`fun _ => 0`** (`R3/ComparatorBridge.lean:85`), and **spatial decay comes from compact
support**, `h.force_support.1 : HasCompactSupport f` (`R3/ComparatorBridge.lean:86`,
`R3/ProblemStatement.lean:66-67`).

---

## The obligation graph I verified (short form)

```
Comparator.ForceConditionDecay (toComparator f)                          <-- item (A)
  = forceConditionDecay_of_compact h.force_smooth h.force_support.1      R3/ComparatorBridge.lean:22,86
      <- CompactSpatialForceDecay.forceConditionDecay                    CompactSpatialForceDecay.lean:85
      needs: ContDiff inf f  AND  HasCompactSupport f
        f := PositiveTimeForce.force (R3CompactCandidate.compactForce F)  R3/ActualCandidate.lean:84
             = timeCutoff(t) . outerCutoff(x) . F
        HasCompactSupport: tsupport subset Icc (1/16) (21/16) x outerSupport
                                                                   PositiveTimeForce.lean:61-80
        ContDiff inf F  <-  CandidateFromLimits.force_smooth              CandidateFromLimits.lean:86
InitialVelocityConditionDecay (fun _ => 0)                              <-- item (C), trivial
  = zero_initial_condition_decay                                        ComparatorR3Bridge.lean:18
smoothness of F through t = 1                                           <-- item (B), the weight
  force := SpacetimeGluing.smoothExtension 1 (tracedResidual u p L) ...  CandidateFromLimits.lean:82
    glue: t<=1 -> tracedResidual;  t>1 -> Borel series of the t=1 jets   SpacetimeGluing.lean:192
    tracedResidual_smooth on Iic 1 x univ  <- SpacetimeEndpoint.contDiffOn_joint_extension
                                          CandidateFromLimits.lean:47, SpacetimeEndpoint.lean:250
      needs hlim : TendstoLocallyUniformly (every jet of the residual) as t -> 1^-
        <- MixedPeriodicAssembly.boundaryLimits_locallyUniform            MixedPeriodicAssembly.lean:310
        <- JointResidualLimits.locallyUniform_of_joint_limits             JointResidualLimits.lean:55
        <- boundaryLimits_joint                                           JointResidualLimits.lean:130
             needs  VanishingJointJets (residual)  AND  AwayExtensions (fields)
               VanishingJointJets  <- StageEstimates.exists_schedule      MixedCandidateAssembly.lean:67
                                   <- MixedDiagonalResidual.physical_vanishingJointJets :168
                                   <- StageEstimates.finite_residual      MixedCandidateAssembly.lean:62
               AwayExtensions      <- MixedDiagonalExtensions.diagonal_awayExtensions_local
                                        GermCandidateAssembly.lean:256-261
                                   <- (endpoints B N0 hN).potential/.direct/.pressure
                                        ActualCandidateAssembly.lean:1160
blowup                                                                  <-- item (C), the real part
  SpeedUnboundedAtOne (activatedVelocity (periodicVelocity ASum BSum))
    <- activatedVelocity_speed_unbounded                                TimeLocalization.lean:174
    <- MixedPeriodicAssembly.periodicVelocity_speed_unbounded            MixedPeriodicAssembly.lean:322
    <- GermCandidateAssembly.origin_blowup                               GermCandidateAssembly.lean:146
    <- FinalSlowBase.axis_tendsto                                        FinalSlowBase.lean:372
    <- BaseResidual.baseVelocity_axis_tendsto_atTop                      BaseResidual.lean:104
       ||u(t,0)|| = (1-t)^(-(1/2+h)) * j  exactly, with j > 0            BaseResidual.lean:90-100
```

---

## Per-declaration findings

Tags: `[OK]` mechanism verified; `[UNCLEAR]` statement read, mechanism outside my scope;
`[KERNEL-RISK]`; `[SUSPICIOUS]`. Column *cone* = `in_cone` from
`audits/nse-deep/CONE.csv` (see the loud caveat in **Cone status** below).

### A. The force-decay / data-condition layer

| # | declaration | file:line | statement (my words) | actual mechanism | cone | verdict |
|---|---|---|---|---|---|---|
| A1 | `Comparator.ForceConditionDecay` | `ComparatorChallenges/NavierStokes.lean:185`, field `decay` at `:190-191` | `forall m K, exists C, forall x, forall t >= 0, ||iteratedFDerivWithin R m (uncurry f) (univ x Ici 0) (x,t)|| <= C/(1+||x||+t)^K` | the challenge structure; `C` is bound **after** `m,K` and **before** `x,t`, so it is uniform in `x,t` — the strong reading | n/a | OK (statement is the strong one) |
| A2 | `NavierStokesR3.forceConditionDecay_of_compact` | `R3/ComparatorBridge.lean:22-45` | `ContDiff inf f` + `HasCompactSupport f` ==> the comparator's whole-space force condition | builds `K := Prod.snd '' tsupport f` compact (`:25-26`), `SupportedIn K f` by `image_eq_zero_of_notMem_tsupport` (`:27-31`), a **time** bound from `hs.isCompact.exists_bound_of_continuousOn` on `Prod.fst` over `tsupport f` giving `T := max M 0 + 1` (`:32-43`), then `CompactSpatialForceDecay.forceConditionDecay` (`:44`). Note `|t| <= M` on the support and `linarith` — correct for both signs of `t` | True | OK |
| A3 | `CompactSpatialForceDecay.forceConditionDecay` | `CompactSpatialForceDecay.lean:85` | compact spatial support + compact future time support + `ContDiffOn` ==> `ForceConditionDecay (toComparator f)` | `intro m K` then `jet_decay` yields one `C`, then `refine <C,?_>; intro x t ht` — **`C` is fixed before `x,t`**, matching A1 token for token `[child: ns-forcedecay]`, re-checked by me at the call site | True | OK |
| A4 | `CompactSpatialForceDecay.jet_decay` | `CompactSpatialForceDecay.lean:44-78` | for **every real** `K` (incl. negative and large): `||jet|| <= C/(1+||x||+t)^K` | bounds the **product** `||jet||*(1+||x||+t)^K` on the compact box `Icc 0 (T+1) x S`; outside `S` or after `T+1` the jet is **exactly 0** (`:22`, `:32`), `C := max M 1 > 0` `[child]` | True | OK |
| A5 | `PositiveTimeForce.force` / `_contDiff` / `_eq` / `_eq_zero` | `R3/PositiveTimeForce.lean:46,49,53,57` | `force f (t,x) := timeCutoff t . f (t,x)`, smooth, `= f` on `t in [3/8,1]`, `=0` where `f=0` | `timeCutoff t := SmoothCutoffs.cutoff ((8/5)(t-11/16))`, `=1` on `[3/8,1]` by `abs_le`+`nlinarith` (`:28-32`), `=0` off `[1/16,21/16]` by two `linarith` branches (`:34-44`). All numerals are 2-digit rationals | True | OK |
| A6 | `PositiveTimeForce.force_tsupport_subset` | `R3/PositiveTimeForce.lean:61-70` | `tsupport (force f) subset Icc (1/16) (21/16) x K` given `f` vanishes off `K` | `closure_minimal` into a closed product; both coordinates by `by_contra` on the **support** (not tsupport) — correct order of closure | True | OK |
| A7 | `PositiveTimeForce.force_compactPositiveTimeSupport` | `R3/PositiveTimeForce.lean:72-80` | `HasCompactSupport (force f)` **and** `tsupport subset Ioi 0 x univ` | `(isCompact_Icc.prod hK).of_isClosed_subset isClosed_closure hs`; positivity of time by `1/16 > 0` and `linarith`. **This is the entire source of item (A)'s spatial and temporal decay** | True | OK |
| A8 | `R3CompactCandidate.compactForce` / `_supported` | `R3CompactCandidate.lean:88,94` | `compactForce F (t,x) := outerCutoff x . F (t,x)`; vanishes off `outerSupport` | `outerCutoff x := spatialCutoff ((1/2).x)`, `outerSupport := (2.) '' supportCylinder` compact by `isCompact_supportCylinder.image` (`:39-44`). `spatialCutoff` is a genuine bump, proved `=1` on a nonempty set `[child: ns-forcedecay]` — so this is **not** vacuous compactness | True | OK |
| A9 | `R3CompactCandidate.local_model_equation` | `R3CompactCandidate.lean:139-160` | cutting velocity/pressure spatially and cutting the force by `outerCutoff` **preserves** `residual = force` for all `t` | 3-way split: inside `supportCylinder` use `outerCutoff = 1` (`:150`); outside, the residual is 0 by `residual_eq_zero_of_eventually_zero`; if additionally `outerCutoff x != 0` then `x` is in `innerCube (1/4)` (`:157`) so `U =f= u` near `(t,x)` and `hNS` forces `F (t,x) = 0` (`:158-160`). **No junk value, no gap in the annulus between the two cutoffs** — this is the one place a sloppy proof would have broken and it does not | True | OK — clean and checkable |
| A10 | `R3/ActualCandidate.of_localized_fields` | `R3/ActualCandidate.lean:78-122` | assembles `ProblemStatement.CandidateProperties 1 (velocity A B) (pressure P) (PositiveTimeForce.force (compactForce F)) supportCylinder` | `hNS` (`:90-102`) splits at `t < 3/8`: early, both residual and cut force are **0** (activated fields vanish for `|t| <= 3/8`, `:40-49`), so the time cutoff cannot break the equation; late, `timeCutoff = 1`. `force_support` from A7, `energy_bounded` from `CompactEnergy.uniform_finite_energy` | True | OK |
| A11 | `R3/ProblemStatement.CompactPositiveTimeSupport` | `R3/ProblemStatement.lean:66-67` | `HasCompactSupport f AND tsupport f subset Ioi 0 x univ` | definition; the `.1` component is what A2 consumes | True | OK |
| A12 | `zero_initial_condition_decay` | `ComparatorR3Bridge.lean:18-22` | `InitialVelocityConditionDecay (fun _ => 0)` | `divergence_const`, `contDiff_const`, decay by `<0, by simp>` (all `iteratedFDeriv` of a constant are 0, RHS `0/(1+||x||)^K = 0`). Quantifier order of the challenge field (`ComparatorChallenges/NavierStokes.lean:155`) is `forall m K, exists C, forall x` — matched, and trivially so | True | OK (item (C)-datum is trivial, as the parent said) |
| A13 | `CandidateFromLimits.force_derivative_decay` / `force_mixed_derivative_decay` | `CandidateFromLimits.lean:140,152` | all jets of the **periodic** force decay like `C(1+t)^(-K)` | `CompactForceDecay.iteratedFDeriv_decay` from global smoothness + spatial periodicity + `force_time_support`. **Time decay only** — correct for the periodic branch (D); the whole-space branch (C) does not use it | `:140` **False**, `:152` True | OK |
| A14 | `CandidateFromLimits.force_time_support` | `CandidateFromLimits.lean:124-125` | `CompactFutureTimeSupport (force ...)` with `T = 2` | `<2, by norm_num, force_zero_from>`; `force_zero_from` (`:114`) is `SpacetimeGluing.smoothExtension_zero_from`, i.e. the Borel extension is **compactly supported in time** by construction. Confirms the brief's "decay in `t` is cheap" | True | OK |

### B. Smoothness through the blowup time

| # | declaration | file:line | statement (my words) | actual mechanism | cone | verdict |
|---|---|---|---|---|---|---|
| B1 | `CandidateFromLimits.force` | `CandidateFromLimits.lean:82-84` | the NS force **is defined** as `SpacetimeGluing.smoothExtension 1 (tracedResidual u p L) (tracedResidual_smooth ...)` | definition. So the PDE field of the candidate is definitionally close to true and all content moves to smoothness/decay/blowup — the brief's premise, re-verified | True | OK |
| B2 | `SpacetimeGluing.glue` / `smoothExtension` | `SpacetimeGluing.lean:192,339` | `glue T f g z = if z.1 <= T then f z else g z`; `smoothExtension T f hf` uses for `g` a **real Borel series** `sum_j cutoff(scale_j (t-T)) (t-T)^j / j! . jet_j` (`SpatialBorelExtension.lean:434-437,301`) | `[child: ns-gluing]`: `ContDiff` on **all** of spacetime including `t=T`, via `HasFDerivWithinAt.union` at the seam (`SpacetimeGluing.lean:235`). **No growth condition on the jets is assumed**: the per-degree scale is constructed from compact-support sup bounds (`SpatialBorelExtension.lean:130-144,182-199,236-248`). **The cheap trick is absent**: the extension is not "0 past T", and nothing forces `L x n = 0` | True | OK — this is legitimate Borel/Whitney gluing |
| B3 | `SpacetimeEndpoint.contDiffOn_joint_extension` | `SpacetimeEndpoint.lean:250` | jets of `f` converging locally uniformly as `t -> T^-` ==> `ContDiffOn R inf (extendTrace T f L)` on `closedPast T = Iic T x univ` | `[child: ns-endpoint]`: genuine. One-sided derivative at `t=T` is produced by Mathlib's MVT lemma `hasFDerivWithinAt_closure_of_tendsto_fderiv` (`:170-172`); `UniqueDiffOn (Iic T x univ)` really is supplied and really is true (`:37`); local uniformity is **used** (`:75-91`) and pointwise convergence would not suffice. Conclusion holds for **all** `n` (`boundary_jets_eq_limits` `:277`, via `extendJets :175` + `HasFTaylorSeriesUpToOn :228`) | True | OK |
| B4 | `CandidateFromLimits.tracedResidual_smooth` | `CandidateFromLimits.lean:47-55` | `ContDiffOn inf (tracedResidual u p L) (closedPast 1)` | `apply SpacetimeEndpoint.contDiffOn_joint_extension` with `J := ftaylorSeries R (pastResidual u p)`; the three side goals are `rfl` (`:52`), `pastResidual_derivative_recurrence` (`:53`) and `pastResidual_locallyUniform_limit ... (hlim n)` (`:55`). So the theorem is exactly B3 instantiated, plus `hlim` | True | OK, **conditional on `hlim`** |
| B5 | `hlim` as a section `variable` | `CandidateFromLimits.lean:39-41` | `forall n, TendstoLocallyUniformly (fun t x => iteratedFDeriv R n (residual) (t,x)) (fun x => L x n) (nhdsWithin (< 1))` | **a hypothesis of this module**, not proved here. `PastExtension.lean:279` only *transfers* it `[child: ns-endpoint]` | True | OK as engineering; the content is upstream |
| B6 | `JointResidualLimits.locallyUniform_of_joint_limits` | `JointResidualLimits.lean:55-63` | pointwise-in-`x` **joint** (product-filter) convergence ==> `TendstoLocallyUniformly` | `tendstoLocallyUniformly_iff_forall_tendsto`, then continuity of the limit map from `continuous_of_joint_limits` (`:30-51`, proved in full by an epsilon/2 triangle argument) and `uniformity_trans`. This is a real theorem and the hypothesis (joint, not pointwise) is genuinely stronger | True | OK — no sleight of hand |
| B7 | `JointResidualLimits.boundaryLimits` | `JointResidualLimits.lean:120-124` | the boundary jet family: **`0` at `x = 0`**, else `ftaylorSeries` of `Classical.choice (hext x hx)).value` at `(1,x)` | `dite` on `x = 0`. **This is where the blow-up point is handled by fiat**: the limit tensors at the singular point are *defined* to be zero, and the definition is only justified because `VanishingJointJets` is separately required in every consumer (`boundaryLimits_joint :130-139`). Not circular — but it is the hinge | True | OK (see E-1) |
| B8 | `JointResidualLimits.AwayExtensions` | `JointResidualLimits.lean:81-82` | for every `x != 0` there is a genuine open-neighbourhood `C^inf` extension of the field across `t=1` agreeing with it on `t<1` (`OneSidedExtension`, `:73-79`) | definition. Strong: it says the fields are already smooth across the singular time everywhere except the single axis point `x=0` | True | OK (definition), see E-2 |
| B9 | `JointResidualLimits.VanishingJointJets` | `JointResidualLimits.lean:84-86` | **every** jet of the residual tends to `0` in `nhdsWithin (openPast 1) (1,0)` | definition. The whole "force is smooth at the blowup point" claim is this predicate | True | OK (definition) |
| B10 | `MixedPeriodicAssembly.boundaryLimits_locallyUniform` | `MixedPeriodicAssembly.lean:310-320` | supplies exactly the `hlim` shape for the **periodic** residual | `locallyUniform_of_joint_limits` + `boundaryLimits_joint hz eA ev ep`, after rewriting the filter by `JointResidualLimits.past_filter` (`:89-90`: `nhdsWithin (openPast 1) (1,x) = nhdsWithin(<1) x nhds x`, proved by `nhdsWithin_prod_eq`). The filter identity is correct | True | OK |
| B11 | `MixedCandidateAssembly.StageEstimates` | `MixedCandidateAssembly.lean:29-65` | the quantitative record: raw stage bounds, a **gain** sequence `gain J -> atTop`, and `finite_residual : forall J m, JetRate (nhdsWithin(openPast 1)(1,0)) q (residual of the J-th truncation) m (gain J - residualLoss m)` | `Prop`-carrying structure with data fields. `JetRate l q f m r := exists C >= 0, eventually ||grad^m f|| <= C q^r` (`DiagonalResidual.lean:33-34`) and `q -> 0`, so **larger `r` = smaller**. This is the honest shape of "the truncated residual is flat to arbitrarily high order at the singular point" | True | OK |
| B12 | `MixedCandidateAssembly.StageEstimates.exists_schedule` | `MixedCandidateAssembly.lean:67-91` | from `StageEstimates`, a diagonal schedule `a` exists with `VanishingJointJets` of the diagonal residual | delegates to `MixedDiagonalResidual.exists_physical_schedule_residual_zero` (`:200`) feeding **all 20 fields of `E`**. Nothing is discarded, nothing extra assumed | True | OK |
| B13 | `MixedDiagonalResidual.physical_vanishingJointJets` | `MixedDiagonalResidual.lean:168-195` | the diagonal residual has vanishing joint jets at `(1,0)` | `residual_jetRate ... m 1 zero_le_one` then `SimilarityApproach.jet_tendsto_zero` with `physicalQ -> 0`. Only rate `1` is needed per order `m`, which the `gain J -> infinity` supply provides. Logic direction is right | True | OK |
| B14 | `GermCandidateAssembly.exists_candidate_witness_of_finite_stages` | `GermCandidateAssembly.lean:164-271` | from finite-stage data (support, endpoints, axis germs, `StageEstimates`) produce the schedule, the away-extensions, and the **force with all consequences** | `E.exists_schedule` (`:223`) gives `hz` = `VanishingJointJets`; `ea/eb/ep` from `MixedDiagonalExtensions.diagonal_awayExtensions_local` (`:256-261`) using hypotheses `eA/eB/eP`; blow-up from `origin_blowup` (`:264`); then `CandidateConsequences.mixed_exists_force_with_consequences` (`:266-271`). **Every analytic input is a named hypothesis discharged at the call site** `ActualCandidateAssembly.lean:1155-1161` | True | OK (structure), UNCLEAR for the deep inputs |
| B15 | `ActualCandidateAssembly.endpoints` / `estimates` / `witness` / `selected_witness` | `ActualCandidateAssembly.lean:1100,1090,1153,1177` | discharge `eA/eB/eP` (via `GermEndpointInputs.actual_germ_stage_endpoints_of_estimates`) and `E` (via `GluedStageEstimates.actualStageEstimates`) for the concrete construction | these are the two places where the deep analysis is actually cashed in. I read the call sites, **not** the ~100-file quantitative machine behind them | True | UNCLEAR — escalated E-3 |

### C. The blowup

| # | declaration | file:line | statement (my words) | actual mechanism | cone | verdict |
|---|---|---|---|---|---|---|
| C1 | `ProblemStatement.SpeedUnboundedAtOne` | `ProblemStatement.lean:94-96` | `forall M>0, forall delta>0, exists t x, t in Ioo 0 1 AND 1-delta < t AND M < ||u (t,x)||` | definition. Non-vacuous: no empty index set, no `tsupport subset empty` trick. `zero_velocity_not_unbounded` (`:151`) proves the zero field fails it, so the constructed `u` is provably `!= 0` | True | OK |
| C2 | `BaseResidual.baseVelocity_norm_at_origin` | `BaseResidual.lean:90-100` | **exactly** `||baseVelocity(t,0)|| = (1-t)^(-A h) . d.axial 0 (0,0)` for `t<1`, given `d.axial j (0,0) = 0` for `j>0` and `0 < d.axial 0 (0,0)` | from `baseVelocity_at_origin` (`:61-88`): `velocity_on_axis` + `physicalChart_origin` + `slowSum_eq_leading_of_positive_zero`, then `norm_smul` and `abs_of_pos`. **A closed-form blow-up rate, not an abstract limit** | True | OK — strongest non-triviality evidence in my scope |
| C3 | `BaseResidual.baseVelocity_axis_tendsto_atTop` | `BaseResidual.lean:104-114` | `||baseVelocity(t,0)|| -> atTop` as `t -> 1^-` | `A h = 1/2 + h > 0` (`CoordinateAlgebra.lean:18`, `linarith` from `0<h`), then `negative_power_tendsto_atTop` times a positive constant, `congr'` with C2 on `self_mem_nhdsWithin` | True | OK |
| C4 | `FinalSlowBase.axis_tendsto` | `FinalSlowBase.lean:372-378` | the same for the shipped slow base | `apply BaseResidual.baseVelocity_axis_tendsto_atTop` with the concrete data; the positivity side goal is closed by `rw [leading_origin]; exact W.axis.small.j_pos` — i.e. `j > 0` is a **field of the profile witness**, and `leading_origin` (`:356`) proves `coefficients.axial 0 (0,0) = W.axis.j` | True | OK |
| C5 | `FinalSlowBase.profileData_nonempty` / `actualProfile` | `FinalSlowBase.lean:627-634` | the profile witness exists; `actualProfile := Classical.choice profileData_nonempty` | `exists_nominal_cone` + `ModulatedProfileAssembly.exists_of_certificate`. So `j>0` is **not** a dangling hypothesis: it is a field of an object whose existence is a theorem. Whether that theorem is sound is outside my scope | True | UNCLEAR (escalated E-4) |
| C6 | `GermCandidateAssembly.potentialSum_eq_base_germ` | `GermCandidateAssembly.lean:75-95` | near a point where the initial field and every stage vanish and the zeroth cutoff is `1`, the diagonal potential sum **equals the base** | `AxisPreservation.potentialSum_eq_first_near` + `scaledCutoff_eventually_one`; the `hsmall : |scales 0 * q w| < 1/2` hypothesis is what makes the zeroth cutoff `1` | True | OK |
| C7 | `GermCandidateAssembly.origin_eventually_base` | `GermCandidateAssembly.lean:109-144` | on a left neighbourhood of `t=1`, the assembled velocity at the **origin** equals the explicit slow base at the origin | uses `AxisZeroOn` for `initial` and every `stage` (`:112-113`) at the axis point `(t,0)`, `radialProjection_origin`, `physicalQ -> 0` at the origin to get `hsmall`, and `angularSum_axis` to kill the direct part (`:136-139`). **Consequence: the entire correction machinery vanishes in a neighbourhood of the axis, so the blow-up is literally the explicit self-similar base** | True | OK — and see E-5 |
| C8 | `GermCandidateAssembly.origin_blowup` | `GermCandidateAssembly.lean:146-159` | `||assembled velocity (t,0)|| -> atTop` as `t -> 1^-` | `(FinalSlowBase.axis_tendsto ...).congr'` along C7 | True | OK |
| C9 | `MixedPeriodicAssembly.periodicVelocity_speed_unbounded` | `MixedPeriodicAssembly.lean:322-334` | the periodized velocity satisfies `SpeedUnboundedAtOne` | `periodicVelocity_origin` (`:87-89`, the periodization is the identity at the origin because `0` is in the cutoff plateau), then an explicit filter argument: `Ioi (max 0 (1-delta))` is in `nhdsWithin(<1)`, intersect with `M < ||.||` eventually. Correct and non-vacuous | True | OK |
| C10 | `TimeLocalization.activatedVelocity_speed_unbounded` (+`_iff`) | `TimeLocalization.lean:174-193` | the time-activated field keeps the blow-up | shrinks `delta` to `min delta (1/4)` so that the switch is `= 1` (`activatedVelocity_eq_late`); the `iff` direction uses `activatedVelocity_norm_le`. **This is the right way round**: activation cannot manufacture blow-up | True | OK |
| C11 | `SpatialLocalization.unbounded_of_origin_blowup` / `localizedVelocity_origin_blowup` | `SpatialLocalization.lean:540-556` | same conversion for the spatially localized field, using that the cutoff is `1` near the origin for `t > 3/4` | `private` lemma; identical filter argument to C9 | True (`:540`) | OK |
| C12 | `R3CompactCandidate.local_model_unbounded` | `R3CompactCandidate.lean:162-176` | blow-up transports from the periodic model `U` to the spatially cut field `u` | takes the blow-up point `x`, replaces it by its lattice `representative` inside `innerCube (1/4)` (`:168`), uses spatial periodicity of `U` at that time (`:169-173`) and local agreement `U =f= u` there (`:174`). **Genuine transport, not an upper-bound-only argument** | True | OK |
| C13 | `R3CompactCandidate.Properties.not_global_agreement` | `R3CompactCandidate.lean:263-279` | a future-smooth competitor cannot agree with the candidate on `Ico 0 1` | competitor bounded by `M` on the **compact** `Icc 0 1 x K`; `speed_unbounded` at threshold `max M 1` gives a point; `velocity_support` places it in `K`; contradiction. Non-vacuous | **False** (dead: the live path uses `R3/CandidateBreakdown.lean:18`) | OK |
| C14 | `R3/ProblemStatement.GlobalFiniteEnergySolution` | `R3/ProblemStatement.lean:125-135` | competitor class: no support, periodicity, pressure-growth or decay assumption; PDE on `Ioi 0`; `UniformFiniteEnergy (Ici 0)` with an **explicit** `Integrable` field (`:71-83`) | `Type`-valued structure. The explicit integrability closes the "totalized Bochner integral of a non-integrable function is 0" junk-value hole | True | OK — good hygiene |

---

## Kernel-risk assessment

Instrument: comment-stripped regex census over the **21 files I read** (I re-derived line numbers
on the original text; the counts below are for comment-stripped source, and I checked each hit
by reading it).

| pattern | hits in my 21 files | comment |
|---|---|---|
| `sorry` / `admit` | **0** | |
| `axiom` (declaration) | **0** | |
| `native_decide` | **0** | |
| `macro` / `macro_rules` / `elab` / `elab_rules` / `syntax` / `notation3` | **0** | vector (3) absent |
| `set_option` | **0** | |
| `unsafe` / `partial` | **0** / **0** | |
| `decide` | **1** | `NaturalCore.lean:120`, `zero_pow (by decide : 2 != 0)` |
| `termination_by` / `decreasing_by` | **0** / **0** | |
| `WellFounded` / `Acc.rec` / explicit `.rec` | **0** / **0** / **0** | |
| `inductive` | **0** | |
| `Nat.pow` / `Nat.div` / `Nat.mod` / `Nat.gcd` / `Nat.beq` / `Nat.ble` | **0** | |
| numeral literal with 3+ digits | **0** | the largest literals anywhere in my 21 files are 2-digit (`3/8`, `1/16`, `21/16`, `11/16`, `8/5`, `2`, `1/4`, `1/2`) |
| `norm_num` | 45 | all on 1–2-digit rationals; e.g. `CandidateFromLimits.lean:125` (`0 <= 2`), `GermCandidateAssembly.lean:126` (`(0:R) < 1/2`), `R3CompactCandidate.lean:54,59` |
| `nlinarith` | 18 | e.g. `PositiveTimeForce.lean:26`-block `:32`, `R3CompactCandidate.lean:56`; all on the same small rationals |
| `rfl` | 62 | all on `def`-unfolding / structure-projection / `abbrev` transparency, e.g. `CandidateFromLimits.lean:52,63,76` (`ftaylorSeries` agreement), `MixedCandidateAssembly.lean:186,191`. **No `rfl` on recursive data** |
| `Classical.choice` / `Classical.choose` | 11 | `FinalSlowBase.lean:634` (`actualProfile`), `JointResidualLimits.lean:124,139` (`boundaryLimits`), `GermCandidateAssembly.lean:235,239`, `MixedCandidateAssembly.lean:172,176`, `MixedCandidateWitness.lean:113,117`, `MixedPeriodicAssembly.lean:228,229` |
| `local instance` | 2 | `DiagonalResidual.lean:20,23`: `private local instance : NormedAddCommGroup (SpaceTime ->L SpaceTime ->L Space) := inferInstance` |

**Vector (1) — recursive inductive types / recursor reduction.** Absent from my scope. There is no
`inductive`, no explicit `.rec`, no `termination_by`, no `WellFounded`, no `Acc.rec` in any of the
21 files. The only inductive-type reductions are `structure` projections and anonymous
constructors on single-constructor `Prop`- and `Type`-valued structures (`StageEstimates`,
`OneSidedExtension`, `CandidateProperties`, `Properties`, `ProfileData`) — the safest pattern
there is. The only recursion I found in the immediate neighbourhood is
`GermCandidateAssembly.initializedSeries` (`:52-55`), a two-case match on `Nat` whose `_zero`/
`_succ` equations are proved by `rfl` (`:57-61`) — a single iota step per use, over a
match-on-constructor, not a nested/indexed family. `[child: ns-gluing]` reports the same for
`SpacetimeGluing.normalIter` (`SpacetimeGluing.lean:38`, structural `Nat.rec`, one iota step) and
`[child: ns-endpoint]` reports the only induction in `SpacetimeEndpoint.lean` (`:302`) is a
*proof* by induction, which the kernel merely typechecks. **Does the kernel have to reduce a
risky recursor to accept this layer? No.**

**Vector (2) — Nat / GMP numeral arithmetic.** Effectively absent. Zero
`Nat.pow/div/mod/gcd/beq/ble`; **zero literals with more than two digits** in any of my 21 files.
The single `decide` (`NaturalCore.lean:120`) is `Nat.decEq 2 0`, one single-digit comparison.
All 45 `norm_num` and 18 `nlinarith` calls are over 2-digit rationals such as
`8/5 * (3/8 - 11/16) <= 1` (`PositiveTimeForce.lean:32`); the certificates the kernel must
recompute are products of numbers below 100. `[child: ns-forcedecay]` reports the largest literal
in its 11 files is `2026` (a year in a docstring); `[child: ns-endpoint]` reports no literal above
3 digits. **The kernel never evaluates a numeral that could stress GMP.** This is far from any
known kernel-arithmetic stress regime.

**Vector (3) — custom metaprogramming.** **Zero** occurrences across all 21 files (and zero in
all files read by all three children). Under the threat model, finding any would have been a
finding; there is none. The only attribute-level manipulation anywhere near my scope is the two
`private local instance ... := inferInstance` lines at `DiagonalResidual.lean:20,23`. These
re-assert the *canonical* instances for an iterated continuous-linear-map type (presumably to
avoid an instance-search blow-up); because the right-hand side is `inferInstance` they cannot
smuggle in a different norm. Benign, but it is the only place in my scope where an instance is
being managed by hand, so I record it.

**Non-kernel risk I do want on the record:** `Classical.choice` at
`JointResidualLimits.lean:124` inside `boundaryLimits` and at `FinalSlowBase.lean:634` for
`actualProfile`. Both are ordinary noncomputable choice over a proved `Nonempty`/`AwayExtensions`,
and `boundaryLimits_independent` (`:175`) exists to show the choice does not matter. They are
irreducible for the kernel (so they *reduce* `decide`-style risk), but they are exactly the shape
in which a construction can be "defined to be what we need": see E-1.

---

## Escalations

**E-1 (rank 1) — the blow-up point's boundary jets are DEFINED to be zero, and the whole force
smoothness rests on one predicate.** `JointResidualLimits.lean:120-124`:
`boundaryLimits f hext x := if hx : x = 0 then 0 else ftaylorSeries (Classical.choice (hext x hx)).value (1,x)`.
The `x = 0` branch is legitimate only because `boundaryLimits_joint` (`:130-139`) demands
`VanishingJointJets f` (`:84-86`), i.e. **every** jet of the Navier–Stokes residual tends to `0`
at the singular point `(1,0)` from the past. That predicate is discharged for the shipped
construction by `MixedCandidateAssembly.StageEstimates.exists_schedule`
(`MixedCandidateAssembly.lean:67-91`) from the field
`StageEstimates.finite_residual` (`:62-65`), which asserts
`JetRate ... (residual of the J-th truncation) m (gain J - residualLoss m)` with
`gain J -> atTop` (`:38`).
*Question for an expert:* is `finite_residual` a genuine estimate for the shipped stages — i.e.
does the correction iteration really drive the truncated residual to order `q^(gain J)` with
`gain J -> infinity` **uniformly in the derivative order** in the sense of the quantifier order
actually written at `:62-65` (`forall J m`, one `C` per `(J,m)`), and is `residualLoss m` finite
for every `m`? A loss `residualLoss m` growing faster than `gain` can be made to grow would make
the *diagonal* limit fail even though every finite `J` is fine.
*What would settle it:* the file:line where `GluedStageEstimates.actualStageEstimates`
(`ActualCandidateAssembly.lean:1090-1098`) constructs `gain`, `residualLoss` and
`finite_residual`, plus an explicit statement of the two sequences and a check that
`gain J - residualLoss m -> infinity` in `J` for each fixed `m` (which is all `:62-65` needs).

**E-2 (rank 2) — `AwayExtensions` asserts the fields are already `C^inf` across `t=1` off the
axis.** `JointResidualLimits.lean:81-82` + `:73-79`: for every `x != 0` there is an open
neighbourhood of `(1,x)` and a genuinely smooth function on it agreeing with the field on `t<1`.
For the shipped construction this is produced by
`MixedDiagonalExtensions.diagonal_awayExtensions_local` (`GermCandidateAssembly.lean:256-261`)
from the hypotheses `eA/eB/eP` (`:178-186`), discharged at
`ActualCandidateAssembly.lean:1160` by `(endpoints B N0 hN).potential/.direct/.pressure`
i.e. `GermEndpointInputs.actual_germ_stage_endpoints_of_estimates`
(`ActualCandidateAssembly.lean:1104-1115`).
*Question for an expert:* is the per-stage `OneSidedExtension` obligation genuinely established
for the constructed stages (each stage being smooth across `t=1` away from the axis), and does
`diagonal_awayExtensions_local` really produce an extension for the **infinite diagonal sum**
rather than only for each finite prefix? The sum is locally finite only where the cutoffs bite,
so the answer depends on `SublevelShrinkingSupport` (`:172-177`) actually forcing local
finiteness near `(1,x)` for `x != 0`.
*What would settle it:* reading `MixedDiagonalExtensions.diagonal_awayExtensions_local` and
confirming (i) a locally finite sum near `(1,x)`, (ii) that the "away" condition
`EndpointCoordinates.endpointRoot (2h) (x 2) < qbig` (`:179`) covers **all** `x != 0` including
`x 2 = 0, x != 0` (which is handled separately by `hA0/hB0/hP0` at `:232-245` — check that those
three really cover the punctured plane `x != 0, x 2 = 0`).

**E-3 (rank 3) — the two places where the deep analysis is cashed in.**
`ActualCandidateAssembly.lean:1090-1098` (`estimates := GluedStageEstimates.actualStageEstimates ...`)
and `:1100-1115` (`endpoints := GermEndpointInputs.actual_germ_stage_endpoints_of_estimates ...`).
Everything in my scope is a correct reduction **to these two terms**. They are the entry points
to roughly 100 files of quantitative machinery that I did not read.
*Question for an expert:* do `actualStageEstimates` and
`actual_germ_stage_endpoints_of_estimates` have any hypothesis that is itself only an existence
assertion about the singular flow (which would make the whole result conditional/circular:
"assume a singular solution exists, then a singular solution exists")?
*What would settle it:* a dependency walk from those two terms listing every `structure` field
that is an *assumption about the limit object* rather than about a finite stage. I note that the
author's own design intent points the other way — `StageEstimates`' docstring
(`MixedCandidateAssembly.lean:27-28`) says "no infinite residual limit is a field here", and the
fields I read do only mention finite truncations `uncutVelocity A B J` and
`uncutPrefix P (J+1)` — so this is a check, not an accusation.

**E-4 (rank 4) — the blow-up amplitude `j > 0` is a field of a chosen witness.**
`FinalSlowBase.lean:372-378` closes the positivity side goal with `W.axis.small.j_pos`, and
`W` comes from `actualProfile := Classical.choice profileData_nonempty` (`:627-634`), i.e. from
`NominalConeAssembly.exists_nominal_cone` and `ModulatedProfileAssembly.exists_of_certificate`.
*Question for an expert:* is `exists_nominal_cone` a construction with an explicitly positive
axis datum `j`, or does it obtain `j > 0` from a fixed-point/compactness argument whose
hypotheses could be vacuous? If `j` could be `0` the blow-up rate `(1-t)^{-(1/2+h)} . j` would be
identically `0` and `speed_unbounded` would be false — but then the repo would be *inconsistent*
(because `ProblemStatement.lean:151 zero_velocity_not_unbounded` is also proved), not merely
wrong. So this is a soundness-of-the-existence-theorem question, not a hole in the plumbing.
*What would settle it:* the file:line of `NominalProfile.Witness.axis.small.j_pos`'s construction
in `exists_nominal_cone`.

**E-5 (rank 5) — the corrections vanish near the axis, so the blow-up is the bare self-similar
base; the stress force must therefore also vanish near the axis.**
`GermCandidateAssembly.lean:109-144` proves the assembled velocity **equals** the explicit slow
base on a left neighbourhood of `t=1` at the origin, using `AxisZeroOn` (`:24-25`) for the
initial field and **every** stage. Combined with
`FinalSlowBase.exists_final_base:673-675` (`residual (base) = stressForce + error`) and
`:679-681` (`error` has `AllJetsFlat`), the residual near the axis is `stressForce + flat`.
`stressForce` can only be flat there if the stress coefficients are supported away from the
axis — which is what `:657-662` (`SlowStressSupport.radialSupport ... activeLeft activeRight`)
and `ActualCandidateAssembly.lean:642-647` (`axis_not_active`) appear to arrange.
*Question for an expert:* is `stressForce` (and hence the *force* the Clay statement exhibits)
provably zero on a **neighbourhood** of the axis for `t` near `1`, so that the residual near the
blow-up point is only the flat `error`? If instead `stressForce` merely *decays* there, then
`VanishingJointJets` needs the corrections to cancel it — but the corrections are zero there by
`AxisZeroOn`, so the two requirements would be in tension.
*What would settle it:* the file:line proving `stressForce H v upper B z = 0` for `z` in a
neighbourhood of `(1,0)` (or the quantitative statement replacing it), and a check that
`activeLeft W > 0`.

**E-6 (rank 6) — `CONE.csv`'s `in_cone=False` is not reliable evidence of dead code.**
In my scope, `R3CompactCandidate.lean:256 Properties.forceConditionDecay` and `:263
Properties.not_global_agreement`, `CandidateFromLimits.lean:140 force_derivative_decay` and
`:212 candidateStatement_of_residual_limits`, `FinalSlowBase.lean:361 origin`,
`NaturalCore.lean:443 speedUnbounded_of_axis_tendsto` and seven `boundaryLimits_*` lemmas in
`JointResidualLimits.lean` are marked `False`. For each one I found a *live duplicate* that is
`True` (e.g. `NavierStokesR3.forceConditionDecay_of_compact` `R3/ComparatorBridge.lean:22`,
`R3/CandidateBreakdown.lean:18`, `FinalSlowBase.axis_tendsto` `:372`, the inline filter argument
at `MixedPeriodicAssembly.lean:327-334`), so in my scope the `False` flags look *correct*.
But `[child: ns-forcedecay]` reports the opposite failure mode: **5 of its 8 `False` decls are
used by `True` callers** through dot notation, e.g. `R3CompactCandidate.lean:46` used at `:92`,
`SpatialLocalization.lean:37` used at `:53`, `:136` at `:155`, `:107` at `:197`,
`R3/PositiveTimeForce.lean:24` at `:51`. So the cone extractor drops dot-notation /
projection-notation edges.
*Question:* was `CONE.csv` built from source text rather than from a real dependency graph?
*What would settle it:* rebuild the cone from `.olean` constant dependencies, or at minimum
re-run the extractor with dot-notation resolution and re-check every `False` in `TARGETS.md`.
**Until then, no audit conclusion should rest on `in_cone=False` meaning "dead".**

---

## Cone status of everything I audited

All of the following are `in_cone=True`: `CandidateFromLimits.lean:28,47,57,69,82,86,89,99,108,114,119,124,128,152,167,186`;
`R3/PositiveTimeForce.lean:21,24,28,34,46,49,53,57,61,72` (all 10);
`R3/ComparatorBridge.lean:22,48,77` (all 3);
`R3/ActualCandidate.lean:67,78,143`;
`R3CompactCandidate.lean:39,46,49,64,71,88,90,94,99,139,162,179,248`;
`GermCandidateAssembly.lean:24,27,75,109,146,164`;
`JointResidualLimits.lean:30,55,73,81,84,92,100,108,120,126,130,148`;
`MixedCandidateAssembly.lean:29,67`; `MixedCandidateWitness.lean:25,41`;
`MixedDiagonalResidual.lean:168,200`; `MixedPeriodicAssembly.lean:310,322`;
`FinalSlowBase.lean:356,372,627,634`; `BaseResidual.lean:61,90,104`;
`SpatialLocalization.lean:531,540,553`; `TimeLocalization.lean:174,187`;
`ProblemStatement.lean:94,101`; `R3/ProblemStatement.lean:66,92,125,173`;
`ActualCandidateAssembly.lean:1090,1100,1121,1153,1177`.

`in_cone=False`: `CandidateFromLimits.lean:140,212`; `R3CompactCandidate.lean:256,263`;
`FinalSlowBase.lean:361`; `NaturalCore.lean:443`;
`JointResidualLimits.lean:141,156,169,175,191,220,240`.

**Nothing central to items (A), (B) or (C) is out of the cone.** Every `False` above has a live
`True` counterpart on the path (see E-6). The one that would have been alarming —
`FinalSlowBase.lean:361 origin`, the closed-form blow-up identity — is `False` only because the
live path uses the `Tendsto` version `axis_tendsto` (`:372`, `True`), which re-proves the same
identity through `BaseResidual.baseVelocity_axis_tendsto_atTop` (`:104`, `True`) and
`baseVelocity_norm_at_origin` (`:90`, `True`). So the closed-form rate **is** in the cone.
Given E-6, treat this whole section as indicative, not authoritative.

---

## Verdict summary

Declarations examined and tagged in this report: **41**.
`[OK]` **35** · `[UNCLEAR]` **6** (B14, B15, C5, plus the deep inputs behind E-1/E-2/E-3) ·
`[KERNEL-RISK]` **0** · `[SUSPICIOUS]` **0**.
Children: `ns-gluing` 151 decls (0 KERNEL-RISK, 2 SUSPICIOUS, 2 UNCLEAR);
`ns-forcedecay` 48 decls (45 OK, 3 UNCLEAR, 0 KERNEL-RISK, 0 SUSPICIOUS);
`ns-endpoint` 73 decls (73 OK, 0 KERNEL-RISK, 0 SUSPICIOUS).

**Bottom line for my three items.**
(A) is real but **cheap, and correctly done**: the whole-space force is
`timeCutoff(t) . outerCutoff(x) . F`, its `tsupport` is inside the compact
`Icc (1/16) (21/16) x outerSupport` and inside `t>0`
(`R3/PositiveTimeForce.lean:61-80`), and `CompactSpatialForceDecay.forceConditionDecay`
(`:85`) delivers the challenge's exact quantifier order with `C` fixed before `x` and `t`, for
every real `K`. The cutting does **not** damage the PDE, and the proof that it does not
(`R3CompactCandidate.lean:139-160`, `R3/ActualCandidate.lean:90-102`) is the most careful piece
of Lean in my scope. (C)-datum is trivially true (`u0 = 0`). (C)-blowup is **genuine and
closed-form**: `||u(t,0)|| = (1-t)^{-(1/2+h)} . j` with `j > 0`
(`BaseResidual.lean:90-100`, `FinalSlowBase.lean:372-378`).
(B) is where all the weight now is, and the *plumbing* is honest: the gluing is a real Borel
extension with no assumed growth condition and no "all jets vanish" trick
(`SpacetimeGluing.lean:192,235`), and the one-sided Whitney theorem is genuine
(`SpacetimeEndpoint.lean:250,277`). The entire mathematical content has been pushed into two
predicates, `VanishingJointJets` and `AwayExtensions` (`JointResidualLimits.lean:84,81`), and
those are discharged from `StageEstimates.finite_residual` and the per-stage endpoint
obligations at `ActualCandidateAssembly.lean:1090,1100`. **That pair of terms is where an
independent expert should now look; nothing before it is broken.**

---

## Residue

* **No build.** No `lake build`/`lake env` was possible (no built Mathlib, disk full), so I
  cannot certify that these files *elaborate*, that names resolve to the Mathlib lemmas I assumed
  (e.g. `hasFDerivWithinAt_closure_of_tendsto_fderiv`, `Filter.EventuallyEq.iteratedFDerivWithin`,
  `LinearMap.trace_eq_sum_inner`), or that `#print axioms` is clean. Everything here is
  source-level reading.
* **The quantitative engine.** I did not read `GluedStageEstimates`, `ActualStageEstimates`,
  `CutStageEstimates.RawStageBounds`, `DiagonalJetBounds`, `MixedDiagonalSchedule`,
  `MixedDiagonalExtensions`, `GermEndpointInputs`, or the ~100 `Actual*`/`Physical*` files. So I
  cannot confirm `StageEstimates` is inhabited for the shipped fields (E-1, E-3), nor that the
  per-stage `OneSidedExtension`s exist (E-2).
* **The profile existence theorems.** `NominalConeAssembly.exists_nominal_cone` and
  `ModulatedProfileAssembly.exists_of_certificate` (`FinalSlowBase.lean:628-629`) were not read;
  `j > 0` and `0 < h < 1/2` are fields of those witnesses (E-4).
* **`stressForce` near the axis.** I inferred from `FinalSlowBase.lean:657-662` and
  `ActualCandidateAssembly.lean:642-647` that the stress force is supported away from the axis,
  but I did not read the lemma that proves it vanishes on a neighbourhood of `(1,0)` (E-5).
* **`JointResidualLimits.lean:141-325`** — statements read, proofs skimmed. The seven `False`
  `boundaryLimits_*` lemmas there were not verified.
* **Uniqueness.** `WholeSpaceUniqueness.candidate_global_agrees_before_one` — the other half of
  the (C) argument — is out of my scope (it is worker `ns-spine`'s E-5).
* **`CONE.csv` reliability.** See E-6; my cone table inherits that defect.
