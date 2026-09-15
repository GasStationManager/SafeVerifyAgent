# Worker report: NS FORCE DECAY conditions (comparator `ForceConditionDecay`)

Repo audited: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5), READ-ONLY.
Method: source-level reading (python/grep). **No `lake build`, no `lake env`, nothing kernel-checked here.**
Mathlib was not built, but a Mathlib *source* checkout was available at `/tmp/junk_packages_w4/mathlib`
(commit `8a17838`); the repo's `lake-manifest.json` pins mathlib rev `85e3a25e` (`inputRev v4.34.0-rc2`),
so **the Mathlib signatures I quote are from a NEARBY, not the pinned, revision** (see Residue).

## Scope

| file | lines | decls (regex count) | how read |
|---|---|---|---|
| `NavierStokes/CompactSpatialForceDecay.lean` | 97 | 6 | **line by line, whole file** |
| `NavierStokes/CompactForceDecay.lean` | 209 | 17 | **line by line, whole file** |
| `NavierStokes/ComparatorBridge.lean` | 253 | 27 | line by line for the force/jet part (:21-:134, :176-:189); skimmed the viscosity-rescaling algebra (:144-:174, :191-:252) |
| `NavierStokes/R3/ComparatorBridge.lean` | 90 | 3 | **line by line, whole file** |
| `NavierStokes/R3/PositiveTimeForce.lean` | 82 | 10 | **line by line, whole file** |
| `NavierStokes/R3CompactCandidate.lean` | 281 | 30 | line by line :24-:123 and :246-:281 (cutoff/force/Properties); rest skimmed |
| `NavierStokes/SmoothCutoffs.lean` | 309 | 47 | line by line :27-:135 (`cutoff` + derivative-support block); rest skimmed |
| `NavierStokes/SpatialLocalization.lean` | 588 | 94 | line by line :28-:175 (`radialSquare`..`cutPressure`); rest skimmed (only :197, :207 inspected) |
| `NavierStokes/ProblemStatement.lean` | — | 25 | targeted read of :30-:100 (defs `Space`, `futureDomain`, `CompactFutureTimeSupport`, `SpeedUnboundedAtOne`) |
| `NavierStokes/R3/ProblemStatement.lean` | — | 25 | targeted read of :60-:135 (`CompactPositiveTimeSupport`, `CandidateProperties`, `GlobalFiniteEnergySolution`) |
| `NavierStokes/ComparatorDefinitions.lean` | 245 | 16 | **byte-diffed against `ComparatorChallenges/NavierStokes.lean`** |
| `NavierStokes/ComparatorSolution.lean`, `NavierStokes/ComparatorR3Theorem.lean` | 33 / 47 | 2 / 2 | **line by line** (to locate the live path) |

Declarations examined individually and given a verdict below: **48**.

### Live path for the force condition (established, not assumed)

`ComparatorSolution.lean:16` `Comparator.navier_stokes_breakdown_R3`
→ `ComparatorR3Theorem.lean:38` `ComparatorBridge.navier_stokes_breakdown_R3`
→ `R3/ComparatorBridge.lean:77` `comparator_of_breakdown`
→ `R3/ComparatorBridge.lean:22` `forceConditionDecay_of_compact`
→ `CompactSpatialForceDecay.lean:85` `forceConditionDecay`
→ `CompactSpatialForceDecay.lean:44` `jet_decay` → `:22` `jet_zero_outside`, `:32` `jet_zero_after`
→ `ComparatorBridge.lean:101` `toComparator_jet_norm`.

The second route `ComparatorR3Theorem.lean:21` `option_C_of_compact_candidate` (viscosity rescaling,
uses `CompactSpatialForceDecay.rescale_supported`) is **off** the live path (`in_cone=False`, consistent).
`CompactForceDecay.lean` is the *periodic* (option D) branch: it is reached through
`ComparatorBridge.lean:117` `forceConditionPeriodic_of_decay` (`ComparatorTheorem.lean:38`,
`PeriodicPaperComparator.lean:25`) and through `CandidateFromLimits.lean:146,161`.

## (a) Quantifier order — verbatim comparison

Challenge, `ComparatorChallenges/NavierStokes.lean:190-191`:

```
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + ‖x‖ + t) ^ K
```

`diff -u ComparatorChallenges/NavierStokes.lean NavierStokes/ComparatorDefinitions.lean` differs
**only** in the module docstring/header and in the two trailing `sorry` challenge theorems
(challenge `:272-284`). The whole definitions block, including `ForceCondition` (:175/:149),
`ForceConditionDecay` (challenge `:185-191` = definitions `:159-165`), `IsOnePeriodic`, and
`NavierStokesExistenceAndSmoothnessRn`, is **byte-identical**, same namespace `NavierStokes.Comparator`,
same `local notation "ℝ^" n`, same `variable {n : ℕ}`, same `open ContDiff` (so `∞` is `C^∞`, not `ω`).
`ComparatorSolution.lean:16-19` is token-identical to challenge `:273-276`.
**So there is no weakened private copy of the force condition.**

The repo's proof `CompactSpatialForceDecay.forceConditionDecay:85-95`:

```
theorem forceConditionDecay {S : Set Space} (hS : IsCompact S) {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (hs : SupportedIn S f)
    (htime : CompactFutureTimeSupport f) :
    Comparator.ForceConditionDecay (ComparatorBridge.toComparator f) := by
  refine ⟨⟨ComparatorBridge.toComparator_smooth hf⟩, ?_⟩
  intro m K                                   -- ∀ m, ∀ K   (in this order)
  obtain ⟨C, _, hb⟩ := jet_decay hS hf hs htime m K   -- C := C(S,f,m,K) only
  refine ⟨C, ?_⟩                              -- ∃ C  CLOSED HERE, before x and t
  intro x t ht                                -- ∀ x, ∀ t ≥ 0
  rw [ComparatorBridge.toComparator_jet_norm f m x ht]
  exact hb t ht x
```

**Verdict: quantifier order is exactly the challenge's.** `C` is produced by `jet_decay` from
`S, f, m, K` alone and is fixed by `refine ⟨C, ?_⟩` *before* `intro x t ht`; it is impossible for
`C` to depend on `x` or `t` (they are not in scope at that point). No fatal weakening.
The `smooth` field is discharged by `toComparator_smooth` (`ComparatorBridge.lean:95-99`), giving
`ContDiffOn ℝ ∞ (↿(toComparator f)) (univ ×ˢ Ici 0)` — the challenge's field verbatim.

## (b) Every real `K`, including negative and large `K`

`jet_decay` (`CompactSpatialForceDecay.lean:44-48`) takes `(m : ℕ) (K : ℝ)` with **no sign
hypothesis** and returns `∃ C, 0 < C ∧ ∀ t ≥ 0, ∀ x, ‖jet‖ ≤ C / (1+‖x‖+t)^K`. `^` here is
`Real.rpow` (exponent `K : ℝ`). Mechanism, and why all signs are covered:

* The bound is obtained by bounding the **product** `‖jet z‖ * (1+‖z.2‖+z.1)^K` on the compact set
  `Icc 0 (T+1) ×ˢ S` (`:57-66`), not by bounding `‖jet‖` and then estimating the weight. That is why
  no sign of `K` is needed.
* Continuity of the weight for **negative** `K` needs the base to be nonzero: `:59-64` discharges the
  `rpow_const` side goal by `left` + `1 + ‖z.2‖ + z.1 ≠ 0`, using `htz : 0 ≤ z.1` from
  `hz.1.1` (`z.1 ∈ Icc 0 (T+1)`) and `norm_nonneg z.2`. Correct and necessary.
* `C := max M 1` (`:67`), where `M` comes from `IsCompact.exists_bound_of_continuousOn` (Mathlib:
  `∃ C, ∀ x ∈ s, ‖f x‖ ≤ C`, no positivity), and `0 < max M 1` is proved. Large `K` is not special:
  it only makes `M` larger, uniformly over the same compact set.
* Off the compact set the jet is **exactly 0**, and `0 ≤ C / (1+‖x‖+t)^K` follows from
  `hp : 0 < (1+‖x‖+t)^K` (`:69`, `Real.rpow_pos_of_pos`), valid for every real `K`. So negative `K`
  (where the right side is small) is still fine, because the left side is `0` there.

Contrast (worth recording): the *periodic* analogue `CompactForceDecay.iteratedFDeriv_decay:138-142`
**does** require `hK : 0 ≤ K`; the negative-`K` case is repaired one level up in
`ComparatorBridge.forceConditionPeriodic_of_decay:127-134` by instantiating at `max K 0` and using
`Real.rpow_le_rpow_of_exponent_le (1 ≤ 1+t) (-max K 0 ≤ -K)`. That repair is valid. The whole-space
branch needs no such repair.

## (c) Outside the compact support: exactly zero, and the `t = 0` boundary

Yes — two lemmas, both giving `= 0`, not "small":

* `jet_zero_outside` (`:22-30`): for `x ∉ K` (`K` closed) and `0 ≤ t`,
  `iteratedFDerivWithin ℝ m f futureDomain (t,x) = 0`. Mechanism: build
  `f =ᶠ[𝓝[futureDomain] (t,x)] 0` from an open spatial neighbourhood
  `{z | z.2 ∉ K} ∈ 𝓝 (t,x)` (`:26-27`, uses `hK.isOpen_compl.preimage continuous_snd`) intersected
  with `self_mem_nhdsWithin`, then `Filter.EventuallyEq.iteratedFDerivWithin_eq` (`:30`).
* `jet_zero_after` (`:32-41`): same shape with the open half-space `{z | T < z.1}`, for `T < t`.

**The `t = 0` boundary is handled correctly.** `SupportedIn` (`:19-20`) only asserts `f (t,x) = 0`
for `0 ≤ t`; the `filter_upwards` at `:28` therefore takes **two** filter facts —
`mem_nhdsWithin_of_mem_nhds hU` **and `self_mem_nhdsWithin`** — and the second supplies
`hd : z ∈ futureDomain`, i.e. `hd.1 : 0 ≤ z.1`, which is exactly what `hf z.1 hd.1 z.2 hz` needs
(`:29`). Without `self_mem_nhdsWithin` this step would be false at `t = 0` (points with `z.1 < 0`).
The Mathlib lemma used,
`Filter.EventuallyEq.iteratedFDerivWithin_eq (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) (n)`
(`Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:557`), is a *within* statement and needs no
`UniqueDiffOn`; the pointwise side condition `hx` is supplied as `hf t ht x hx` (`:30`) /
`hf t ht.le x` (`:41`). The final `simpa` closes with `iteratedFDerivWithin_fun_zero`
(`Mathlib/Analysis/Calculus/ContDiff/Basic.lean:56`, unconditional). Sound.

Where does the compact spatial support come from? Two independent suppliers, both genuine:

* `R3/ComparatorBridge.lean:25-31`: `K := Prod.snd '' tsupport f`, compact by
  `hs.isCompact.image continuous_snd`, and `SupportedIn K f` by `image_eq_zero_of_notMem_tsupport`.
  Time support: `:32-43` bounds `|t|` on `tsupport f` and takes `T := max M 0 + 1`.
* the constructed force: `R3CompactCandidate.compactForce f := fun z => outerCutoff z.2 • f z`
  (`R3CompactCandidate.lean:88`), spatially supported in `outerSupport` (`:41`, `:94-97`), then
  `PositiveTimeForce.force` multiplies by a smooth time cutoff (`R3/PositiveTimeForce.lean:46-47`),
  giving `CompactPositiveTimeSupport` (`:72-80`) which `R3/ActualCandidate.lean:88` feeds into
  `CandidateProperties.force_support`.

**Cutoff non-vacuity (the question asked): the bump is genuinely nonzero, proved.**
`SmoothCutoffs.cutoff := cutoffBump` where `cutoffBump : ContDiffBump 0` with `rIn = 1/2, rOut = 1`
(`SmoothCutoffs.lean:27-33`), and `cutoff_one_of_abs_le : |x| ≤ 1/2 → cutoff x = 1`
(`SmoothCutoffs.lean:40-42`) via Mathlib `ContDiffBump.one_of_mem_closedBall`
(`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean:137`). Downstream:
`SpatialLocalization.spatialCutoff_eq_one` proves `spatialCutoff x = 1` for `x ∈ plateau`
(`SpatialLocalization.lean:143-151`) and `zero_mem_plateau` proves `plateau ≠ ∅`
(`SpatialLocalization.lean:140`, `0 ∈ plateau`). Likewise `outerCutoff x = 1` on `supportCylinder`
(`R3CompactCandidate.lean:49-62`) and `timeCutoff = 1` on `Icc (3/8) 1`
(`R3/PositiveTimeForce.lean:28-32`). **So no downstream "compactly supported" claim is vacuous by a
collapsed cutoff.** The cutoffs cannot kill the force on `[3/8, 1] × plateau`.

## (d) `UniqueDiffOn` at every `within`→full transfer

| transfer site | `UniqueDiffOn` supplied? |
|---|---|
| `ComparatorBridge.lean:101-114` `toComparator_jet_norm` (coordinate swap of the jet) | **YES**, `:107-108` `hs : UniqueDiffOn ℝ futureDomain := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ`, passed to `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right` |
| `CompactSpatialForceDecay.lean:51-54` continuity of the jet | **YES**, `((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ)` into `ContDiffOn.continuousOn_iteratedFDerivWithin (hmn) (hs)` |
| `CompactForceDecay.lean:128-131` `nhdsWithin univ` → full `iteratedFDeriv` | not needed: `s = univ`, closed by `iteratedFDerivWithin_univ` (unconditional) |
| `ComparatorBridge.lean:55-58` `temporalDerivative_eq` (`derivWithin (Ici 0) → deriv`) | not needed: guarded by `ht : 0 < t` and `derivWithin_of_mem_nhds (Ici_mem_nhds ht)`, i.e. interior only |
| `jet_zero_outside`/`jet_zero_after` | not needed: pure `within` statements (`EventuallyEq.iteratedFDerivWithin_eq`) |

I re-checked the Mathlib signature actually being used at `:112-114`:
`LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f) (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x ∈ s) (i)`
(`Mathlib/Analysis/Calculus/ContDiff/Basic.lean:484`). The repo passes `(x := (x, t))` (a point of
`Space × ℝ`, the *domain* `G`) with `hx := ⟨ht, mem_univ _⟩`, i.e. `prodComm (x,t) = (t,x) ∈ Ici 0 ×ˢ univ`
— the argument roles line up, and `he : prodComm ⁻¹' futureDomain = univ ×ˢ Ici 0` is proved by
`ext`/`simp [futureDomain, and_comm]` (`:109-111`). **No junk-value hole found in (d).**

## Per-declaration findings

`in_cone` from `audits/nse-deep/CONE.csv` (source-level token graph; see the loud caveat in (f)).

### `NavierStokes/CompactSpatialForceDecay.lean` (whole-space / option C — the live branch)

| decl | file:line | what it says (my words) | proof mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `SupportedIn` | :19 | def: `f (t,x) = 0` for all `t ≥ 0` and all `x ∉ K` | definition | True | OK |
| `jet_zero_outside` | :22 | for closed `K`, `x ∉ K`, `t ≥ 0`: the one-sided jet of order `m` on `futureDomain` is exactly `0` | `EventuallyEq` in `𝓝[futureDomain]` from open `{z.2 ∉ K}` **plus `self_mem_nhdsWithin`** (needed at `t=0`), then `EventuallyEq.iteratedFDerivWithin_eq` | True | OK |
| `jet_zero_after` | :32 | if `f` vanishes for `t ≥ T` then the jet vanishes for `t > T` | same, with open `{T < z.1}`; note strict `T < t` (correct: locality needs a neighbourhood) | True | OK |
| `jet_decay` | :44 | for compact `S`, `f` smooth on `futureDomain`, spatially supported in `S`, time support `≤ T`: `∀ m, ∀ K : ℝ, ∃ C > 0, ∀ t ≥ 0, ∀ x, ‖jet‖ ≤ C/(1+‖x‖+t)^K` | compactness bound of the *product* `‖jet‖ * weight` on `Icc 0 (T+1) ×ˢ S`; the two exterior regimes use `jet_zero_after` / `jet_zero_outside` and `rpow_pos_of_pos` | True | OK |
| `rescale_supported` | :80 | support is preserved by `rescale a c` when `0 ≤ c` | `simp` with `hf (c*t)` and `smul_zero` | **False** (consistent: only used by `ComparatorR3Theorem.lean:30`, itself `in_cone=False`) | OK |
| `forceConditionDecay` | :85 | those hypotheses give the comparator's `ForceConditionDecay (toComparator f)` | `⟨⟨toComparator_smooth⟩, …⟩`; `intro m K` → `jet_decay` → `refine ⟨C, ?_⟩` → `intro x t ht` → `toComparator_jet_norm` | True | OK |

### `NavierStokes/ComparatorBridge.lean` (jet/force part)

| decl | file:line | statement | mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `toComparator` | :21 | `(t,x) ↦ f (t,x)` becomes `x t ↦ f (t,x)` | def | True | OK |
| `fromComparator` | :25 | inverse reindexing | def | True | OK |
| `toComparator_smooth` | :95 | `ContDiffOn ∞ f futureDomain → ContDiffOn ∞ (↿(toComparator f)) (univ ×ˢ Ici 0)` | `hf.comp (snd, fst)` with the set inclusion `⟨hz.2, mem_univ _⟩` | True | OK |
| `fromComparator_smooth` | :89 | mirror image | same | True | OK |
| `toComparator_jet_norm` | :101 | **norms of the two jets agree**: `‖iteratedFDerivWithin ℝ m (↿(toComparator f)) (univ ×ˢ Ici 0) (x,t)‖ = ‖iteratedFDerivWithin ℝ m f futureDomain (t,x)‖` for `t ≥ 0` | `LinearIsometryEquiv.prodComm` + `norm_iteratedFDerivWithin_comp_right` with `UniqueDiffOn futureDomain`; preimage identity proved by `ext` | True | OK — this is the one nontrivial coordinate step and it is done properly |
| `forceConditionPeriodic_of_decay` | :117 | nonnegative-exponent time-decay bounds ⇒ comparator `ForceConditionPeriodic` | `max K 0` + `rpow_le_rpow_of_exponent_le`; `C` chosen before `intro x t ht` | True | OK |
| `rescale`, `rescale_smooth`, `rescale_support`, `rescale_periodic` | :61,:67,:81,:75 | time/amplitude rescaling preserves smoothness, compact time support, periods | direct; `rescale_support` uses `nlinarith [(div_le_iff₀ hc).mp ht]` (small rationals) | True | OK |
| `temporalDerivative_eq` | :55 | `∂_t` equals `derivWithin … (Ici 0)` **for `0 < t`** | `derivWithin_of_mem_nhds (Ici_mem_nhds ht)`, then `rfl` | True | OK (correctly restricted to `t > 0`) |
| `zero_initial_condition` | :136 | zero field satisfies the periodic initial condition | `divergence_const`, `rfl` | True | OK |

### `NavierStokes/R3/ComparatorBridge.lean`

| decl | file:line | statement | mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `forceConditionDecay_of_compact` | :22 | `ContDiff ℝ ∞ f` + `HasCompactSupport f` ⇒ comparator `ForceConditionDecay (toComparator f)` | `K := snd '' tsupport f`; `SupportedIn` from `image_eq_zero_of_notMem_tsupport`; `T := max M 0 + 1` from a bound on `|t|` over `tsupport f`; then `CompactSpatialForceDecay.forceConditionDecay` | True | OK |
| `globalSolutionOfComparator` | :48 | a comparator solution yields the paper's `GlobalFiniteEnergySolution` | field-by-field; energy via `memLp_two_iff_integrable_sq_norm` | True | OK (out of my scope beyond the force field) |
| `comparator_of_breakdown` | :77 | candidate + "no global finite-energy solution" ⇒ option (C) with the **same** force | `⟨fun _ => 0, toComparator f, …, forceConditionDecay_of_compact h.force_smooth h.force_support.1, …⟩` | True | OK |

### `NavierStokes/R3/PositiveTimeForce.lean`

| decl | file:line | statement | mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `timeCutoff` | :21 | `cutoff ((8/5)(t - 11/16))` | def | True | OK |
| `timeCutoff_contDiff` | :24 | `C^∞` | `cutoff_contDiff.comp` | **False** (dot-notation false negative; used at `:51`) | OK |
| `timeCutoff_eq_one` | :28 | `= 1` on `Icc (3/8) 1` | `cutoff_one_of_abs_le` + `abs_le` + `nlinarith` on small rationals | True | OK (this is the non-vacuity anchor in time) |
| `timeCutoff_eq_zero` | :34 | `= 0` off `Icc (1/16) (21/16)` | `cutoff_zero_of_one_le_abs`, both sides by `linarith` | True | OK |
| `force` | :46 | `f` multiplied by the time cutoff | def | True | OK |
| `force_contDiff` | :49 | smooth | `.smul` | True | OK |
| `force_eq` | :53 | unchanged on `Icc (3/8) 1` | `timeCutoff_eq_one` | True | OK |
| `force_eq_zero` | :57 | zero where `f` is zero | `smul_zero` | True | OK |
| `force_tsupport_subset` | :61 | `tsupport ⊆ Icc (1/16) (21/16) ×ˢ K` | `closure_minimal` + two `by_contra` | True | OK |
| `force_compactPositiveTimeSupport` | :72 | compact support strictly inside `t > 0` | `of_isClosed_subset` + `linarith` on `1/16 > 0` | True | OK |

### `NavierStokes/R3CompactCandidate.lean` (only the cutoff/force part)

| decl | file:line | statement | mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `Properties` | :24 | structure of candidate hypotheses, incl. `force_support : ∃ K, IsCompact K ∧ SupportedIn K f` and `force_time_support` | structure | True | OK (a *hypothesis bundle*, see Escalation 1) |
| `outerCutoff` | :39 | `spatialCutoff ((1/2)•x)` — the twice-wider cutoff | def | True | OK |
| `outerSupport` | :41 | `2 • supportCylinder` | def | True | OK |
| `outerSupport_compact` | :43 | compact | `image` of a compact set | True | OK |
| `outerCutoff_smooth` | :46 | `C^∞` | `.comp` | **False** (dot-notation false negative; used at `:92` and `R3/ActualCandidate.lean:69`) | OK |
| `outerCutoff_one` | :49 | `= 1` on `supportCylinder` | two `cutoff_one_of_abs_le` + `nlinarith`/`norm_num` on `1/16, 1/2` | True | OK (non-vacuity anchor in space) |
| `outerCutoff_zero_outside` | :64 | `= 0` off `outerSupport` | `by_contra` + `spatialCutoff_support_subset` | True | OK |
| `compactForce` | :88 | `outerCutoff z.2 • f z` | def | True | OK |
| `compactForce_smooth` / `_supported` / `_time_support` | :90/:94/:99 | smoothness, `SupportedIn outerSupport`, time support preserved | direct | True | OK |
| `Properties.forceConditionDecay` | :256 | `Properties u p f ⇒ Comparator.ForceConditionDecay (toComparator f)` | `obtain` the compact `K`, then `CompactSpatialForceDecay.forceConditionDecay` | True | OK, but **dead code**: no other file references it (grep) |

### `NavierStokes/CompactForceDecay.lean` (periodic / option D branch)

| decl | file:line | statement | mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `unitCube`, `isCompact_unitCube` | :27,:31 | closed unit cube in `EuclideanSpace`, compact | `isCompact_univ_pi` + image of `toLp` | True | OK |
| `integerShift`, `integerShift_apply` | :36,:39 | lattice vector `∑ nᵢ • eᵢ`, its `j`-th coordinate is `n j` | `simp [coordinateVector, zsmul_eq_mul]` | True | OK |
| `fractionalPoint`, `_mem_unitCube`, `_eq_sub` | :45,:48,:53 | coordinatewise `Int.fract`; lands in the cube; equals `x - integerShift ⌊x⌋` | `Int.fract_nonneg`, `Int.fract_lt_one`, `Int.self_sub_floor` | True | OK |
| `periodic_integerShift` | :62 | unit periods in each axis ⇒ periodicity under any integer lattice vector | `Finset.induction_on` over `Fin 3`, `(hbase i).zsmul (n i) |>.add_period ih` | True | OK (the only recursor use in this file; see (e)) |
| `periodic_fractionalPoint` | :77 | `g (t, fract x) = g (t, x)` | `Periodic.sub_eq` | True | OK |
| `periodic_bound_on_timeInterval` | :89 | continuous + spatially periodic ⇒ bounded on `Icc a b × ℝ³`, `C > 0` | bound on `Icc a b ×ˢ unitCube`, transported by periodicity; `max C 1` | True | OK |
| `iteratedFDeriv_periods` | :104 | periods pass to the full jet of every order | `iteratedFDeriv_comp_add_right` with the shift `(0, eᵢ)` | True | OK |
| `iteratedFDeriv_eq_zero_after` | :119 | full jet vanishes for `t > T` when `f` vanishes for `t ≥ T` | `EventuallyEq` on open `{T < z.1}`, `nhdsWithin_univ`, `iteratedFDerivWithin_univ` | True | OK |
| `iteratedFDeriv_decay` | :138 | **time-only** decay `‖iteratedFDeriv m f (t,x)‖ ≤ C (1+t)^(-K)` for `0 ≤ K`; `C` uniform in `x` | `periodic_bound_on_timeInterval` on `[0,T+1]`, `C := M (1+(T+1))^K`, `rpow_le_rpow_of_nonpos`; `t > T+1` by vanishing | True | **UNCLEAR (naming/docstring only)** — see Escalation 3: the docstring at :135 says "arbitrary polynomial decay" while the statement has **no spatial decay at all** (impossible for a periodic field). The *statement* is what option (D) needs, so no mathematical defect. |
| `spacetimeCoordinate` | :170 | the 4 unit directions `(1,0), (0,eᵢ)` | `Fin.cases` | True | OK |
| `norm_spacetimeCoordinate` | :173 | each has norm 1 | `simp [Prod.norm_def]` | **False** — genuinely unused by name (a `@[simp]` lemma; grep finds no other reference) | OK |
| `mixed_component_le_full` | :181 | one component of the jet evaluated on unit directions is `≤ ‖jet‖` | `PiLp.norm_apply_le` + `le_opNorm` | True | OK |
| `mixed_coordinate_decay` | :195 | same time-decay bound for every mixed coordinate derivative and component | composition of the two above | True | OK |

### Cutoff layer (`SmoothCutoffs.lean`, `SpatialLocalization.lean`) — only the requested decls

| decl | file:line | statement | mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `cutoffBump` | SmoothCutoffs:27 | `ContDiffBump 0` with `rIn = 1/2 < rOut = 1` | structure instance; both side goals `norm_num` | True | OK |
| `cutoff` | :33 | the bump as `ℝ → ℝ` | def (coercion) | True | OK |
| `cutoff_contDiff` | :35 | `C^∞` | `cutoffBump.contDiff` | True | OK |
| `cutoff_mem_Icc` | :37 | `0 ≤ cutoff ≤ 1` | bump lemmas | True | OK |
| `cutoff_one_of_abs_le` | :40 | **`|x| ≤ 1/2 → cutoff x = 1`** | `ContDiffBump.one_of_mem_closedBall` | True | OK — **the non-vanishing anchor**, so `cutoff` is a genuine bump, not `0` |
| `cutoff_zero_of_one_le_abs` | :44 | `1 ≤ |x| → cutoff x = 0` | `ContDiffBump.zero_of_le_dist` | True | OK |
| `cutoff_support` / `cutoff_tsupport` | :51/:57 | support `= Ioo (-1) 1`, tsupport `= Icc (-1) 1` | `support_eq`/`tsupport_eq` of the bump | True | OK (an *equality*, so support is provably nonempty) |
| `radialSquare` | SpatialLocalization:32 | `x₀² + x₁²` | def | True | OK |
| `radialSquare_contDiff` | :37 | `C^∞` | projections `.pow 2 |>.add` | **False** (dot-notation false negative; used at `:53`) | OK |
| `cutoffProfile`, `spatialCutoff` | :41,:49 | `cutoff (16 r²) * cutoff (4 x₂)` | def | True | OK |
| `spatialCutoff_contDiff` | :52 | `C^∞` | `.comp` of the profile | True | OK |
| `spatialCutoff_mem_Icc` | :55 | in `[0,1]` | product of two `[0,1]` factors | **False** — genuinely unused (grep) | OK |
| `supportCylinder` | :72 | `{r² ≤ 1/16 ∧ |x₂| ≤ 1/4}` | def | True | OK |
| `isClosed_supportCylinder` | :75 | closed | `isClosed_le` ∩ | True | OK |
| `isCompact_supportCylinder` | :79 | compact | `convert!` to `AxisymmetricFields.isCompact_cylinder (1/32) (1/4)`, then `ext`+`simp`+`linarith` | True | OK (`convert!` noted in (e)) |
| `spatialCutoff_support_subset` | :89 | `support ⊆ supportCylinder` | two `by_contra` with `cutoff_zero_of_one_le(_abs)` | True | OK |
| `spatialCutoff_tsupport_subset`, `_hasCompactSupport` | :104,:107 | closure version; compact support | `closure_minimal`; `of_isClosed_subset` | True / **False** (`:107` used at `:197`) | OK |
| `supportCylinder_coordinate_bound` | :110 | `x ∈ supportCylinder → |xᵢ| ≤ 1/4` for each `i` | `fin_cases i` + `sq_abs` + `nlinarith` | True | OK |
| `plateau`, `isOpen_plateau`, `zero_mem_plateau` | :134,:136,:140 | open cylinder `{r² < 1/32, |x₂| < 1/8}`, open, contains `0` | `isOpen_lt`; `norm_num [plateau, radialSquare]` | True / **False** (`:136` used at `:155`) / True | OK |
| `spatialCutoff_eq_one` | :143 | **`spatialCutoff = 1` on the nonempty open `plateau`** | two `cutoff_one_of_abs_le`, `abs_of_nonneg`, `linarith` | True | OK — settles the vacuity question |

## Kernel-risk assessment

Counts below are over the 11 files listed in Scope, computed by regex over the original files.

**(1) recursive inductives / recursors / `Acc.rec` / well-founded unfolding / structure eta.**
No `inductive`, no `structure` with recursive fields, **no `.rec`, no `termination_by`, no `WellFounded`,
no `Acc.`** anywhere in these files. Recursion appears only through Mathlib induction principles:
`Finset.induction_on` (`CompactForceDecay.lean:69`) and `Nat.rec` via `induction n`
(`SmoothCutoffs.lean:83, 119, 179`). All three are inductions over an **abstract** parameter inside a
`Prop` proof; the kernel type-checks the recursor application but is never asked to *reduce* a
recursor on a closed numeral, so there is no iterated-unfolding blowup. Structure eta: the only
structure literal on the critical path is `cutoffBump` (`SmoothCutoffs.lean:27-31`) and the
`Prop`-structure instances built by `refine ⟨…⟩` for `ForceConditionDecay` /
`CandidateProperties`; projections there reduce in one step. `Fin.cases` at
`CompactForceDecay.lean:171,174` is a `Fin 4` case split (4 branches, closed). **Risk: negligible.**

**(2) Nat GMP numeral arithmetic.**
Zero `decide`, zero `native_decide`, zero `Nat.pow/div/mod/gcd/beq/ble` in these files
(the single `Nat.` token is `Nat.succ_pos n` at `SmoothCutoffs.lean:291`, an abstract `n`).
**The largest numeric literal in any of the 11 files is the copyright year `2026`
(`ComparatorDefinitions.lean:2`); no literal with ≥ 3 digits occurs anywhere else.** All arithmetic
is over `ℝ` with small rationals (`1/16, 1/8, 3/8, 5/8, 11/16, 21/16, 1/32, 1/2, 16, 4, 2`).
Tactic census over these files (regex over original text): `linarith` 27 standalone, `nlinarith` 8
(`ComparatorBridge:87`, `PositiveTimeForce:32`, `R3CompactCandidate:56`,
`SpatialLocalization:118,119,123,124`, `SmoothCutoffs:152`), `norm_num` 16, `positivity` 4
(`CompactSpatialForceDecay:69`, `R3/ComparatorBridge:35`, `SmoothCutoffs:237,306`),
`decide` 0, `fin_cases` 1 (`SpatialLocalization:114`), `convert!` 1
(`SpatialLocalization:80`). The kernel must recheck each `linarith`/`nlinarith` certificate as a
`ℝ`-ring identity with those small rationals: microseconds, no bignum path. `Int.floor`/`Int.fract`
(`CompactForceDecay.lean:46-58`) are applied to **abstract** reals — no closed `Int` computation.
**Risk: essentially zero. This is the cleanest possible profile for vector (2).**

**(3) custom metaprogramming.** Zero `macro`, `elab`, `syntax`, `set_option`, `native_decide`,
`axiom`, `unsafe`, `partial`, `implemented_by`, `@[instance]` overrides, `deriving` in all 11 files.
I explicitly checked the 4 regex hits for `partial` in `ComparatorDefinitions.lean` (:49, :128, :162,
:195): all four are the LaTeX string `\partial` inside docstrings — **false positives, not Lean
`partial`**. Likewise the 2 `axiom` hits in `ProblemStatement.lean` (:8, :117) are prose
("is a proposition, not an axiom"). `local notation "ℝ^" n` / `"ℝ³"`
(challenge :66-67 = definitions :40-41) is notation only, identical on both sides of the diff.
`#print axioms` is invoked at `ComparatorSolution.lean:31-32` (that output cannot be seen without a
build — see Residue). **Risk: none found; the "any instance is itself a finding" trigger did not fire.**

## Escalations (ranked)

1. **The whole force-decay layer is conditional; its hypotheses are the payload.** Every theorem in
   my scope takes `SupportedIn`/`HasCompactSupport`/`CompactFutureTimeSupport`/`ContDiffOn` as
   *hypotheses* (`CompactSpatialForceDecay.lean:44-48, 85-88`; `R3/ComparatorBridge.lean:22-23`).
   The force `f ≡ 0` satisfies all of them, so *this layer alone* proves nothing about a real force.
   Note carefully that this is **not** a vacuity attack on the headline claim: option (C)
   (`ComparatorSolution.lean:16-19`) asserts `¬ ∃ v p, …`, so a zero force would make the headline
   **false**, not vacuous. Expert question: is the force produced by
   `R3/ActualCandidate.lean:78-122` (i.e. `PositiveTimeForce.force (compactForce f)`) together with
   `speed_unbounded` (`ProblemStatement.lean:94-96`) genuinely inconsistent with global regularity?
   What would settle it: audit `NavierStokesR3.theorem_1_1` (`R3/Theorem.lean:46`) and
   `SpeedUnboundedAtOne`, and `R3/ComparatorBridge.lean:64-74` (`energy_bounded`) — **outside my
   scope, and that is where the mathematical risk lives, not in the decay estimates.**
2. **`iteratedFDerivWithin` of the zero function is used without `UniqueDiffOn`** at
   `CompactSpatialForceDecay.lean:30` and `:41` (`simpa using he.iteratedFDerivWithin_eq …`). The
   closing `simp` relies on `iteratedFDerivWithin_fun_zero`
   (`Mathlib/…/ContDiff/Basic.lean:56`), which in the Mathlib source I could read is stated
   **unconditionally**. Expert question: in the *pinned* mathlib rev `85e3a25e`, is
   `iteratedFDerivWithin_fun_zero` still unconditional, and is it sound there (`fderivWithin` of a
   constant on a non-unique-diff set)? What would settle it: `#print axioms` + reading that lemma at
   the pinned rev. Note `futureDomain` **is** unique-diff (proved at `ComparatorBridge.lean:107-108`),
   so even a hypothesis-carrying version could be discharged; the mathematical content is fine.
   Severity: low, and any defect would be Mathlib's, not this repo's.
3. **Docstring overclaim at `CompactForceDecay.lean:135-137`**: "Every actual full derivative has
   arbitrary polynomial **decay**" — the statement at `:138-142` gives `C * (1+t)^(-K)`, i.e. decay in
   **time only**, with no spatial decay (correct: the field there is spatially periodic, so spatial
   decay is impossible). The lemma name `iteratedFDeriv_decay` inherits the ambiguity. The consumer
   `forceConditionPeriodic_of_decay` (`ComparatorBridge.lean:117-134`) needs exactly the time-only
   form, so nothing is broken. Expert question: none mathematical; recommend renaming/annotating so
   no downstream reader mistakes it for the whole-space (`ForceConditionDecay`) bound.
4. **Dead declarations on the force path** (no risk, but they should not be mistaken for coverage):
   `R3CompactCandidate.Properties.forceConditionDecay:256`,
   `CompactForceDecay.norm_spacetimeCoordinate:173`,
   `SpatialLocalization.spatialCutoff_mem_Icc:55` — all unreferenced (grep over `NavierStokes/`).

## (f) Cone status — LOUD tooling warning

Of the 48 decls I audited, 8 are `in_cone=False` in `CONE.csv`:
`CompactForceDecay.lean:173` `norm_spacetimeCoordinate`,
`CompactSpatialForceDecay.lean:80` `rescale_supported`,
`R3CompactCandidate.lean:46` `outerCutoff_smooth`,
`R3/PositiveTimeForce.lean:24` `timeCutoff_contDiff`,
`SpatialLocalization.lean:37` `radialSquare_contDiff`, `:55` `spatialCutoff_mem_Icc`,
`:107` `spatialCutoff_hasCompactSupport`, `:136` `isOpen_plateau`.

**`in_cone=False` in `CONE.csv` must NOT be read as "unused / off the proof path".** Five of these
eight are demonstrably used by `in_cone=True` declarations, in every case through **dot notation**:

* `outerCutoff_smooth` used at `R3CompactCandidate.lean:92` (`outerCutoff_smooth.comp …`) inside
  `compactForce_smooth` (`in_cone=True`), and again at `R3/ActualCandidate.lean:69`;
* `radialSquare_contDiff` used at `SpatialLocalization.lean:53` (`radialSquare_contDiff.prodMk …`)
  inside `spatialCutoff_contDiff` (`in_cone=True`);
* `timeCutoff_contDiff` used at `R3/PositiveTimeForce.lean:51` (`timeCutoff_contDiff.comp …`) inside
  `force_contDiff` (`in_cone=True`);
* `isOpen_plateau` used at `SpatialLocalization.lean:155` (`isOpen_plateau.mem_nhds hx`);
* `spatialCutoff_hasCompactSupport` used at `SpatialLocalization.lean:197`.

The pattern is exact: the cone builder resolves a dotted token by dropping **leading** components
(longest-suffix match), so `foo_lemma.comp` resolves to `comp`/nothing and the edge
`caller → foo_lemma` is lost. Consequence for the whole audit: **the cone under-approximates; any
"dead code, don't audit" decision taken from `in_cone=False` is unsafe.** The remaining three are
genuinely unreferenced (`norm_spacetimeCoordinate`, `spatialCutoff_mem_Icc`) or reachable only via
`ComparatorR3Theorem.lean:21` `option_C_of_compact_candidate`, itself `in_cone=False`
(`rescale_supported`) — that one is consistent.

Nothing central in my scope is `in_cone=False`: the live spine
(`forceConditionDecay:85`, `jet_decay:44`, `jet_zero_outside:22`, `jet_zero_after:32`,
`toComparator_jet_norm:101`, `forceConditionDecay_of_compact:22`, `comparator_of_breakdown:77`,
`cutoff_one_of_abs_le:40`, `spatialCutoff_eq_one:143`, `zero_mem_plateau:140`,
`outerCutoff_one:49`, `timeCutoff_eq_one:28`) is `in_cone=True` throughout.

## Residue (not checked, and why)

* **No build.** Nothing here is kernel-verified. Elaboration-level facts I cannot confirm: that each
  `simp`/`simpa` actually closes its goal, that implicit-argument unification is as I read it, and
  the `#print axioms` output at `ComparatorSolution.lean:31-32` (which would show whether only
  `propext/Classical.choice/Quot.sound` are used).
* **Mathlib revision mismatch.** Signatures were read at `/tmp/junk_packages_w4/mathlib` commit
  `8a17838`, but the manifest pins `85e3a25e`. Statements of
  `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right`,
  `Filter.EventuallyEq.iteratedFDerivWithin_eq`, `iteratedFDerivWithin_fun_zero`,
  `ContDiffOn.continuousOn_iteratedFDerivWithin`, `IsCompact.exists_bound_of_continuousOn`,
  `ContDiffBump.one_of_mem_closedBall`, `Real.rpow_*` could in principle differ at the pinned rev.
* **Out of scope, deliberately untouched:** `NavierStokesR3.theorem_1_1` (`R3/Theorem.lean:46`),
  `SpeedUnboundedAtOne` and its construction, `R3/CompactEnergy` (`energy_bounded`),
  the periodic-side `ComparatorTheorem.lean` chain past `forceConditionPeriodic_of_decay`,
  and the entire `Actual*` construction stack that produces the raw fields `A B P`.
  **The mathematical weight of option (C) sits there, not in the force-decay estimates.**
* I did not verify that `ProblemStatement.CandidateProperties`-level `force_periodic`
  (`ProblemStatement.lean:108`) is consistent with the whole-space `SupportedIn` route; the two
  branches use different force classes and I only followed the whole-space one end-to-end.
* Skimmed-only regions (`SpatialLocalization.lean:175-588`, `SmoothCutoffs.lean:136-309`,
  `R3CompactCandidate.lean:124-245`, `ComparatorBridge.lean:144-252`) were scanned for the vector
  (1)(2)(3) patterns and numerals but not read for mathematical content.
