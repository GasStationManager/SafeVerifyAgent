# Worker report — thread `ns-transition-ramp`

Target: `openai/NavierStokesAndEuler` @ `f9e8bc5`, clone `/home/gsm/.openclaw/workspace/repos/NSE` (read-only).
Files: `NavierStokes/TransitionRamp.lean` (2253 lines) and `NavierStokes/OutgoingHistories.lean` (1278 lines).
No Mathlib and no `lake build` on this box. **Every claim below is source-level.** Anything needing
elaboration/kernel execution is tagged **UNBUILT**.

## Headline

**OK — no kernel-risk finding, and no dishonesty finding, in either file.** I looked for the four
shapes the brief named and found the artifact doing the *honest* thing in all four, in a way I can
cite:

1. **The ramp junction is not a junction.** The ramp is built from one globally smooth `sigma`
   (`OutgoingSchedule.lean:26-27`), and the one genuinely piecewise object in scope,
   `physicalF`/`physicalU` (`TransitionRamp.lean:702-706`), is proved smooth **without ever matching
   one-sided derivatives**: `physicalF_eq_log` (`:959`) shows the two `if`-branches *agree on the
   whole open half-plane* `0 < p.1`, so `physicalF_smooth` (`:999`) is two `congr_of_eventuallyEq`
   arguments on two open sets that cover the domain. The junction radius `p.1 = radius0` sits in the
   interior of the first one.
2. **The smoothness is uniform, not per-`k`.** `sigma_contDiff : ContDiff ℝ ∞ sigma`
   (`OutgoingSchedule.lean:37`), one statement, no `k`-dependent constant.
3. **The one bound that really does hold only on a subinterval is *stated* that way and is
   *weakened in shape*, not widened.** `SmallLogControl.log_value` is on `Icc 0 (bigTime+w₁+w₂)`
   (`TransitionRamp.lean:1281`) while its two siblings are on `Icc 0 finalTime` (`:1277`, `:1279`).
   Past the junction the artifact does **not** re-use it: it switches to a **one-sided** conclusion
   (`normalizedLog … ≤ B + 1`, `:1852`) justified by the exact affine hold `normalizedLog_hold`
   (`:1826`), and the consumer only ever needs the upper side because it feeds `Real.exp`
   (`exp_jet_bound_local_of_upper`, `:1784`).
4. **Constants are quantified before the index they are claimed uniform in.**
   `exists_uniform_initialLog_bound` (`:1510`) is `∃ B > 0, ∀ C, 0 < C → …` and `B` (`:1518`) is built
   from `Λ`, a phase bound and a jet constant only — no `C`. `ordered_seed_bounds` (`:2182-2183`) is
   `∃ B, … ∃ K, … ∃ BJ, … ∀ C, 0 < C → ∀ E, ∀ δ, …`. The doc comment at `:2176` ("chosen after the
   scale and before `C`") is accurate.

Kernel-risk vectors: **(1) essentially nil** (one structural `ℕ` recursion, one 5-constructor enum,
no `.rec`, no `Acc.rec`, no `termination_by`, no `WellFounded`, no `deriving`); **(2) nil** (largest
closed numeral in scope is `1000`, at `TransitionRamp.lean:747`, inside `(0:ℝ) ≤ 1/1000`; zero
`decide`); **(3) nil** (zero metaprogramming, confirming the repo-wide result).

## Disagreements with the brief

**D1 — REFUTED: `OutgoingHistories.lean` is NOT "the ramp's likely consumer side". It has zero
contact with `TransitionRamp.lean` in either direction.**
```
$ grep -c 'TransitionRamp'    NavierStokes/OutgoingHistories.lean   ->  0
$ grep -c 'OutgoingHistories' NavierStokes/TransitionRamp.lean      ->  0
```
Their import lines are disjoint: `OutgoingHistories.lean:1-4` imports
`CorrectedPulseAmplitude`, `SchedulePressure`, `ProfileHistories`,
`Mathlib.MeasureTheory.Integral.IntegralEqImproper`; `TransitionRamp.lean:1-3` imports
`ActivationStocks`, `ReferenceJetBounds`, `Mathlib.Analysis.Calculus.ContDiff.Bounds`. Neither is in
the other's import closure. Their only shared ancestor relevant to the brief is
`NavierStokes.OutgoingSchedule` (`TransitionRamp.lean:23` uses `OutgoingSchedule.sigma`;
`OutgoingHistories.lean:24` opens `NavierStokes.OutgoingSchedule`). The real consumers of
`TransitionRamp` are 12 other files (`ActivationContinuation`, `NominalProfile`,
`NominalConeAssembly`, `MatchingConeBounds`, `MatchingDebtBounds`, `RampParameters`, …);
`OutgoingHistories`'s consumers are `PulseCone`, `NominalProfile`, `TailCone`,
`OutgoingEntranceCone`, `PulseEnergyHistory` (+ 10 files that name it without importing it directly).
Consequence: a defect in one could not corrupt the other, and my (C) junction analysis for
`OutgoingHistories` is about a *different* junction (`y = 0`, ideal past vs. corrected present).

**D2 — NOTE: the brief's declaration counts are theorem-only.** `INVENTORY.csv` has **168** rows for
`TransitionRamp.lean` (137 `theorem` + 28 `def` + 3 `structure`), of which **158** are `in_cone`;
the brief's "127 declarations `in_cone = True`" is exactly the *theorem* subset. Same for
`OutgoingHistories.lean`: 209 rows (161 `theorem` + 44 `def` + 4 `abbrev`), **153** in-cone, of which
**114** are theorems. This matters because 10 in-`TransitionRamp` theorems and 47
in-`OutgoingHistories` theorems are `in_cone = False`, i.e. out of the top claims' cone.

**D3 — NOTE, instrument correction: `INVENTORY.csv`'s `bare_rfl` column only sees term-mode
`:= rfl` whole-proofs, so it undercounts proof-closing `rfl` by 18:1 in my scope.** It reports
`bare_rfl = 0` for `TransitionRamp.lean` and `1` for `OutgoingHistories.lean`
(`RFL_SITES.csv` line 354 / `SITES_bare_rfl_proof.md` line 574:
`OutgoingHistories.lean:501 M_eq_massMoment`, whose `:= rfl` is on line 502). In fact the two files
carry **19** bare `rfl` in proof-closing position (16 + 3), listed and classified in (D) below.
This matters for vector (1) precisely because a terminal `rfl` after `rw` is where a defeq/iota
assumption hides. (The two extra `rfl`s at `TransitionRamp.lean:1475` and
`OutgoingHistories.lean:881` are *arguments*, not closers, and are excluded from the 19.)

## Scope

| item | TransitionRamp.lean | OutgoingHistories.lean |
|---|---|---|
| lines in file | 2253 | 1278 |
| **lines read line-by-line** | **2253 (100%, lines 1-2253 in 13 windows)** | **1278 (100%, lines 1-1278 in 10 windows)** |
| declarations (INVENTORY) | 168 (137 thm / 28 def / 3 structure) | 209 (161 thm / 44 def / 4 abbrev) |
| in-cone declarations | 158 (127 thm) | 153 (114 thm) |
| declarations whose **statement** I read | 168 (all) | 209 (all) |
| declarations whose **proof** I audited step-by-step | 41 (see (B)) | 27 (see (B)) |
| declarations audited by pattern-membership only | 127 | 182 |
| out-of-file windows read as targeted excerpts (grep + `sed`, not line-by-line) | `OutgoingSchedule.lean:18-60`, `FlatCutoff.lean:20-140`, `ReferencePath.lean:800-830`, `ActivationContinuation.lean:1380-1400 / 1504-1508 / 1660-1801`, `MatchingConeBounds.lean:290-320 / 980-995`, `StressActivation.lean:536-552 / 798-812`, `UniformAngularReset.lean:918-1000 / 1102-1155`, `NaturalAxisData.lean:30-50`, `NominalProfile.lean:119-142` | same list |
| grep-only (counts, no reading) | whole clone for consumer census, numerals, kernel tokens | idem |

Sampling scheme for (B): I enumerated the **distinct proof patterns** (10 in `TransitionRamp`, 10 in
`OutgoingHistories`, table below), audited **one full instance of each**, and audited **every
instance** of the error-hiding patterns the brief named — every `nlinarith` (11 + 0), every
`field_simp`-then-`ring` (5 + 13), every `convert` (7 + 3), every `calc` (10 + 8), every bare `rfl`
(16 + 3), every `omega` (3 + 0), and every derivative/`ContDiff` combinator term that carries a
smoothness claim across the junction (the 6 lemmas of (C)). I did **not** re-check each of the
remaining ~300 term-mode `ContDiff`/`HasDerivAt` closure chains individually; they are one pattern
and a mis-assembled one would not elaborate.

## (A) What each file constructs, and who consumes it

**`TransitionRamp.lean`** builds the *last two control ramps* of the NS reference continuation, in a
logarithmic radial clock `y` (`X = radius0 · exp y`). `step b w y = OutgoingSchedule.sigma ((y-b)/w)`
(`:23`) is a smooth `0→1` step over `[b, b+w]`. Two slopes multiply the actual REF lag stock by
`damping T κ` and switch it off: `axialSlope` (`:84`) turns the axial control off over
`[bigTime, bigTime+w₁]`, and `angularSlope` (`:80`) interpolates the angular control to the terminal
value `-2/5` over `[bigTime+w₁, bigTime+w₁+w₂]`. Both are *integrated* (`integrate`, `:50`;
`logField`/`axialField`, `:125`/`:129`), so all profile values, including at the joins, are defined by
integrals. `StockReference` (`:195`) packages a reference profile family with its positive-radius
log chart; `ofNatural` (`:753`) instantiates it from the completed natural REF path.
`bigTime = log(100/radius0)` (`:269`), `finalTime = log(110/radius0)` (`:270`). `physicalF`/`physicalU`
(`:702`/`:705`) transport the log-clock fields back to physical radius with an `if p.1 ≤ radius0`
that turns out to be redundant (see (C)); `physicalProfiles` (`:1062`) is the `Profiles` structure the
later cone and matching modules consume. The quantitative half proves parameter-jet bounds:
`parameterJet` (`:327`), `compact_stock_jet_bound` (`:576`), `damped_integral_bound` (`:541`),
`local_composition_jet_bound` (`:1605`, the Faà-di-Bruno-style `n! · B · Dⁿ`), and the two terminal
results `exists_joint_small_control` (`:1434`) and `ordered_seed_bounds` (`:2179`).
Consumers (verified by grep, 103 `TransitionRamp.` reference lines in 12 files, corroborated by an
independent recon child): `ActivationContinuation.lean` (the one caller of
`exists_joint_small_control`, at `:1710`), `NominalProfile.lean`, `NominalConeAssembly.lean`,
`MatchingConeBounds.lean`, `MatchingDebtBounds.lean`, `RampParameters`/`ReferenceEndpointRamp`,
`ModulatedProfileAssembly.lean`, and others.

**`OutgoingHistories.lean`** builds the *five moment histories* of the corrected outgoing pulse in a
global log-radius `y` (`X p = exp p.1`, `:102`), on the whole plane (`logDomain.carrier = univ`,
`:36-38` — so, unlike `TransitionRamp`, there is no radial-axis domain at all). Each history is
`history initial f = initial p.2 + primitive f p` (`:62`): `M, I, J, S, Pi` (`:135-139`) with fixed
initial values `initialM … initialPi` (`:127-133`). It then derives the transport factor `XW`/`W`
(`:286-288`), the two lag sources `Sq`, `Sn` (`:295`, `:297`), the two lag stocks `angularStock`,
`axialStock` (`:303`, `:307`), their normalized ratios `Qs`, `Ns` (`:312`, `:314`), proves the two ODEs
`Qs_equation` (`:453`) / `Ns_equation` (`:461`), identifies every history with an **improper past
integral over `Iic y`** (`:774-829`), and finally rescales to an arbitrary entrance radius `XR`
(`physicalX … physicalS`, `:1183-1189`) showing the scaling cancels from both lags
(`Qs_dilation` `:1248`, `Ns_dilation` `:1257`). Consumers: `PulseCone.lean`, `TailCone.lean`,
`OutgoingEntranceCone.lean`, `PulseEnergyHistory.lean`, `NominalProfile.lean` (direct imports);
`OutgoingCone.lean`, `TerminalHistoryBridge.lean`, `NominalConeAssembly.lean`,
`HeatSwitchHistoryDerivatives.lean`, `HeatSwitchCone.lean`, `OutgoingNegativeSlopeCone.lean`,
`ShapedWaitBounds.lean`, `RepairConeBounds.lean` (named uses).

## (B) Proof-pattern census and per-site audit

### Distinct proof patterns

| # | pattern | count (TR / OH) | full instance audited | verdict |
|---|---|---|---|---|
| P1 | term-mode `ContDiff`/`ContDiffOn` closure chain | ~55 / ~30 | `angularSlope_smooth` TR:92-97 | OK |
| P2 | `HasDerivAt.unique` to *compute* a partial derivative | ~12 / ~18 | `dEta_energyDensity` OH:227-234 | OK |
| P3 | `filter_upwards` + `congr_of_eventuallyEq` local-identity transfer | 9 / 4 | `physicalF_smooth` TR:999-1022 | OK (this is the junction technique, (C)) |
| P4 | `intervalIntegral` split + `integral_congr` + `integral_norm_bound` | 8 / 4 | `damped_integral_bound` TR:541-565 | OK |
| P5 | `induction` on `ℕ` to build a `max` over `n ≤ N` | 3 / 0 | `compact_stock_jet_bound` TR:576-602 | OK |
| P6 | `field_simp [ne']` then `ring` | 5 / 13 | `physical_radial_equations` TR:1152-1178 | OK — every site supplies its `≠ 0` |
| P7 | `nlinarith [hints]` real-arithmetic close | 11 / 0 | `L_pos_parameterInterval` TR:740-749 | OK |
| P8 | `by_cases` on an interval boundary, two branches | 11 / 6 | `initial_layer_bound` TR:433-453 | OK — partitions, no gap |
| P9 | structure instance (`where`) with proved fields | 4 / 0 | `ofNatural` TR:753-763 | OK |
| P10 | improper-integral evaluation on a half-line | 0 / 10 | `exponential_past` OH:678-686 | OK |

### Every instance of the error-hiding patterns

**`nlinarith` (TR: 11 sites; OH: 0).** All eleven are *real* inequality steps with the needed
product hints supplied explicitly; none is an attempt to prove a nonlinear fact from nothing.
| line | goal (paraphrase) | context it needs | verdict |
|---|---|---|---|
| 550 | `M·y ≤ M·(T + κ·y)` when `y ≤ T` | `mul_nonneg hκ.1 hy` given | OK |
| 565 | `M·T + (κM)(y-T) ≤ M(T+κy)` | `mul_nonneg (mul_nonneg hκ.1 hM) hT.le` | OK |
| 610 | `a·|z|·d/2 ≤ d·M` from `a·|z| ≤ M`, `0 ≤ d` | both hints given | OK |
| 669 | `(2/5)·step ≤ 2/5` from `step ≤ 1` | `(step_mem …).2` | OK |
| 745 | `η² ≤ 121/100` from `-11/10 < η < 11/10` | supplies `(η+11/10)(11/10-η) ≥ 0` — the exact SOS certificate | OK |
| 749 | `0 < 1 - 2hη²` | `hm : h·η² ≤ (1/1000)(121/100)` from `SmallParameters.h_le` (`NaturalAxisData.lean:43`) | OK, linear in the product |
| 1327 | `T + κy < s(1+finalTime)` | `hTs`, `hκy` in context | OK |
| 1349 | tolerance bookkeeping `< ε` | `hcontrol y hyf` | OK |
| 1731 | `1 ≤ 1 + ΛA + L` | `mul_nonneg hΛ.le hA` | OK |
| 1939, 2202 | `… ≤ … + |log 220 / 2|` | `abs_nonneg` | OK |

**`field_simp` then `ring` (TR: 5; OH: 13).** Every site names its nonvanishing side conditions and
each one is a *proved positivity*, never an assumption: TR:1176-1178 uses `hX.ne'` (`0 < p.1`
hypothesis) and `hfp.ne'` from `physicalF_positive` (`:1049`); TR:1258/1331/1767 close arithmetic with
positive constants; OH:328/340/419/429/441/450/479/570/960/1035/1040/1254/1261 all use
`(X_pos p).ne'` (`X = exp`, `:104`), `(H_pos w p).ne'` (`:148`), `(E_pos w p).ne'` (`:143`),
`d.core.P_pos`, `(shape_pos eta)`, or `(Real.sqrt_pos.mpr (by positivity)).ne'`. **OK.**

**`convert` (TR: 7; OH: 3).** All ten are `convert!` (no reducible-transparency unification) at
`using 1` or `using 2` and each is followed by an explicit `ring`/`funext`/`simp only` that discharges
the residual goal: TR:180 (+`ring`), 1123 (+`simp only; ring`), 1144 (+`ring`), 1583 (+`ring`),
2002 (+`ring`), 2070 (+`ring`), 2098 (+`ring`); OH:94 (+`funext`+`exact`), 349 (+`ring`),
847 (+`funext`+`dsimp`+`ring`). No `convert` here is hiding a mismatched statement. **OK.**

**`calc` chains whose endpoints must match (TR: 10; OH: 8).** I checked each chain's first and last
line against the theorem statement. Two deserve naming:
* `finalTime_sub_bigTime` (TR:1186-1192): `log(110/radius0) - log(100/radius0) = log(11/10)`. The
  chain goes `_ = log 110 - log 100 := by ring` (legal only *after* the two `Real.log_div` rewrites on
  line 1188, which are present) `_ = log(110/100) := (Real.log_div …).symm` `_ = _ := by norm_num`
  (i.e. `110/100 = 11/10`). Endpoints match the statement. **OK.**
* `damped_integral_bound` (TR:562-565): starts at `|∫₀^y F|` via `abs_add_le` after
  `rw [← hsplit]`, ends at `M·(T+κy)`. Endpoints match. **OK.**
The rest are `Real.exp`/`Real.log` regroupings (`OH:701-703, 735-738, 990-992, 1158-1161`) closed by
`rw [← Real.exp_add]; congr 2; ring` — endpoint-checked, **OK**.

**`simp` closing an inequality: 0 sites in either file.** Every inequality is closed by
`linarith`/`nlinarith`/`gcongr`-free explicit `mul_le_mul*`/`abs_*` lemmas, or `norm_num` on closed
rationals. **OK.**

**`omega` (TR: 3; OH: 0).** TR:1699, 1782, 1796, each discharging `i ≠ 0` for
`le_self_pow₀ hD (…)` from a context `hi : 1 ≤ i`. **OK.**

### Leaf-hypothesis trace for the top 3 results

The precedent the brief named (`GenericSupportedPolynomial.lean:130 hres`, proved by nobody) does
**not** recur here. I traced each terminal result's non-trivial hypotheses to a proved supplier:

| result | hypothesis | supplier | verdict |
|---|---|---|---|
| `ordered_seed_bounds` TR:2179 | `hsmall : SmallParameters h j` | **constructed** at `MatchingConeBounds.lean:987-988`: `⟨F.data.h_pos, hh, hjpos, (min_le_right _ _).trans (by norm_num)⟩` with `j := min (jcap/2) (1/2000)` (`:982`) | OK |
| " | `δ ≤ R.bigTime` (`:2187`) | **proved** at `ActivationContinuation.lean:1699-1704` from `freeze_before_Xbig` (`ReferencePath.lean:807-817`: `N.endpoint * exp(2δ) < Xbig = 100`, itself from `endpoint ≤ 4` and `exp(2δ) < 41/40`) | OK — this is the ramp's one arithmetically delicate leaf and it is discharged |
| " | `R.SmallLogControl … 1 T κ w₁ w₂` | **proved** by `exists_small_log_control` TR:1287 | OK |
| `exists_joint_small_control` TR:1434 | `hb : δ ≤ bigTime`, `hK : IsCompact K`, `hKJ` | as above; `isCompact_Icc` and `original_interval_interior` at `ActivationContinuation.lean:1711` | OK |
| `physicalProfiles` TR:1062 | `f_smooth`, `U_smooth` fields | `physicalF_smooth` `:999`, `physicalU_smooth` `:1024` — real proofs, not `sorry`, not fields | OK |
| `Pi_eq_future_integral` OH:859 | `w.pressure_neutral` | **theorem** `UniformAngularReset.lean:1130-1133`, derived from the `ResetWitness.pressure` field (`:927-928`), and `ResetWitness` is **inhabited** by `exists_scheduled_reset` (`:937-999`), which supplies all seven fields with real proofs (`:965-999`) | OK |

No `sorry`, no `axiom`, no `opaque`, no assumed structure field left dangling in either file.

## (C) Junction analysis

### C1 — how the ramp gets `C^∞` (chain re-derived from the original files)

```
TransitionRamp.lean:23   noncomputable def step (b w y : ℝ) : ℝ := OutgoingSchedule.sigma ((y - b) / w)
TransitionRamp.lean:25   theorem step_smooth (b w : ℝ) : ContDiff ℝ ∞ (step b w) :=
TransitionRamp.lean:26     OutgoingSchedule.sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const w)
```
```
OutgoingSchedule.lean:26  def sigma (x : ℝ) : ℝ :=
OutgoingSchedule.lean:27    FlatCutoff.edge 1 x / (FlatCutoff.edge 1 x + FlatCutoff.edge 1 (1 - x))
OutgoingSchedule.lean:37  theorem sigma_contDiff : ContDiff ℝ ∞ sigma :=
```
The denominator is proved *strictly* positive everywhere (`sigma_denom_pos`, `:29-35`, by `by_cases 0 < x`
and `FlatCutoff.edge_pos`/`edge_nonneg`), so `ContDiff.div` applies globally — there is **no** removable
singularity and **no** case split in `sigma`.
```
FlatCutoff.lean:26   def edge (c x : ℝ) : ℝ :=
FlatCutoff.lean:27     if x ≤ 0 then 0 else Real.exp (-c / x ^ 2)
FlatCutoff.lean:131  theorem edge_contDiff {c : ℝ} (hc : 0 < c) {n : ℕ∞} : ContDiff ℝ n (edge c) := by
FlatCutoff.lean:118  theorem polynomialEdge_contDiff {c : ℝ} (hc : 0 < c) (p : ℝ[X]) {n : ℕ∞} :
FlatCutoff.lean:119    ContDiff ℝ n (polynomialEdge c p) := by
FlatCutoff.lean:120    apply contDiff_all_iff_nat.2 (fun m => ?_) n
FlatCutoff.lean:121    induction m generalizing p with
```
**So the `if` *is* there, one level below `sigma`, at `x = 0` — and its smoothness is proved the
honest way**: not by asserting that the one-sided derivatives match, but by closing the whole
*inverse-polynomial family* `polynomialEdge c p` under differentiation (`derivativePolynomial`,
`:86-87`), proving `HasDerivAt` **at `x = 0` from the difference quotient**
(`polynomialEdge_hasDerivAt`, `:89-111`, the `rfl` case at `:97` uses
`hasDerivAt_iff_tendsto_slope`), and inducting on `m`. The limit input is Mathlib's
`expNegInvGlue.tendsto_polynomial_inv_mul_zero` (`:82`), majorized by `edge_le_glue` (`:50`). This is
the same Whitney/Borel-flavoured construction the audit already blessed at
`SpacetimeGluing.lean:192,235` — verdict **OK**, and it is *proved in-repo*, not assumed.

**Uniformity check.** `polynomialEdge_contDiff` proves `∀ m : ℕ` and then coerces via
`contDiff_all_iff_nat`, so `edge_contDiff`'s `n : ℕ∞` and `sigma_contDiff`'s `∞` are **one uniform
statement** — there is no `∃ C_k` anywhere in the chain, and no `ω`/analytic claim is made. **OK.**
The `sigma` interface is: `sigma_zero {x} (hx : x ≤ 0)` (`:44`), `sigma_one {x} (hx : 1 ≤ x)` (`:47`),
`sigma_nonneg` (`:52`), `sigma_le_one` (`:55`) — the two conditional ones have **non-strict**
hypotheses, so `step_zero`/`step_one` (TR:31/34) are also non-strict and give the ramp value exactly
*at* both ends of `[b, b+w]`. Strictness is load-bearing only on the *width*: `step_zero` and
`step_one` need `0 < w` (TR:31, `:34`), because they divide by `w`. **OK.**

### C2 — the real piecewise object, and why it has no junction

```
TransitionRamp.lean:702  noncomputable def physicalF (T κ w₁ w₂ : ℝ) : Field := fun p =>
TransitionRamp.lean:703    if p.1 ≤ R.radius0 then R.profiles.f p else Real.exp (R.logAmplitude T κ w₁ w₂ (R.logPoint p))
TransitionRamp.lean:705  noncomputable def physicalU (T κ w₁ : ℝ) : Field := fun p =>
TransitionRamp.lean:706    if p.1 ≤ R.radius0 then R.profiles.U p else R.axialVelocity T κ w₁ (R.logPoint p)
```
This is where a fake would live. It does not, because of:
```
TransitionRamp.lean:959  theorem physicalF_eq_log {T κ w₁ w₂ : ℝ} (hT : 0 < T)
TransitionRamp.lean:960      (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
TransitionRamp.lean:961      (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {p : Point}
TransitionRamp.lean:962      (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
TransitionRamp.lean:963      let R := ofNatural F hΛ hsmall hδ hδT hP0
TransitionRamp.lean:964      R.physicalF T κ w₁ w₂ p = Real.exp (R.logAmplitude T κ w₁ w₂ (R.logPoint p))
```
i.e. **on the whole open half-plane `0 < p.1` the `if` is redundant**: in the `p.1 ≤ radius0` branch
(`:968-976`) the identity is proved by pushing through `log_fields_eq_activation` and
`controlled_eq_reference_before` down to `N.refF_eq_logtime`. Therefore
```
TransitionRamp.lean:999  theorem physicalF_smooth … : ContDiffOn ℝ ∞ (…physicalF T κ w₁ w₂) (…radialDomain.carrier)
TransitionRamp.lean:1007   by_cases hX : 0 < p.1
TransitionRamp.lean:1017   exact (hs.congr_of_eventuallyEq he).contDiffWithinAt
TransitionRamp.lean:1018   · have hbefore : p.1 < R.radius0 := (le_of_not_gt hX).trans_lt R.radius0_pos
TransitionRamp.lean:1022   exact ((R.profiles.f_smooth.contDiffAt …).congr_of_eventuallyEq he).contDiffWithinAt
```
is a cover of the domain by the **two open sets** `{0 < p.1}` and `{p.1 < radius0}` (the second is
open and, since `radius0_pos`, contains every `p.1 ≤ 0`), on each of which `physicalF` is
*eventually equal* to a single smooth function. **The junction radius `p.1 = radius0` lies in the
interior of the first set, so no one-sided derivative is ever matched, and no `C^k`-for-each-`k`
statement is ever made.** Same argument for `physicalU` (`:1024-1047`). **Verdict OK** — this is the
honest construction and it is exactly parallel to the already-audited
`SpacetimeEndpoint.lean:250,277` pattern.

The reason the redundancy is legitimate: `hb : δ ≤ R.bigTime`. That is the ordering that makes the
"before" region of the ramp coincide with the frozen reference. It is **proved**, not assumed, at
`ActivationContinuation.lean:1699-1704` (see (B)). If `hb` were false the two branches would
disagree and `physicalF_eq_log` would be unprovable — the artifact does not paper over this.

### C3 — the interval facts, and the one subinterval bound

```
TransitionRamp.lean:1275  structure SmallLogControl (K : Set ℝ) (N : ℕ) (ε T κ w₁ w₂ : ℝ) : Prop where
TransitionRamp.lean:1276    finish_before : R.bigTime + w₁ + w₂ < R.finalTime
TransitionRamp.lean:1277    axial_jets : ∀ y ∈ Icc (0 : ℝ) R.finalTime, ∀ η ∈ K, ∀ n ≤ N,
TransitionRamp.lean:1279    positive_log_jets : ∀ y ∈ Icc (0 : ℝ) R.finalTime, ∀ η ∈ K, ∀ n ≤ N, 0 < n →
TransitionRamp.lean:1281    log_value : ∀ y ∈ Icc (0 : ℝ) (R.bigTime + w₁ + w₂), ∀ η ∈ K,
TransitionRamp.lean:1282      |R.logAmplitude T κ w₁ w₂ (y, η) - R.initialLog η| < ε
```
`finish_before` (`:1276`) is **strict** `<`, so `Icc 0 (bigTime+w₁+w₂) ⊊ Icc 0 finalTime`: the value
bound really does live on a strict subinterval, while the two jet bounds live on the whole interval.
This is *mathematically necessary*: past `bigTime+w₁+w₂` the angular slope is exactly `-2/5`
(`angularSlope_after`, `:115-118`), so `logAmplitude` drifts linearly and `|logAmplitude - initialLog|`
grows without bound; the two-sided statement on `Icc 0 finalTime` would be **false**.

The artifact never widens it. Three checks:
* **Physical restatement is exact, not looser.** `SmallPhysicalControl.log_value` (`:1358`) is on
  `Icc R.radius0 (radius R.radius0 (R.bigTime + w₁ + w₂))` while its siblings (`:1354`, `:1356`) are on
  `Icc R.radius0 110`. The translation `small_physical_of_log_control` (`:1371`) discharges it at
  `:1406-1412` with `hyend : R.logTime X ≤ R.bigTime + w₁ + w₂ := (A.logTime_le_iff hp).mpr hX.2` —
  the exact `logTime`/`radius` adjunction, no slack. **OK.**
* **Past the junction, the shape of the conclusion changes.** `normalizedLog_bounds_of_control`
  (`:1847`) concludes for **all** `y ≥ 0` (`:1851`) but the value part is **one-sided**:
  `R.normalizedLog T κ w₁ w₂ C y η ≤ B + 1` (`:1852`), *not* `|·| ≤ B+1`. For `y > a := bigTime+w₁+w₂`
  it rewrites with `normalizedLog_hold` (`:1826`, the exact affine hold) and then
  `sub_le_self _ (mul_nonneg (by norm_num) (sub_nonneg.mpr hay))` (`:1883`) — i.e. it uses that
  subtracting `(2/5)(y-a) ≥ 0` can only *decrease* the value. **This is the single sharpest honest
  move in the file.** And the consumer only needs the upper side, because it feeds
  `exp_jet_bound_local_of_upper` (`:1784`, hypothesis `hvalue : g η ≤ B`) at `:2000`. Bounding
  `|iteratedDeriv n (exp ∘ g)|` needs an *upper* bound on `g η`, never a lower one. **OK.**
* **The jet bounds, which *are* on the whole interval, are extended past `finalTime` by the hold
  lemma, not by re-reading the hypothesis.** `axialVelocity_jets_of_control` (`:1949`) and
  `MatchingConeBounds.axial_error_jet` (`:304`) both `by_cases y ≤ finalTime` and, in the `else`
  branch, rewrite with `axialField_hold` (`:184`) before applying the hypothesis at `finalTime`
  (`MatchingConeBounds.lean:310-320`; TR:`1966-1974`). **OK.**

`<` vs `≤` audit of the ramp interface: `step_zero`/`step_one` need `0 < w` (strict, division);
`hp : p.1 ≤ b` / `b + w ≤ p.1` are non-strict (so the "before"/"after" lemmas hold *at* the joins);
`finish_before` is strict `<` and is only ever weakened with `.le` (`:1856`, `:1899`, `:2147`);
`logField_hold`/`axialField_hold` need `bigTime+w₁+w₂ ≤ a ≤ y` (both non-strict, `:176`, `:186`).
An independent read-only consumer sweep of all 103 `TransitionRamp.` reference lines in 12 files
(delegated, then spot-verified by me at `ActivationContinuation.lean:1395/1506/1798-1799` and
`NominalProfile.lean:121/140`) found **no** case where a consumer supplies a weaker interval or trades
strictness in the unsafe direction; the only trades are `<` → `≤`. **OK.**

### C4 — `OutgoingHistories`'s own junction (`y = 0`), and its one-sided-derivative lemma

`OutgoingHistories` has a different junction: the ideal exponential past (`y ≤ 0`) versus the
corrected present. Its identities are stated *only* on the half-line, non-strictly: `E_ideal` (`:490`),
`U_ideal` (`:495`), `M_ideal` (`:937`), `Pi_ideal` (`:962`), `Sq_ideal` (`:1030`), `Sn_ideal` (`:1094`),
all with `{y : ℝ} (hy : y ≤ 0)`. Derivatives of these one-sided identities are transferred by
```
OutgoingHistories.lean:929  /-- A left closed interval determines the derivative even at its endpoint. -/
OutgoingHistories.lean:930  theorem derivative_from_left {f g : ℝ → ℝ} {v y : ℝ} (hy : y ≤ 0)
OutgoingHistories.lean:931      (hf : DifferentiableAt ℝ f y) (hg : HasDerivAt g v y)
OutgoingHistories.lean:932      (he : ∀ t ≤ 0, f t = g t) : HasDerivAt f v y := by
OutgoingHistories.lean:933    have hd : deriv f y = v := (uniqueDiffOn_Iic 0 y hy).eq_deriv _
```
**This is the honest form of a one-sided argument and it is not the fake shape.** It does **not**
derive differentiability from one-sided agreement; it *assumes* two-sided `DifferentiableAt ℝ f y`
(`hf`) and only transfers the derivative's *value*, which is legitimate because `Iic 0` has the unique
differentiability property at `y ≤ 0`. Its two callers supply `hf` from the **global** smoothness of
the constructed field, never from the piecewise formula: `dY_H_ideal` (`:984`) at `:994` passes
`(dY_hasDerivAt (H_smooth w) (y, eta)).differentiableAt`, and `dY_U_ideal` (`:999`) at `:1001` passes
`(dY_hasDerivAt (U_smooth d ha) (y, eta)).differentiableAt`. **OK.**

The improper-past identification is also honest: integrability on `Iic 0` is **proved**
(`exponential_past` `:678`, from Mathlib's `integrableOn_exp_mul_Iic`), each initial constant is
**proved equal** to its improper integral (`mass_past` `:688` → `initialM`, `angular_past` `:705` →
`initialI`, `transport_past` `:714`, `energy_past` `:740`, `pressure_past` `:764`), and `Iic y` is
reached from `Iic 0` by an explicit split `Iic_union_Ioc_eq_Iic` (`past_integrable` `:665-670`,
`past_integral` `:672-676`). **No interchange of limits is asserted anywhere in the file.** The one
forward-in-`y` integral, `Pi_eq_future_integral` (`:859`), gets its `Ioi y` integrability from
`E_square_integrable` (`:833`), which is proved by exhibiting *compact support* of the correction
(`support changeE ⊆ Icc (d.releaseStart - 4) d.releaseStart`, `:839`) plus
`SchedulePressure.angular_square_integrable`. **OK.**

`OutgoingHistories` contains **no** `Icc a b`-restricted estimate at all — every result is at an
arbitrary `y : ℝ`, or on a half-line `Iic y`/`Ioi y`, or under `y ≤ 0` / `d.core.endpoint ≤ y`. So the
"bound on a subinterval, used on the whole interval" shape has **no place to live** in that file, and
the boundary case `y = d.core.endpoint` is covered by both `E_before` (`:483`, `y ≤ endpoint`) and
`U_after_endpoint` (`:574`, `endpoint ≤ y`), which is why `angular_product_eq` (`:578`) can
`by_cases` with no gap. **OK.**

## (D) Kernel-risk sweep, vectors (1)(2)(3)

Repo-token sweep over both files (grep, then every hit read in the original):

| token | TransitionRamp | OutgoingHistories | note |
|---|---|---|---|
| `inductive` | **0** | **0** | |
| `structure` | 3 (`:195`, `:1275`, `:1352`) | 0 | `:1275`/`:1352` are `Prop`-valued; none recursive |
| `.rec` / `Acc.rec` / `Nat.rec` / `WellFounded` | **0** | **0** | |
| `termination_by` | **0** | **0** | |
| `deriving` | **0** | **0** | |
| `decide` / `native_decide` | **0** | **0** | |
| `Nat.pow`/`div`/`mod`/`gcd` | **0** | **0** | |
| `axiom`/`opaque`/`unsafe`/`partial def` | **0** | **0** | |
| `macro`/`elab`/`syntax`/`notation`/`run_cmd`/`set_option` | **0** | **0** | confirms the repo-wide result |
| `sorry`/`admit` | **0** | **0** | |
| `induction`/`cases` | 10 (`:334, 341, 363, 377, 391, 400, 417, 590, 790, 1632`) | **0** | |
| recursive `def` | **1** (`parameterJet`, `:327-329`) | **0** | |
| proof-closing bare `rfl` | 16 | 3 | see D3 above |

**Vector (1) — recursive types, recursors, iota.** The *entire* recursion surface of my scope is:
```
TransitionRamp.lean:327  noncomputable def parameterJet : ℕ → Field → Field
TransitionRamp.lean:328    | 0, F => F
TransitionRamp.lean:329    | n + 1, F => parameterPartial (parameterJet n F)
```
one **structural** recursion on `ℕ` (hence compiled to `Nat.rec`/`brecOn`, **not** `WellFounded.fix`,
and hence carrying **no** `Acc.rec` — which is why the audit's `termination_by`/`wf`/explicit-`.rec`
censuses see nothing here), plus nine `ℕ`-`induction`/`cases` tactic uses and one `cases r` on
`StressActivation.HistoryRow`:
```
StressActivation.lean:539  inductive HistoryRow
StressActivation.lean:540    | mass | angular | transport | energy | pressure
```
a **five-constructor, non-recursive, non-indexed** enum, so `TransitionRamp.lean:790`
(`· cases r <;> rfl`) is five one-step match reductions against `profileHistory`
(`StressActivation.lean:800-805`).

Classification of the 19 proof-closing bare `rfl` for iota exposure:
* **Iota on `parameterJet` at `0` (5 sites, one step each):** TR:342, 364, 378, 401, 418, all
  `| zero => rfl` in the `induction n` base case, where the goal mentions `parameterJet 0 F`.
  TR:342 additionally needs `iteratedDeriv 0 f x ≡ f x`, i.e. one further `Nat.rec` base reduction
  inside Mathlib's `iteratedFDeriv` plus a `ContinuousMultilinearMap` structure/eta unfold.
  **UNBUILT** that these are the exact reduction sequences (no kernel here), but the *shape* is a
  single base-case iota; peak recursion depth **1**.
* **Iota on a 5-constructor enum (1 site, 5 branches):** TR:790.
* **No iota at all (13 sites)** — delta/beta/proj only, on non-recursive definitions:
  TR:370, 537, 700, 860, 890, 901, 1232, 1398, 1466, 1995 (unfolding `integrate`, `primitive`,
  `logField`, `chart`, `physicalF` after the `ite` is eliminated, and `Prod` projections) and
  OH:502, 510, 1179 (`M ≡ massMoment`, `Ns` ≡ its ratio).
* No bare `rfl` in scope is asked to reduce a recursive function at a *symbolic* argument, and none
  is asked to unfold a well-founded recursion. **Verdict for vector (1): OK / negligible.**

**Vector (2) — `Nat` arithmetic delegated to GMP.** Zero `decide`, zero `Nat.pow/div/mod/gcd`, zero
`Finset`/`Nat.choose`/`Nat.factorial` *closed* evaluations.
* **Largest closed numeral in scope: `1000`**, at
  `TransitionRamp.lean:747` — `have hm := mul_le_mul hs.h_le hsquare (sq_nonneg η) (by norm_num : (0 : ℝ) ≤ 1 / 1000)`.
  Runners-up: `220` (`:718`, `:1247` — `show (220 : ℝ) = 2 * 110 by norm_num`, `:1896`, `:1939`,
  `:2198`, `:2202`), `121` and `100` (`:744` — `η ^ 2 ≤ (121 / 100 : ℝ)`), `110` (`:270`, `:1190-1191`,
  `:1264-1268`), `100` (`:269`, `:1198-1201`).
  **Largest closed numeral in `OutgoingHistories.lean`: `32`** (`:1109`).
* **Peak kernel numeral work: 4-digit `Nat`/`Int` literal arithmetic inside `norm_num` certificates
  on `ℝ`** — the hardest single item is `(220 : ℝ) = 2 * 110` (`:1247`) and
  `Real.log_div (by norm_num) …` on `110/100` (`:1188-1191`). Every exponent in scope is either the
  literal `2` (`contDiffAt_snd.pow 2`, `pow_two`) or a *symbolic* `n : ℕ`
  (`D ^ i`, `(B+1) ^ n`, `n.factorial`, `:1609-1610, 1774, 1983, 2084, 2197`) — the `factorial` and
  `^ n` are never evaluated at a literal, they are majorized symbolically by `finite_majorant`
  (`:1630`). `d.core.lam ^ (28 : ℕ)` appears in `ResetWitness` (`UniformAngularReset.lean:929`, out of
  scope) with a *variable* base, so again no numeral computation.
  **This is nowhere near GMP-stress territory. Verdict for vector (2): OK.**

**Vector (3) — custom metaprogramming.** Zero occurrences of any of
`macro`/`macro_rules`/`elab`/`syntax`/`notation`/`run_cmd`/`#eval`/`set_option`/`native_decide`/
`attribute`-with-custom-elab in either file. The only attributes are `@[simp]`
(`TransitionRamp.lean:65`; `OutgoingHistories.lean:512, 521, 523, 525, 527, 529, 531, 532`), which do
not extend the elaborator. **Verdict for vector (3): OK.** (Consistent with the established
repo-wide result; I did not re-derive that result.)

### Per-site verdict table (audited sites)

| site | what it is | verdict |
|---|---|---|
| TR:23, 25 `step`, `step_smooth` | ramp primitive; smoothness by composition from `sigma_contDiff` | OK |
| TR:31, 34 `step_zero`, `step_one` | ramp endpoints; non-strict in `y`, strict in `w` | OK |
| TR:80, 84 `angularSlope`, `axialSlope` | the two ramps | OK |
| TR:105-122 `*_before`, `*_after` | ramp plateau values at and beyond the joins | OK |
| TR:160 `integrate_affine_after` | affine continuation past a constant slope | OK |
| TR:174, 184 `logField_hold`, `axialField_hold` | the exact hold; `-2/5` slope for the angular one | OK |
| TR:195 `StockReference` | 5 data + 4 Prop fields, all instantiated at `:753` | OK |
| TR:327-329 `parameterJet` | the only recursion in scope; structural on `ℕ` | OK (see D) |
| TR:424-484 `integral_norm_bound`, `initial_layer_bound`, `late_layer_bound` | interval-split integral estimates; `Icc` hypotheses restricted correctly at `:453`, `:469`, `:483` | OK |
| TR:541 `damped_integral_bound` | `M(T+κy)`; splits at `T`, uses `damping_eq_constant` for `t ≥ T` | OK |
| TR:576 `compact_stock_jet_bound` | `∃ M ≥ 0, ∀ n ≤ N`; `induction N` building a `max` | OK |
| TR:702-706 `physicalF`, `physicalU` | the piecewise definitions | OK — junction is removable, (C2) |
| TR:959, 979 `physicalF_eq_log`, `physicalU_eq_log` | the branch-agreement identity that removes the junction | OK, **load-bearing** |
| TR:999, 1024 `physicalF_smooth`, `physicalU_smooth` | `C^∞` through `radius0` by open cover + `congr_of_eventuallyEq` | OK, **load-bearing** |
| TR:1062 `physicalProfiles` | the `Profiles` structure the cone modules consume; both smoothness fields are real proofs | OK |
| TR:1152 `physical_radial_equations` | the two prescribed log-clock ODEs; `field_simp` with `hX.ne'`, `hfp.ne'` | OK |
| TR:1186-1212 `finalTime_*`, `logTime_*`, `radius0_lt_100` | the `100`/`110`/`11/10` geometry | OK |
| TR:1275, 1352 `SmallLogControl`, `SmallPhysicalControl` | the two control records; **`log_value` on a strict subinterval, by necessity** | OK / **NOTE** |
| TR:1287 `exists_small_log_control` | constructs the thresholds; `w0 := min ((finalTime-bigTime)/4) (ε/4)` | OK |
| TR:1371 `small_physical_of_log_control` | log→physical restatement; the `log_value` interval is translated *exactly* (`:1410`) | OK, **load-bearing** |
| TR:1510 `exists_uniform_initialLog_bound` | `∃ B, ∀ C` — binder order correct, `B` (`:1518`) is `C`-free | OK |
| TR:1605 `local_composition_jet_bound` | `n! · B · Dⁿ`; constant *is* `n`-dependent and is *stated* so | OK |
| TR:1630 `finite_majorant` | majorizes an `n`-dependent constant over `n ≤ N`; `induction N` | OK |
| TR:1662, 1722 `exists_uniform_logPhi_jets`, `exists_normalized_natural_jets` | `∃ B ≥ 0, ∀ C, ∀ E, ∀ Y, ∀ n ≤ N` — `N` fixed *before* `B`; no claim of `n`-uniformity | OK |
| TR:1784 `exp_jet_bound_local_of_upper` | needs only an **upper** bound on `g η` — the reason the one-sided value bound suffices | OK, **load-bearing** |
| TR:1826, 1835 `normalizedLog_hold`, `normalizedLog_hold_positive_jet` | exact affine hold; jets are hold-invariant for `n > 0` | OK |
| TR:1847 `normalizedLog_bounds_of_control` | extends to all `y ≥ 0` by **weakening to one-sided**, not by widening `log_value` | OK, **sharpest honest move** |
| TR:1891 `endpointLog_jets_of_control` | uses `log_value` **only at the endpoint** `a` (`:1908`, `⟨ha0, le_rfl⟩`) | OK |
| TR:1976, 2005 `physicalF/U_postaxis_jet_bound` | `K/C` and `B+1`; the `C`-dependence is explicit in the bound | OK |
| TR:2179 `ordered_seed_bounds` | terminal result; `∃B ∃K ∃BJ ∀C`; covers **all** `X ≥ 0` in two branches (`:2221`) | OK |
| OH:36-38 `logDomain` | `carrier = univ` — no radial-axis domain, hence no junction | OK |
| OH:62 `history` | `initial p.2 + primitive f p` | OK |
| OH:127-139 `initialM … Pi` | the five histories and their initial data | OK |
| OH:286-314 `XW, W, Sq, Sn, angularStock, axialStock, Qs, Ns` | transport factor and the two lags | OK |
| OH:412, 422 `Qs_integrated`, `Ns_integrated` | equation (9); `field_simp` with `X_pos`, `H_pos` | OK |
| OH:431, 443 `Qs_hasDerivAt`, `Ns_hasDerivAt` | I re-derived the quotient rule by hand and it matches the stated derivative exactly | OK |
| OH:453, 461 `Qs_equation`, `Ns_equation` | the two ODEs; no derivative identity is an input | OK |
| OH:483-499 `E_before`, `E_ideal`, `U_ideal`, `U_before_pulse` | ideal-past identities, all `y ≤ …` non-strict | OK |
| OH:665-686 `past_integrable`, `past_integral`, `exponential_past` | improper-past machinery; integrability **proved** | OK |
| OH:688-772 `mass/angular/transport/energy/pressure_past` | each initial constant **equals** its improper integral | OK, **load-bearing** |
| OH:833, 859 `E_square_integrable`, `Pi_eq_future_integral` | the one forward integral; integrability from compact support of the correction | OK |
| OH:921-935 `exponential_integral_left`, `derivative_from_left` | one-sided derivative transfer with two-sided differentiability **assumed** | OK, **load-bearing** |
| OH:1130 `exponential_sum_past` | two-exponential past | OK |
| OH:1183-1189 `physicalX … physicalS` | entrance-radius rescaling | OK |
| OH:1248, 1257 `Qs_dilation`, `Ns_dilation` | `XR` cancels from both lags | OK |
| OH:1263-1276 `p1`, `p2`, `p1_dilation`, `p2_dilation` | `p2` divides by `(1 - 2·d.h·η²) · E w p` with **no** nonvanishing hypothesis | **NOTE** — see Escalation E2 |

## Escalations

**E1 — Is `physicalF_eq_log`'s hypothesis `hb : δ ≤ bigTime` supplied at *every* call site, or only
at the one I traced?**
*Precise question:* `physicalF_smooth` (`TransitionRamp.lean:999`) and every downstream physical-field
lemma carry `hb : δ ≤ (ofNatural …).bigTime`. I verified the single discharge at
`ActivationContinuation.lean:1699-1704` (via `ReferencePath.freeze_before_Xbig`, `:807`), and I
verified that `exists_joint_small_control` (`TransitionRamp.lean:1434`) has exactly one caller
(`ActivationContinuation.lean:1710`). But `physicalProfiles` (`TransitionRamp.lean:1062`) takes `hb`
as a *parameter* and is referenced from `NominalProfile.lean` and `NominalConeAssembly.lean`. Does
**every** construction of a `physicalProfiles` term in the repo obtain `hb` from
`freeze_before_Xbig`, or does some path obtain it from a weaker `δ`-smallness assumption that is
itself only assumed?
*What would settle it:* the list of every term of type `Profiles _` built via
`TransitionRamp.physicalProfiles`, with the provenance of its `hb` argument chased to either
`ReferencePath.freeze_before_Xbig` or a hypothesis of a top-level theorem. If the latter, whether that
top-level theorem is itself instantiated. (A `lake build` with `#print axioms` on the two headline
theorems would settle the whole family at once; not possible here.)

**E2 — `OutgoingHistories.p1`/`p2` divide by `1 - 2·d.h·η²` with no nonvanishing side condition.
Do their consumers establish it?**
*Precise question:*
```
OutgoingHistories.lean:1263  noncomputable def p1 (XR : ℝ) (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
OutgoingHistories.lean:1264    physicalX XR p * Qs w Amp p / (1 - 2 * d.h * p.2 ^ 2)
OutgoingHistories.lean:1266    physicalX XR p * Ns w Amp p / ((1 - 2 * d.h * p.2 ^ 2) * E w p)
```
Lean's `x / 0 = 0` makes these total, and `p1_dilation`/`p2_dilation` (`:1268`, `:1273`) are true even
at a zero of the denominator because `ring` treats `/` as `* ·⁻¹`. So **nothing in this file is
wrong**. But any consumer that reads `p1` as "the physical source ratio" needs
`1 - 2·d.h·η² ≠ 0`. The uses I see are `TailCone.lean:1478, 1495, 1551`, `OutgoingCone.lean:221, 225,
314, 337, 355, 370-377, 535, 655`, `NominalConeAssembly.lean:883`.
*What would settle it:* for each of those sites, the hypothesis in scope that gives
`1 - 2·d.h·η² > 0` (I expect it from `d.h ≤ 1/1000`-style smallness plus `η ∈ Icc (-1) 1`, by exact
analogy with `L_pos_parameterInterval`, `TransitionRamp.lean:740-749`, which proves precisely
`0 < 1 - 2hη²` on `parameterInterval`). If some site lacks it, the *statement* there is vacuous rather
than false — still worth knowing. This is outside my two files, so I did not resolve it.

**E3 — Is `TransitionRamp.lean:342`'s bare `rfl` really a `rfl`, and what does the kernel reduce?**
*Precise question:* `parameterJet_eq_iteratedDeriv`'s base case (`:342`) closes
`parameterJet 0 F p = iteratedDeriv 0 (fun η => F (p.1, η)) p.2` by bare `rfl`. Mathlib proves
`iteratedDeriv_zero` by `simp [iteratedDeriv]`, not by `rfl`, which suggests the definitional path
here goes through the `continuousMultilinearCurryFin0` equiv and a `ContinuousMultilinearMap` coercion.
*What would settle it:* `set_option pp.all true in #check @iteratedDeriv` plus `example : ... := rfl`
at the relevant instantiation, and `#print axioms` / a `whnf` trace showing the reduction is
`Nat.rec`-base + structure-projection only. Marked **UNBUILT**. Even in the worst case this is a
depth-1 iota plus projections, so I rate the kernel risk negligible; the escalation is about
*confirming the shape*, not about doubting the result.

## Residue — what I could NOT check

1. **Anything requiring elaboration or the kernel.** No Mathlib, no `lake build`. I never confirmed
   that a single line of either file elaborates, that a bare `rfl` closes, that `nlinarith` finds its
   certificate, or that `field_simp` leaves the goal I claim it leaves. All of (B) and (D) is
   source-shape reasoning. **UNBUILT.**
2. **Mathlib lemma statements.** I took the *names* `ContDiff.div`, `norm_iteratedFDerivWithin_comp_le`,
   `integrableOn_exp_mul_Iic`, `integral_exp_mul_Iic`, `intervalIntegral.integral_Iic_sub_Iic`,
   `intervalIntegral.integral_Iic_add_Ioi`, `uniqueDiffOn_Iic`, `contDiff_all_iff_nat`,
   `contDiff_succ_iff_deriv`, `expNegInvGlue.tendsto_polynomial_inv_mul_zero`,
   `le_self_pow₀`, `iteratedDeriv_const_add`, `iteratedDeriv_const_mul`, `EventuallyEq.iteratedDeriv_eq`
   at face value. If any has a different hypothesis shape than I assumed, several of my OK verdicts
   would need revisiting. **UNBUILT.**
3. **The `∞` in `ContDiff ℝ ∞`.** I read it as `C^∞` (`(⊤ : ℕ∞)` coerced into `WithTop ℕ∞`), **not**
   `ω`/analytic, on the evidence that `FlatCutoff.polynomialEdge_contDiff` obtains it from
   `contDiff_all_iff_nat` over `n : ℕ` and that `edge_contDiff`'s index is `{n : ℕ∞}`
   (`FlatCutoff.lean:118, 131`). I could not confirm the notation's meaning in this Mathlib version.
4. **Downstream sufficiency.** I verified that no consumer *misuses* the ramp's intervals. I did not
   verify that the bounds the ramp *provides* are strong enough for what the cone/matching modules
   need — that is a different question and a different worker's scope.
5. **E1, E2, E3 above.**
6. **The 10 out-of-cone `TransitionRamp` theorems and 47 out-of-cone `OutgoingHistories` theorems**
   were read but not traced to consumers, since by construction they have none in the top claims' cone.
7. **`ResetWitness`'s upstream.** I confirmed `exists_scheduled_reset`
   (`UniformAngularReset.lean:937`) constructs all seven fields, but I did not audit
   `uniform_reset_branch` or `actual_debt_first_jet_bound`, which it consumes.
8. **The audit's own `CONE.csv` derivation.** I used its `in_cone` column as given; I did not
   re-derive the cone.
