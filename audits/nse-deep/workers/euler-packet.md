# Worker report — `euler-packet`: the sole source of finiteness in the Euler half

Scope owner: read-only auditor. Repo under audit: `/home/gsm/.openclaw/workspace/repos/NSE`
(openai/NavierStokesAndEuler @ `f9e8bc5`). No Mathlib build available: **source-level reading only**,
so nothing below is a claim that the file compiles — it is a claim about what the text says.
Nothing under the audit path was modified.

Assignment: the two items two prior workers left open as load-bearing and unread —
`Euler/PacketStageInitialLimit.lean:106 initialDataLimit_no_euler` and
`Euler/PacketInfiniteConstruction.lean:68 constructionScales` — plus whatever the finiteness of the
Euler lifespan `Tstar` actually rests on.

Three read-only sub-workers were used for depth (their reports are cited inline and kept as
`_scratch-packet-contradiction.md`, `_scratch-packet-horizon.md`, `_scratch-packet-series.md`).

## Verdict in one line

The packet-construction finiteness chain is **earned analysis, not a trick**: `Tstar` is provably in
`[baseHorizon/12, baseHorizon] ⊆ (0,1]`, the `Classical.choice` at `PacketInfiniteConstruction.lean:69`
is a choice on a type whose `Nonempty` is *proved* (`exists_scales`, `PacketInductionScales.lean:123`),
the packet recursion is **structural** (no `termination_by`, no `WellFounded`, no `Acc.rec`), the
convergence conditions are real `Summable` + `tsum ≤ δ` statements, and the kernel is asked to compute
essentially nothing (`decide` appears 3× in the whole chain, all of the form `(by decide : 2 ≠ 0)`).
The one *audit-process* defect I found is in our own instrument, not in the artifact: **`CONE.csv`
systematically drops the edges that carry this chain**, so the very theorems that make the Euler claim
non-vacuous are marked `in_cone=False` (details in `## Cone status`, with a measured fix).

## Scope

| file | lines | decls (CONE.csv) | read |
|---|---|---|---|
| `Euler/PacketStageInitialLimit.lean` | 114 | 11 | **in full, line by line** |
| `Euler/PacketInfiniteConstruction.lean` | 77 | 12 | **in full, line by line** |
| `Euler/PacketInductionScales.lean` | 221 | 16 | **in full, line by line** |
| `Euler/PacketStageContradiction.lean` | 73 | 2 | **in full, line by line** |
| `Euler/PacketInitialSmoothLimit.lean` | 99 | 13 | **in full, line by line** |
| `Euler/SmoothL2Series.lean` | 159 | 23 | **in full, line by line** |
| `Euler/OrdinaryEulerVaryingHorizon.lean` | 109 | 5 | **in full, line by line** |
| `Euler/PacketFiniteLifespan.lean` | 60 | 9 | **in full, line by line** |
| `Euler/PacketInductionStage.lean` | 145 | 19 | `structure Stage` (:23-52) in full, rest skimmed |
| `Euler/PacketInductionScaleBounds.lean` | 122 | 22 | :1-80 read, rest skimmed |
| `Euler/PacketSourceScaleSequence.lean` | 182 | 21 | :1-45 read (the definitions), rest skimmed |
| `Euler/PacketStageGrowth.lean` | 95 | 5 | :12-95 read (all 5 decls) |
| `Euler/PacketSourceScaleChoice.lean` | 246 | 20 | `SmallSeries` block :110-140 + `scaleSequence` :226-244 read |
| `Euler/OrdinaryEulerLifespan.lean` | 86 | 9 | :29-65 read |
| `Euler/PacketStageLocalExistence.lean` | 86 | 2 | :39-64 read |
| `Euler/PacketBaseGuardScales.lean` | 79 | 10 | definitions read; delegated in depth to `packet-horizon` |

Totals: **16 files, 199 declarations in CONE.csv terms; 91 declarations in 8 files read line by line**
(every declaration of those files), plus ~40 further declarations read individually inside the other
8 files. Sub-workers read, in addition, `Euler/PacketStageContradiction.lean`'s dependency cone
(`OrdinaryEulerRestriction`, `EulerBreakdownCriterion`), the `baseHorizon`/`Tstar` chain through
`Euler/EulerFiniteLifespan.lean` and `Euler/Solution.lean`, and the summability chain
(`PacketCommonScaleChoice`, `PacketPressureSeries`, `ParentRenewalPrefix`, `ParentRenewalScaleCosts`).

## A. `initialDataLimit_no_euler` — what it says and what it uses

Exact statement, `Euler/PacketStageInitialLimit.lean:106-112` (verbatim):

```lean
theorem initialDataLimit_no_euler :
    ¬ ∃ U : EulerOrdinarySobolev.Evolution (baseHorizon S.J S.X)
        (baseHorizon_pos S.J S.j_one S.x_pos).le,
      (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field=
        (initialDataLimit P hq hB).field :=
  no_euler_evolution_of_initial_H3 P (initialDataLimit P hq hB).field
    (initialDataLimit_Hm P hq hB hstep 3)
```

In words: for an *actual* stage family `P : ∀ n, Stage S n` whose stage-to-stage initial increments obey
`hstep` (:61-65), there is **no** Euler evolution on the closed interval `[0, baseHorizon S.J S.X]` whose
velocity at time `0` equals the limit datum. It is a term-mode one-liner: everything is imported from
`no_euler_evolution_of_initial_H3` plus the H³ convergence `initialDataLimit_Hm … 3`.

**Is it a `Classical.choose` of a hidden existence claim? No.** The proof term names exactly two facts:

1. `initialDataLimit_Hm` (`:84-104`): `∀ s, Tendsto (fun n => derivativeSum s (u_n(0,·) - u∞)) atTop (𝓝 0)`,
   i.e. the stage initial data converge to `initialDataLimit` in **every** Sobolev order. Its proof is
   honest bookkeeping: `initial_velocity_partial` (:69-82, induction on `N`, using `hstep`) identifies the
   stage-`(1+N)` initial velocity with `initialBase + initialPartial … N`, and then
   `EulerPacketInitial.fullInitialLimit_Hm` supplies the convergence; the only manipulation is an index
   shift `n ↦ n+1` via `tendsto_add_atTop_iff_nat 1` (:96-103). No choice, no interchange beyond a
   finite index shift.
2. `no_euler_evolution_of_initial_H3` (`Euler/PacketStageContradiction.lean:67-72`), which is
   `rintro ⟨U,hU⟩; exact false_of_evolution P u₀ hinit U hU`.

**The content is in `false_of_evolution` (`PacketStageContradiction.lean:25-65`)**, and I read it in full.
Mechanism, with no step omitted:

* `durations n := (P n).parent.T`, each in `(0, baseHorizon S.J S.X]` (`horizon_le`, a `Stage` field).
* `V n := (P n).state.regularity.ordinaryEvolution` — the stage's own genuine evolution on its own horizon.
* `hfield` (:37-46): the difference of the *hypothetical* `U` restricted to `durations n` and `V n`, read at
  time `0`, is exactly `u_n(0,·) - u₀`. Proved by `funext` + `velocity_match`, i.e. by definitional
  bookkeeping, not by an estimate.
* `hlim` (:52-56): therefore the H³ norm of that difference at time 0 → 0 — this is where `hinit`
  (= `initialDataLimit_Hm … 3`) enters.
* `hno := U.no_gradient_escape_of_initial_tendsto_varying …` (:57) — the **a-priori bound**, see below.
* `heq` (:60-64): `‖fderiv ℝ ((V n).velocity (times n)).field 0‖ = (P n).activationGradient`, by `rfl`
  after rewriting with `velocity_match`. This is *definitional*: `activationGradient` is literally
  `‖fderiv ℝ (fun x => P.state.evolution.velocity (P.time,x)) 0‖` (`PacketStageGrowth.lean:49-50`).
* `exact gradient_atTop P` (:65) — the **divergence**.

So the contradiction is `divergence ∧ no-escape`, and both halves are proved, not assumed:

* Divergence: `gradient_atTop` (`PacketStageGrowth.lean:83-93`) = `previousShear_ge_index`
  (`:25-34`, `(n:ℝ)+1 ≤ previousShear S.J S.X n` by induction on `n`, from the `Scales`-derived
  `shear_separation`, `PacketInductionScaleBounds.lean:61-67`) combined with `gradient_lower`
  (`:52-81`, `previousShear/2 ≤ activationGradient`, proved from the *frame decomposition*: the strain at
  the origin equals the frame's rank-one shear term up to `frame.G + frame.error`, and those two are
  ≤ `previousShear/2` by the `activationMargin` budget). Nothing here is a hypothesis of the theorem
  being audited; all inputs are `Stage` fields that the successor constructions must discharge.
* No-escape: `Evolution.no_gradient_escape_of_initial_tendsto_varying`
  (`Euler/OrdinaryEulerVaryingHorizon.lean:96-107`) reduces to `no_gradient_escape_varying` (:61-94),
  which is (i) an H³ stability estimate `h3_stability` with a Gronwall factor
  `exp (3 * stabilityConstant U.referenceSize * T)` and a smallness side condition
  `640 * ε n * exp(...) ≤ 1/2` (:38-48 — note the estimate is *not* claimed unconditionally),
  (ii) the Sobolev embedding `real_smooth_fderiv_le_H3` (:81-83) to convert H³ closeness into closeness
  of `fderiv` at the origin, and (iii) `EulerBreakdownCriterion.no_escape_near_compact_trajectory`
  (:74-78): a sequence that stays within `err n → 0` of a **continuous** function on the compact
  `[0,T]` cannot tend to `atTop`. That is the real reason a blowup cannot happen inside the lifespan
  of a fixed solution, and it is the step that makes the whole argument non-circular: the hypothetical
  `U` supplies the continuous trajectory, the packets supply the divergence.

**Vacuity check.** The negated existential could be cheap in two ways, and both are closed off *by the
artifact itself*: (a) if `Evolution T` were uninhabitable, then `initialDatum_local`
(`PacketFiniteLifespan.lean:27-30`, via `Stage.exists_local_evolution`,
`PacketStageLocalExistence.lean:39-41`) could not produce an evolution for the **same** datum on
`(0, baseHorizon/12]` — it does; (b) if `.field` equality were unachievable for a silly coercion reason,
the same local-existence lemma could not conclude `(E.velocity ⟨0,…⟩).field = u₀.field`. So the pair
"exists on `[0,L]`, `L ≤ baseHorizon/12`" + "does not exist on `[0,baseHorizon]`" is **mutually
constraining**: a junk definition of `Evolution`/`HasEulerEvolution` that made one side trivial would
make the other side false. That is the strongest non-vacuity argument available without a build, and it
is checkable: read `PacketStageLocalExistence.lean:39-86` and `OrdinaryEulerLifespan.lean:29-34`.

## B. `constructionScales` — what is chosen, where it is proved, and is the recursion sound

```lean
abbrev ConstructionScales :=                             -- PacketInfiniteConstruction.lean:65-66
  Scales (requiredExponent : ℝ) (commonThreshold gradientConstant hessianConstant)

def constructionScales : ConstructionScales :=            -- :68-70
  Classical.choice (exists_scales (requiredExponent : ℝ)
    (commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))
```

* **What is chosen.** `Classical.choice`, not `Exists.choose`: the argument is a `Nonempty (Scales c B)`
  and the chosen object is a *record of numbers and inequalities*, `structure Scales`
  (`PacketInductionScales.lean:83-112`): `J D : ℕ`, `X δ : ℝ`, the guards `3 ≤ J`, `2000 ≤ D`, `8 ≤ X`,
  `0 < δ ≤ 1/16`, `δ ≤ activationMargin`, `10^6 * geometryConstant * δ ≤ 1`, the frequency guards
  (`normal_frequency`, `previous_floor`, `first`), **six `SmallSeries` fields** (`frequency_series`,
  `activation_series`, `correction_series`, `bad_series`, `good_series`, `renewal_series`),
  `time_small : baseHorizon J X ≤ 1` and `localized : baseGuardCost … ≤ 1/2`. Crucially the record
  contains **no packet, no frame, no evolution** — so choosing it cannot smuggle in an object whose
  existence is the thing to be proved. (That is also what the file's own docstring claims,
  `PacketInductionScales.lean:6-8`; unlike the docstring, the field list is checkable, and it checks out.)
* **Where the existence is proved.** `exists_scales` (`PacketInductionScales.lean:123-193`), read in full.
  Mechanism: `exists_base_power` (:114-121) picks `D ≥ 2000` with `firstFrequencyPower < D*(theta/100)`
  (Archimedean `exists_nat_gt`); `EulerPacketCommonScaleChoice.exists_common_guards` (:125-127) picks a
  single `J ≥ 3` that works for *all* the cost specs simultaneously (`extraCost` is a
  `Sum Unit Bool → CostSpec`, i.e. a **finite** family, :70-73 — the simultaneity is over a `Fintype`,
  not over a limit); `η` is the explicit minimum of four margins (:128-139) with `positivity` for
  `0 < η`; then `hchoice η hη` yields `X₀, δ`; then `hevent` (:150-171) is a `filter_upwards` of **seven**
  `Eventually`s at `atTop` in `X` (X ≥ X₀, X ≥ 48000, `FirstScaleGuards`, all-`n` universal frequency,
  `X^D ≥ B`, previous-frequency floor, base guards) and `hevent.exists` (:172) extracts one `X`.
  Every field of the record is then discharged by a named fact; nothing is `sorry`, nothing is a
  hypothesis of `exists_scales` itself except `0 ≤ c`.
  **Consequence:** the `Classical.choice` is on a type that is *proved* nonempty at exactly the
  parameters used (`packets := stages constructionScales le_rfl le_rfl`, :72 — `le_rfl` is legitimate
  because `ConstructionScales` is `Scales (requiredExponent : ℝ) (commonThreshold …)`, the very values
  the `Stage` constructions demand). There is **no subclass gap** here (question C(a)).
* **Is the construction an infinite recursion, and is it well-founded?**
  ```lean
  def stages : (n : ℕ) → Stage S n           -- PacketInfiniteConstruction.lean:39-41
    | 0 => S.firstStage
    | n+1 => (stages n).successor hq hB
  ```
  This is **structural** recursion on `ℕ` with a dependent motive (`Stage S n`). Evidence, all of it
  syntactic and checkable: (i) there is no `termination_by` / `decreasing_by` in the file; (ii)
  `stages_zero` (:43) and `stages_succ` (:45-46) are proved **`:= rfl`**, which only typechecks if the
  equation compiler produced `Nat.rec`-style equations that reduce by iota — a `WellFounded.fix`
  definition does not give `rfl` for its unfolding lemma. So no `Acc.rec` is involved, and the kernel's
  well-founded-recursion machinery is never exercised. The *successor* itself
  (`Stage.successor`, :21-25) is a two-case `cases n` dispatch into `forwardNext` (the `0 → 1` step) and
  `joinedNext` (all later steps); it is a `def` by tactics, so it elaborates to `Nat.casesOn`, again one
  iota step on a symbolic argument.
* **Is summability/convergence proved rather than assumed?** Proved, in two independent places.
  1. The `Scales` record's six series fields are `SmallSeries`, and `SmallSeries`
     (`PacketSourceScaleChoice.lean:121-124`) is
     `nonneg : ∀ n, 0 ≤ f n`, `summable : Summable f`, `total_le : (∑' n, f n) ≤ δ`. This is a **genuine**
     absolute-convergence statement with a total-mass bound; the `Summable` field closes the
     `tsum = 0`-junk loophole that a bare `(∑' n, f n) ≤ δ` would leave open. `term_le` (:126) is the
     *derived* pointwise corollary, not the definition. My sub-worker `packet-series` traced the actual
     decay to `scaleSequence J X (n+1) = ((J+n:ℕ):ℝ)^2 * scaleSequence J X n`
     (`PacketSourceScaleChoice.lean:226-228`) → ratio test → an explicit geometric majorant `r·rⁿ` with
     `r < 1` and `tsum ≤ r/(1-r)`, uniform over the finite `Fintype` of cost specs. So the decay is
     **derived from the explicit scale sequence**, not posited.
  2. The initial-datum limit is a series of smooth L² fields that is absolutely summable **in every**
     Sobolev order: `actual_increment_summable` (`PacketInitialSmoothLimit.lean:48-53`),
     `initialLimit := sumField … ` (:63-65) where `sumField` (`SmoothL2Series.lean:101`) is built from
     `limitData` (:98-100), which needs (a) a *uniform* jet bound `∀ n q, tensorNorm q (partialSum A n) ≤
     ∑' i, tensorNorm q (A i)` (:87-90) and (b) `CauchySeq` of the partial sums in L² (:92-96). The
     smoothness of the limit is therefore obtained from completeness plus uniform jet control — the
     honest route — and `sumField_derivativeSum_tendsto` (:119-127) is what `initialDataLimit_Hm`
     consumes.

## C. Choice on a subclass? limit interchange? junk value? — concrete answers

| risk | present? | evidence |
|---|---|---|
| `Classical.choice`/`choose` of a statement proved only for a subclass | **No** | The only choice in the construction is `PacketInfiniteConstruction.lean:69` on `exists_scales (requiredExponent:ℝ) (commonThreshold …) (Nat.cast_nonneg _)`, and `exists_scales` (`PacketInductionScales.lean:123`) is stated for **all** `c B` with `0 ≤ c`; the instantiation is exactly the pair the consumers need, and `packets` (:72) passes `le_rfl le_rfl` for `hq`/`hB`. Downstream choices are `Exists.choose` on statements proved for *this* datum: `lifespan := initialDatum_finite_lifespan.choose` (`PacketFiniteLifespan.lean:54`), `FiniteLifespan.evolution := (L.shorter S hS hST).choose_spec.choose` (`OrdinaryEulerLifespan.lean:60-61`). |
| limit interchange (sum ↔ limit, no uniform control) | **No** | Every `tsum` step is `Summable`-guarded (`SmallSeries.summable`; `Summable.sum_le_tsum` at `SmoothL2Series.lean:88-90`; `hs.tsum_le_tsum` at `PacketSourceScaleChoice.lean:137`). The H^s convergence of the datum is `sumField_derivativeSum_tendsto` (`SmoothL2Series.lean:119`) which is a *finite* sum over `range (q+1)` of jet-wise limits (`tendsto_finsetSum`, :115) — a finite interchange only. The one index manipulation in the scope files is `tendsto_add_atTop_iff_nat 1` (`PacketStageInitialLimit.lean:96`), a shift, not an interchange. |
| junk value | **No exploitation found; two junk sites are load-bearing in the *safe* direction** | (i) `activationGradient := ‖fderiv ℝ (fun x => …velocity (P.time,x)) 0‖` (`PacketStageGrowth.lean:49`). `fderiv` is `0` off differentiability, so the junk value would make the *claimed divergence* **harder**, not easier: `gradient_lower` (:52) must produce a genuine positive lower bound `previousShear/2`, which it does via `strain_origin` and the frame decomposition. Direction of the junk is against the claimant. (ii) `sSup {T | HasEulerEvolution A T}` (`OrdinaryEulerLifespan.lean:46`): `sSup` of an unbounded or empty set is junk `0` in Mathlib, and both are excluded *on the spot* — `hne` from local existence (:39) and `hbdd` from `hfail` (:41). (iii) `Nat`-subtraction sites in the cost algebra are guarded by `3 ≤ J`, `d ≤ 2` (reported by sub-worker `packet-series`). |
| circularity | **No** | The hypothetical evolution `U` is the *source* of the continuous comparison trajectory in `no_escape_near_compact_trajectory` (`OrdinaryEulerVaryingHorizon.lean:72-78`); the packets are the source of divergence. Neither side assumes the other's conclusion. |

## D. Is `Tstar` provably `> 0` and `≤ 1`, and is the bound arithmetic or analysis?

`Tstar` is **analysis, not arithmetic**. Chain (verified by sub-worker `packet-horizon`, hop by hop):

1. `Euler/Solution.lean:44` (headline `exists_compact_smooth_euler_singularity`) instantiates
   `Tstar := lifespan.duration` (:57), `0 < Tstar := lifespan.duration_pos` (:59).
2. `lifespan := initialDatum_finite_lifespan.choose` (`PacketFiniteLifespan.lean:54`), whose type
   `FiniteLifespan initialDatum` carries `duration_pos : 0 < duration`,
   `shorter : ∀ S ∈ (0,duration), HasEulerEvolution A S`, `maximal : ∀ S > duration, ¬ …`
   (`OrdinaryEulerLifespan.lean:29-33`).
3. `exists_finite_lifespan` (`OrdinaryEulerLifespan.lean:35-54`) sets
   `duration := sSup {T | HasEulerEvolution A T}`, gets `BddAbove` from `initialDatum_no_base`
   (the theorem of part A) and positivity from `initialDatum_local`
   (`PacketFiniteLifespan.lean:27` ← `Stage.exists_local_evolution`,
   `PacketStageLocalExistence.lean:39-41`, which proves existence on `[0,L]` with
   `0 < L ≤ baseHorizon/12` by taking an H³-Cauchy limit of the stage evolutions restricted to the
   common interval).
4. `Tstar ≤ baseHorizon constructionScales.J constructionScales.X` is `lifespan_le_base`
   (`PacketFiniteLifespan.lean:56`, `= initialDatum_finite_lifespan.choose_spec`), and
   `baseHorizon J X ≤ 1` is the `Scales` **field** `time_small` (`PacketInductionScales.lean:110`),
   discharged inside `exists_scales` at :154/:167 by `filter_upwards` on `eventually_base_guards`
   (`Euler/PacketBaseGuardScales.lean`), whose engine is `baseHorizon_tendsto_zero` (:42) →
   `tendsto_rpow_neg_atTop (0 < 1000)` (:48). `baseHorizon J X = 6*(J:ℝ)^2*X^(-498:ℝ)` (:14) is a **real
   rpow**; the "`≤ 1`" is `X → ∞` asymptotics, and the kernel is never asked to evaluate it.
5. Therefore `baseHorizon/12 ≤ Tstar ≤ baseHorizon ≤ 1` and `Tstar > 0`. **`Tstar = 0` is impossible**:
   `0 < baseHorizon` is used as an explicit argument (`PacketFiniteLifespan.lean:51`) and rests on
   `J ≥ 3`, `X ≥ 8` — `Scales` fields (:88, :90) exposed as `j_one`/`x_pos`
   (`PacketInductionScaleBounds.lean:19-21`). So the singularity time is genuinely interior, and the
   statement is not the degenerate "blowup at time 0".

**Vector-2 answer for `Tstar`: nothing.** No `decide`, no `Nat.pow`, no numeral evaluation carries the
bound; the large literals (498, 1000, 2000, 48000, 10⁶) are exponents/coefficients on **real** bases
(`rpow`/`npow` of a *variable* `X`) or arguments to `omega`/`norm_num`/`positivity` certificates on
≤4-digit rationals.

## Per-declaration findings

`Euler/PacketInfiniteConstruction.lean` — all 12 declarations, read line by line.

| decl | line | statement (my words) | proof mechanism | verdict |
|---|---|---|---|---|
| `Stage.successor` | 21 | from a stage at `n`, build a stage at `n+1` | tactic `cases n`: `forwardNext` for `0`, `joinedNext` for `n+1` (one `Nat.casesOn`, symbolic) | OK |
| `Stage.successor_time` | 27 | the successor's time is the parent's `nextTime` | same case split, two named lemmas | OK |
| `stages` | 39 | the infinite stage family | **structural** recursion on `ℕ`, dependent motive; no `termination_by` | OK (see kernel section) |
| `stages_zero` | 43 | `stages 0 = S.firstStage` | `rfl` — 1 iota step | OK |
| `stages_succ` | 45 | `stages (n+1) = (stages n).successor …` | `rfl` — 1 iota step; also *evidence* the recursion is not well-founded-compiled | OK |
| `stages_time` | 48 | time of stage `n+1` is `nextTime` of stage `n` | applies `successor_time` | OK |
| `stages_initial_step` | 52 | the `hstep` increment identity for `n ≠ 0` | `cases n`; `zero` is `(hn rfl).elim`; `succ` is `joinedNext_initial_velocity` | OK |
| `stages_gradient_atTop` | 61 | stage gradients → ∞ | `Stage.gradient_atTop (stages …)` | OK |
| `ConstructionScales` | 65 | `Scales` at the required exponent/threshold | `abbrev` | OK |
| `constructionScales` | 68 | *the* scale record | `Classical.choice` of a **proved** `Nonempty` | OK (see B) |
| `packets` | 72 | the packet family at those scales | `stages constructionScales le_rfl le_rfl` | OK |
| `packets_gradient_atTop` | 74 | packet gradients → ∞ | `Stage.gradient_atTop packets` | OK |

`Euler/PacketStageInitialLimit.lean` — all 11 declarations, read line by line.

| decl | line | statement (my words) | proof mechanism | verdict |
|---|---|---|---|---|
| `initialTailInput` | 24 | the joined input of stage `1+i` | `(P (1+i)).joinedInput` | OK |
| `initialTail_parameter` | 32 | its parameter size respects the shifted envelope | `parameterEnvelope_shift` + a `Stage` guard | OK |
| `initialTail_scale` | 37 | its support scale is the shifted `supportScale` | `supportScale_shift` + guard | OK |
| `initialTail_sigma` | 41 | tilt bound `σ·x_i ≤ 2` | `scaleSequence_shift` + guard | OK |
| `initialTail_four` | 45 | `4 ≤ frequency` | `frequency_shift` + `S.normal_frequency` | OK |
| `initialTail_frequency` | 49 | frequency guard holds | `frequency_shift` + guard | OK |
| `initialBase` | 53 | stage 1's initial velocity as a smooth L² field | projection | OK |
| `initialDataLimit` | 55 | the limit datum | `EulerPacketInitial.fullInitialLimit` applied to the five tail guards; the `320/20/1000` are envelope *parameters*, `(by norm_num)` proves `(0:ℝ) < 320`-style side goals | OK |
| `initial_velocity_partial` | 69 | stage `1+N` initial velocity `= initialBase + initialPartial N` | induction on `N`; `succ` uses `hstep` and `sum_range_succ`; `zero` uses `velocity_match` | OK |
| `initialDataLimit_Hm` | 84 | stage data → limit in every H^s | `fullInitialLimit_Hm` + the identity above + `tendsto_add_atTop_iff_nat 1` | OK |
| `initialDataLimit_no_euler` | 106 | no Euler evolution on `[0,baseHorizon]` with this datum | `no_euler_evolution_of_initial_H3` + the `s=3` case above | OK (content in `PacketStageContradiction`) |

`Euler/PacketStageContradiction.lean` (2), `Euler/OrdinaryEulerVaryingHorizon.lean` (5),
`Euler/PacketFiniteLifespan.lean` (9), `Euler/PacketInductionScales.lean` (16),
`Euler/PacketInitialSmoothLimit.lean` (13), `Euler/SmoothL2Series.lean` (23) — all read; the
load-bearing ones are dissected in sections A/B/C/D above. Summary verdicts:

| decl | line | one-line reason | verdict |
|---|---|---|---|
| `Stage.false_of_evolution` | `PacketStageContradiction.lean:25` | divergence (`gradient_atTop`) vs. no-escape (`no_gradient_escape_of_initial_tendsto_varying`); both proved | OK |
| `Stage.no_euler_evolution_of_initial_H3` | `:67` | `rintro` + the above | OK |
| `Evolution.no_gradient_escape_varying` | `OrdinaryEulerVaryingHorizon.lean:61` | H³ stability (with an explicit smallness side condition) + Sobolev embedding + compact-trajectory no-escape | OK |
| `Evolution.no_gradient_escape_of_initial_tendsto_varying` | `:96` | supplies `ε n := ‖·‖ + 1/(n+1) > 0` to the above | OK |
| `Evolution.eventually_h3_bound_varying` | `:28` | `h3_stability` under `640·ε·exp(3·C·T) ≤ 1/2`, eventually true since `ε → 0` | OK |
| `Evolution.sampled_h3_tendsto_zero_varying` | `:50` | `squeeze_zero'` | OK |
| `Evolution.restricted_exponential_le` | `:21` | monotonicity of `exp` | OK |
| `initialDatum` / `initialDatum_Hm` | `PacketFiniteLifespan.lean:18,20` | the limit datum for `packets`, and its H^s convergence | OK |
| `initialDatum_local` | `:27` | `Stage.exists_local_evolution` (H³-Cauchy limit of stage evolutions on `[0,baseHorizon/12]`) | OK |
| `initialDatum_no_base` | `:31` | `Stage.initialDataLimit_no_euler` | OK |
| `initialDatum_solenoidal` / `_divergence` | `:38,42` | from the local evolution's `solenoidal` field | OK |
| `initialDatum_finite_lifespan` | `:46` | `exists_finite_lifespan` with `B := baseHorizon`, `hB := baseHorizon_pos` | OK |
| `lifespan` / `lifespan_le_base` | `:54,56` | `.choose` / `.choose_spec` | OK |
| `exists_finite_lifespan` | `OrdinaryEulerLifespan.lean:35` | `sSup` of the evolution-time set; `Nonempty` + `BddAbove` both supplied | OK |
| `exists_scales` | `PacketInductionScales.lean:123` | see B; 7-fold `filter_upwards` + `.exists` | OK |
| `Scales` (structure) | `:83` | numbers, inequalities and 6 `SmallSeries`; **no packet/frame/evolution field** | OK |
| `Scales.initial_series` / `.pressure_series` | `:199,205` | `add_series` of two `SmallSeries` | OK |
| `Scales.stage` | `:211` | packages the numeric guards into `StageGuards` | OK (`StageGuards` internals not read — see Residue) |
| `correctionCostSpec` / `correctionCost_eq` | `:45,62` | cost spec with `b := 1/4`; the cost equals `frequency^(-1/4)` | OK |
| `activationMargin` / `_pos` / `_small` / `_le_half` | `:29,32,36`, `PacketStageGrowth.lean:12` | `1/(32(A+1))` and its three elementary bounds by `positivity`/`field_simp`/`div_le_iff₀` | OK |
| `actual_increment_summable` | `PacketInitialSmoothLimit.lean:48` | `Summable` of the H^s norms of the increments, from `high` + `mean` summability | OK |
| `initialLimit` / `fullInitialLimit` | `:63,84` | `sumField` of that absolutely summable series, plus the stage-1 base | OK |
| `initialLimit_Hm` / `fullInitialLimit_Hm` | `:69,86` | `sumField_derivativeSum_tendsto` | OK |
| `initialLimit_support` / `_compact` | `:75,80` | pointwise limit + closed superset ⇒ `tsupport ⊆ closedBall 0 2`, compact | OK |
| `sumField` / `limitData` | `SmoothL2Series.lean:101,98` | smooth limit from uniform jet bounds + L² Cauchy | OK |
| `sumField_derivativeSum_tendsto` | `:119` | finite sum over `range (q+1)` of jet-wise limits | OK |
| `sumField_support` | `:146` | by contradiction from `sumField_pointwise_tendsto` | OK |
| `partialSum*` (`_field`,`_jet`,`_value`,`_norm`) | `:39-66` | inductions on `n`, `sum_range_succ` | OK |
| `Stage.activationGradient` | `PacketStageGrowth.lean:49` | `‖fderiv …‖` at the origin (junk-`0` off differentiability, safe direction) | OK |
| `Stage.gradient_lower` | `:52` | reverse triangle inequality on the frame decomposition + the `activationMargin` budget | OK |
| `Stage.gradient_atTop` | `:83` | `previousShear_ge_index` + `gradient_lower`, `tendsto_atTop.2` | OK |
| `Scales.previousShear_ge_index` | `:25` | induction on `n` using `shear_separation` (`previousShear² ≤ shear/4`) | OK |
| `Scales.shear_separation` | `PacketInductionScaleBounds.lean:61` | from `actual.normal.parent.term_le` + `δ ≤ 1/16` | OK |
| `SmallSeries` | `PacketSourceScaleChoice.lean:121` | `nonneg` + **`Summable`** + `tsum ≤ δ` — a real convergence statement | OK |
| `scaleSequence` | `:226` | `x(0)=X`, `x(n+1)=((J+n:ℕ):ℝ)²·x(n)`; `_succ` by `rfl` | OK |
| `previousShear`/`previousFrequency`/`olderShear` | `PacketSourceScaleSequence.lean:30,34,38` | structural 2-case recursions; `X^1000`, `X^D` on a **variable** real base | OK |
| `baseHorizon` | `PacketBaseGuardScales.lean:14` | `6·J²·X^(-498)`, real rpow | OK |

**Counts over what I examined myself: OK 63, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0.**
Sub-workers add: `packet-contradiction` OK 14 / UNCLEAR 1 / KR 0 / SUSP 0;
`packet-horizon` (chain of 10 files) 0 KR / 0 SUSP; `packet-series` OK 62 / UNCLEAR 4 /
KERNEL-RISK 2 (both low: the `rfl` unfolding of `stages` and of `scaleSequence`) / SUSP 0.

## E. Kernel-risk assessment (vectors 1, 2, 3)

Measured by regex over the 16 files of my scope (raw source, comments included, so the counts are
upper bounds), plus the three sub-workers' independent passes over their own file sets.

| token | hits in my scope | where / how big |
|---|---|---|
| `decide` | **3** | `PacketBaseGuardScales.lean:58,59` (`(by decide : 2 ≠ 0)`, `(by decide : 3 ≠ 0)`), `PacketInductionStage.lean:72` (`(by decide : 2 ≠ 0)`). Kernel work: one `Nat.beq`/`Decidable` reduction on a 1-digit literal each. |
| `native_decide` | 0 | — |
| `set_option`, `macro`, `elab`, `syntax`, `axiom`, `sorry`, `unsafe`, `partial` | 0 | — (consistent with the repo-wide scan) |
| `local instance` | **1** | `SmoothL2Series.lean:17`: `private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩`. Benign: the `Fact` is *true* and proved; it only unblocks `Lp`-exponent instances. |
| `termination_by` / `decreasing_by` / `WellFounded` / `Acc.rec` | **0** | The packet recursion is structural (see below). |
| explicit `.rec` / `.brecOn` | 0 | Recursors appear only as the equation compiler's output. |
| `:= rfl` proofs | 5 | `stages_zero`/`stages_succ` (`PacketInfiniteConstruction.lean:43,46`), `increment_field` (`PacketInitialSmoothLimit.lean:23`), `scaleSequence_zero`/`_succ` (`PacketSourceScaleChoice.lean:229,232`), plus `heq` closed by `rfl` inside `false_of_evolution` (`PacketStageContradiction.lean:63`) and `firstStage_horizon`-style `rfl`s outside my scope. Each is **one** iota/delta step on symbolic arguments. |
| `norm_num` | 44 | all on ≤4-digit rationals (`(0:ℝ) < 320`, `1/16 ≤ 1/4`, `(2-1000/2:ℝ) = -498`). Kernel recomputes these certificates with `Nat` ops on small numerals. |
| numerals ≥ 1000 | 30 | `X^1000`, `X^(-1000:ℝ)`, `X^(-498:ℝ)`, `X^D` (`D ≥ 2000`), `48000 ≤ X`, `10⁶·geometryConstant·δ ≤ 1`. In **every** case the base is a *variable real*, so these are `Monoid.npow`/`Real.rpow` applications the kernel never evaluates; the only `ℕ` literals reaching a decision procedure are `2000 ≤ max 2000 d` (`omega`/`le_max_left`) and `2 ≠ 0`, `3 ≠ 0`. |

**Vector (1), recursors / well-founded recursion.** Does the kernel have to reduce a recursor to accept
these files? Yes, but only in the weakest possible form:
* `stages` (`PacketInfiniteConstruction.lean:39`) is structural recursion on `ℕ` into a **dependent**
  motive `Stage S n`. Its two unfolding lemmas are `rfl` (:43, :46), which is *exactly* the evidence that
  no `WellFounded.fix`/`Acc.rec` is in play — a well-founded definition's unfolding lemma is not `rfl`.
  So the kernel performs **one** iota step per use, on a symbolic `n+1`, never a chain at a closed
  numeral. There is no `Stage` *literal* anywhere in the chain, hence no unfolding of `stages 17`.
* `Stage` (`PacketInductionStage.lean:23`) is a **structure** (28 fields), parameterised — not indexed —
  by `n`; there is no recursive occurrence, so no nested/indexed-family recursor and no large
  elimination. `partialSum` (`SmoothL2Series.lean:39`), `scaleSequence`, `previousShear`,
  `previousFrequency`, `olderShear` are all 2-case structural recursions on `ℕ`, used only through their
  `rfl`/`simp` equations.
* Conclusion for vector (1): **no kernel-risk item found in this scope.** The one honest caveat is the
  same one worker `jet-inductives` raised: without a build I cannot see the *elaborated* definition, so
  "structural" rests on the `rfl` evidence, not on inspecting `stages.eq_def`.

**Vector (2), GMP `Nat` arithmetic.** The kernel is asked to evaluate essentially nothing: three
`decide`s on 1-digit `Nat` disequalities and ~44 small `norm_num` certificates. Every large constant in
the finiteness argument lives on the **real** side (`rpow`/`npow` of a variable). In particular the
load-bearing bound `baseHorizon J X ≤ 1` is real-analytic (`tendsto_rpow_neg_atTop`), **not** a numeral
computation. **No kernel-risk item.**

**Vector (3), metaprogramming.** None in the packet construction. Two attribute/instance sites are worth
recording because the repo-wide scan reported "zero": `SmoothL2Series.lean:17`
`private local instance : Fact (0 < (1:ℝ))` (harmless), and — found by sub-worker `packet-horizon`,
outside my files but *on the headline path* — `Euler/Solution.lean:41`
`attribute [local instance] CompletePartialOrder.toSupSet`, which changes how the `sSup`s in the
**headline statement** elaborate. That is a statement-fidelity question, not a kernel question, and it is
escalation **P1** below.

### Cone status of every theorem I audited — and a defect in our own instrument

Looking up my declarations in `audits/nse-deep/CONE.csv` produced an alarming pattern: the *entire
finiteness chain* is marked `in_cone=False`, including `initialDataLimit_no_euler`
(`PacketStageInitialLimit.lean:106`), `false_of_evolution` (`PacketStageContradiction.lean:25`),
`initialDatum_no_base` and `initialDatum_finite_lifespan` and `lifespan_le_base`
(`PacketFiniteLifespan.lean:31,46,56`), `gradient_lower`, `gradient_atTop`, `previousShear_ge_index`
(`PacketStageGrowth.lean:52,83,25`), and `Scales.initial_series`/`pressure_series`
(`PacketInductionScales.lean:199,205`) — while `lifespan` itself (`:54`) is `in_cone=True`.

That combination is impossible for a real dependency graph (`lifespan := initialDatum_finite_lifespan.choose`
*is* the reference), so I diagnosed `audits/cone.py`. Its reference resolver
(`cone.py`, the `for t in set(IDENT.findall(body))` loop) resolves a token only **exactly** or by
**suffix**. Dot-notation therefore breaks it in two ways:

1. **trailing projection** — `initialDatum_finite_lifespan.choose` (`PacketFiniteLifespan.lean:54`),
   `hT.choose`, `(…).choose_spec`: the whole dotted token matches no declaration, and no *suffix* of it
   does either, so the edge is dropped;
2. **leading local receiver** (generalized field notation, the dominant style in this repo) —
   `S.previousShear_ge_index n` (`PacketStageGrowth.lean:91`), `P.gradient_lower hn0` (:90),
   `(P n).horizon_le`: here the *head* is a local variable, so again nothing resolves.

I measured the size of the blind spot, on the same 4 seeds, without touching `audits/cone.py`
(probe copies live in `audits/nse-deep/workers/_probe/`):

| resolver | declarations in cone | theorems in cone | gained vs. baseline | lost |
|---|---|---|---|---|
| current `cone.py` (baseline) | 28,145 / 52,516 | 19,214 | — | — |
| + strip **trailing** components | 28,386 | 19,401 | **+241** | 0 |
| + strip trailing **and** leading components | **37,149** | **26,684** | **+9,004** | 0 |

The trailing-only fix already recovers 7 of the 8 finiteness declarations listed above; the
both-direction resolver recovers all 8 (`previousShear_ge_index` needs the leading-receiver rule).
Since a cone is only safe when it **over**-approximates, this is a strict improvement: zero
declarations left the cone in either variant.

*Practical consequence for the audit's headline number:* the published denominator ("22,643 in-cone
theorems", `FINDINGS.md`) comes from the pre-import-cut CONE.csv; with the import cut it is 19,214, and
with dot-notation resolution repaired it is **26,684**. Any statement of the form "N of M in-cone
theorems read" should be recomputed, and — more importantly — **`in_cone=False` must not be used to
deprioritise a declaration reached through `.choose` or through `X.foo` field notation.** The finiteness
spine of the Euler claim is precisely such a cluster, and it was very nearly triaged away.

## Escalations (ranked)

**P1 — statement fidelity at the headline, `Euler/Solution.lean:41-56`** (found by sub-worker
`packet-horizon`). Line 41 is `attribute [local instance] CompletePartialOrder.toSupSet`, and the
theorem statement at :43-56 (which diffs verbatim against `ComparatorChallenges/Euler.lean:170-183`)
contains `sSup`/lattice notation. *Question for an expert:* with that local instance in scope, does
every `sSup`/order-theoretic operation in the headline statement elaborate to the **same** term as in
the Comparator's challenge file, where the instance is absent? *What would settle it:* elaborate both
statements and compare (`#print axioms` is not enough; `set_option pp.all true` on both, or
`example : (Euler.exists_compact_smooth_euler_singularity_statement) = (challenge_statement) := rfl`).
This is the only place in the chain where a *statement* could differ from what a reader thinks it says.

**P2 — is `EulerOrdinarySobolev.Evolution` a *stronger* notion than "smooth Euler solution"?** (found by
sub-worker `packet-contradiction`). `false_of_evolution` refutes the existence of an `Evolution` on
`[0,baseHorizon]`; the strength of the headline depends on that class not being artificially narrow.
Concretely, `referenceSize` is a supremum of `tensorNorm 4` over the whole closed horizon
(`OrdinaryEulerStability.lean:17-33`) and is finite only because `Evolution` carries
`velocity_continuous` at **every** jet order (`OrdinaryEulerDifference.lean:21-32`). *Question:* does
every classical smooth-in-space, `C¹`-in-time Euler solution with compactly supported smooth data
satisfy all the `Evolution` fields — in particular the all-order jet continuity — or does the class
exclude solutions that the mathematical claim should cover? *What would settle it:* a lemma in the repo
(or a referee's argument) constructing an `Evolution` from the standard local well-posedness statement;
if that lemma does not exist, the theorem should be read as "no *Evolution-class* solution", which is
weaker than "no Euler solution".

**P3 — `audits/cone.py` under-approximation (our instrument, fix measured above).** *Question:* accept
the both-direction resolver (or at least the trailing-strip rule) and regenerate `CONE.csv`?
*What would settle it:* the numbers in the table above are reproducible with
`audits/nse-deep/workers/_probe/cone_{base,tail,both}.py` on the same 4 seeds; the correctness argument
is that dot-notation tokens are references and dropping them is unsound *for a cone*, while
over-approximation is safe by design. Until then, every prior worker's "out of cone, skipped" note
should be re-checked for `.choose`/field-notation reachability.

**P4 — the 28 `Stage` fields must be *discharged* by the two successor constructions** (both sub-workers
converge on this). Everything I verified is conditional on `∀ n, Stage S n` being inhabited: the
divergence uses `Stage`/`ParentFrame`/`Scales` fields, and the finiteness uses `horizon_le`. The
inhabitation lives in `S.firstStage` (`BaseInductionStage.lean:22`, and `firstStage_horizon` :98),
`Stage.forwardNext` (`PacketForwardSuccessor.lean`) and `Stage.joinedNext`
(`PacketJoinedSuccessor.lean`) — **none of which any worker has read**. *Question:* does `joinedNext`
really produce `compression`, `frame_error ≤ priorError`, `tilt_lower/upper`, and the three cumulative
`∑ i ∈ range n` bounds at `n+1` *without* re-assuming a bound at `n+1`? *What would settle it:* read
those two files declaration by declaration; they are the last unaudited load-bearing block of the Euler
half.

**P5 — `EulerProof.lean:20603/20644` state `(∑' n, f n) ≤ δ` with no `Summable`** (found by
`packet-series`). In isolation such a lemma is junk-vulnerable (`tsum = 0` when not summable); in the
chain the callers repair it because `SmallSeries` carries `Summable`. *Question:* is there any consumer
of those two lemmas that does **not** also have summability in hand? *What would settle it:* grep the
consumers and check each.

**P6 — no *effective* lower bound on `Tstar`.** `X` comes from `Eventually.exists`
(`PacketInductionScales.lean:172`), so `baseHorizon constructionScales.J constructionScales.X` is a
non-explicit positive real and `Tstar ∈ [baseHorizon/12, baseHorizon]` is non-effective. Sound, but any
claim of the form "blowup before time 1 with an explicit datum" should note that the datum and the time
are non-constructive (`Classical.choice` at `PacketInfiniteConstruction.lean:69`).

## Residue — what I could not check

1. **No build.** Everything is source reading; I cannot see elaborated terms, so "structural recursion",
   "one iota step", and "no `Acc.rec`" rest on syntactic evidence (`rfl` unfolding lemmas, absence of
   `termination_by`) rather than on `set_option diagnostics true` output. Same caveat as `jet-inductives`.
2. **`Stage` inhabitation** (`firstStage`, `forwardNext`, `joinedNext`) — escalation P4. This is the
   largest unread load-bearing block; my "OK" verdicts are conditional on it.
3. **`StageGuards`' 13 fields** and the `ActualBounds`/`FirstScaleGuards`/`UniversalFrequency` record
   internals: I read where they are supplied in `exists_scales`, not what each field demands.
4. **`h3_stability`** (`OrdinaryH3Envelope.lean:119`) and `no_escape_near_compact_trajectory`
   (`EulerProof.lean:12522`) were read by sub-worker `packet-contradiction` at statement level plus proof
   skeleton, not line by line.
5. **The `high`/`mean` field constructions** behind `EulerPacketInitial.Input` (`actual_high_summable`,
   `actual_mean_summable` in `PacketInitialSummability.lean`): I verified that summability is *required*
   and *used*, not the estimates that produce it.
6. I did not audit the Navier–Stokes half at all, and I did not re-verify the two prior Euler-spine
   reports; I only closed the two items they left open.
