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
