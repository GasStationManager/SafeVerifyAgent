# Worker report: one-sided C^inf (Whitney-type) ENDPOINT EXTENSION + past extension

Target: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5). READ-ONLY; nothing
under that path was modified. No `lake build` / `lake env` was run (no built Mathlib on this box).
Mathlib *source* signatures quoted below were read from an unrelated local checkout
`/home/gsm/.openclaw/workspace/repos/PartitionPowerGap/lean/.lake/packages/mathlib` (toolchain **v4.29.0**),
while NSE pins **v4.34.0-rc2** (`NSE/lean-toolchain`). Version caveat recorded in ## Residue.

## Scope

Read **line by line, in full**:

| file | lines | decl count (theorem/def/abbrev) | read |
|---|---|---|---|
| `NavierStokes/SpacetimeEndpoint.lean` | 390 | **30** (24 theorem, 4 def, 2 abbrev) | all 30 line-by-line |
| `NavierStokes/PastExtension.lean` | 338 | **43** (39 theorem, 3 def, 1 abbrev) | all 43 line-by-line |

Total in scope: **73 declarations, all read line-by-line** (statement *and* proof term/tactic block).

Skimmed for context only (quoted with file:line, not audited):
`NavierStokes/CandidateFromLimits.lean:20-75`; `NavierStokes/TimeLocalization.lean:27-31,59-63,74-80,133-138`;
`NavierStokes/SmoothCutoffs.lean:246-302`; `NavierStokes/ProblemStatement.lean:42-45,126-130`;
`NavierStokes/PeriodicUniqueness.lean:43-46`; `NavierStokes/JointResidualLimits.lean:130-165,285-325`;
`audits/nse-deep/CONE.csv`. Mathlib sources read: `Analysis/Calculus/FDeriv/Extend.lean:36-88`,
`Topology/UniformSpace/UniformApproximation.lean:120-160`,
`Topology/UniformSpace/LocallyUniformConvergence.lean:56-57`,
`Analysis/Calculus/ContDiff/FTaylorSeries.lean:133-139,557-560,634-640,856-860`,
`Analysis/Calculus/ContDiff/Defs.lean:458-463,858-866`, `Analysis/Calculus/TangentCone/Real.lean:91-92`,
`Analysis/Calculus/TangentCone/Prod.lean:63-65`, `Topology/Order/DenselyOrdered.lean:214`.

**Headline verdict.** The two central theorems are, as far as source reading can determine, a
**genuine** one-sided Whitney/Taylor endpoint extension result. They are *not* the junk-value trick.
The real one-sided differentiability at `t = T` is done by a genuine Mathlib mean-value theorem
(`hasFDerivWithinAt_closure_of_tendsto_fderiv`), the locally-uniform hypothesis is genuinely needed and
genuinely used, and `boundary_jets_eq_limits` really does hold for **all** `n`, not just `n = 0`.
The weight of the claim sits **entirely** in the hypothesis `hlim` (locally uniform convergence of
*every* derivative order as `t -> 1^-`), which in these two files is **assumed, never proved**
(`CandidateFromLimits.lean:39-41` keeps it as a `variable`), and in the one-sidedness of the conclusion
(nothing here gives smoothness for `t > 1`). Kernel risk in both files is essentially **nil**.

---

## Answers to the mandated questions

### (a) `extendTrace` verbatim; are the higher boundary jets patched?

`SpacetimeEndpoint.lean:40-42` (verbatim):

```lean
/-- Extend by the boundary trace. Only closed-past smoothness is claimed. -/
def extendTrace {V : Type*} (T : ℝ) (f : SpaceTime → V) (L : Space → V)
    (z : SpaceTime) : V := if z.1 < T then f z else L z.2
```

So **yes**: it is exactly `if z.1 < T then f z else L z.2` — a discontinuous patch in general, rescued
only by the limit hypothesis. Note it also overwrites *all* of `t > T` with the trace `L z.2`
(constant in time), which is harmless because every conclusion is restricted to `closedPast T`
(`:26`, `Iic T ×ˢ univ`). `extendTrace_at` (`:48-50`, `@[simp]`) fixes the boundary value `= L x`.

Higher jets: correct, the call site (`CandidateFromLimits.lean:28-31`) supplies only the 0th jet
`fun x => (L x 0).curry0`. The higher jets come out right because a **second, separate** family is
patched jet-by-jet:

```lean
def extendJets (T) (J) (L) (z) : FormalMultilinearSeries ℝ SpaceTime V :=
  fun n => extendTrace T (fun y => J y n) (fun x => L x n) z          -- :175-178
```

and `hasFTaylorSeriesUpToOn_extension` (`:228-246`) proves that this family is an *actual*
`HasFTaylorSeriesUpToOn ∞ (extendTrace T f (fun x => (L x 0).curry0)) (extendJets T J L) (closedPast T)`.
All three structure fields of Mathlib's `HasFTaylorSeriesUpToOn`
(`FTaylorSeries.lean:133-139`: `zero_eq`, `fderivWithin` for all `m < n`, `cont` for all `m <= n`)
are supplied, and the `fderivWithin` field is supplied **at every point of `closedPast T`, boundary
included** (`:242-243` -> `extendedJets_hasFDerivWithinAt` `:198-224`). Then
`iteratedFDerivWithin_extension` (`:262-275`) converts it with
`HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`
(`FTaylorSeries.lean:634-636`, needs `m <= n` and `UniqueDiffOn`) and
`boundary_jets_eq_limits` (`:277-288`) specialises to `z = (T, x)`.

**`boundary_jets_eq_limits` is proved for ALL `n`**: `(n : ℕ)` is a universally quantified argument
(`:284`), the proof is `rw [iteratedFDerivWithin_extension ... n (T, x) ⟨le_refl T, mem_univ x⟩]` then
`exact extendTrace_at T _ _ x` (`:287-288`). Nothing restricts to `n = 0`. Verdict **OK** — this is the
honest answer, and I checked it specifically because "only the 0th jet is patched" looks like a gap and
is not one.

### (b) Exact hypotheses of `contDiffOn_joint_extension` (`:250-260`); is the boundary real?

```lean
theorem contDiffOn_joint_extension {T : ℝ} {f : SpaceTime → V}
    {J : SpaceTime → FormalMultilinearSeries ℝ SpaceTime V}
    {L : Space → FormalMultilinearSeries ℝ SpaceTime V}
    (hzero : ∀ z : SpaceTime, z.1 < T → (J z 0).curry0 = f z)
    (hderiv : ∀ n : ℕ, ∀ z : SpaceTime, z.1 < T →
      HasFDerivAt (fun y => J y n) (J z (n + 1)).curryLeft z)
    (hlim : ∀ n : ℕ, TendstoLocallyUniformly (fun t x => J (t, x) n)
      (fun x => L x n) (𝓝[<] T)) :
    ContDiffOn ℝ ∞ (extendTrace T f (fun x => (L x 0).curry0)) (closedPast T) :=
  (hasFTaylorSeriesUpToOn_extension hzero hderiv hlim).contDiffOn
```

* Hypotheses are only about the **open** past `z.1 < T`: `J` is the true jet family of `f` there
  (`hzero` pins the 0th jet to `f`, `hderiv` pins `J (n+1)` as the actual Frechet derivative of `J n`),
  plus locally uniform convergence of each order at the boundary filter `𝓝[<] T`.
  **No hypothesis at `t = T`.** So the theorem is not trivially true.
* Conclusion is `ContDiffOn ℝ ∞ … (closedPast T)` with `closedPast T = Iic T ×ˢ univ` (`:26`), which
  **includes `t = T`**. `∞` here is `(⊤ : ℕ∞)` (via `open scoped ContDiff`), and
  `HasFTaylorSeriesUpToOn.contDiffOn` is stated for `{n : ℕ∞}` (`ContDiff/Defs.lean:458-459`), so no
  `ω`/analytic sleight of hand.
* **Differentiability AT the boundary is genuinely established.** The lemma that does the work is
  Mathlib's `hasFDerivWithinAt_closure_of_tendsto_fderiv`, applied at
  **`SpacetimeEndpoint.lean:171-172`** inside `hasFDerivWithinAt_extendTrace` (`:139-172`). Its Mathlib
  source (`Analysis/Calculus/FDeriv/Extend.lean:36-88`) is exactly the mean-value-inequality argument
  (`Convex.norm_image_sub_le_of_norm_fderivWithin_le'`), hypotheses
  `DifferentiableOn ℝ f s`, `Convex ℝ s`, `IsOpen s`, `∀ y ∈ closure s, ContinuousWithinAt f s y`,
  `Tendsto (fderiv ℝ f) (𝓝[s] x) (𝓝 f')`, conclusion `HasFDerivWithinAt f f' (closure s) x`.
  The NSE application is the term at **`:170-172`**
  (`simpa only [closure_openPast] using hasFDerivWithinAt_closure_of_tendsto_fderiv hd
  (openPast_convex T) (openPast_isOpen T) hc hdf`), with all five hypotheses supplied locally:
  `hd : DifferentiableOn ℝ (extendTrace T f L) (openPast T)` (`:154-156`),
  `openPast_convex` (`:31-32`), `openPast_isOpen` (`:28-29`),
  `hc : ∀ y ∈ closure (openPast T), ContinuousWithinAt …` (`:157-164`, boundary case by
  `extendTrace_continuousWithinAt_boundary`), and
  `hdf : Tendsto (fderiv ℝ (extendTrace T f L)) (𝓝[openPast T] (T,x)) (𝓝 (L' x))` (`:165-169`, which
  is where `hlim'` for the derivative order is spent), then `closure (openPast T) = closedPast T`
  (`:34-35`) is rewritten in. **Use is legitimate.**
* `UniqueDiffOn ℝ (closedPast T)` **is** supplied and **is** true: `closedPast_uniqueDiff` (`:37-38`)
  `= (uniqueDiffOn_Iic T).prod uniqueDiffOn_univ`; Mathlib `uniqueDiffOn_Iic`
  (`TangentCone/Real.lean:91-92`) is proved from `convex_Iic` + `interior_Iic = Iio` nonempty, and
  `UniqueDiffOn.prod` (`TangentCone/Prod.lean:63-65`) is the genuine product lemma (import at
  `SpacetimeEndpoint.lean:2`). It is used only where it should be: to make the jets *unique*
  (`:274-275`, `:322`). It is **not** used as a substitute for boundary differentiability.
* So the answer to "or does it only use that `closedPast T`-relative derivatives are junk-free" is:
  **no**. `HasFDerivWithinAt … (closedPast T) (T, x)` is a real one-sided derivative claim and it is
  proved by MVT, not by unique-diff bookkeeping.

Verdict: **OK**.

### (c) Is the hypothesis genuine locally uniform convergence, and is it genuinely needed/used?

* Genuine: `TendstoLocallyUniformly` is Mathlib's real definition
  (`LocallyUniformConvergence.lean:56-57`): `∀ u ∈ 𝓤 β, ∀ x, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t,
  (f y, F n y) ∈ u`. In NSE the index filter is `p = 𝓝[<] T` (time) and the uniformity is over a
  spatial neighbourhood of each `x`. So: for each spatial point, uniform closeness on a whole spatial
  neighbourhood, eventually as `t -> T^-`. Assumed for **every** order `n` (`:127-128`).
* Genuinely used, and pointwise would **not** suffice. The single place local uniformity is consumed is
  `joint_tendsto_at_boundary` (`:75-91`), which produces
  `Tendsto f (𝓝[openPast T] (T, x)) (𝓝 (L x))` — convergence along the **joint spacetime** filter, i.e.
  `y` is allowed to move with `t`. It is obtained from Mathlib
  `tendsto_comp_of_locally_uniform_limit` (`UniformApproximation.lean:155-160`), whose hypothesis
  `∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u` is *precisely* local uniformity
  (supplied verbatim at `:89-91`). Fixed-`x` pointwise convergence cannot give a limit along
  `𝓝[openPast T] (T,x)`; and that joint limit is exactly what
  `hasFDerivWithinAt_closure_of_tendsto_fderiv` needs (`h : Tendsto (fderiv …) (𝓝[s] x) …`, with
  `s = openPast T`, a 4-dimensional neighbourhood filter). It is also used, again unavoidably, for
  continuity of the trace `L` (`trace_continuous` `:64-71`, via `TendstoLocallyUniformly.continuous`,
  `UniformApproximation.lean:120-123`) which is a hypothesis of the MVT-based lemma (`f_cont`).
  **No step of either central proof uses only pointwise convergence.** I looked for it; there is no gap
  here.
* Non-vacuity of the filter: `𝓝[<] T` is `NeBot` by instance `nhdsLT_neBot`
  (`Topology/Order/DenselyOrdered.lean:214`), so `Filter.Eventually.frequently` at `:69` and
  `TendstoLocallyUniformly.continuous` are discharged legitimately, not by a bottom filter.

### (d) `PastExtension`: how the residual is continued to `t <= 0`; is the recurrence real; seams

* Continuation is a hard truncation: `zeroBefore g z = if 0 ≤ z.1 then g z else 0`
  (`PastExtension.lean:31-32`); `pastVelocity = zeroBefore (activatedVelocity u)` (`:112`),
  `pastPressure = zeroBefore (activatedPressure p)` (`:115`), and
  `pastResidual u p z = navierStokesResidual (pastVelocity u) (pastPressure p) z.1 z.2` (`:217-218`).
* **The `t = 0` seam is real and it IS proved smooth — trivially, because the field is identically zero
  near `t = 0`.** `activatedVelocity_zero_germ` (`:117-122`) / `activatedPressure_zero_germ`
  (`:124-129`) prove `activatedVelocity u =ᶠ[𝓝 (0,x)] 0` from
  `SmoothCutoffs.timeSwitch_eventually_zero` (`SmoothCutoffs.lean:267`), itself resting on
  `timeSwitch_zero_of_abs_le : |t| ≤ 3/8 → timeSwitch t = 0` (`SmoothCutoffs.lean:256`). So the glue is
  `0` glued to `0`. `zeroBefore_contDiffOn_past` (`:82-97`) then does a clean trichotomy
  `t<0 / t=0 / t>0`: locally constant `0`, locally constant `0` (germ), locally equal to the activated
  field (`smooth_at_interior hg ⟨hpos, hz.1⟩`, `ProblemStatement.lean:126-130`, legitimate because
  `preSingularDomain = Ico 0 1 ×ˢ univ`, `ProblemStatement.lean:42`, is a neighbourhood at `t ∈ Ioo 0 1`).
  Verdict **OK**, conditional on `SmoothCutoffs.timeSwitch_contDiff` (`SmoothCutoffs.lean:248`), which is
  another worker's scope.
* **`t = 3/8` is not a seam** and **`t = 3/4` is not a seam**: activation is a *smooth multiplication*
  `activatedVelocity u z = timeSwitch z.1 • u z` (`TimeLocalization.lean:27-28`), not a piecewise
  definition; `3/8` and `3/4` are only where the smooth cutoff is flat (`= 0` resp. `= 1`,
  `SmoothCutoffs.lean:256,262`). So there is exactly **one** gluing seam in this file (`t = 0`) plus the
  endpoint patch at `t = 1` handled by `extendTrace`.
* `pastResidual_derivative_recurrence` (`:299-312`) **genuinely proves a derivative statement**; it does
  not restate a hypothesis. Proof: `pastResidual_smooth … |>.contDiffAt` on the *open* set
  `openPast 1` (`:305-307`), then `ContDiffAt.iteratedFDeriv_right`
  (`ContDiff/Comp.lean:732-733`, with `1 + (n:ℕ∞) ≤ ⊤`) to get `ContDiffAt ℝ 1 (iteratedFDeriv ℝ n …)`,
  then `differentiableAt.hasFDerivAt` and `simp only [fderiv_iteratedFDeriv]`
  (`FTaylorSeries.lean:856-860`, a Mathlib `rfl`) to identify the derivative with
  `(iteratedFDeriv ℝ (n+1) …).curryLeft`. Verdict **OK**. (Note it uses ambient `iteratedFDeriv`, which
  is legitimate here only because `openPast 1` is open — `openPast_isOpen`, `:28`.)
* `pastResidual_locallyUniform_limit` (`:279-295`) is a **transfer** lemma, not an existence proof: it
  takes local uniform convergence of `iteratedFDeriv ℝ n` of the *true* residual
  `fun z => navierStokesResidual u p z.1 z.2` and returns the same for `pastResidual u p`. Mechanism:
  the two functions have equal germs for `t > 3/4` (`pastResidual_eventuallyEq_late` `:255-259`,
  `pastResidual_iteratedFDeriv_eq_late` `:267-275`, via
  `Filter.EventuallyEq.iteratedFDerivWithin_eq` `FTaylorSeries.lean:557-558` + `iteratedFDerivWithin_univ`)
  and `∀ᶠ t in 𝓝[<] 1, 3/4 < t` (`:289-292`). Mathematically valid. **But its own docstring admits the
  point** (`:277-278`): *"This hypothesis is not supplied by the zero extension itself."* This is where
  the analytic content of the whole endpoint story is *assumed*, see Escalation E1.

### (e) Vacuity / junk-value traps

I looked for each pattern named in the brief and found **no** trap in these two files:

* `ContDiffOn` on a set with empty interior: **no**. `closedPast T = Iic T ×ˢ univ` has interior
  `Iio T ×ˢ univ` (nonempty), `closure (openPast T) = closedPast T` is *proved* (`:34-35`), and
  `UniqueDiffOn` holds (`:37-38`), so `iteratedFDerivWithin` is not junk and the boundary jet claim
  `boundary_jets_eq_limits` has content.
* Filter-bottom abuse: **no**. `𝓝[<] T` is `NeBot` by instance (`DenselyOrdered.lean:214`);
  `𝓝[openPast T] (T,x)` is `NeBot` because `(T,x) ∈ closure (openPast T)` (and a sibling file even
  proves it explicitly, `JointResidualLimits.lean:162-165`). `Filter.NeBot` obligations at
  `SpacetimeEndpoint.lean:69` and `:109-111` (`tendsto_nhds_unique`) are discharged by that instance —
  silently, but correctly.
* `EventuallyEq`/`EqOn` at a boundary point: the two uses at `t = T` are
  `extendTrace_continuousWithinAt_boundary` (`:93-102`) and `hdf` (`:170-...`), both `filter_upwards
  [self_mem_nhdsWithin]` on the *nonempty* `𝓝[openPast T]` filter. `PastExtension.lean:271-275` uses
  `EventuallyEq.iteratedFDerivWithin_eq`, which additionally requires the pointwise equality
  `f₁ x = f x` — supplied as `heq.eq_of_nhds` (`:275`). Correct.
* `if h : P then witness else 0` dite-collapse: **none in these two files**. The only `if`s are the two
  decidable real comparisons `extendTrace` (`:41-42`) and `zeroBefore` (`PastExtension.lean:31-32`),
  both with *both* branches meaningful and both branches separately proved. (A `dite` + `Classical.choice`
  pattern does appear one level up at `JointResidualLimits.lean:138-139` — out of my scope, see E1.)
* Name-vs-statement inflation: mild only. `pastResidual` is the residual of the **modified** fields, and
  equals the true NS residual of `(u,p)` only for `t > 3/4` (`pastResidual_eq_late` `:261-264`; the
  activation error terms are visible in `TimeLocalization.lean:133-134`). The file's docstring (`:215-216`)
  says "the actual residual of the **new** fields", so this is disclosed, not hidden. Flagged as context,
  not fraud.

### (f) Kernel-risk pass (see also ## Kernel-risk assessment)

Repo-wide-style token scan over the two files (grep, counts exact):

| token | SpacetimeEndpoint.lean | PastExtension.lean |
|---|---|---|
| `decide` / `native_decide` | 0 | 0 |
| `axiom` / `sorry` / `admit` / `unsafe` / `partial` | 0 | 0 |
| `macro` / `elab` / `syntax` / `set_option` | 0 | 0 |
| `termination_by` / `WellFounded` / `Acc.` / `.rec` / `Nat.rec` | 0 | 0 |
| bare `rfl` | 0 | **1** (`:332`) |
| `induction` | **1** (`:302`) | 0 |
| `norm_num` | 0 | **1** (`:290`, `(3/4:ℝ) < 1`) |
| `linarith` | 0 | 4 (`:177,181,185,190`) |
| numeric literals | `0`, `1` only | `0`, `1`, `3/4`, `3/8`(via import) |
| literals with >=4 digits | 0 | 0 |

### (g) Cone status (from `audits/nse-deep/CONE.csv`)

All **central** decls are `in_cone=True`: `openPast`(:25), `closedPast`(:26), `extendTrace`(:41),
`extendJets`(:175), `hasFDerivWithinAt_extendTrace`(:139), `extendedJets_hasFDerivWithinAt`(:198),
`hasFTaylorSeriesUpToOn_extension`(:228), `contDiffOn_joint_extension`(:250),
`iteratedFDerivWithin_extension`(:262), `boundary_jets_eq_limits`(:277), and in `PastExtension`
`zeroBefore`(:31), `pastResidual`(:217), `pastResidual_smooth`(:220),
`pastResidual_iteratedFDeriv_eq_late`(:267), `pastResidual_locallyUniform_limit`(:279),
`pastResidual_derivative_recurrence`(:299). **Nothing central is out of cone.**

`in_cone=False` (all 12, none load-bearing for the final claim):
`SpacetimeEndpoint.lean` — `locallyUniform_linearMap`(:130), `extendedJets_contDiffOn`(:291),
`boundary_tensors_contDiff`(:330), `exists_joint_endpoint_extension`(:374).
`PastExtension.lean` — `zeroBefore_eqOn_nonneg`(:42), `pastVelocity_eq_activated`(:131),
`pastPressure_eq_activated`(:135), `pastVelocity_zero_negative`(:139), `pastPressure_zero_negative`(:142),
`pastVelocity_eq_late`(:175), `pastPressure_eq_late`(:179), `pastVelocity_divergence_free`(:193),
`pastVelocity_speed_unbounded`(:208), `pastResidual_eq_late`(:261),
`exists_joint_endpoint_extension_of_residual_limits`(:317).
Two of these deserve a note (not an alarm): the *packaged* existence statements
`exists_joint_endpoint_extension`(:374) and `exists_joint_endpoint_extension_of_residual_limits`(:317)
are **not** in the cone — the cone goes through `contDiffOn_joint_extension` + `boundary_jets_eq_limits`
directly from `CandidateFromLimits.lean:49,60`. And `extendedJets_contDiffOn`(:291), the only
`induction`-on-`ℕ` proof in either file, is out of cone, which reduces cone kernel risk further.

---

## Per-declaration findings

### `NavierStokes/SpacetimeEndpoint.lean` (30 decls, all read)

| # | name | file:line | statement in my words | proof mechanism | in_cone | verdict |
|---|---|---|---|---|---|---|
|1|`Space`|:22|abbrev for `ProblemStatement.Space`|abbrev|True|OK|
|2|`SpaceTime`|:23|abbrev for `ProblemStatement.SpaceTime` (= `ℝ × Space`)|abbrev|True|OK|
|3|`openPast`|:25|`Iio T ×ˢ univ`|def|True|OK|
|4|`closedPast`|:26|`Iic T ×ˢ univ` (includes `t = T`)|def|True|OK|
|5|`openPast_isOpen`|:28|open|`isOpen_Iio.prod isOpen_univ`|True|OK|
|6|`openPast_convex`|:31|convex|`(convex_Iio T).prod convex_univ`|True|OK|
|7|`closure_openPast`|:34|`closure (openPast T) = closedPast T`|`simp [closure_prod_eq, closure_Iio]`|True|OK|
|8|`closedPast_uniqueDiff`|:37|`UniqueDiffOn ℝ (closedPast T)`|`(uniqueDiffOn_Iic T).prod uniqueDiffOn_univ`; both Mathlib lemmas verified true|True|OK|
|9|`extendTrace`|:41|`if z.1 < T then f z else L z.2`|def (discontinuous patch)|True|OK (see (a))|
|10|`extendTrace_of_lt`|:44|`= f z` for `z.1 < T`|`simp [ite_eq_left]`|True|OK|
|11|`extendTrace_at`|:48|`extendTrace T f L (T,x) = L x`|`simp [lt_self_iff_false]`; `@[simp]`|True|OK|
|12|`hasFDerivAt_extendTrace`|:56|strictly-inside Frechet derivative of `f` transfers to the patch|`hf.congr_of_eventuallyEq` on the open set `{y.1 < T}`|True|OK|
|13|`trace_continuous`|:64|loc.-unif. limit of continuous slices is continuous|`TendstoLocallyUniformly.continuous` + `Eventually.frequently` (needs `NeBot (𝓝[<]T)`, instance exists)|True|OK|
|14|`joint_tendsto_at_boundary`|:75|`Tendsto f (𝓝[openPast T] (T,x)) (𝓝 (L x))` — **joint** spacetime limit|`tendsto_comp_of_locally_uniform_limit` (`UniformApproximation.lean:155`); this is where local uniformity is spent|True|**OK / load-bearing**|
|15|`extendTrace_continuousWithinAt_boundary`|:93|patch is continuous within `openPast` at `(T,x)`|`extendTrace_at` + #14 + `congr'`|True|OK|
|16|`trace_periodic`|:105|spatial period passes to the trace|two `tendsto_at` + `tendsto_nhds_unique`|True|OK|
|17|`extendTrace_periodic`|:116|patch is spatially periodic everywhere|`by_cases t < T`, both branches|True|OK|
|18|`locallyUniform_linearMap`|:130|a CLM preserves loc.-unif. limits|`A.uniformContinuous`|**False**|OK (unused)|
|19|`hasFDerivWithinAt_extendTrace`|:139|`HasFDerivWithinAt (extendTrace T f L) (extendTrace T f' L' z) (closedPast T) z` for **all** `z ∈ closedPast T`|inside (`:151`): #12. **At `t = T` (`:152-172`): Mathlib `hasFDerivWithinAt_closure_of_tendsto_fderiv` applied at `:170-172`, a genuine MVT-based extension theorem**|True|**OK / the crux**|
|20|`extendJets`|:175|patch each jet order by its own spatial trace|def|True|OK|
|21|`derivative_trace_continuous`|:180|each limit tensor `L · n` is continuous|#13 + slice continuity from `hderiv`|True|OK|
|22|`extendedJets_hasFDerivWithinAt`|:198|`d/dz (extendJets · n) = (extendJets · (n+1)).curryLeft` within `closedPast T`, incl. boundary|#19 with `f = J · n`, `f' = (J · (n+1)).curryLeft`; curry equiv as CLM; `split_ifs at h ⊢ <;> exact h` (defeq shuffle, ugly but honest)|True|**OK / load-bearing**|
|23|`hasFTaylorSeriesUpToOn_extension`|:228|`HasFTaylorSeriesUpToOn ∞` for the patch with the patched jets on `closedPast T`|all three structure fields proved (`zero_eq` by `hzero`/`simp`; `fderivWithin` and `cont` by #22)|True|**OK / load-bearing**|
|24|`contDiffOn_joint_extension`|:250|`ContDiffOn ℝ ∞` on `closedPast T` (boundary included)|`.contDiffOn` of #23 (`ContDiff/Defs.lean:458`, `{n : ℕ∞}`)|True|**OK** (see (b))|
|25|`iteratedFDerivWithin_extension`|:262|relative jets of the patch `=` patched jets, all `n`|`eq_iteratedFDerivWithin_of_uniqueDiffOn` + #8|True|OK|
|26|`boundary_jets_eq_limits`|:277|`iteratedFDerivWithin ℝ n (patch) (closedPast T) (T,x) = L x n` for **ALL n**|#25 at `(T,x)` then `extendTrace_at`|True|**OK** (see (a))|
|27|`extendedJets_contDiffOn`|:291|each extended jet tensor is itself `C^∞` on `closedPast T`|`induction m` on ℕ + `contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn` + `contDiffOn_infty`; the `n = ω → AnalyticOn` side goal is killed by `by simp` because `m` is a `Nat` cast|**False**|OK (unused)|
|28|`boundary_tensors_contDiff`|:330|`ContDiff ℝ ∞ (fun x => L x n)`|#27 composed with `x ↦ (T,x)`|**False**|OK (unused; docstring claims Taylor–Borel necessity but nothing consumes it)|
|29|`field_locallyUniform_limit`|:343|`f`-slices converge loc.-unif. to `(L · 0).curry0`|`curryFin0` equiv + `hzero` rewrite|True|OK|
|30|`unit_periods_joint_extension`|:360|patch keeps unit spatial periods on `univ`|#17 + #29|True|OK|

### `NavierStokes/PastExtension.lean` (43 decls, all read)

| # | name | file:line | statement in my words | proof mechanism | in_cone | verdict |
|---|---|---|---|---|---|---|
|1|`pastDomain`|:24|`openPast 1`|abbrev|True|OK|
|2|`zeroBefore`|:31|`if 0 ≤ z.1 then g z else 0`|def (truncation)|True|OK|
|3|`zeroBefore_of_nonneg`|:34|`= g` for `t ≥ 0`|`simp`|True|OK|
|4|`zeroBefore_of_neg`|:38|`= 0` for `t < 0`|`simp`|True|OK|
|5|`zeroBefore_eqOn_nonneg`|:42|`EqOn` on `Ici 0 ×ˢ univ`|#3|**False**|OK|
|6|`zeroBefore_eventuallyEq_pos`|:47|germ equality for `t > 0`|open set `{0 < w.1}`|True|OK|
|7|`zeroBefore_eventually_zero_neg`|:54|germ `= 0` for `t < 0`|open set `{w.1 < 0}`|True|OK|
|8|`zeroBefore_eventually_zero_at_zero`|:61|if `g` has zero germ at `(0,x)` so does `zeroBefore g`|`filter_upwards` + `by_cases`|True|OK / seam-critical|
|9|`zeroBefore_eventuallyEq_nonneg`|:70|germ equality at **every** `t ≥ 0` incl. `t = 0`|`t>0` case #6; `t=0` case #8 composed with the zero germ|True|OK / seam-critical|
|10|`zeroBefore_contDiffOn_past`|:82|`ContDiffOn ℝ ∞ (zeroBefore g) (openPast 1)` from smoothness on `Ico 0 1 ×ˢ univ` + zero germ at `t=0`|trichotomy `t<0 / t=0 / t>0`; first two by `contDiffAt_const.congr_of_eventuallyEq`; third by `smooth_at_interior` (`ProblemStatement.lean:126`)|True|**OK / the `t=0` seam**|
|11|`zeroBefore_periodic`|:100|periods survive truncation|`by_cases 0 ≤ t`|True|OK|
|12|`pastVelocity`|:112|`zeroBefore (activatedVelocity u)`|def|True|OK|
|13|`pastPressure`|:115|`zeroBefore (activatedPressure p)`|def|True|OK|
|14|`activatedVelocity_zero_germ`|:117|activated velocity `≡ 0` near `(0,x)`|`timeSwitch_eventually_zero` (`SmoothCutoffs.lean:267`) + `zero_smul`|True|OK (depends on cutoff file)|
|15|`activatedPressure_zero_germ`|:124|same for pressure|same + `zero_mul`|True|OK|
|16-19|`past{Velocity,Pressure}_eq_activated`(:131,:135), `..._zero_negative`(:139,:142)|values on `t≥0` / `t<0`|#3/#4|**False**×4|OK|
|20|`pastVelocity_smooth`|:145|`ContDiffOn ℝ ∞ (pastVelocity u) (openPast 1)`|#10 + `activatedVelocity_smooth` + #14|True|OK|
|21|`pastPressure_smooth`|:150|same for pressure|#10 + #15|True|OK|
|22|`pastVelocity_periodic`|:155|periods on `Iio 1`|#11|True|OK|
|23|`pastPressure_periodic`|:160|same|#11|True|OK|
|24|`pastVelocity_eventuallyEq_activated`|:165|germ equality for `t ≥ 0`|#9|True|OK|
|25|`pastPressure_eventuallyEq_activated`|:170|same|#9|True|OK|
|26|`pastVelocity_eq_late`|:175|`= u` for `t ≥ 3/4`|#3 + `activatedVelocity_eq_late` (`TimeLocalization.lean:74`)|**False**|OK|
|27|`pastPressure_eq_late`|:179|same|same|**False**|OK|
|28|`pastVelocity_eventuallyEq_late`|:183|germ `= u` for `t > 3/4`|#24 + `activatedVelocity_eventuallyEq_late`|True|OK|
|29|`pastPressure_eventuallyEq_late`|:188|same|same|True|OK|
|30|`pastVelocity_divergence_free`|:193|divergence-free on all `t < 1`|`t≥0` by germ transfer; `t<0` by `simp [spatialDerivative]` on the zero function|**False**|OK|
|31|`pastVelocity_speed_unbounded`|:208|speed still unbounded at `t=1`|transfer through `activatedVelocity_speed_unbounded`|**False**|OK|
|32|`pastResidual`|:217|NS residual of the **modified** fields|def|True|OK (name is honest: `past`, not `u`'s residual)|
|33|`pastResidual_smooth`|:220|`ContDiffOn ℝ ∞` on `openPast 1`|`contDiffOn_residual` + #20 + #21|True|OK / load-bearing|
|34|`pastResidual_periodic`|:227|unit periods on `Iio 1`|`residual_periods` + #22/#23|True|OK|
|35|`pastResidual_eventually_zero_nonpos`|:233|residual germ `= 0` for every `t ≤ 0`|`residual_eventually_zero` fed with #7 (t<0) and #8 (t=0)|True|OK|
|36|`pastResidual_zero_nonpos`|:244|`pastResidual u p (t,x) = 0` for `t ≤ 0`|`.self_of_nhds` of #35|True|OK (genuinely stronger than pointwise: it comes from a germ)|
|37|`pastResidual_eq_activated`|:248|`= ` residual of the activated fields for `t ≥ 0`|`residual_congr` + #24/#25|True|OK|
|38|`pastResidual_eventuallyEq_late`|:255|germ `=` true NS residual of `(u,p)` for `t > 3/4`|`residual_eventuallyEq` + #28/#29|True|OK|
|39|`pastResidual_eq_late`|:261|pointwise version|`.self_of_nhds`|**False**|OK|
|40|`pastResidual_iteratedFDeriv_eq_late`|:267|**all** iterated derivative tensors agree with the true residual's for `t > 3/4`|`EventuallyEq.iteratedFDerivWithin_eq` (needs the point equality — supplied) + `iteratedFDerivWithin_univ`|True|OK|
|41|`pastResidual_locallyUniform_limit`|:279|**transfers** an assumed loc.-unif. limit from the true residual to `pastResidual`|#40 + `∀ᶠ t in 𝓝[<]1, 3/4 < t` (`norm_num`)|True|**OK as a lemma / SUSPICIOUS as a foundation — see E1**|
|42|`pastResidual_derivative_recurrence`|:299|`HasFDerivAt (iteratedFDeriv ℝ n R) ((iteratedFDeriv ℝ (n+1) R z).curryLeft) z` for `z.1 < 1`|`contDiffAt` on the open past + `ContDiffAt.iteratedFDeriv_right` + `fderiv_iteratedFDeriv`|True|**OK — a real proof, not a restatement**|
|43|`exists_joint_endpoint_extension_of_residual_limits`|:317|packaged existence of the endpoint extension|`SpacetimeEndpoint.exists_joint_endpoint_extension` with `J := ftaylorSeries ℝ (pastResidual u p)`, `hzero` by `rfl`|**False**|OK (unused; cone uses `CandidateFromLimits` instead)|

---

## Kernel-risk assessment

**Vector (1) — recursive inductives / recursor reduction / `Acc.rec` / well-founded unfolding / structure eta.**
Zero `termination_by`, `WellFounded`, `Acc.`, `.rec`, `Nat.rec`, `structure`, `inductive` in either file
(grep, 0 hits). The only ℕ-recursion is `induction m with | zero | succ m ih` at
`SpacetimeEndpoint.lean:302`, inside `extendedJets_contDiffOn`, which is
**(a) a proof by induction, not a definition by recursion**, and **(b) `in_cone=False`**. The kernel
type-checks one `Nat.rec` *motive application* with a universally quantified `m`; it never has a
concrete numeral to unfold, so there is **no recursor reduction burden at all**. Induction over the jet
order `n` is likewise absent: every jet statement is `∀ n : ℕ, …` and `extendJets` is defined
non-recursively (`:175-178`, `fun n => extendTrace …`). `FormalMultilinearSeries` is a plain function
type, so no eta-heavy structure recursion. Deepest unfolding the kernel must do: the `rfl` at
`PastExtension.lean:332` (`(ftaylorSeries ℝ R z 0).curry0 = R z`), which unfolds
`ftaylorSeries`/`iteratedFDeriv 0`/`continuousMultilinearCurryFin0` — a handful of definitional steps
plus structure eta, constant size, independent of any numeral. **Risk: negligible.**

**Vector (2) — Nat GMP numeral arithmetic (`decide`, `Nat.pow/div/mod/gcd/beq/ble`, huge literals,
`norm_num` certificates).** Zero `decide`, zero `native_decide`, zero `Nat.*` arithmetic, zero literals
with 4+ digits. The complete list of numerals the kernel sees: `0`, `1`, `3/4` (as `ℝ` division of
`OfNat` literals) in `PastExtension.lean`, plus `3/8` reached only through imported
`SmoothCutoffs` lemmas. The single `norm_num` (`PastExtension.lean:290`, `(3/4 : ℝ) < 1`) produces a
one-step rational certificate over `ℝ` (`Nat` operands `3`, `4`, `1`), i.e. a couple of machine-word
`Nat` comparisons. Four `linarith` calls (`:177,181,185,190`) on `3/4 ≤ t → 0 ≤ t`-type goals produce
small rational-coefficient certificates. **The kernel performs no non-trivial computation.
Risk: none.**

**Vector (3) — custom metaprogramming.** Zero `macro`, `elab`, `syntax`, `notation`, `set_option`,
`attribute` beyond one `@[simp]` (`SpacetimeEndpoint.lean:48`), zero `axiom`, `sorry`, `unsafe`,
`partial` in either file. Consistent with the repo-wide scan. **No finding.**

**Net.** These two files carry essentially no kernel-exploitation surface. If this proof is wrong, it is
wrong *mathematically* or *by hypothesis*, not by kernel abuse.

---

## Escalations (ranked)

**E1 — the analytic heart is ASSUMED, and it is assumed one level up where a `Classical.choice` is
hiding.** `PastExtension.lean:279-295` only *transfers* the hypothesis; `CandidateFromLimits.lean:39-41`
holds `hlim : ∀ n, TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n (true NS residual) (t,x))
(fun x => L x n) (𝓝[<] 1)` as a **`variable`**, i.e. assumed, and `include hu hp hlim` (`:43`) injects it
into `tracedResidual_smooth` (`:47-55`) and `tracedResidual_boundary_jets` (`:57-66`). The only place I
found that *produces* such a hypothesis is `JointResidualLimits.lean:148-154`
(`boundaryLimits_locallyUniform`), which derives it from two assumed predicates
`VanishingJointJets f` and `AwayExtensions f`, and whose jet family is literally
`Classical.choice (hext x hx)` (`JointResidualLimits.lean:138-139`).
*Question for an expert:* is `AwayExtensions f` (existence, for every `x ≠ 0`, of a one-sided
`C^∞` extension of `f` past `t = 1` near `x`, with joint jet limits) ever **proved** for the
constructed candidate, or is it an axiom-shaped hypothesis of the top-level theorem? If the latter, the
"smooth force through the blowup time" claim is conditional on precisely the regularity it purports to
construct.
*What would settle it:* the hypothesis chain of the final `theorem` in the repo's root
(`NavierStokes.lean` / `ProblemStatement`-level statement) printed with `#print axioms` and with every
hypothesis traced to either a proof or a `variable`. Owner: whoever has `JointResidualLimits.lean` /
`CandidateFromLimits.lean` / the root theorem.

**E2 — the conclusion is strictly ONE-SIDED; "smooth THROUGH `t = 1`" is not what these theorems say.**
`SpacetimeEndpoint.lean:250-260` concludes only `ContDiffOn ℝ ∞ … (closedPast 1)` = `Iic 1 ×ˢ univ`, and
`:277-288` pins only the `closedPast 1`-relative jets at `(1,x)`. Note also that `extendTrace`
(`:41-42`) sets the function equal to the *time-independent* trace `L z.2` for **all** `t ≥ T`, which is
certainly not a solution of anything for `t > 1`.
*Question:* which declaration supplies smoothness on a **two-sided** neighbourhood of `t = 1`
(candidate: `SpacetimeGluing.lean:406`, which has an identically-shaped `hlim` hypothesis), and does the
future-side extension use the *same* `L x n` jets, so that the two one-sided Taylor families actually
agree to infinite order?
*What would settle it:* the statement of the gluing theorem in `SpacetimeGluing.lean` plus the final
force smoothness statement (is it `ContDiffOn … futureDomain = Ici 0 ×ˢ univ`,
`ProblemStatement.lean:45`, i.e. genuinely across `t = 1`?). Owner: the `SpacetimeGluing` worker.

**E3 — the `t = 0` seam is smooth only because `timeSwitch` is flat at `0`; that flatness is imported.**
`PastExtension.lean:82-97` is correct *given* `activatedVelocity u =ᶠ[𝓝 (0,x)] 0`
(`:117-122`), which is exactly `SmoothCutoffs.timeSwitch_eventually_zero` (`SmoothCutoffs.lean:267`) and
`timeSwitch_zero_of_abs_le` (`SmoothCutoffs.lean:256`), plus `timeSwitch_contDiff`
(`SmoothCutoffs.lean:248`).
*Question:* is `SmoothCutoffs.scaledCutoff` a genuinely `C^∞` function (a real bump/mollifier, e.g. via
Mathlib's `expNegInvGlue`/`ContDiffBump`) with `= 1` on `|t| ≤ 3/8`-scale and `= 0` for `t ≥ 3/4`, or is
it a piecewise `if` whose smoothness lemma is where the fraud would live?
*What would settle it:* reading `SmoothCutoffs.lean:1-250` line by line. Owner: the `SmoothCutoffs`
worker. (Everything I verified in my two files is conditional on that one file.)

**E4 — disclosure, not fraud, but the reader must not be misled: the smooth object is the residual of a
CUT-OFF field.** `pastResidual` (`PastExtension.lean:217-218`) is the NS residual of
`timeSwitch·u`, `timeSwitch·p` truncated to `t ≥ 0`; it equals the true residual of `(u,p)` only for
`t > 3/4` (`:261-264`), the difference being the cutoff terms visible at
`TimeLocalization.lean:133-134` (`deriv timeSwitch • u` and `(τ² − τ) • advection`).
*Question:* does the final theorem's force equal the NS residual of the *original* `u,p` on the region
where blowup is claimed, or only of the activated pair — and is the "solution" whose blowup is asserted
`u` or `timeSwitch·u`? *What would settle it:* the root statement's fields. Owner: the
`ProblemStatement`/root-theorem worker.

**E5 (low) — cosmetic/robustness.** `extendedJets_hasFDerivWithinAt` finishes with
`unfold … ; split_ifs at h ⊢ <;> exact h` (`SpacetimeEndpoint.lean:222-224`). It is sound but relies on
the two `if`s having syntactically identical decidability instances; a reviewer should confirm the file
compiles from a clean state (I could not build). Similarly `hzero` is discharged by bare `rfl` at
`PastExtension.lean:332` and `CandidateFromLimits.lean:52,63` — check that `ftaylorSeries`'s 0th jet is
still `rfl`-equal to the function in v4.34.0-rc2.

---

## Residue (what I could NOT check, and why)

1. **No compilation.** No built Mathlib on this box (disk full) and the brief forbids `lake build` /
   `lake env`. So: I cannot confirm that either file actually type-checks, that the `simp only`/`simpa`
   steps close their goals, that `split_ifs at h ⊢ <;> exact h` (`:222-224`) really discharges both
   branches, or that the implicit arguments I read as intended are the ones Lean elaborates. Everything
   above is source-level reading.
2. **Mathlib version skew.** The Mathlib signatures I quote were read from a **v4.29.0** checkout, while
   NSE pins **v4.34.0-rc2**. All eight lemmas I checked are long-standing, but a signature change
   (especially around `WithTop ℕ∞` / `ω` in `HasFTaylorSeriesUpToOn.contDiffOn`) cannot be excluded.
3. **`#print axioms` not available**, so I cannot certify that these decls depend only on the three
   standard axioms; the grep evidence (no `axiom`, no `sorry`, no `native_decide` in either file) is
   necessary but not sufficient — an imported file could still carry one.
4. **Out-of-scope dependencies I only skimmed and did not verify**: `SmoothCutoffs` (smoothness and
   flatness of `timeSwitch` — E3), `ResidualRegularity` (`contDiffOn_residual`, `residual_congr`,
   `residual_eventually_zero`, `residual_eventuallyEq`, `residual_periods`), `TimeLocalization`
   (`activated*_smooth`, `activated*_eq_late`), `ProblemStatement`
   (`navierStokesResidual`, `spatialDivergence`, `preSingularDomain`, `smooth_at_interior`),
   `JointResidualLimits` (`AwayExtensions`, `VanishingJointJets`, `boundaryLimits*` — E1),
   `SpacetimeGluing` (future side — E2). If the endpoint story is broken, my reading says it is broken in
   one of those, not in the two files I was given.
5. I did not attempt to construct a counter-model to `contDiffOn_joint_extension`; my confidence that it
   is a true theorem rests on recognising it as the standard one-sided Whitney/MVT argument and on
   having read the Mathlib workhorse's own proof.

## Verdict counts (my 73 decls)

OK **73**, UNCLEAR 0, KERNEL-RISK 0, SUSPICIOUS 0 — with the standing qualification that
`pastResidual_locallyUniform_limit` (`PastExtension.lean:279`) is *OK as a lemma* while being the seam
where the entire analytic burden is handed to an assumed hypothesis (E1), and that all 73 verdicts are
conditional on residue items 1-4.
