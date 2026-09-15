# Worker report — NS SPACETIME GLUING (force smooth THROUGH t = 1)

Auditor: read-only child worker. Repo: `/home/gsm/.openclaw/workspace/repos/NSE`
(clone of `openai/NavierStokesAndEuler` @ `f9e8bc5`). NOTHING under that path was modified.
No `lake build` / `lake env` was run (no Mathlib build on this box): this is **source-level**
audit only. Every claim below carries `file:line` re-read in the original file.

## Scope

Assigned files (read line by line):

| file | lines | decls (theorem/def/abbrev/structure) | how read |
|---|---|---|---|
| `NavierStokes/SpacetimeGluing.lean` | 435 | 40 (30 thm / 7 def / 3 abbrev) | **every line, every proof** |
| `NavierStokes/GenericEndpointExtension.lean` | 874 | 91 (72 thm / 19 def) | lines 413–874 **every line**; lines 20–411 verified by mechanical diff to be a type-generalised **verbatim copy** of `SpacetimeGluing.lean` (see below), so read once |

Dependencies I had to open because the assigned questions cannot be answered without them
(the Taylor–Borel branch and the closed-past input live there):

| file | lines | decls | how read |
|---|---|---|---|
| `NavierStokes/SpatialBorelExtension.lean` | 519 | 70 (56/14) | **every line** (this is the actual Borel summation) |
| `NavierStokes/BorelExtension.lean` | 380 | 54 (44/10) | lines 1–175 line-by-line (`monomial`, `term`, jet-at-0 lemma, bounds); rest skimmed |
| `NavierStokes/SpacetimeEndpoint.lean` | 389 | 31 (25/4/2) | lines 1–300 line-by-line (`extendTrace`, `hasFDerivWithinAt_extendTrace`, `hasFTaylorSeriesUpToOn_extension`, `contDiffOn_joint_extension`, `boundary_jets_eq_limits`); 300–389 skimmed |
| `NavierStokes/CandidateFromLimits.lean` | 222 | 18 (16/2) | **every line** (the caller: `force`, `force_smooth`) |
| `NavierStokes/JointResidualLimits.lean` | ~340 | 34 | lines 1–200 line-by-line (`OneSidedExtension`, `AwayExtensions`, `VanishingJointJets`, `boundaryLimits`) |
| `NavierStokes/SmoothCutoffs.lean`, `NavierStokes/DiagonalScale.lean` | — | — | targeted: `cutoff` (`:33,40,44`), `doublingEnvelope` (`:91`) |
| `NavierStokes/MixedPeriodicAssembly.lean` | — | — | targeted `:338–368` (who discharges `hlim`) |

**Important structural finding first:** `GenericEndpointExtension.lean:20–411`
(`namespace NavierStokes.GenericEndpointExtension.Gluing`) is `SpacetimeGluing.lean:15–395`
with `ProblemStatement.SpaceTime` replaced by `ℝ × X` plus `omit [FiniteDimensional ℝ X] in`
lines. I diffed the two ranges: the only differences are the namespace, the type variables, the
`omit` lines, `past` being `Iic T ×ˢ univ` instead of the abbreviation
`SpacetimeEndpoint.closedPast T`, and the fact that the generic copy **drops**
`smoothExtension_unit_periods` and `exists_smooth_periodic_extension_of_limits`. Proof scripts
are character-identical. So the audit of `SpacetimeGluing.lean` is simultaneously an audit of
`GenericEndpointExtension.lean:20–411`; `GenericEndpointExtension.lean:413–874` is genuinely
new material (closure-completion + strip machinery) and is reported separately.

---

## Answers to the assigned questions

### (a) What IS `glue` / `smoothExtension`?

```lean
-- SpacetimeGluing.lean:191-193
/-- Glue along the time hyperplane, using the past branch at the join. -/
def glue {W : Type*} (T : ℝ) (f g : SpaceTime → W) (z : SpaceTime) : W :=
  if z.1 ≤ T then f z else g z
```

```lean
-- SpacetimeGluing.lean:337-342
def smoothExtension (T : ℝ) (f : SpaceTime → V) (hf : ContDiffOn ℝ ∞ f (past T)) :
    SpaceTime → V :=
  glue T f (SpatialBorelExtension.rightExtension (normalTrace T f)
    (normalTrace_contDiff hf) T)
```

So yes, it is exactly `if t ≤ T then f z else <else>`, with the past branch used **at** `t = T`.

The `else` branch is **not** zero and **not** a junk value. It is
`SpatialBorelExtension.rightExtension a ha T (t,x) = extension a ha (t-T, x)`
(`SpatialBorelExtension.lean:475`) where `extension` is a genuine convergent series
(`SpatialBorelExtension.lean:301`, closed form at `:434-437`):

```lean
extension a ha z = ∑' j : ℕ, (SmoothCutoffs.cutoff ((scale a ha j : ℝ) * z.1) *
                              (z.1 ^ j / (j.factorial : ℝ))) • a j z.2
```

with coefficients `a j = normalTrace T f j` = the **actual one-sided time jets of `f` at `T`**
(`SpacetimeGluing.lean:310-311`, identified with `iteratedDerivWithin j (fun t => f (t,x)) (Iic T) T`
at `:320-324`).

Smoothness is claimed and proved on **all of spacetime**, i.e. `ContDiff ℝ ∞` (not `ContDiffOn`,
not "on each side"), including at `t = T`:

* `smoothExtension_contDiff` (`SpacetimeGluing.lean:344-351`) = `contDiff_glue hf (rightExtension_contDiff …).contDiffOn` + jet matching by
  `SpatialBorelExtension.rightExtension_right_jets` (`SpatialBorelExtension.lean:487`) and
  `normalTrace_eq_time_jet` (`SpacetimeGluing.lean:320`).
* `contDiff_glue` (`:294-306`) reduces to `contDiff_glue_finite` (`:262-289`) for every `m : ℕ`
  via `contDiff_infty.mpr`, converting the hypothesis (equality of the two **one-sided**
  `iteratedDerivWithin` time jets at `T`) into equality of `normalIter` by
  `time_slice_iteratedDerivWithin` (`:94-114`).
* The seam is handled honestly: `hasFDerivAt_glue` (`:211-240`) does a `lt_trichotomy` on `t`,
  and at `t = T` it uses `HasFDerivWithinAt.union` of the past-side and future-side one-sided
  derivatives together with `past_union_future : past T ∪ future T = univ` (`:185-189`), then
  `hasFDerivWithinAt_univ` (`:235-236`). That is the correct way to get a two-sided
  `HasFDerivAt` at the interface — no `ContDiffOn`-on-a-thin-set trick.
* The induction in `contDiff_glue_finite` (`:271-289`) differentiates in **each** spacetime
  direction `v` (`contDiff_succ_iff_fderiv_apply`, `:274`), rewrites
  `fun z => fderiv ℝ (glue T f g) z v = glue T (directional (past T) f v) (directional (future T) g v)`
  (`:277-282`), and re-establishes the jet-matching hypothesis for the differentiated pair with
  `normal_match_directional` (`:151-164`), whose proof derives the tangential/mixed matching from
  Schwarz symmetry (`directional_commute`, `:56-73`, via `isSymmSndFDerivWithinAt`) rather than
  assuming it. This is the honest structure the docstring at `:291-293` advertises.

### (b) Is a real Borel / Taylor summation performed? Which growth condition, hypothesis or proof?

**Yes — a real Borel summation, and NO growth condition is assumed.** The growth control is
*constructed*:

1. Summand: `term b j a z = cutoff (b * z.1) • ((z.1^j / j!) • a j z.2)`
   (`SpatialBorelExtension.lean:63-64` + `BorelExtension.lean:78,26`).
2. Spatially localised summand: `localizedTerm m b j a = spatialCutoff m z.2 • term b j a z`
   (`SpatialBorelExtension.lean:66-67`), where `spatialCutoff m` is a `ContDiffBump` with
   `rIn = m+1`, `rOut = m+2` (`:29-35`).
3. `template m j a = localizedTerm m 1 j a` has **compact support** (`:84-103`), hence for every
   `(m,j,k)` a finite sup bound `templateBound ha m j k` exists (`:130-144`).
4. `boundSum ha j = ∑_{m<j} ∑_{k<j} templateBound ha m j k` (`:182-183`) — a *finite* sum, one per
   degree, over the finitely many spatial windows and derivative orders below that degree.
5. `localScale ha j` is chosen with `2^j * boundSum j < localScale j` (`:196-199`), and
   `scale = DiagonalScale.doublingEnvelope (localScale)` (`:203`) makes it strictly increasing and
   doubling (`:211-215`; `doublingEnvelope` is plain structural recursion, `DiagonalScale.lean:91-93`).
6. Consequence, **proved**: `‖iteratedFDeriv ℝ k (localizedTerm m (scale j) j (a j)) z‖ ≤ (1/2)^j`
   whenever `m < j` and `k < j` (`:236-248`), for all `z`; the `majorant` (`:250-252`) is
   summable (`:254-261`), giving `contDiff_tsum` smoothness of `localizedExtension` (`:320-324`)
   and, by local equality with it on the ball where `spatialCutoff m ≡ 1` (`:334-355`),
   `extension_contDiff` (`:350`).
7. Jets: `extension_time_jets` (`:409-422`) proves
   `iteratedDeriv k (fun t => extension a ha (t,x)) 0 = a k x`, using
   `BorelExtension.iteratedDeriv_term_zero` (`BorelExtension.lean:139-145`), which is valid because
   `SmoothCutoffs.cutoff = 1` on `|x| ≤ 1/2` (`SmoothCutoffs.lean:40`), so near `t=0` each term is
   exactly the monomial.
8. Compact time support: `extension_zero_of_one_le_abs` (`:441-451`) from
   `cutoff_zero_of_one_le_abs` (`SmoothCutoffs.lean:44`) — each term dies for `|t| ≥ 1` because
   `scale j ≥ 1`.

So the condition needed is "for each degree, finitely many sup-norms of a *compactly supported*
template are finite", which is **proved** (`:130-134`), not assumed. Price paid instead:
`[FiniteDimensional ℝ X]` (needed for `ContDiffBump`, `:29`) and `[CompleteSpace V]` (needed for
`tsum`, `:299`). This is a correct parametrised Borel lemma; the docstring claim "no global growth
restriction" (`:508-509`) matches the statement. `tsum` is **not** used as a junk default: summability
is proved (`:308-313`, `:315-318`).

### (c) Is the smoothness honest, or the cheap "zero past T" trick? — HONEST here, but read the LOUD caveat

`smoothExtension_zero_from` (`SpacetimeGluing.lean:359-365`: extension `= 0` for `t ≥ T+1`) and
`smoothExtension_iteratedFDeriv` (`:368-373`: every mixed jet on the closed past, **including the
boundary `t = T`**, equals `f`'s) are **not** in contradiction and do **not** force `L x n = 0`.
Reason: the future branch is compactly supported in `t - T ∈ [-1,1]` yet has *prescribed* jets at
`t = T`; that is exactly Borel's lemma, and the file really proves both properties of the same
series (jets: `:487`; vanishing: `:502-505`). I checked specifically for the fraud pattern
"extension ≡ 0 past T and matching then forces all jets to vanish": it is **absent**. Nowhere in
`SpacetimeGluing.lean` or `GenericEndpointExtension.lean` is a hypothesis `L x n = 0` or
`normalTrace = 0` used to get smoothness. (`Gluing.smoothExtension_zero_fiber`,
`GenericEndpointExtension.lean:670-686`, is the *converse* direction and is optional: it says a
fibre that already vanishes on the past stays zero.)

**LOUD CAVEAT (where the vanishing really lives — upstream, and ASSUMED).** The force in the NS
cone is `SpacetimeGluing.smoothExtension 1 (tracedResidual u p L) …`
(`CandidateFromLimits.lean:82-84`), and the boundary jets `L` come from
`JointResidualLimits.boundaryLimits` (`JointResidualLimits.lean:120-124`):

```lean
boundaryLimits f hext x = if hx : x = 0 then 0 else ftaylorSeries ℝ (Classical.choice (hext x hx)).value (1, x)
```

* At the single spatial point `x = 0` **all boundary jets are defined to be `0`**
  (`JointResidualLimits.lean:123`, `:126-128`), and this is *legitimated* only by the hypothesis
  `VanishingJointJets f` (`:84-86`), i.e. `∀ n, iteratedFDeriv ℝ n f → 0` along
  `𝓝[openPast 1] (1, 0)` — a **hypothesis**, at the one point `(1,0)`.
* At every `x ≠ 0` the jets are those of an **assumed** smooth one-sided extension across `t = 1`:
  the structure `OneSidedExtension` (`:73-79`) and `AwayExtensions` (`:81-82`) are *assumptions*
  that the residual already continues smoothly through the blowup time away from the axis point.
* `CandidateFromLimits.lean:39-41` takes `hlim` (locally uniform convergence of **every** derivative
  of the residual as `t → 1⁻`) as a **variable**, and the module docstring admits it
  (`CandidateFromLimits.lean:13-14`: "The residual limits and the existence of singular incoming
  fields remain analytic hypotheses. This module does not prove the unconditional candidate.").
  `MixedPeriodicAssembly.exists_candidate_force` (`:338-360`) discharges `hlim` from `hz :
  VanishingJointJets …` + three `AwayExtensions …` — i.e. it *moves* the assumption, it does not
  remove it.

Verdict on (c): the gluing/Borel machinery in my scope is honest and general. The "smooth through
the blowup" claim is only as strong as `VanishingJointJets` + `AwayExtensions` + `hlim`, which are
assumptions at this layer. That is the correct place to point the expert (see Escalations).

Other cheap-trick checks in my scope, all negative:
* `ContDiffOn` on a set with empty interior: no. `past T = Iic T ×ˢ univ` has dense interior, and
  `past_regular`/`future_regular` (`:175-183`) prove `s ⊆ closure (interior s)`, which is what
  Schwarz needs.
* Hypothesis containing the conclusion: `contDiff_glue`'s `hmatch` (`:296-298`) is about one-sided
  *slice* derivatives only; joint/mixed smoothness is derived, not assumed.
* Junk values: `if z.1 ≤ T` uses classical decidability inside `noncomputable section` (`:15`);
  both branches are genuine functions. `fderivWithin`'s junk-zero convention is never exploited:
  every use is guarded by a `ContDiffOn`/`UniqueDiffOn` hypothesis (`:42-52`, `:169-173`).
* Name-vs-statement: names match statements throughout the two files; `smoothExtension_iteratedFDeriv`
  really is about `iteratedFDeriv` of the glued function on the whole closed past (`:368-370`).

### (d) Kernel-risk pass (both in-scope files)

Mechanical grep over `SpacetimeGluing.lean` + `GenericEndpointExtension.lean`:

* `decide` / `native_decide` / `macro` / `macro_rules` / `elab` / `syntax` / `set_option` /
  `axiom` / `unsafe` / `partial` / `sorry`: **0 occurrences in both files** (grep count 0/0).
* `termination_by`, `decreasing_by`, `WellFounded`, `Acc.`, explicit `.rec`: **0**.
* Recursive data / recursor reduction: exactly one recursive definition per file,
  `normalIter` (`SpacetimeGluing.lean:38-40`, `GenericEndpointExtension.lean:41-44`) — structural
  recursion on `ℕ` (compiles to `Nat.rec`), used only through `induction n` and one-step iota
  reductions: `SpacetimeGluing.lean:82` (`rfl` on `normalIter _ 0 = id`), `:100`
  (`simp only [iteratedDerivWithin_zero, normalIter]`), `:111-113` (`simpa only [… normalIter …]`).
  No closed numeral is ever fed to `normalIter`, so the kernel never unfolds it more than one step.
  Same for `GenericEndpointExtension.lean:89`, `:107`, `:119`.
* Numerals / `Nat` arithmetic: no `Nat.pow`/`div`/`mod`/`gcd`/`beq`/`ble`, no literal above `2`.
  The only `Nat.` occurrences are simp-lemma *names* (`Nat.cast_add`, `Nat.cast_one` at
  `SpacetimeGluing.lean:289`, `GenericEndpointExtension.lean:308,447`), i.e. no computation.
  `norm_num` appears 5× in `GenericEndpointExtension.lean` (`:450, 576, 588, 648, 784`) and 0× in
  `SpacetimeGluing.lean`; the goals are tiny (`(-1:ℝ) ≠ 1`, `(0:ℕ∞) < 1`, `-1 ≤ 0 ∧ 0 ≤ 1`,
  `0 ∈ Ioo (-1/2) (1/2)`), so the certificates the kernel recomputes are `Int`/`Nat` literals of
  one digit.
* `if … then … else` on `z.1 ≤ T` over `ℝ` (`SpacetimeGluing.lean:193`,
  `GenericEndpointExtension.lean:208, 763`) uses `Real.decidableLE`, which is classical, so the
  kernel never *evaluates* the branch condition; it only rewrites via `ite_eq_left/ite_eq_right`
  (`:198, 208, 228, 236, 239, 363, 381, 383`).
* Structure eta **is** exercised (Prod projections/`⟨t,x⟩` patterns everywhere, e.g.
  `SpacetimeGluing.lean:144-145` `hv : v = v.1 • timeVector + (0, v.2) := by ext <;> simp`).
  This is standard, sound Lean-4 kernel eta for structures; I flag it only because it is the one
  kernel feature the proof actually depends on.
* Dependency files behave the same: `SpatialBorelExtension.lean` and `BorelExtension.lean` contain
  `Nat.factorial` **symbolically** (`BorelExtension.lean:26,40`) and never at a literal argument;
  the only numerals are `1`, `2`, `1/2`, `(1/2)^j` inside real-analytic estimates.

**Kernel-risk conclusion for vectors (1)(2)(3): the kernel is not asked to perform any risky
computation in this scope.** (1) is one iota step of `Nat.rec`; (2) is single-digit literals; (3)
has zero instances of custom metaprogramming — which by the parent's own rule means *no finding*
in these files.

### (e) Cone status (`audits/nse-deep/CONE.csv`)

* `SpacetimeGluing.lean`: 40 decls, **39 `in_cone=True`**, 1 `False`:
  `NavierStokes.SpacetimeGluing.exists_smooth_periodic_extension_of_limits` (`:400`,
  `in_cone=False`, `in_import_closure=True`). **FLAG:** the file's advertised "complete
  constructive endpoint theorem" packaging theorem (docstring `:396-399`) is *dead* with respect to
  the final target; the cone reaches the same content through
  `smoothExtension_contDiff/_eqOn_past/_zero_from/_iteratedFDeriv/_unit_periods` directly
  (all `True`). Not a defect, but the shiny packaging theorem is not what the proof uses.
* `GenericEndpointExtension.lean`: 91 decls, 71 `True`, 20 `False` — the `False` set is
  `normalTrace_add_period (:348)`, `smoothExtension_zero_from (:381)`,
  `smoothExtension_iteratedFDeriv (:390)`, `smoothExtension_add_period (:398)`,
  `closedInterval_subset_closure_openInterval (:586)`, `stripClosedField_zero (:593)`,
  `stripClosedField_add_period (:613)`, `lowerClamp_contDiff (:638)`,
  `Gluing.smoothExtension_zero_fiber (:670)`, `upperClosed_zero (:702)`,
  `upperClosed_add_period (:709)`, `lowerClosed_zero (:745)`, `lowerClosed_add_period (:753)`,
  `closedStripExtension_zero (:793)`, `closedStripExtension_add_period (:802)`,
  `closedStripExtension_zero_parameter (:814)`, `extension_zero_of_fiber (:842)`,
  `extension_add_period (:849)`, `extension_zero_parameter (:856)`,
  `extension_iteratedFDeriv (:861)`. All of these are periodicity/vanishing *accessories*; the
  central `Gluing.contDiff_glue (:313)`, `Gluing.smoothExtension_contDiff (:366)`,
  `closedField_contDiffOn (:541)`, `closedStripExtension_contDiff (:775)`,
  `extension_contDiff (:830)` are `True`.
* Dependencies: `SpatialBorelExtension.lean` 58 True / 12 False; `SpacetimeEndpoint.lean` 27 True /
  4 False (`locallyUniform_linearMap :130`, `extendedJets_contDiffOn :291`,
  `boundary_tensors_contDiff :330`, `exists_joint_endpoint_extension :374`);
  `CandidateFromLimits.lean` 16 True / 2 False — and one of the two is
  **`candidateStatement_of_residual_limits (:212, in_cone=False)`**, i.e. the *conditional*
  reduction of the headline statement is not the route the final theorem takes (it goes through
  `MixedPeriodicAssembly`/`CandidateConsequences`). `JointResidualLimits.lean` is mostly
  `False` (13 True / 21 False), but the load-bearing `VanishingJointJets (:84)`,
  `AwayExtensions (:81)`, `boundaryLimits (:120)`, `boundaryLimits_joint (:130)`,
  `boundaryLimits_locallyUniform (:148)` are `in_cone=True`.

---

## Per-declaration findings

### `NavierStokes/SpacetimeGluing.lean` (all 40 decls examined)

| name | line | what the statement says (my words) | actual proof mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `Space`, `SpaceTime` | 22,23 | abbreviations for `ProblemStatement.Space/SpaceTime` | — | T,T | OK |
| `timeVector` | 25 | the vector `(1,0)` in spacetime | definition | T | OK |
| `nat_le_infty` | 27 | `(n : WithTop ℕ∞) ≤ ∞` | `ENat.natCast_lt_of_coe_top_le_withTop` | T | OK |
| `infty_add_one_le` | 30 | `∞ + 1 ≤ ∞` | `simpa [ENat.coe_top_add_one]` | T | OK |
| `directional` | 35 | `fderivWithin ℝ f s z v` | definition (junk-zero possible off differentiability, always used with `ContDiffOn`) | T | OK |
| `normalIter` | 38 | iterate `directional … timeVector` `n` times | structural `Nat` recursion | T | OK |
| `directional_contDiffOn` | 42 | directional derivative of a `C^∞`-on-`s` field is `C^∞` on `s` | `hf.fderivWithin hs infty_add_one_le |>.clm_apply contDiffOn_const` | T | OK |
| `normalIter_contDiffOn` | 47 | all normal iterates are `C^∞` on `s` | induction on `n` | T | OK |
| `directional_commute` | 56 | two fixed directional derivatives commute on a regular closed domain | Schwarz: `isSymmSndFDerivWithinAt` + `fderivWithin_clm_apply`; needs `UniqueDiffOn` and `s ⊆ closure (interior s)` | T | OK |
| `normalIter_directional` | 76 | any fixed direction commutes with all normal iterates | induction + `directional_commute` + `fderivWithin_congr'` | T | OK |
| `time_slice_iteratedDerivWithin` | 94 | joint normal iterates = genuine one-sided `iteratedDerivWithin` of the time slice on `I` | induction; chain rule along `t ↦ (t,x)` with `HasDerivWithinAt.derivWithin` | T | OK |
| `boundary_fderiv_eq` | 118 | matching boundary values + matching normal derivative ⇒ full `fderivWithin` tensors agree at `(T,x)` | tangential part by uniqueness of `HasFDerivAt` of the trace map; then decompose `v = v.1 • timeVector + (0, v.2)` | T | OK |
| `normal_match_directional` | 151 | matching all normal traces ⇒ matching after any directional derivative | `normalIter_directional` on both sides + `boundary_fderiv_eq` at levels `n`, `n+1` | T | OK |
| `past`, `future` | 166,167 | `Iic T ×ˢ univ`, `Ici T ×ˢ univ` | definitions | T,T | OK |
| `past_uniqueDiff`, `future_uniqueDiff` | 169,172 | both closed half-spaces are unique-diff | product of `uniqueDiffOn_Iic/Ici` with `univ` | T,T | OK |
| `past_regular`, `future_regular` | 175,180 | each is inside the closure of its interior | `interior_prod_eq`, `closure_Iio/Ioi` | T,T | OK |
| `past_union_future` | 185 | the two halves cover spacetime | `le_total z.1 T` | T | OK |
| `glue` | 192 | `if z.1 ≤ T then f z else g z` | definition (past branch at the seam) | T | OK |
| `glue_eqOn_past` | 195 | glue `= f` on the closed past | `ite_eq_left` | T | OK |
| `glue_eqOn_future` | 200 | glue `= g` on the closed future **given** matching boundary values | case split at `t = T`, uses `hvalue` | T | OK |
| `hasFDerivAt_glue` | 211 | one-sided derivatives with matching boundary values glue into a genuine two-sided `HasFDerivAt` everywhere | trichotomy in `t`; interior cases by `nhds` membership; seam case by `HasFDerivWithinAt.union` + `past_union_future` + `hasFDerivWithinAt_univ` | T | OK |
| `hasFDerivAt_glue_of_normal` | 244 | same, needing only value + first normal derivative matching | `boundary_fderiv_eq` supplies the full-tensor matching | T | OK |
| `contDiff_glue_finite` | 262 | matching **all** normal jets ⇒ `ContDiff ℝ m` of the glue, every finite `m` | induction on `m` generalising `f g`; `contDiff_succ_iff_fderiv_apply`; `fderiv (glue) · v = glue (directional f v) (directional g v)`; hypothesis regenerated by `normal_match_directional` | T | OK (one unbuildable name, see Escalation 3) |
| `contDiff_glue` | 294 | matching all **one-sided slice** time jets ⇒ `ContDiff ℝ ∞` of the glue on all spacetime | `contDiff_infty.mpr` + `contDiff_glue_finite`, converting slice jets to `normalIter` by `time_slice_iteratedDerivWithin` | T | OK |
| `normalTrace` | 310 | the `n`-th normal jet of a closed-past field as a spatial function | definition | T | OK |
| `normalTrace_contDiff` | 313 | each normal trace is `C^∞` in `x` | `normalIter_contDiffOn` composed with `x ↦ (T,x)` | T | OK |
| `normalTrace_eq_time_jet` | 320 | the normal trace really is `iteratedDerivWithin n (f(·,x)) (Iic T) T` | `time_slice_iteratedDerivWithin` | T | OK |
| `normalTrace_add_period` | 326 | spatial periods of `f` on the past pass to every normal trace | `iteratedDerivWithin_congr` | T | OK |
| `smoothExtension` | 339 | glue `f` (past) to the Taylor–Borel realisation of its own normal jets (future) | definition; **takes the proof `hf` as an argument** | T | OK (see Escalation 4) |
| `smoothExtension_contDiff` | 344 | the glued field is `ContDiff ℝ ∞` on **all** of spacetime | `contDiff_glue` + `rightExtension_contDiff` + `rightExtension_right_jets` | T | OK |
| `smoothExtension_eqOn_past` | 354 | it agrees with `f` on the closed past | `glue_eqOn_past` | T | OK |
| `smoothExtension_zero_from` | 359 | it vanishes for `t ≥ T+1` | `SpatialBorelExtension.rightExtension_zero_from` (cutoff support) | T | OK |
| `smoothExtension_iteratedFDeriv` | 368 | every mixed jet on the closed past, boundary included, equals `f`'s `iteratedFDerivWithin` | `iteratedFDerivWithin_eq_iteratedFDeriv` (needs `UniqueDiffOn` + `ContDiffAt`) + `iteratedFDerivWithin_congr` | T | OK |
| `smoothExtension_add_period` | 376 | spatial periods survive on both branches | past branch by `hperiod`; future branch by `rightExtension_add_period` | T | OK |
| `smoothExtension_unit_periods` | 388 | unit spatial periodicity on `Iic T` ⇒ on all spacetime | previous lemma per coordinate | T | OK |
| `exists_smooth_periodic_extension_of_limits` | 400 | from jet recurrence + locally uniform left limits + periodicity on `Iio T`, there **exists** a global `C^∞` periodic field agreeing with `f` on the open past, vanishing after `T+1`, with boundary jets `= L` | `extendTrace` + `SpacetimeEndpoint.contDiffOn_joint_extension` + `smoothExtension_*` | **False** | OK but DEAD (see (e)) |

### `NavierStokes/GenericEndpointExtension.lean`

Lines 20–411 (`…Gluing.*`, 40 decls incl. `timeVector :28`, `normalIter :41`, `glue :207`,
`contDiff_glue :313`, `smoothExtension :361`, `smoothExtension_contDiff :366`): verdict **OK**,
identical proofs to the table above (verified by diff, see Scope).

New material, examined line by line:

| name | line | statement (my words) | proof mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `exists_limit_of_uniformContinuousOn` | 429 | uniform continuity on `s` + completeness ⇒ a limit exists at every closure point | Cauchy filter (`cauchy_map_iff'`) + `mem_closure_iff_nhdsWithin_neBot` | T | OK |
| `actualJet_hasFDerivAt` | 442 | inside an open `s`, `iteratedFDeriv n f` is differentiable with derivative `(iteratedFDeriv (n+1) f).curryLeft` | `ContDiffAt.iteratedFDeriv_right` | T | OK |
| `actualJet_uniformContinuousOn` | 455 | a bound on jet `n+1` ⇒ jet `n` is Lipschitz, hence uniformly continuous, on a **convex** `s` | `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`, `ContinuousMultilinearMap.curryLeft_norm` | T | OK |
| `closureJet` | 473 | `extendFrom s (iteratedFDeriv ℝ n f)` | definition | T | OK (junk value only off `closure s`) |
| `closureJet_limit/_continuousOn/_eq/_eventuallyEq` | 476,484,492,499 | the completed tensors are the actual limits, continuous on `closure s`, and agree with the real jets inside | `tendsto_extendFrom`, `continuousOn_extendFrom`, `extendFrom_extends` | T | OK |
| `closureJet_hasFDerivWithinAt` | 508 | the completed tensors differentiate into each other on `closure s` | `hasFDerivWithinAt_closure_of_tendsto_fderiv` (needs open + convex + tendsto of `fderiv`) | T | OK |
| `closedField` | 529 | value extension `= (closureJet s f 0 x).curry0` | definition | T | OK |
| `closedField_eq` | 533 | agrees with `f` inside `s` | `closureJet_eq` then `rfl` | T | OK |
| `closedField_contDiffOn` | 541 | **globally bounded** jets on a convex open `s` ⇒ `C^∞` on `closure s` | builds `HasFTaylorSeriesUpToOn ∞` from the three previous lemmas, then `.contDiffOn` | T | OK — note `hb` (uniform bound of *every* jet over all of `s`) is a strong ASSUMED input |
| `openStrip`/`closedStrip`/`…_isOpen/_convex`/`closure_openStrip` | 563–576 | `Ioo(-1,1) ×ˢ univ` etc. | `closure_Ioo` | T | OK |
| `stripClosedField_contDiffOn` | 579 | previous theorem specialised to the strip | `simpa [closure_openStrip]` | T | OK |
| `stripClosedField_zero` | 593 | a fibre vanishing on the open strip vanishes at the two completed endpoints | `EqOn.of_subset_closure` with continuity | F | OK |
| `stripClosedField_add_period` | 613 | ditto for spatial periods | same | F | OK |
| `lowerClamp` | 636 | `t * smoothTransition (2t+2)`: smooth retraction, identity for `t ≥ -1/2`, lands in `[-1,1]` for `t ≤ 1` | `Real.smoothTransition` lemmas; `:645-657` by `nlinarith`/case split | T/F | OK |
| `clamped`, `clamped_contDiffOn` | 659,663 | precompose with the clamp; `C^∞` on `Gluing.past 1` | composition + `lowerClamp_mem` | T | OK |
| `Gluing.smoothExtension_zero_fiber` | 670 | a fibre zero on the whole past stays zero everywhere after gluing | `extension_zero_of_coefficients_zero` + `normalTrace_eq_time_jet` + `iteratedDerivWithin_congr` | F | OK |
| `upperClosed`(+3) | 688–713 | Borel-extend the clamped field past `t=1`; smooth, equal to `f` on `[-1/2,1]`, preserves zero fibres and periods | `Gluing.smoothExtension_*` | T/F | OK |
| `reflect`, `lowerClosed`(+3) | 715–757 | mirror-image construction below `t=-1` | reflection + `upperClosed_*` | T/F | OK |
| `closedStripExtension` | 761 | `if t ≤ 0 then lowerClosed else upperClosed` | definition | T | OK |
| `closedStripExtension_eq` | 766 | equals `f` on the closed strip | both branches agree with `f` on the overlap `[-1/2,1/2]` | T | OK |
| `closedStripExtension_contDiff` | 775 | globally `C^∞` | trichotomy at `t=0`; **at `t=0` it does not glue at all** — it shows the `if` is *eventually equal* to `upperClosed` on `Ioo(-1/2,1/2)` via `closedStripExtension_eq` + `upperClosed_eq`, so no seam analysis is needed | T | OK — the honest trick is genuine local agreement, not a seam claim |
| `closedStripExtension_zero/_add_period/_zero_parameter` | 793,802,814 | vanishing fibres, periods, and `|t| ≥ 2 ⇒ 0` | branchwise | F | OK |
| `extension` (+`_contDiff`,`_eq`,`_zero_of_fiber`,`_add_period`,`_zero_parameter`,`_iteratedFDeriv`) | 826–870 | from interior smoothness + **uniform jet bounds** on the open strip: a global `C^∞` field equal to `f` inside, vanishing for `|t| ≥ 2`, preserving zero fibres/periods, with the same jets inside | composition of everything above | T/F | OK |

### Dependencies examined (relevant rows only)

| name | file:line | statement | mechanism | in_cone | verdict |
|---|---|---|---|---|---|
| `rightExtension` | `SpatialBorelExtension.lean:475` | `extension a ha (z.1 - T, z.2)` | definition | T | OK |
| `rightExtension_contDiff` | `:477` | globally `C^∞` | `extension_contDiff` ∘ CLM | T | OK |
| `rightExtension_right_jets` | `:487` | one-sided `iteratedDerivWithin k … (Ici T) T = a k x` | `iteratedFDerivWithin_eq_iteratedFDeriv` (the function is smooth on all of ℝ, so one-sided = two-sided) + `rightExtension_time_jets` | T | OK |
| `rightExtension_zero_from` | `:502` | `0` for `t ≥ T+1` | `extension_zero_of_one_le_abs` | T | OK |
| `extension_contDiff` | `:350` | the Borel series is `C^∞` | local congruence with `localizedExtension`, `contDiff_tsum` with the constructed majorant | T | OK |
| `extension_time_jets` | `:409` | `iteratedDeriv k (extension(·,x)) 0 = a k x` | `ContinuousMultilinearMap.tsum_eval` + `iteratedDeriv_term_zero` + `tsum_eq_single` | T | OK |
| `iteratedDeriv_term_zero` | `BorelExtension.lean:139` | `iteratedDeriv k (term b j v) 0 = if k = j then v else 0` | eventual equality with the monomial (cutoff `= 1` near `0`) | T | OK |
| `extendTrace` | `SpacetimeEndpoint.lean:41` | `if z.1 < T then f z else L z.2` | definition | T | OK |
| `hasFDerivWithinAt_extendTrace` | `:139` | the derivative extends to the boundary | `hasFDerivWithinAt_closure_of_tendsto_fderiv` on the convex open past + locally uniform limits | T | OK |
| `hasFTaylorSeriesUpToOn_extension` | `:228` | the limit tensors form a genuine Taylor family on the **closed** past | all three fields proved (`:238-246`) | T | OK |
| `contDiffOn_joint_extension` | `:250` | ⇒ `ContDiffOn ℝ ∞` on the closed past | `.contDiffOn` | T | OK |
| `boundary_jets_eq_limits` | `:277` | the boundary jets are exactly `L x n` | `iteratedFDerivWithin_extension` + `extendTrace_at` | T | OK |
| `VanishingJointJets` | `JointResidualLimits.lean:84` | *all* jets of the residual `→ 0` at `(1,0)` along the open past | **definition of a hypothesis** | T | SUSPICIOUS (assumed, not proved here) |
| `AwayExtensions` / `OneSidedExtension` | `:81` / `:73` | for every `x ≠ 0` there **exists** a smooth field on a neighbourhood of `(1,x)` agreeing with `f` on the past part | **definition of a hypothesis** — i.e. "the residual already continues smoothly through `t=1` away from the axis" | T | SUSPICIOUS (assumed, not proved here) |
| `boundaryLimits` | `:120` | `0` at `x = 0`, otherwise the Taylor series of the chosen one-sided extension | `Classical.choice` on `AwayExtensions` | T | UNCLEAR — jets at the axis point are *defined* to be zero; legitimacy rests entirely on `VanishingJointJets` |
| `force` / `force_smooth` | `CandidateFromLimits.lean:82,86` | the NS force is `smoothExtension 1 (tracedResidual …)`; it is `ContDiff ℝ ∞` | direct application of `smoothExtension_contDiff` | T,T | OK mechanically; conditional on `hu hp hlim` |
| `candidateStatement_of_residual_limits` | `CandidateFromLimits.lean:212` | the headline candidate statement, **conditional** on `hlim`, `hunbounded`, `hdiv`, periodicity | packaging | **False** | UNCLEAR (not the route the cone takes) |

---

## Kernel-risk assessment

**(1) Recursive inductive types / recursor reduction / `Acc.rec` / well-founded unfolding /
structure eta.** Must the kernel do the risky computation? Almost nothing. The only recursive
definitions reachable from this scope are `normalIter` (`SpacetimeGluing.lean:38`,
`GenericEndpointExtension.lean:41`) and `DiagonalScale.doublingEnvelope`
(`DiagonalScale.lean:91-93`), both **structural** on `ℕ` (`Nat.rec`), never applied to a closed
numeral, so at most one iota step per use (`SpacetimeGluing.lean:82,100,112`). There is no
`Acc.rec`, no `termination_by`, no `decreasing_by`, no `WellFounded` in any file I read. Structure
eta for `Prod` is used pervasively and is the only kernel feature the argument leans on. Size:
trivial.

**(2) `Nat` GMP numeral arithmetic (`decide`, `Nat.pow/div/mod/gcd/beq/ble`, huge literals,
`norm_num` certificates).** Zero `decide`/`native_decide` in the whole scope. No `Nat` arithmetic
function is applied to literals; `Nat.factorial` appears only symbolically
(`BorelExtension.lean:26,40`, `SpatialBorelExtension.lean:437`). All numeral goals are single-digit
rationals discharged by `norm_num`/`linarith`/`nlinarith`/`omega`
(`GenericEndpointExtension.lean:450,576,588,648,655,784`; `DiagonalScale.lean:110,119,127`), so the
certificates the kernel recomputes are of size O(1). Size: trivial.

**(3) Custom metaprogramming.** Grep for `macro|macro_rules|elab|syntax|set_option|native_decide|
axiom|unsafe|partial|sorry` over both in-scope files returns **0 matches** (also 0 in
`SpatialBorelExtension.lean`, `BorelExtension.lean`, `SpacetimeEndpoint.lean`,
`CandidateFromLimits.lean`, `JointResidualLimits.lean`). No finding.

Net: **this scope is not where a kernel exploit lives.** The risk here is ordinary mathematics
(assumed analytic inputs), not kernel trust.

---

## Escalations (ranked)

**E1 — The whole "force is smooth through the blowup" reduces to two ASSUMED analytic inputs.**
`JointResidualLimits.lean:81` (`AwayExtensions`) and `:84` (`VanishingJointJets`), consumed via
`MixedPeriodicAssembly.lean:343-346` to produce `hlim` for `CandidateFromLimits.lean:39-41`, whose
`force` (`:82`) and `force_smooth` (`:86`) are then unconditional-looking.
*Precise question for the expert:* `AwayExtensions (originalResidual A v p)` literally assumes the
NS residual of the candidate has a genuine `C^∞` extension to a full neighbourhood of `(1,x)` for
every `x ≠ 0` (`OneSidedExtension`, `:73-79`). Is that assumption discharged for the actual
candidate anywhere (`SlowBaseEndpoint.lean:364,422,439`, `MixedDiagonalExtensions.lean:205`,
`OffplaneCorrectionExtensions.lean:1059-1061`, `LocalScheduleWitness.lean:49-105`), and is it
discharged *without* circularity (i.e. not by invoking the very smooth continuation it is meant to
provide)? *What would settle it:* an unconditional proof of `AwayExtensions` and
`VanishingJointJets` for the constructed fields, checked for whether it secretly assumes the
residual is zero/flat near `t=1`, plus a `#print axioms` on the final theorem in a real build.

**E2 — The boundary jets at the axis point are DEFINED to be zero.**
`JointResidualLimits.lean:120-128`: `boundaryLimits f hext 0 n = 0` by `dif_pos`, with
`VanishingJointJets` (`:84`) as the only justification, and note that `VanishingJointJets` is stated
at the **single point** `(1, (0 : Space))` — not on the whole terminal slice.
*Precise question:* is the joint limit at `(1,0)` genuinely enough, given that
`boundaryLimits_locallyUniform` (`:148`) then claims *locally uniform* convergence in `x` around
**every** `x`, using the away-extension jets for `x ≠ 0`? The topological step
(`locallyUniform_of_joint_limits`, `:55-63`) looks correct, but it consumes
`Tendsto F (p ×ˢ 𝓝 x)` which at `x = 0` is exactly the strong hypothesis. *What would settle it:*
an expert check that `VanishingJointJets` as stated (product filter at one point) is what the
manuscript actually proves about the residual, and is not a weaker/one-point surrogate for a
slice-wide flatness statement.

**E3 — Two Mathlib API steps I cannot type-check without a build.**
`SpacetimeGluing.lean:274` `contDiff_succ_iff_fderiv_apply` with the middle field discharged by
`by simp` (`:275`), and `SpacetimeGluing.lean:71-73`
`(hf z hz).isSymmSndFDerivWithinAt (by simp [minSmoothness_of_isRCLikeNormedField]) hs (hregular hz) hz`.
*Precise question:* does the `by simp` at `:275` close a genuinely trivial side goal (for
`n = (m : ℕ)` the analyticity clause of `contDiff_succ_iff_fderiv*` is vacuous) rather than a real
smoothness obligation, and does `isSymmSndFDerivWithinAt` really apply at a **boundary** point of
`past T` with only `s ⊆ closure (interior s)`? *What would settle it:* `lake build` of this file
plus `#check` of the two lemma signatures at the pinned Mathlib rev; the Schwarz side condition is
the only place where the "no mixed-tensor assumption" claim (`:291-293`) could quietly fail.

**E4 — `smoothExtension`/`force` are definitions that take proof terms as arguments.**
`SpacetimeGluing.lean:339` (`hf : ContDiffOn ℝ ∞ f (past T)` is a *definitional* argument) and
`CandidateFromLimits.lean:82-84` (`force u p hu hp L hlim`). This is sound (proof irrelevance) but
means there is **no unconditional force object** in the development: every downstream statement
about "the force" is parameterised by the analytic hypotheses. *Precise question:* does the final
target theorem quantify these away correctly, or does some statement read as unconditional while
its subject term embeds `hlim`? *What would settle it:* the exact statement + hypotheses of the
top-level theorem, and confirmation that `candidateStatement_of_residual_limits`
(`CandidateFromLimits.lean:212`, `in_cone=False`) is not the advertised deliverable.

**E5 — `GenericEndpointExtension.closedField_contDiffOn` needs GLOBAL jet bounds.**
`GenericEndpointExtension.lean:541-543`, hypothesis
`hb : ∀ n, ∃ C, ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C`, i.e. every derivative uniformly bounded over
the **whole** (unbounded, since `s = Ioo(-1,1) ×ˢ univ`) strip. *Precise question:* for the callers
(`InitialHarmonicContinuation.lean:590`, `OffplaneJetExtensions.lean:76,118`) is `hb` proved on the
unbounded strip, or only on compact spatial sets (which would not suffice for this lemma as
stated)? *What would settle it:* reading the `hb` supplied at those call sites.

**E6 — Dead advertising.** `SpacetimeGluing.lean:400`
`exists_smooth_periodic_extension_of_limits` carries the grand docstring ("A complete constructive
endpoint theorem…", `:396-399`) but is `in_cone=False`. Low severity, but it is the theorem a
reader would check first, and it is not the one the proof uses.

---

## Residue (what I could NOT check, and why)

1. **No type-checking at all.** No Mathlib build on this box (instructed not to run `lake`), so I
   cannot confirm that any lemma name exists, that any `simp only [...]` closes its goal, that the
   `omit …` lines are legal, or that the files compile. All verdicts are "the statement says X and
   the tactic script is a plausible, structurally correct proof of X".
2. **No `#print axioms`.** I cannot rule out `sorryAx`/`Classical.choice`-beyond-choice or an
   `axiom` introduced in a *different* file that leaks in through the import closure. I only verified
   textually that the audited files declare no axioms.
3. `ProblemStatement.Space`/`SpaceTime` were taken on trust as `EuclideanSpace ℝ (Fin 3)` and
   `ℝ × Space`; I did not open `ProblemStatement.lean`. If `Space` were degenerate (e.g. a
   0-dimensional or trivial type) several statements would be vacuous — **worth a 2-minute check by
   whoever owns that file.**
4. `PastExtension.pastResidual`, `pastResidual_derivative_recurrence`,
   `pastResidual_locallyUniform_limit` (`CandidateFromLimits.lean:53,55`) and
   `navierStokesResidual` itself were not audited: whether the "residual" is the true NS residual is
   another worker's scope. If it is not, everything above is smoothness of the wrong object.
5. `SpatialBorelExtension.lean` was read fully, but `BorelExtension.lean:175-380` and
   `SpacetimeEndpoint.lean:300-389` were only skimmed (bounds/packaging lemmas of the same shape as
   ones I did read in full).
6. Whether `VanishingJointJets`/`AwayExtensions` are actually *provable* for the candidate
   (`MixedDiagonalResidual.lean:186`, `GlobalBaseError.lean:202`, `SlowBaseEndpoint.lean:364`) is
   outside my file scope — that is E1 and belongs to the workers on those files.
