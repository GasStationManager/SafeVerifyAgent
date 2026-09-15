# Worker report: does FORCE (compact support + smoothness) or DIVERGENCE-FREE depend on a wave existing?

Repo: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5). READ-ONLY. No `lake build`
(no Mathlib built). All claims below are from source text at the cited `file:line`.

## TL;DR

- **(i) FORCE — compact spatial support: NO dependence on the wave tower whatsoever.** Compact support is *imposed
  by multiplying by two fixed smooth cutoffs* (one in `x`, one in `t`), and the compactness proof consumes only
  "`K` is compact" + "`f` vanishes off `K`", the latter itself being a one-line `simp` on the cutoff. The module
  that proves it (`NavierStokes/R3/PositiveTimeForce.lean`) imports **nothing** from the construction —
  only `NavierStokes.R3.ProblemStatement` and `NavierStokes.SmoothCutoffs`. The statements are true verbatim for
  `f = 0`. **Force smoothness through `t = 1`: also independent of the wave tower** — it is a Whitney/Borel gluing
  theorem (`SpacetimeGluing.smoothExtension_contDiff`) applied to the traced residual, whose only inputs are
  (a) smoothness of velocity/pressure on the *open/pre-singular* past and (b) existence of locally uniform limits
  of all residual derivatives at `t → 1⁻` (in the actual pipeline: `VanishingJointJets`, i.e. all residual jets
  tend to **0**). Nothing supplies "at least one wave" and nothing needs to.
- **(ii) DIVERGENCE-FREE: proved structurally / termwise, so an empty (all-zero) tower is trivially divergence
  free.** Two summands: the potential part is `spatialCurl` of something, killed by `div ∘ curl = 0`; the angular
  part is killed termwise over a *finite* `Finset.range N` by the azimuthal-ansatz identity `divergence_rotationField`.
  Neither needs an inhabitant of `Index`/`Label`. Both hold for the zero field.
- **Force nontriviality is never an input.** `f ≠ 0` is only ever *derived*, and derived from the blow-up
  (`speed_unbounded`) by uniqueness. So the force's non-triviality rides entirely on the velocity blow-up claim.

---

## 0. The two headline force requirements (what must be proved)

`NavierStokes/R3/ProblemStatement.lean:92-109` (the whole-space Theorem 1.1 record):

```lean
structure CandidateProperties (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain
  pressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain
  support_compact : IsCompact K
  velocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => u (t, x)) ⊆ K
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => p (t, x)) ⊆ K
  force_smooth : ContDiff ℝ ∞ f
  force_support : CompactPositiveTimeSupport f
  zero_initial_velocity : ∀ x : Space, u (0, x) = 0
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    NavierStokes.ProblemStatement.spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    navierStokesResidual ν u p t x = f (t, x)
  energy_bounded : UniformFiniteEnergy (Ico 0 1) u
  speed_unbounded : SpeedUnboundedAtOne u
```

with, at `NavierStokes/R3/ProblemStatement.lean:66-67`:

```lean
def CompactPositiveTimeSupport (f : VelocityField) : Prop :=
  HasCompactSupport f ∧ tsupport f ⊆ positiveTimeDomain
```

and `positiveTimeDomain := Ioi 0 ×ˢ univ` (`:53`). So the two demands are exactly
`ContDiff ℝ ∞ f` (global, hence through and past `t = 1`) and `HasCompactSupport f ∧ tsupport f ⊆ {t>0}`.

Note `preSingularDomain := Ico 0 1 ×ˢ univ` (`NavierStokes/ProblemStatement.lean:42`): the *velocity* is never
claimed smooth at `t = 1`. Only the force is.

Note also the *periodic* record used inside the construction, `NavierStokes/ProblemStatement.lean:101-114`, which
does **not** ask for compact spatial support at all — only `CompactFutureTimeSupport f`
(`:89-90`, "`∃ T, 0 ≤ T ∧ ∀ t ≥ T, ∀ x, f (t,x) = 0`"), with the docstring at `:87-88` saying explicitly
"Spatial support is not required to be compact in the lift." The compact spatial support is manufactured later,
in step 2 below.

## 1. Where the force is defined (the candidate's own residual)

`NavierStokes/CandidateFromLimits.lean:80-87` (verbatim, def at `:82` as flagged):

```lean
/-- The specified force: glue the traced past residual to the Taylor--Borel
series of its actual normal jets. No force is an input to this definition. -/
def force : VelocityField :=
  SpacetimeGluing.smoothExtension 1 (tracedResidual u p L)
    (tracedResidual_smooth u p hu hp L hlim)

theorem force_smooth : ContDiff ℝ ∞ (force u p hu hp L hlim) :=
  SpacetimeGluing.smoothExtension_contDiff (tracedResidual_smooth u p hu hp L hlim)
```

Section variables (`:35-43`): `u p`, `hu : ContDiffOn ℝ ∞ u preSingularDomain`,
`hp : ContDiffOn ℝ ∞ p preSingularDomain`, `L : Space → FormalMultilinearSeries ℝ SpaceTime Space`, and

```lean
variable (hlim : ∀ n : ℕ, TendstoLocallyUniformly
  (fun t x => iteratedFDeriv ℝ n (fun z => navierStokesResidual u p z.1 z.2) (t, x))
  (fun x => L x n) (𝓝[<] (1 : ℝ)))
```

So `force` is a function of `(u, p, L)` plus two smoothness/limit certificates. **There is no wave, no `Index`,
no `Label`, and no oscillation anywhere in this definition or in `force_smooth`.**

Two further facts about this force, both structural:

- `force_zero_from` (`:114-117`): `2 ≤ t → force … (t,x) = 0`, by `SpacetimeGluing.smoothExtension_zero_from`;
- `force_time_support` (`:124-125`): `CompactFutureTimeSupport (force …) := ⟨2, by norm_num, …⟩`.

And the periodic candidate is assembled at `:167-182` with `divergence_free` supplied as an **input hypothesis**
`hdiv : ∀ t ∈ Ico (0:ℝ) 1, ∀ x, spatialDivergence u t x = 0` (`:170`), passed to
`activatedVelocity_divergence_free u hu hdiv` (`:177`).

### 1a. Where "smooth through `t = 1`" actually comes from

`NavierStokes/SpacetimeGluing.lean:339-352`:

```lean
def smoothExtension (T : ℝ) (f : SpaceTime → V) (hf : ContDiffOn ℝ ∞ f (past T)) :
    SpaceTime → V :=
  glue T f (SpatialBorelExtension.rightExtension (normalTrace T f)
    (normalTrace_contDiff hf) T)

theorem smoothExtension_contDiff {T : ℝ} {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (past T)) : ContDiff ℝ ∞ (smoothExtension T f hf) := by
  apply contDiff_glue hf
    (SpatialBorelExtension.rightExtension_contDiff (normalTrace T f)
      (normalTrace_contDiff hf) T).contDiffOn
  intro n x
  rw [SpatialBorelExtension.rightExtension_right_jets]
  exact (normalTrace_eq_time_jet hf n x).symm
```

The *only* hypothesis is `ContDiffOn ℝ ∞ f (past 1)`, i.e. closed-past smoothness of the traced residual. That in
turn is `CandidateFromLimits.tracedResidual_smooth` (`:47-55`), which is proved from
`PastExtension.pastResidual_derivative_recurrence` + `PastExtension.pastResidual_locallyUniform_limit … (hlim n)`.

In the actual pipeline the jets `L` are `MixedPeriodicAssembly.boundaryLimits` and `hlim` is
`boundaryLimits_locallyUniform hz eA ev ep` (`NavierStokes/MixedPeriodicAssembly.lean:310-320`,
used at `:359-363`), where

```lean
hz : JointResidualLimits.VanishingJointJets (originalResidual A v p)
```

and (`NavierStokes/JointResidualLimits.lean:84-86`)

```lean
def VanishingJointJets (f : SpaceTime → V) : Prop :=
  ∀ n : ℕ, Tendsto (iteratedFDeriv ℝ n f)
    (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))) (𝓝 0)
```

i.e. **every** residual jet tends to **zero** at the endpoint (and only at the axis point `(1,0)`; other `x` are
handled through `AwayExtensions`). Indeed `MixedPeriodicAssembly.lean:275-281`:

```lean
@[simp] theorem boundaryLimits_zero … : boundaryLimits A v p eA ev ep 0 n = 0
```

**Verdict on the sub-question "does smoothness through `t=1` come from the base profile or the correction tower":
neither.** The base fields `A, v, p` are only assumed `ContDiffOn ℝ ∞ … (SpacetimeEndpoint.openPast 1)`
(`MixedPeriodicAssembly.lean:339-341`) — nobody claims they are smooth *at* `t = 1`. The force's smoothness at and
past `t = 1` is produced by the gluing/Borel machinery from the *flatness* (vanishing) of the residual jets. The
tower's role is only to make the residual jets vanish quantitatively (a smallness/gain statement); if the tower
were empty and every field were `0`, the residual would be identically `0`, its jets would vanish trivially, and
`force_smooth` would still hold — with `force = 0`.

## 2. Compact spatial support of the force is imposed by cutoffs (wave-free)

Step A — a *spatial* cutoff is multiplied onto the force. `NavierStokes/R3CompactCandidate.lean:39-41, 88, 94-97`:

```lean
def outerCutoff (x : Space) : ℝ := spatialCutoff ((1 / 2 : ℝ) • x)
def outerSupport : Set Space := (fun x : Space => (2 : ℝ) • x) '' supportCylinder
…
def compactForce (f : VelocityField) : VelocityField := fun z => outerCutoff z.2 • f z
…
theorem compactForce_supported (f : VelocityField) :
    CompactSpatialForceDecay.SupportedIn outerSupport (compactForce f) := by
  intro t ht x hx
  simp [compactForce, outerCutoff_zero_outside hx]
```

`supportCylinder` is a *fixed geometric set* (`NavierStokes/SpatialLocalization.lean:72-73`:
`{x | radialSquare x ≤ 1 / 16 ∧ |x 2| ≤ 1 / 4}`), and `outerSupport_compact`
(`R3CompactCandidate.lean:43-44`) is `isCompact_supportCylinder.image (by fun_prop)`. No field content enters.

Step B — a *time* cutoff. `NavierStokes/R3/PositiveTimeForce.lean:21-22, 46-51, 61-80`:

```lean
def timeCutoff (t : ℝ) : ℝ :=
  NavierStokes.SmoothCutoffs.cutoff ((8 / 5 : ℝ) * (t - 11 / 16))
…
def force (f : VelocityField) : VelocityField :=
  fun z => timeCutoff z.1 • f z

theorem force_contDiff {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (force f) :=
  (timeCutoff_contDiff.comp contDiff_fst).smul hf
…
theorem force_tsupport_subset {f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hf : ∀ t x, x ∉ K → f (t, x) = 0) :
    tsupport (force f) ⊆ Icc (1 / 16 : ℝ) (21 / 16) ×ˢ K := by
  apply closure_minimal _ (isClosed_Icc.prod hK.isClosed)
  rintro ⟨t, x⟩ hz
  constructor
  · by_contra ht
    exact hz (by simp only [force, timeCutoff_eq_zero ht, zero_smul])
  · by_contra hx
    exact hz (force_eq_zero (hf t x hx))

theorem force_compactPositiveTimeSupport {f : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hf : ∀ t x, x ∉ K → f (t, x) = 0) :
    CompactPositiveTimeSupport (force f) := by
  have hs := force_tsupport_subset hK hf
  constructor
  · exact (isCompact_Icc.prod hK).of_isClosed_subset isClosed_closure hs
  · intro z hz
    have ht := (hs hz).1.1
    exact ⟨by change 0 < z.1; linarith, mem_univ _⟩
```

**The entire hypothesis set of the compact-support theorem is `IsCompact K` and `∀ t x, x ∉ K → f (t,x) = 0`.**
`f` is otherwise arbitrary; the theorem is true for `f = 0`. Dependency check: the header of
`NavierStokes/R3/PositiveTimeForce.lean:1-2` is exactly

```lean
import NavierStokes.R3.ProblemStatement
import NavierStokes.SmoothCutoffs
```

and `NavierStokes/SmoothCutoffs.lean:1-8` imports only Mathlib. So the module proving force compact support
has **zero** transitive dependency on the wave/correction tower, `Index`, `Label`, `CellIndex`, or oscillation.

Step C — where the two are used in the headline record. `NavierStokes/R3/ActualCandidate.lean:86-89` and `:109-110`:

```lean
  have hc := R3CompactCandidate.of_localized_fields h
  have hF := PositiveTimeForce.force_contDiff (compactForce_smooth hf)
  have hsupport := PositiveTimeForce.force_compactPositiveTimeSupport
    R3CompactCandidate.outerSupport_compact (compactForce_supported_all_times f)
…
    force_smooth := hF
    force_support := hsupport
```

with the local wrappers at `:67-74`:

```lean
theorem compactForce_smooth {f : VelocityField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (R3CompactCandidate.compactForce f) :=
  (R3CompactCandidate.outerCutoff_smooth.comp contDiff_snd).smul hf

theorem compactForce_supported_all_times (f : VelocityField) (t : ℝ) (x : Space)
    (hx : x ∉ R3CompactCandidate.outerSupport) :
    R3CompactCandidate.compactForce f (t, x) = 0 := by
  simp [R3CompactCandidate.compactForce, R3CompactCandidate.outerCutoff_zero_outside hx]
```

`hf : ContDiff ℝ ∞ f` is the `ContDiff ℝ ∞ forcing` conjunct of
`ActualCandidateAssembly.selected_witness` (`NavierStokes/ActualCandidateAssembly.lean:1138`,
obtained at `R3/ActualCandidate.lean:131-133`), which is `CandidateFromLimits.force_smooth` from §1.

Sanity check that the multiplicative cutoff does not silently break the PDE: `R3CompactCandidate.lean:139-160`
(`local_model_equation`) shows the equation still holds pointwise, by proving `f (t,x) = 0` at the awkward points
(`x ∉ supportCylinder` but `outerCutoff x ≠ 0`) from the residual vanishing there (`:151-160`). Again purely
local/structural, no wave input.

### (i) VERDICT

**Force compact spatial support: entirely independent of the wave tower** — it is a cutoff multiplication whose
proof takes only `IsCompact K` + "vanishes off `K`", from a module with no construction imports.
**Force smoothness through `t = 1`: also independent** — Whitney/Borel gluing of the traced residual, driven by
*vanishing* residual jets. Both would be proved identically if `Index`/`Label` were empty and every field were
`0`; in that case `force = 0`, which still satisfies `ContDiff ℝ ∞ 0` and `CompactPositiveTimeSupport 0`. So yes:
in the degenerate/empty case the residual is smooth and compactly supported *because the oscillation contributes
`0`* — the force clauses of Theorem 1.1 carry no information about the tower being inhabited.

## 3. Divergence-free: structural, termwise, wave-free

The candidate velocity is `TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity ASum BSum)`
(`ActualCandidateAssembly.lean:1136`). Chain, innermost first.

(a) Activation is a scalar multiple in time — `NavierStokes/TimeLocalization.lean:27-28, 119-125`:

```lean
def activatedVelocity (u : VelocityField) : VelocityField :=
  fun z => timeSwitch z.1 • u z
…
theorem activatedVelocity_divergence_free (u : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence (activatedVelocity u) t x = 0 := by
  intro t ht x
  rw [activatedVelocity_divergence u hu t ht x, hdiv t ht x, mul_zero]
```

(b) Splitting the two summands — `NavierStokes/MixedPeriodicAssembly.lean:147-164`:

```lean
theorem periodicVelocity_divergence_free {A v : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (times ×ˢ (univ : Set Space)))
    (hd : ∀ t ∈ times, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    {t : ℝ} (ht : t ∈ times) (x : Space) :
    spatialDivergence (periodicVelocity A v) t x = 0 := by
  …
  rw [spatialDivergence_add
    (hleft.differentiable (by simp) x) (hright.differentiable (by simp) x),
    SpatialLocalization.periodicVelocity_divergence_free hA ht x,
    periodize_divergence_free (SpatialLocalization.cutPotential_supported v) t (hd t ht) x,
    add_zero]
```

(c) Summand 1 = `div ∘ curl = 0`. `NavierStokes/SpatialLocalization.lean:210-214, 258-262`:

```lean
noncomputable def periodicPotential (A : VelocityField) : VelocityField :=
  PeriodicLocalization.periodize (cutPotential A)

noncomputable def periodicVelocity (A : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (periodicPotential A)
…
theorem periodicVelocity_divergence_free {A : VelocityField} {times : Set ℝ}
    (hA : ContDiffOn ℝ ∞ A (times ×ˢ (univ : Set Space))) {t : ℝ}
    (ht : t ∈ times) (x : Space) : spatialDivergence (periodicVelocity A) t x = 0 :=
  SpatialCurl.spatialDivergence_spatialCurl_on
    ((periodicPotential_smoothOn hA).of_le (nat_le_infty 2)) ht x
```

Hypothesis: `C²` of the potential. Nothing else. True for `A = 0`.

(d) Summand 2 = periodized angular field; periodization is reduced to one local copy
(`MixedPeriodicAssembly.lean:119-135`, `periodize_divergence_free`, hypothesis = "SupportedInCube" +
div-free on one copy), and the local `hd` is supplied by
`LocalAngularDiagonal.spatialCut_angularSum_divergence` (used at `GermCandidateAssembly.lean:262-263`,
`MixedCandidateAssembly.lean:199`, `MixedCandidateWitness.lean:140`), which reduces to
`DirectAngularDiagonal.spatialCut_angularSum_divergence` (`NavierStokes/DirectAngularDiagonal.lean:459-469`)
and then to `angularSum_divergence` (`:291-313`):

```lean
  obtain ⟨N, hN⟩ := angularSum_eventuallyEq_partial ha hqAt.continuousAt (hpos x hx)
    (fun j => (D j).scalar)
  rw [divergence_congr hN]
  …
  rw [divergence_finset_sum _ _ x (fun j _ => hs j)]
  apply Finset.sum_eq_zero
  intro j _
  exact divergence_cut_angular hU (D j) (a j) q hq hx
```

That is literally **`Finset.sum_eq_zero` over a finite prefix `Finset.range N`, each term zero**. The per-term
lemma is the azimuthal-ansatz identity `DirectAngularDiagonal.field_divergence` (`:175-183`):

```lean
theorem field_divergence (hU : IsOpen U) {w : SpaceTime} (hw : w ∈ physicalDomain U) :
    spatialDivergence (angularField D.scalar) w.1 w.2 = 0 := by
  by_cases hr : 0 < radius w
  · rw [angularField_eq_rotationField]
    exact divergence_rotationField ((rate_smoothAt hU D.smooth hw hr).differentiableAt (by simp))
  · have hz : radius w = 0 := …
```

i.e. "an azimuthal (rotation) field has zero divergence, for any smooth scalar rate".

### (ii) VERDICT

**Divergence-free does not require a wave.** It is proved (1) by `div ∘ curl = 0` for the potential part, (2)
termwise over a *finite* `Finset.range N` for the angular part, each term by a rotation-field identity, (3) with
periodization and time-activation preserving it by congruence/scalar multiplication. Every hypothesis is a
smoothness or support hypothesis; no clause anywhere asks for an inhabitant of `Index`, `Label`, or `CellIndex`.
An empty tower (all stage fields `= 0`) satisfies `divergence_free` trivially — cf. the artifact's own
`zero_force_has_global_solution` at `NavierStokes/R3/ProblemStatement.lean:189-203`, where `divergence_free` for
the zero field is closed by `simp [spatialDivergence, spatialDerivative]`.

## 4. Is the force nonzero? Does anything require it?

Nothing *requires* a nonzero force as an input. Non-triviality is only ever **derived, from the blow-up**:

- `NavierStokes/MaximalLifespan.lean:273-290`:

```lean
/-- The specified force must be nonzero somewhere before the breakdown
time. Otherwise uniqueness identifies the candidate with the zero solution. -/
theorem candidate_force_nonzero_before_one {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, f (t, x) ≠ 0 := by
  by_contra hnot
  …
  apply unbounded_speed_excludes_uniform_bound h.speed_unbounded
```

  and it is packaged as `Consequences.force_nonzero` (`NavierStokes/CandidateConsequences.lean:140`), proved by
  `consequences_of_candidate` (`:144-149`) as `MaximalLifespan.candidate_force_nonzero_before_one h`.

- `NavierStokes/R3/CandidateBreakdown.lean:51-62`:

```lean
theorem force_nonzero_of_no_global_solution {ν : ℝ} {f : VelocityField}
    (hf : CompactPositiveTimeSupport f)
    (h : ¬ Nonempty (GlobalFiniteEnergySolution ν f)) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : Space, f (t, x) ≠ 0 := by
  have hne : f ≠ fun _ => 0 := by
    intro he
    subst f
    exact h (zero_force_has_global_solution ν)
```

Both are contrapositives of `speed_unbounded` / "no global solution". Consequence: **if the wave tower is empty
and the velocity does not actually blow up, then `f = 0` is perfectly consistent with every force clause** of
`CandidateProperties` — and `R3/ProblemStatement.lean:189-214` (`zero_force_has_global_solution`) then hands you a
global finite-energy solution, so the `breakdownStatement` conjunct is what fails, not any force-regularity or
divergence clause.

## 5. Summary table

| clause | proof mechanism | needs a wave? |
|---|---|---|
| `force_smooth : ContDiff ℝ ∞ f` | `SpacetimeGluing.smoothExtension_contDiff` (Whitney glue + Borel right-extension) ∘ two cutoff multiplications | **No** |
| `force_support : HasCompactSupport f ∧ tsupport f ⊆ {t>0}` | `outerCutoff z.2 • ·` then `timeCutoff z.1 • ·`; `force_compactPositiveTimeSupport` takes only `IsCompact K` + vanishing off `K` | **No** |
| `CompactFutureTimeSupport` (periodic lift) | `⟨2, by norm_num, smoothExtension_zero_from⟩` | **No** |
| `divergence_free` | `div ∘ curl = 0` + `Finset.sum_eq_zero` over `range N` of rotation fields + periodization congruence + `timeSwitch` scaling | **No** |
| `f ≠ 0` | derived from `speed_unbounded` by uniqueness; never assumed | rides on blow-up only |

## 6. Caveats / limits of this audit

- No `lake build` was possible (no built Mathlib), so this is a source-level audit: I read the actual statements
  and proof terms/tactics, not the elaborated proofs. I did not verify that the cited lemmas typecheck.
- I did not chase `VanishingJointJets`'s ultimate provenance to the leaf estimates. It is produced by
  `StageEstimates.exists_schedule` (`NavierStokes/MixedCandidateAssembly.lean:67-91`) out of the `gain` /
  `residualLoss` bookkeeping fields (`:34-65`), a purely quantitative schedule argument. Whether *that* chain is
  vacuous when `Index` is empty is a separate question (and is the parent's other thread); either way it does not
  change the (i)/(ii) verdicts, which are about clauses whose proofs are structural.
- `VanishingJointJets` is stated only at the single endpoint `(1, 0)` (`JointResidualLimits.lean:84-86`); other
  spatial points are covered by `AwayExtensions`. Worth a separate look if someone audits the jet limits.
