# NS deliverable spine — read-only audit (worker: ns-spine)

Target: `/home/gsm/.openclaw/workspace/repos/NSE` @ f9e8bc5 (clone of openai/NavierStokesAndEuler).
Nothing under that path was modified. No `lake build` was run (no built Mathlib on this box);
this is **source-level reading** of actual statements and actual proof terms/tactics.
Every line citation below was read in the ORIGINAL file (line numbers verified by re-reading).

## Scope

Root: `NavierStokes.lean:1-2` imports exactly `NavierStokes.ComparatorSolution` and
`NavierStokes.PaperResults`. `PaperResults.lean` is a 4-line import hub (0 declarations).

Files read **line by line, in full** (19 files, 167 decls counted by
`theorem|lemma|def|structure|inductive|abbrev|instance` on comment-stripped text):

| file | decls | read |
|---|---|---|
| `NavierStokes.lean` | 0 | full (2 lines) |
| `NavierStokes/PaperResults.lean` | 0 | full (4 lines) |
| `NavierStokes/ComparatorSolution.lean` | 2 | full |
| `NavierStokes/PeriodicComparatorSolution.lean` | 1 | full |
| `NavierStokes/ComparatorDefinitions.lean` | 16 | full + byte-diffed vs challenge |
| `ComparatorChallenges/NavierStokes.lean` | 18 | full + byte-diffed vs copy |
| `NavierStokes/ComparatorR3Theorem.lean` | 2 | full |
| `NavierStokes/ComparatorTheorem.lean` | 2 | full |
| `NavierStokes/ComparatorBridge.lean` | 27 | full |
| `NavierStokes/ComparatorR3Bridge.lean` | 4 | full |
| `NavierStokes/R3/ComparatorBridge.lean` | 3 | full |
| `NavierStokes/PeriodicPaperComparator.lean` | 3 | full |
| `NavierStokes/ProblemStatement.lean` | 25 | full |
| `NavierStokes/R3/ProblemStatement.lean` | 25 | full |
| `NavierStokes/R3/Theorem.lean` | 6 | full |
| `NavierStokes/R3/CandidateBreakdown.lean` | 4 | full |
| `NavierStokes/PeriodicPaperTheorem.lean` | 7 | full |
| `NavierStokes/CompactSpatialForceDecay.lean` | 6 | full |
| `NavierStokes/CandidateConsequences.lean` | 16 | lines 20-135 full, 136-217 skimmed |

Skimmed only (statement + entry proof read, not the internals):
`NavierStokes/PeriodicViscosity.lean:24-70`, `NavierStokes/MaximalLifespan.lean:230-292`.

Whole-closure instrument work (grep/python over the import closure of `NavierStokes.lean`:
**753 local modules, 404 520 lines**) is reported in "Kernel-risk assessment".

Two sub-branches were delegated to read-only children and are reported separately:
`ns-spine-r3branch.md` (the `ActualCandidate` / `WholeSpaceUniqueness` construction) and
`ns-spine-periodicbranch.md` (the periodization + `PeriodicViscosityUniqueness` chain).

## The live proof path (short version)

The two deliverables are reached by a **short, entirely readable** adapter chain. Both
final theorems are `exact` one-liners; there is no place in the adapter chain where the
negated proposition could be altered.

```
Comparator.navier_stokes_breakdown_R3        ComparatorSolution.lean:16-20
  = ComparatorBridge.navier_stokes_breakdown_R3   ComparatorR3Theorem.lean:38-44
      <- NavierStokesR3.theorem_1_1                R3/Theorem.lean:46
           <- theorem_1_1_with_initial_rest        R3/Theorem.lean:26
                <- ActualCandidate.selected_candidate_one_with_initial_rest   [child A]
                <- ViscosityScaling.candidate_at_viscosity / normalized_global_solution
                <- CandidateProperties.no_global_solution_one  R3/CandidateBreakdown.lean:43
      <- NavierStokesR3.comparator_of_breakdown    R3/ComparatorBridge.lean:77
           <- zero_initial_condition_decay         ComparatorR3Bridge.lean:18
           <- forceConditionDecay_of_compact       R3/ComparatorBridge.lean:22
                <- CompactSpatialForceDecay.forceConditionDecay  CompactSpatialForceDecay.lean:85
           <- globalSolutionOfComparator           R3/ComparatorBridge.lean:48

Comparator.navier_stokes_breakdown_periodic   ComparatorSolution.lean:23-27
  = ComparatorBridge.navier_stokes_breakdown_periodic  ComparatorTheorem.lean:47-53
      <- PeriodicPaper.periodic_corollary          PeriodicPaperTheorem.lean:155
           <- NavierStokesR3.theorem_1_1_with_initial_rest   (SAME R3 construction)
           <- ParabolicScaling.compressedCandidate + of_compact_candidate (periodize)
           <- CandidateProperties.no_global_solution  PeriodicPaperTheorem.lean:65
                <- PeriodicViscosity.excludes_global_solution  PeriodicViscosity.lean:24
      <- ComparatorBridge.option_D_of_paper_candidate  PeriodicPaperComparator.lean:45
           <- zero_initial_condition               ComparatorBridge.lean:136
           <- forceConditionPeriodic_of_paper_candidate  PeriodicPaperComparator.lean:21
                <- forceConditionPeriodic_of_decay  ComparatorBridge.lean:117
                <- CandidateConsequences.futureJet_decay  CandidateConsequences.lean:79
           <- periodicPaperSolution_of_comparator  PeriodicComparatorSolution.lean:20
```

**Finding S1 (structural, important).** Both deliverables rest on ONE construction:
`PeriodicPaper.periodic_corollary` (`PeriodicPaperTheorem.lean:157-158`) obtains its fields
from `NavierStokesR3.theorem_1_1_with_initial_rest`, i.e. the whole-space candidate, and then
periodizes it. So a defect in the single R3 candidate breaks (C) **and** (D). Verdict:
[OK] as engineering, but it concentrates all risk in one place and both "independent"
deliverables are NOT independent.

**Finding S2.** Several bridge theorems are dead weight w.r.t. the final theorems and should
not be audited as load-bearing: `ComparatorR3Theorem.lean:21 option_C_of_compact_candidate`,
`ComparatorTheorem.lean:25 option_D_of_candidate`, `ComparatorBridge.lean:217
normalized_solution`, `ComparatorR3Bridge.lean:50 normalized_solution_Rn`,
`ComparatorBridge.lean:192 GlobalSolutionOne`, `ComparatorR3Bridge.lean:25 GlobalSolutionRn`.
These are the *viscosity-rescaling* route (`rescaledForce ν f`). The live path does **not**
rescale the force: `comparator_of_breakdown` (`R3/ComparatorBridge.lean:85`) and
`option_D_of_paper_candidate` (`PeriodicPaperComparator.lean:52`) exhibit `toComparator f`
with the SAME `ν` throughout. Good: no viscosity sleight of hand on the live path.

## Answers to the specific questions

### Q1. Which initial datum + force pair is exhibited?

* **Initial datum: literally `fun _ => 0`** in both branches
  (`R3/ComparatorBridge.lean:85`, `PeriodicPaperComparator.lean:52`). This is legitimate:
  Clay (C)/(D) quantify existentially over `u₀` subject to the initial conditions, and the
  zero field satisfies them. All content sits in `f`.
  - `zero_initial_condition_decay` (`ComparatorR3Bridge.lean:18-22`): `div_free` from
    `Comparator.divergence_const`, `smooth` from `contDiff_const`, `decay` by `⟨0, by simp⟩`
    (`iteratedFDeriv` of a constant is 0 for every order, RHS `0/(1+‖x‖)^K = 0`). [OK]
  - `zero_initial_condition` (`ComparatorBridge.lean:136-142`): periodicity by `rfl`. [OK]
* **Force: `toComparator f`** where `f` is the candidate's own force — for (C) the R3
  candidate force, for (D) `periodize f` of the compressed R3 force
  (`PeriodicPaperTheorem.lean:98-99`). The real definitions of `u,p,f` live in the
  `ActualCandidate` chain (delegated to child A).
* **Junk-value / degenerate-collapse check.** The one place a junk value could have been
  exploited is `laplacian_eq` (`ComparatorBridge.lean:41`) and `divergence_eq`
  (`ComparatorBridge.lean:28`), which relate the project's coordinate operators to the
  comparator's `Δ` and `trace ∘ fderiv`:
  - `divergence_eq` is stated **unconditionally**, with no differentiability hypothesis.
    This is nevertheless sound, because *both* sides are built from the same
    `fderiv ℝ (fun y => v (t,y)) x` (`ProblemStatement.lean:59-68` vs
    `ComparatorDefinitions.lean:55`): the proof is `LinearMap.trace_eq_sum_inner` with
    `EuclideanSpace.basisFun`, i.e. `trace A = Σᵢ ⟪A eᵢ, eᵢ⟫ = Σᵢ (A eᵢ) i`, an identity of
    linear maps that holds for the junk value 0 too. It is *not* an
    "equal only where differentiable" claim smuggled in unconditionally. [OK]
  - `laplacian_eq` **does** carry `hv : ContDiff ℝ 2 (v(t,·))` and it is discharged from the
    comparator hypothesis's own `velocity_smooth` (`ComparatorBridge.lean:208-210`,
    `ComparatorR3Bridge.lean:41-43`). So the equation transfer uses real smoothness, not a
    junk collapse. [OK]
  - `temporalDerivative_eq` (`ComparatorBridge.lean:55`) rewrites
    `derivWithin _ (Ici 0) t` to `deriv` for `t > 0` via `derivWithin_of_mem_nhds`, then `rfl`.
    Unconditional and correct (both sides are the same totalized `fderiv … 1`). [OK]
* **Non-triviality certificates supplied by the authors themselves** (this is the strongest
  available evidence against a "collapse everything to 0" degeneracy):
  - `R3/ProblemStatement.lean:189 zero_force_has_global_solution` proves
    `Nonempty (GlobalFiniteEnergySolution ν (fun _ => 0))`, and
    `R3/CandidateBreakdown.lean:53 force_nonzero_of_no_global_solution` combines it with the
    exclusion to prove `∃ t > 0, ∃ x, f (t,x) ≠ 0`. So the exhibited force is **provably not
    identically zero** — otherwise the repo would be inconsistent, not merely wrong.
  - `MaximalLifespan.lean:275 candidate_force_nonzero_before_one` is the analogous certificate
    for the viscosity-one periodic candidate — but note its hypothesis is
    `NavierStokes.ProblemStatement.CandidateProperties u p f` (3 arguments,
    `ProblemStatement.lean:101`), i.e. the **viscosity-one** periodic candidate, **not** the
    shipped `PeriodicPaper.CandidateProperties ν u p f K` (`PeriodicPaperTheorem.lean:26`).
    **Correction, confirmed by the periodic-branch child:** there is NO in-repo lemma proving
    the shipped periodic force nonzero, and no periodic analogue of
    `R3/ProblemStatement.lean:189 zero_force_has_global_solution`. The argument still goes
    through *at the audit level* — the zero fields satisfy every field of
    `PeriodicPaper.GlobalSmoothSolution ν (fun _ => 0)` (`PeriodicPaperTheorem.lean:51-62`:
    smooth, periodic, zero datum, `spatialDivergence 0 = 0`, and
    `navierStokesResidual ν 0 0 = 0`), so `PeriodicPaperTheorem.lean:65 no_global_solution`
    forces the shipped `f ≢ 0` on pain of inconsistency — but this is *my* reasoning, not a
    machine-checked certificate in the artifact. Escalated as E-6.
  - `ProblemStatement.lean:151 zero_velocity_not_unbounded` proves
    `¬ SpeedUnboundedAtOne (fun _ => 0)`, and `speed_unbounded` is a field of *both*
    `CandidateProperties` (`ProblemStatement.lean:114`, `R3/ProblemStatement.lean:109`,
    `PeriodicPaperTheorem.lean:47`). So the constructed velocity is provably `≢ 0`.
  - `SpeedUnboundedAtOne` itself (`ProblemStatement.lean:94-96`) is non-degenerate:
    `∀ M > 0, ∀ δ > 0, ∃ t ∈ Ioo 0 1, 1-δ < t ∧ M < ‖u (t,x)‖`. Nothing vacuous
    (no empty index set, no `tsupport ⊆ ∅` trick).
  Verdict: **the cheap degeneracies are closed off**. A degenerate construction cannot pass
  silently; it would have to be an actual inconsistency.

### Q2. Does the route STRENGTHEN the negated statement `S`? — Private copy check

**Answer: NO, and I checked this byte-exactly.**

There IS a private copy of the challenge structures outside `ComparatorChallenges/`:
`NavierStokes/ComparatorDefinitions.lean` (`NavierStokesExistenceAndSmoothness` at :191,
`…Rn` at :219, `…Periodic` at :236). `ComparatorSolution.lean:8` openly says the adapters
import this copy and "never the challenge module".

I diffed the definition regions programmatically:
`ComparatorChallenges/NavierStokes.lean` **lines 60–270** vs
`NavierStokes/ComparatorDefinitions.lean` **lines 34–244**:
`difflib.unified_diff` returns **0 hunks — the two regions are character-for-character
identical**, including the `open ContDiff Set InnerProductSpace MeasureTheory` /
`open scoped Laplacian` lines, `namespace NavierStokes.Comparator`, both `local notation`
declarations, `variable {n : ℕ}`, all 16 declarations, all docstrings and all field lists.
Both files' only import is `import Mathlib` (challenge :20, copy :20). The only textual
difference between the whole files is the module docstring and the challenge's two
`sorry` theorems (`ComparatorChallenges/NavierStokes.lean:273-284`), which the copy omits.

Field lists therefore agree exactly:
* `NavierStokesExistenceAndSmoothness`: `navier_stokes`, `div_free`, `initial_condition`,
  `velocity_smooth`, `pressure_smooth` (challenge :222/:227/:229/:232/:235 = copy
  :196/:201/:203/:206/:209).
* `…Rn` extends it with `integrable`, `globally_bounded_energy`
  (challenge :250/:253 = copy :224/:227).
* `…Periodic` extends it with `isOnePeriodic_velocity`, `isOnePeriodic_pressure`
  (challenge :267/:269 = copy :241/:243).

Consequences:
* No extra field is present in the copy, so `¬ ∃ v p, S` is not weakened by adding
  requirements to `S`.
* Even structurally, the adapters cannot strengthen `S`: both final proofs are
  `rintro ⟨v, q, hv⟩` and then only *consume* fields of `hv`
  (`R3/ComparatorBridge.lean:87-88`, `PeriodicPaperComparator.lean:40-41`). The negated
  proposition appears verbatim in the theorem statements
  (`ComparatorSolution.lean:19`, `:26`).
* The derived structures the bridges build are **weaker** than the comparator hypothesis, in
  the safe direction: `GlobalFiniteEnergySolution` (`R3/ProblemStatement.lean:125`) demands
  the PDE only on `Ioi 0` where the comparator gives `∀ t ≥ 0`
  (`ComparatorDefinitions.lean:196`); likewise `PeriodicPaper.GlobalSmoothSolution`
  (`PeriodicPaperTheorem.lean:61`). Requiring less of a competitor makes the non-existence
  claim *stronger*, not weaker. [OK]
* `GlobalFiniteEnergySolution.energy_bounded` is `UniformFiniteEnergy (Ici 0)`
  (`R3/ProblemStatement.lean:81-83`: `∃ E ≥ 0, ∀ t ∈ times, SquareIntegrableAtTime u t ∧
  kineticEnergy u t ≤ E`) and it is discharged from the comparator's `integrable` +
  `globally_bounded_energy` at `R3/ComparatorBridge.lean:64-74`, with `E := max 0 (E/2)` and
  `linarith` from the strict `< E`. Correct, and note the authors kept an explicit
  `Integrable` field so the totalized Bochner integral cannot hide infinite energy
  (`R3/ProblemStatement.lean:69-72`, and see `R3/CandidateBreakdown.lean:64-77`). [OK]

**Residual caveat (escalation E-1):** identical *source text* under identical imports/opens is
extremely strong evidence but not a machine proof that the two structures *elaborate* to the
same term. The Comparator harness is what actually checks copy ≡ reference at runtime; on this
box no build could be run. The byte-diff is the best available source-level substitute.

### Q3. Periodic variant and the `isOnePeriodic_pressure` field (previous audit's E3)

**Confirmed: the route rules out ONLY competitors with 1-periodic pressure — and it is
entitled to, because the challenge's own structure demands periodic pressure.**

Chain of evidence:
1. `ComparatorDefinitions.lean:243` = `ComparatorChallenges/NavierStokes.lean:269`:
   `isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)` is a **field of the challenge
   structure** (the challenge docstring at :258-260 attributes it to the "Clay errata").
2. `PeriodicComparatorSolution.lean:31-33` fills
   `PeriodicPaper.GlobalSmoothSolution.pressure_periodic` from `h.isOnePeriodic_pressure`.
3. `PeriodicPaperTheorem.lean:65-73 CandidateProperties.no_global_solution` then **consumes**
   `v.pressure_periodic` (line 72) by passing it into
   `PeriodicViscosity.excludes_global_solution`, whose signature
   (`PeriodicViscosity.lean:38`) takes `hpq : UnitSpatialPeriodsOn (Ici 0) q` and uses it at
   `PeriodicViscosity.lean:64-65` to feed `PeriodicViscosityUniqueness.classical_uniqueness_on_Icc`.
   So competitor pressure periodicity is **essentially used**; a competitor with non-periodic
   pressure would not be excluded by this argument.
4. Verdict on **submission fidelity: [OK]** — the solution proves exactly the challenge's
   proposition, field for field, with no private strengthening. The gap, if any, is between the
   *challenge file* (inherited verbatim from google-deepmind/formal-conjectures, per
   `ComparatorChallenges/NavierStokes.lean:25-31`) and the Clay problem (D). That is an upstream
   statement-fidelity question, not a defect in this submission. Escalated as E-2 with the
   precise mathematical question.

Other periodic-side checks:
* `forceConditionPeriodic_of_decay` (`ComparatorBridge.lean:117-134`) converts the project's
  `C * (1+t)^(-K)` bounds for `K ≥ 0` into the comparator's `C / (1+t)^K` for **all real** `K`
  by taking `max K 0` and `Real.rpow_le_rpow_of_exponent_le` with base `1+t ≥ 1`. The
  negative-`K` case is genuinely handled, not skipped. [OK]
* `IsOnePeriodic` (copy :96) uses `EuclideanSpace.single i 1`; the project's
  `UnitSpatialPeriodsOn` (`ProblemStatement.lean:49-51`) uses
  `coordinateVector i := EuclideanSpace.single i 1` (`ProblemStatement.lean:39`). The transfer
  at `ComparatorBridge.lean:125-126` is `exact hp t ht x i`, i.e. it relies on δ-unfolding a
  `def`. Same proposition; fine for the kernel. [OK]
* `CandidateConsequences.futureJet_decay` (`CandidateConsequences.lean:79-110`): periodic +
  continuous on the slab `Icc 0 (T+1) ×ˢ univ` gives a bound `M` (via
  `MaximalLifespan.periodic_bound_on_slab`), and the jet vanishes for `t > T` by
  `CompactForceDecay.iteratedFDeriv_eq_zero_after`. Honest argument; `futureJet_periodic`
  (`:52-63`) is proved properly with `iteratedFDerivWithin_comp_add_right` + translation
  invariance of `futureDomain` (`:38-50`), not asserted. [OK]

### Q4. Kernel-risk steps on this path

See the next section. Short answer: **the spine files themselves contain no kernel-risk step**.
Every risky pattern in the closure lives deep in the construction, and every `decide` I found
is a two-element check like `0 < 1` or `2 ≠ 0`.

## Per-declaration findings

Verdict tags: [OK] verified mechanism, [UNCLEAR] statement read but mechanism delegated /
not reachable at source level, [KERNEL-RISK], [SUSPICIOUS].

| # | declaration | file:line | statement (my words) | actual mechanism | verdict |
|---|---|---|---|---|---|
| 1 | `Comparator.navier_stokes_breakdown_R3` | `NavierStokes/ComparatorSolution.lean:16` | (C): for every `nu>0` there are `u₀,f` with decay initial+force conditions and no `Rn` solution | `exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu` — pure re-export, statement written out verbatim | OK |
| 2 | `Comparator.navier_stokes_breakdown_periodic` | `ComparatorSolution.lean:23` | (D) likewise for the periodic structure | `exact ComparatorBridge.navier_stokes_breakdown_periodic nu hnu` | OK |
| 3 | `#print axioms` commands | `ComparatorSolution.lean:31-32` | asks Lean to list axioms of both theorems | output not observable without a build; grep shows 0 `sorry`/`axiom` in the whole repo outside `ComparatorChallenges/` | UNCLEAR (residue) |
| 4 | `periodicPaperSolution_of_comparator` | `PeriodicComparatorSolution.lean:20` | a comparator periodic solution with zero datum yields `PeriodicPaper.GlobalSmoothSolution ν f` | field-by-field: `fromComparator` for the coordinate swap, `fromComparator_smooth`, both periodicity fields taken directly from `h`, `divergence_eq` for div-free, `comparator_equation` for the PDE. No hypothesis invented | OK |
| 5 | `Comparator.divergence` | `ComparatorDefinitions.lean:55` | `trace (fderiv ℝ v x)` | junk value 0 off differentiability, documented at :51-52 | OK (identical to challenge) |
| 6 | `Comparator.IsOnePeriodic` | `ComparatorDefinitions.lean:95` | `∀ x i, f (x + single i 1) = f x` | definition | OK |
| 7 | `NavierStokesExistenceAndSmoothness{,Rn,Periodic}` | `ComparatorDefinitions.lean:191,219,236` | the three solution structures | **byte-identical** to `ComparatorChallenges/NavierStokes.lean:217,245,262` (0-hunk diff over lines 60–270 vs 34–244) | OK |
| 8 | `ComparatorBridge.navier_stokes_breakdown_R3` | `ComparatorR3Theorem.lean:38` | (C) with the comparator's quantifiers | destructs `NavierStokesR3.theorem_1_1 ν hν`, then `exact NavierStokesR3.comparator_of_breakdown h hglobal` | OK |
| 9 | `option_C_of_compact_candidate` | `ComparatorR3Theorem.lean:21` | (C) from a `R3CompactCandidate.Properties` witness with a rescaled force | not used by #8; the rescaling route | OK (dead code) |
| 10 | `ComparatorBridge.navier_stokes_breakdown_periodic` | `ComparatorTheorem.lean:47` | (D) with the comparator's quantifiers | destructs `PeriodicPaper.periodic_corollary ν hν`, then `exact option_D_of_paper_candidate h hglobal` | OK |
| 11 | `option_D_of_candidate` | `ComparatorTheorem.lean:25` | (D) from a viscosity-one `CandidateProperties` witness, rescaling the force by `ν²`/`ν` | not used by #10 | OK (dead code) |
| 12 | `toComparator` / `fromComparator` | `ComparatorBridge.lean:21,25` | argument-order swap `(t,x) ↔ x t` | definitions; mutually inverse by `rfl` in use | OK |
| 13 | `divergence_eq` | `ComparatorBridge.lean:28` | `spatialDivergence v t x = Comparator.divergence (v(t,·)) x`, **no differentiability hypothesis** | `LinearMap.trace_eq_sum_inner` with `EuclideanSpace.basisFun` + `EuclideanSpace.inner_single_left`; sound because both sides use the *same* `fderiv`, junk value included | OK (see Q1) |
| 14 | `gradient_eq` | `ComparatorBridge.lean:34` | `pressureGradient p t x = gradient (p(t,·)) x` | `ext_inner_left_basis` on `basisFun`, componentwise `simp` | OK |
| 15 | `laplacian_eq` | `ComparatorBridge.lean:41` | `spatialLaplacian v t x = Δ (v(t,·)) x` **given `ContDiff ℝ 2`** | `laplacian_eq_iteratedFDeriv_orthonormalBasis`, `iteratedFDeriv_two_apply`, `fderiv_clm_apply` with the `C²` hypothesis used to get differentiability of `fderiv` | OK |
| 16 | `temporalDerivative_eq` | `ComparatorBridge.lean:55` | for `t>0`, `temporalDerivative = derivWithin _ (Ici 0) t` | `derivWithin_of_mem_nhds (Ici_mem_nhds ht)` then `rfl` | OK |
| 17 | `rescale`, `rescaledForce` | `ComparatorBridge.lean:61,65` | time/amplitude scaling | definitions; only on the dead rescaling route | OK |
| 18 | `rescale_smooth/_periodic/_support` | `ComparatorBridge.lean:67,75,81` | scaling preserves smoothness, periodicity, compact future time support | composition lemmas; `rescale_support` uses `T/c` and `nlinarith` | OK |
| 19 | `fromComparator_smooth`, `toComparator_smooth` | `ComparatorBridge.lean:89,95` | smoothness transports across the coordinate swap | `ContDiffOn.comp` with the swap map and the set inclusion | OK |
| 20 | `toComparator_jet_norm` | `ComparatorBridge.lean:101` | jet norms agree across the swap on the closed future domain | `LinearIsometryEquiv.prodComm` + `norm_iteratedFDerivWithin_comp_right`, with `UniqueDiffOn` supplied. This is exactly the place where a sloppy proof could have dodged the `t=0` boundary; it does not | OK |
| 21 | `forceConditionPeriodic_of_decay` | `ComparatorBridge.lean:117` | project decay bounds ⇒ `Comparator.ForceConditionPeriodic` for all real `K` | `max K 0` + `Real.rpow_le_rpow_of_exponent_le`; negative `K` handled | OK |
| 22 | `zero_initial_condition` | `ComparatorBridge.lean:136` | `InitialVelocityConditionPeriodic (fun _ => 0)` | `divergence_const`, `contDiff_const`, periodicity by `rfl` | OK |
| 23 | `rescale_{spatialDerivative,divergence,advection,gradient,laplacian,temporalDerivative}` | `ComparatorBridge.lean:144,148,152,156,162,168` | how the operators scale | `fderiv_const_smul_field`, `HasDerivAt` composition; `rescale_temporalDerivative` correctly requires differentiability | OK (dead route) |
| 24 | `smooth_space_slice`, `differentiable_time_slice` | `ComparatorBridge.lean:176,183` | slices of a future-smooth field are smooth / time-differentiable at `t>0` | `ContDiffOn.comp`, `contDiffAt` with `Ici_mem_nhds` | OK |
| 25 | `GlobalSolutionOne` | `ComparatorBridge.lean:192` | project-side periodic global solution, viscosity 1 | Prop-valued structure, 7 fields; PDE only for `t>0` | OK (dead route) |
| 26 | `comparator_equation` | `ComparatorBridge.lean:201` | a comparator periodic solution satisfies the project's residual identity at `t>0` | rewrites via #15/#14/#16 then `h.navier_stokes x t ht.le` and `abel`. Note it uses the comparator equation at `t ≥ 0` only through `t > 0` | OK |
| 27 | `normalized_solution` | `ComparatorBridge.lean:217` | viscosity-`ν` comparator solution ⇒ viscosity-1 project solution | full rescaling computation, `field_simp`/`smul` algebra; both periodicity fields used | OK (dead route) |
| 28 | `zero_initial_condition_decay` | `ComparatorR3Bridge.lean:18` | `InitialVelocityConditionDecay (fun _ => 0)` | `divergence_const`, `contDiff_const`, `⟨0, by simp⟩` for decay | OK |
| 29 | `GlobalSolutionRn` | `ComparatorR3Bridge.lean:25` | project-side whole-space global solution with `MemLp` + energy bound | 7-field Prop structure | OK (dead route) |
| 30 | `comparator_equation_Rn` | `ComparatorR3Bridge.lean:34` | as #26 but for the `Rn` structure | same mechanism | OK |
| 31 | `normalized_solution_Rn` | `ComparatorR3Bridge.lean:50` | viscosity normalization, whole space | includes `MemLp` and energy rescaling with `integral_const_mul` | OK (dead route) |
| 32 | `forceConditionDecay_of_compact` | `R3/ComparatorBridge.lean:22` | `ContDiff ∞ f` + `HasCompactSupport f` ⇒ `Comparator.ForceConditionDecay (toComparator f)` | builds `K := Prod.snd '' tsupport f` (compact), `SupportedIn K f` and a time bound `max M 0 + 1` from `exists_bound_of_continuousOn` on `tsupport f`, then `CompactSpatialForceDecay.forceConditionDecay` | OK |
| 33 | `globalSolutionOfComparator` | `R3/ComparatorBridge.lean:48` | comparator `Rn` solution with zero datum ⇒ `GlobalFiniteEnergySolution ν f` | field-by-field; energy from `memLp_two_iff_integrable_sq_norm` and `E := max 0 (E/2)` + `linarith` | OK |
| 34 | `comparator_of_breakdown` | `R3/ComparatorBridge.lean:77` | R3 candidate + no global finite-energy solution ⇒ option (C) | `refine ⟨fun _ => 0, toComparator f, …⟩`, then `rintro ⟨v,q,hv⟩; exact hglobal ⟨globalSolutionOfComparator hv⟩` | OK |
| 35 | `forceConditionPeriodic_of_paper_candidate` | `PeriodicPaperComparator.lean:21` | periodic candidate's force meets the comparator periodic force condition | `forceConditionPeriodic_of_decay` ∘ `futureJet_decay` | OK |
| 36 | `option_D_same_force_of_paper_candidate` | `PeriodicPaperComparator.lean:31` | the three comparator conjuncts for `u₀ = 0`, `g = toComparator f` | `rintro ⟨v,q,hv⟩; exact hno ⟨periodicPaperSolution_of_comparator hv⟩` | OK |
| 37 | `option_D_of_paper_candidate` | `PeriodicPaperComparator.lean:45` | (D) with the comparator's quantifiers | term-mode `⟨fun _ => 0, toComparator f, …⟩` | OK |
| 38 | `SpeedUnboundedAtOne` | `ProblemStatement.lean:94` | `∀ M>0, ∀ δ>0, ∃ t ∈ Ioo 0 1, 1-δ<t, M < ‖u(t,x)‖` | definition; non-degenerate, no vacuous quantifier | OK |
| 39 | `CandidateProperties` (viscosity 1, periodic) | `ProblemStatement.lean:101` | 11 fields: smoothness on `Ico 0 1 ×ˢ univ`, periodicity, zero datum, force time support, div-free, PDE on `Ioo 0 1`, blow-up | Prop structure; PDE imposed only at interior times, documented at :13-16 | OK |
| 40 | `zero_residual` | `ProblemStatement.lean:141` | residual of the zero fields is 0 | `simp` over the operator definitions | OK |
| 41 | `zero_velocity_not_unbounded` | `ProblemStatement.lean:151` | `¬ SpeedUnboundedAtOne 0` | instantiate at `M=1, δ=1`, `norm_zero` | OK — proves the candidate velocity is `≢ 0` |
| 42 | `unbounded_speed_excludes_uniform_bound` | `ProblemStatement.lean:159` | blow-up excludes any uniform bound on `Ico 0 1` | instantiate at `max C 1` | OK |
| 43 | `NavierStokesR3.…CandidateProperties` | `R3/ProblemStatement.lean:92` | 12 fields; adds `support_compact`, `velocity/pressure_support ⊆ K`, `energy_bounded`, drops periodicity | Prop structure | OK |
| 44 | `GlobalFiniteEnergySolution` | `R3/ProblemStatement.lean:125` | competitor class: smooth on `Ici 0 ×ˢ univ`, zero datum, div-free on `Ici 0`, PDE on `Ioi 0`, `UniformFiniteEnergy (Ici 0)` — **no** support/periodicity/pressure normalization | `Type`-valued structure (not Prop); explicitly weaker than the comparator class | OK |
| 45 | `UniformFiniteEnergy` | `R3/ProblemStatement.lean:81` | one `E ≥ 0` bounding `kineticEnergy` at all times in `times`, with `Integrable` required at each | definition; the explicit `SquareIntegrableAtTime` blocks the "totalized integral of a non-integrable function is 0" trick | OK — good hygiene |
| 46 | `zero_force_has_global_solution` | `R3/ProblemStatement.lean:189` | zero force has a global finite-energy solution at any `ν` | exhibits `v=p=0`, all fields by `simp` | OK — this is what makes the exhibited force provably nonzero |
| 47 | `candidateStatement_iff_nonempty` | `R3/ProblemStatement.lean:157` | bundling witnesses changes nothing | trivial both ways | OK |
| 48 | `CompactPositiveTimeSupport.eq_zero_of_nonpos` | `R3/ProblemStatement.lean:173` | force vanishes at all `t ≤ 0` | `image_eq_zero_of_notMem_tsupport` + `tsupport ⊆ Ioi 0 ×ˢ univ` | OK |
| 49 | `theorem_1_1_with_initial_rest` | `R3/Theorem.lean:26` | for each `ν>0`: a candidate at `ν`, no global finite-energy competitor, and `u=p=0` for `\|t\| ≤ 3/8` | from `ActualCandidate.selected_candidate_one_with_initial_rest` + `ViscosityScaling.candidate_at_viscosity`; exclusion via `hc.no_global_solution_one ⟨normalized_global_solution hν v⟩`; the rest clause by `smul_zero` after `change` | UNCLEAR at this level — delegated to child A |
| 50 | `theorem_1_1`, `candidateStatement`, `coreBreakdownStatement`, `breakdownStatement` | `R3/Theorem.lean:46,52,58,62` | repackagings of #49 | destructure + rebuild; `breakdownStatement := theorem_1_1` | OK |
| 51 | `theorem_1_1_with_dissipation` | `R3/Theorem.lean:66` | #49 plus explicit energy/dissipation inequalities | adds `CompactEnergy.candidate_energy_estimates` | UNCLEAR (not on the deliverable path) |
| 52 | `CandidateProperties.not_global_agreement` | `R3/CandidateBreakdown.lean:18` | a future-smooth `v` cannot agree with the candidate on `Ico 0 1` | `v` is continuous on the **compact** `Icc 0 1 ×ˢ K` hence bounded by `M`; `speed_unbounded` produces a point with `‖u‖ > max M 1`; `velocity_support` places that point in `K`; contradiction. Genuinely non-vacuous | OK — clean and checkable |
| 53 | `CandidateProperties.no_global_solution_one` | `R3/CandidateBreakdown.lean:43` | viscosity-1 candidate excludes a global finite-energy solution | `WholeSpaceUniqueness.candidate_global_agrees_before_one h v` gives agreement on `Ico 0 1`, then #52. **The whole R3 non-existence claim reduces to this uniqueness theorem** | UNCLEAR — uniqueness delegated to child A |
| 54 | `force_nonzero_of_no_global_solution` | `R3/CandidateBreakdown.lean:53` | such a force is nonzero at some positive time | `f = 0` would contradict #46 via `Function.ne_iff` | OK |
| 55 | `CandidateProperties.uniform_l2_sq_bound` | `R3/CandidateBreakdown.lean:66` | `∫ ‖u‖²  ≤ 2E` with integrability, on `Ico 0 1` | unpack `energy_bounded`, `linarith` | OK |
| 56 | `PeriodicPaper.CandidateProperties` | `PeriodicPaperTheorem.lean:26` | 16 fields: as #39 plus `support_compact`, `support_interior ⊆ fundamentalInterior`, cube-intersected supports, `force_zero_nonpos`, PDE at viscosity `ν` | Prop structure | OK |
| 57 | `PeriodicPaper.GlobalSmoothSolution` | `PeriodicPaperTheorem.lean:51` | competitor: smooth on future domain, velocity AND pressure 1-periodic on `Ici 0`, zero datum, div-free on `Ici 0`, PDE on `Ioi 0`. No energy assumption | `Type`-valued structure; every field is supplied by the comparator structure | OK — but see E-2 on `pressure_periodic` |
| 58 | `CandidateProperties.no_global_solution` | `PeriodicPaperTheorem.lean:65` | periodic candidate excludes a global smooth periodic competitor | `PeriodicViscosity.excludes_global_solution` fed 8 candidate fields and 7 competitor fields, **including `v.pressure_periodic` (line 72)** | UNCLEAR (mechanism) / see E-2 |
| 59 | `CandidateProperties.force_derivative_decay` | `PeriodicPaperTheorem.lean:77` | arbitrary polynomial time decay of all force jets | `futureJet_decay` + `futureJet_eq_full` | OK |
| 60 | `of_compact_candidate` | `PeriodicPaperTheorem.lean:92` | periodize a compressed compact whole-space candidate into a periodic candidate | truncate by `beforeOne` (`if t < 1 then g z else 0`, `PeriodicPaperSupport.lean:28`), then `periodize` (lattice sum, `PeriodicLocalization.lean:62`); every field routed through a matching `*_periodize` lemma, blow-up through `speedUnbounded_periodize` | UNCLEAR (the `*_periodize` lemmas not read) — delegated to child B |
| 61 | `PeriodicPaper.periodic_corollary` | `PeriodicPaperTheorem.lean:155` | for each `ν>0`: a periodic candidate at `ν` with no global smooth periodic competitor | `NavierStokesR3.theorem_1_1_with_initial_rest` + `exists_compression_scale` + `ParabolicScaling.compressedCandidate` + #60 + #58 | UNCLEAR — but note the reduction to the R3 construction (Finding S1) |
| 62 | `CompactSpatialForceDecay.jet_zero_outside` / `jet_zero_after` | `CompactSpatialForceDecay.lean:22,32` | one-sided jets vanish off the spatial support / after the time support | `Filter.EventuallyEq.iteratedFDerivWithin_eq` with a `nhdsWithin` neighbourhood; correct use of `mem_nhdsWithin_of_mem_nhds` | OK |
| 63 | `CompactSpatialForceDecay.jet_decay` | `CompactSpatialForceDecay.lean:44` | all real exponents `K`: `‖jet‖ ≤ C/(1+‖x‖+t)^K` | bound `‖J‖·weight` on the compact box `Icc 0 (T+1) ×ˢ S` by `exists_bound_of_continuousOn`, then two `by_cases` handing the outside-`S` and `t>T+1` regions to #62. `C := max M 1 > 0`. Handles negative `K` because the weight is bounded on the box | OK |
| 64 | `CompactSpatialForceDecay.forceConditionDecay` | `CompactSpatialForceDecay.lean:85` | the comparator's whole-space force condition from compact support | #63 + `toComparator_jet_norm` | OK |
| 65 | `CandidateConsequences.futureJet` / `_continuous` / `_periodic` / `_eq_full` | `CandidateConsequences.lean:30,33,52,65` | one-sided spacetime jets, their continuity, spatial periodicity and agreement with the ordinary jet | `iteratedFDerivWithin_comp_add_right` + `future_spatial_translate`; `iteratedFDerivWithin_eq_iteratedFDeriv` with `UniqueDiffOn` | OK |
| 66 | `CandidateConsequences.futureJet_decay` | `CandidateConsequences.lean:79` | periodic force with compact future time support has arbitrary polynomial time decay of all jets | slab bound via `MaximalLifespan.periodic_bound_on_slab` + vanishing after `T`; `rpow` algebra with `Real.rpow_le_rpow_of_nonpos` | OK |
| 67 | `PeriodicViscosity.excludes_global_solution` | `PeriodicViscosity.lean:24` | 15 explicit hypotheses (candidate + competitor) ⇒ `False` | `MaximalLifespan.unbounded_excludes_continuous_extension` + `PeriodicViscosityUniqueness.classical_uniqueness_on_Icc` on each slab `[0,t]` | UNCLEAR — delegated to child B |
| 68 | `MaximalLifespan.candidate_excludes_global_solution` | `MaximalLifespan.lean:237` | viscosity-1 candidate + periodic global competitor ⇒ `False` | restricts the competitor to `lifespanDomain 2` and applies `candidate_no_solution_after_one` | UNCLEAR (dead route: used only by `option_D_of_candidate`) |
| 69 | `MaximalLifespan.zero_classical_solution_of_zero_force` | `MaximalLifespan.lean:260` | zero force ⇒ the zero fields are a classical solution | `zero_residual` + `rfl`s | OK |
| 70 | `MaximalLifespan.candidate_force_nonzero_before_one` | `MaximalLifespan.lean:275` | the candidate's force is nonzero somewhere in `Ioo 0 1` | else uniqueness identifies `u` with 0, contradicting `speed_unbounded` via #42 | OK — second non-triviality certificate |

## Kernel-risk assessment

Instrument: comment-stripped regex census over the **full import closure of
`NavierStokes.lean`** — 753 local `.lean` modules, 404 520 lines (the closure was computed by
transitively resolving `import` lines; `ComparatorChallenges/*` is **not** in it, as claimed at
`ComparatorSolution.lean:8` and `ComparatorChallenges/NavierStokes.lean:32`).

Closure-wide counts (comment-stripped):

| pattern | hits | comment |
|---|---|---|
| `sorry` / `admit` | **0** | also 0 repo-wide outside `ComparatorChallenges/` |
| `axiom` (declaration) | **0** | |
| `native_decide` | **0** | |
| `macro`/`macro_rules`/`elab`/`elab_rules`/`syntax`/`notation3` | **0** | vector (3) absent |
| `set_option` | **0** | |
| `unsafe` / `partial` | **0** / **0** | |
| `decide` | 90 | all tiny — see below |
| `termination_by` | 2 | `VolterraAnalyticBounds.lean:164,184` (`termination_by w.length`) |
| `decreasing_by` | 0 | |
| `Acc.rec` (explicit) | 0 | |
| `WellFounded.fix_eq` | 3 | `GlobalSlowProfiles.lean:910`, `SlowRecursion.lean:953,964` |
| `inductive` | 9 | listed below |
| explicit `.rec` application | 4 | `ActivationContinuation.lean:517,520` (`HistoryRow.rec`), `WeightedODEJets.lean:177,187` (`List.rec`) |
| `norm_num` | 2749 | all on small rationals; largest literals below |
| `Nat.pow` / `Nat.gcd/mod/div/beq/ble` | **0** / **0** | no GMP-heavy Nat kernel arithmetic |
| `attribute [local instance]` | 3 | `Classical.propDecidable`, see below |
| `Classical.choice`/`choose` | 72 | ordinary noncomputable choice |

**Vector (1) — recursive inductive types.** Present in the closure but **not on the spine**.
The 9 `inductive`s are `ClosedIntervalJetAlgebra.lean:244 PolynomialExpression`,
`FlatKernelBounds.lean:76 Expr`, `GenericDifferentialPolynomial.lean:185 Expression`,
`GenericFactorSupport.lean:14 FieldFactor` and `:106 FactorSupportAt` (an **indexed family**,
the most interesting one), `NaturalAxisCoefficients.lean:116 Field`,
`ReservedPatches.lean:22 Slot`, `StressActivation.lean:539 HistoryRow`,
`TorusInverse.lean:190 Direction`. The two explicit `HistoryRow.rec (motive := fun _ => Fin 10)`
applications (`ActivationContinuation.lean:517,520`) are large-elimination-flavoured
(recursor into a data type, 5 branches) — but they are *definitions*, so the kernel only has
to typecheck them, and any `rfl`-style reduction is over a 5-constructor enumeration.
The two `termination_by` functions and the three `WellFounded.fix_eq` rewrites are the
`Acc.rec`-unfolding sites. **None of these appears in any of the 19 spine files**: I grepped
each spine file and there is no `inductive`, no `.rec`, no `termination_by`, no `WellFounded`,
no structure eta trick in them. The spine's only inductive-type reductions are ordinary
`structure` projections on `Prop`-valued and `Type`-valued single-constructor structures
(`⟨…⟩` anonymous constructors and `h.field` projections) — the safest possible pattern.
**Does the kernel have to perform a risky recursor reduction to accept the spine? No.**
For the closure as a whole: yes, at the 4 `.rec` sites and 5 well-founded sites, but the
recursions are over finite enumerations and list lengths, not over deep numeral data.

**Vector (2) — Nat / GMP numeral arithmetic.** Effectively absent.
* Zero `Nat.pow`/`Nat.div`/`Nat.mod`/`Nat.gcd`/`Nat.beq`/`Nat.ble` occurrences.
* All 90 `decide` uses are two-element decisions inside `simp`/`exact` arguments. Sampled
  verbatim: `(by decide : 0 < 1)`, `(by decide : 2 ≠ 0)`,
  `show (0 : Fin 3) ≠ 2 by decide`, `(L, ⟨1, by decide⟩)`,
  `Nat.pow_le_pow_right (by decide : 1 ≤ …)`. The kernel work per site is a single-digit
  `Nat.decLt`/`Nat.decEq`/`Fin` comparison. **Negligible.**
* Largest literals anywhere in the closure: `1152000` and `305719`
  (`AxisModelBounds.lean:25,41,47,56,57`, in the rational `305719/1152000 : ℝ`),
  `1000000` (`ExponentLedger.lean:276`), `500000`/`4501` (`MatchingConeBounds.lean:48`),
  `100000` (`SignedMeanGain.lean:463,973,1329`). These are **real** literals reduced by
  `norm_num` certificates, i.e. 7-digit `Nat` multiplications — trivial for GMP and far from
  any known kernel-arithmetic stress regime. **No spine file contains a literal with more
  than 2 digits** (`3/8` at `R3/Theorem.lean:30`, `1/4`, `1/2`, `2` at
  `MaximalLifespan.lean:249`).
* The two `norm_num` calls in spine files are `PeriodicPaperTheorem.lean:102`
  (`(1/4 : ℝ) < 1/2`) and `:132` (`(0 : ℝ) < 1`). Trivial.

**Vector (3) — custom metaprogramming.** Confirmed **zero** in the closure: no
`macro`, `macro_rules`, `elab`, `elab_rules`, `syntax`, `notation3`, `set_option`,
`native_decide`, `axiom`, `unsafe`, `partial`. Under the threat model, finding *any* would
have been a finding; there is none. The only attribute manipulation is
`attribute [local instance] Classical.propDecidable`.

**`Classical.propDecidable` (parent's extra input).** Four files carry it; **three are in the
`ComparatorSolution` import closure**:
`ActualSignedPhysicalData.lean:22` ✔ in closure, `InitialPhysicalData.lean:28` ✔ in closure,
`PositiveTimeSignedData.lean:24` ✔ in closure, `ActualParticularPhysicalData.lean:24`
✘ **not** in the closure. They are used (487 cross-file references to those three namespaces).

What the instance is doing there: it supplies `Decidable` for the *undecidable* membership
predicates used to define fields by zero-extension, e.g.
`if hL : L ∈ f.active then <real amplitude> else 0`
(`ActualSignedPhysicalData.lean:565,606,618,1211,1219`;
`InitialPhysicalData.lean:268,283,290,599`) and `if 0 < x.1.1 then … else 0`
(`InitialPhysicalData.lean:368,376`). Every consumer then discharges the branch with a proof
via `dite_eq_left/dite_eq_right` or `by_cases` (e.g.
`ActualSignedPhysicalData.lean:571,652,662,881,934,1876,1878`).

Kernel-risk verdict: **this pattern REDUCES kernel-evaluation risk rather than raising it.**
`Classical.propDecidable` is defined from `Classical.choice`, so it is irreducible for the
kernel: a `decide`-style whnf of these `dite`s can never succeed, which is precisely why
every use goes through an explicit rewriting lemma. So it opens no `decide`/GMP door.
The **real** risk it opens is mathematical, not kernel-level: `if <property> then <witness>
else 0` is the canonical shape of a degenerate construction ("return the good object if the
hard condition holds, else 0"). If `f.active` were empty, every amplitude would collapse to 0
and all downstream "bounds" would be vacuously true. Against that failure mode, the two
non-triviality certificates already cited are the effective guard:
`ProblemStatement.lean:151` (`speed_unbounded` forces `u ≢ 0`) and
`R3/CandidateBreakdown.lean:53` + `R3/ProblemStatement.lean:189` (the force is provably
nonzero somewhere at positive time). A total collapse cannot pass silently; it would have to
be an outright inconsistency. Reported as escalation E-3 for the construction auditors.

## Escalations

**E-1 (rank 1) — Statement identity is checked by the Comparator harness, not by anything
readable here.** `NavierStokes/ComparatorDefinitions.lean:34-244` is byte-identical to
`ComparatorChallenges/NavierStokes.lean:60-270` (0-hunk `difflib` diff), and both files' only
import is `import Mathlib`. But identical text is not a machine proof of identical
elaboration, and the challenge module is deliberately outside the proof's import closure
(`ComparatorSolution.lean:8`).
*Question for an expert:* in the actual Comparator run, is the submitted
`NavierStokes.Comparator.navier_stokes_breakdown_R3` / `…_periodic` type checked
**definitionally against the reference declarations** (not merely by name and pretty-printed
form)? *What would settle it:* the Comparator log showing the reference statement and the
submitted statement unified (or `isDefEq` succeeding) in one environment; equivalently a build
that imports both modules and closes
`example : (∀ nu, nu > 0 → <reference type>) = (∀ nu, nu > 0 → <submitted type>) := rfl`.

**E-2 (rank 2) — The periodic claim excludes only competitors with 1-periodic PRESSURE.**
`ComparatorDefinitions.lean:243` (= challenge `:269`) makes `isOnePeriodic_pressure` a field
of the negated structure; `PeriodicComparatorSolution.lean:33` transports it and
`PeriodicPaperTheorem.lean:72` **essentially consumes** it inside
`PeriodicViscosity.excludes_global_solution` (`PeriodicViscosity.lean:38,64-65`). Submission
fidelity is fine; the question is upstream statement fidelity.
*Question for an expert:* for periodic NS with periodic force `f` and zero datum, a smooth
periodic velocity forces `∇p` periodic, hence `p = p_per + a(t)·x` with the linear part
determined by the torus mean of the equation. Is requiring `p` itself periodic therefore
(a) no loss, because any competitor with a nonzero linear pressure part can be gauged to one
with periodic pressure while keeping the same `ν`, the same `f` and the same zero datum, or
(b) a genuine restriction that removes a mean-drift family of solutions? If (b), Clay (D)
would not be settled even by a correct proof of this Lean statement.
*What would settle it:* a written gauge argument (or counterexample) for the transformation
`v ↦ v + b(t)` with a compensating spatial shift, checked against the fixed force `f` and the
fixed initial condition `v(·,0) = 0`; plus a citation for the Clay errata wording that the
formal-conjectures comparator claims to encode
(`ComparatorChallenges/NavierStokes.lean:258-260`).

**E-3 (rank 3) — Zero-extension `dite` definitions in three in-closure data files.**
`ActualSignedPhysicalData.lean:22`, `InitialPhysicalData.lean:28`,
`PositiveTimeSignedData.lean:24` enable `Classical.propDecidable` and define amplitudes as
`if hL : L ∈ f.active then <real> else 0`
(`ActualSignedPhysicalData.lean:565,606,618,1211,1219`;
`InitialPhysicalData.lean:268,283,290,368,376,599`).
*Question for an expert:* is `active` proved non-empty at the point where the final velocity
is assembled, and is any quantitative lower bound (not just an upper bound) ever proved for
an amplitude on the active set? *What would settle it:* the file:line where a strict
positivity / non-vanishing statement about the assembled velocity is proved, independent of
the `speed_unbounded` field, plus confirmation that no `bound ≤ C` lemma in the chain is
satisfied only through the `else 0` branch.

**E-4 (rank 4) — Both deliverables rest on one construction.**
`PeriodicPaperTheorem.lean:157-158` derives the periodic corollary from
`NavierStokesR3.theorem_1_1_with_initial_rest`, so (C) and (D) share the R3 candidate.
*Question:* is the compression + periodization step
(`exists_compression_scale`, `ParabolicScaling.compressedCandidate`,
`PeriodicPaperTheorem.lean:92 of_compact_candidate`) sound in particular for the
`speed_unbounded` transport (`speedUnbounded_periodize` at `:120-121`) — i.e. does the lattice
sum really preserve the blow-up rather than merely preserve an upper bound?
*What would settle it:* reading `speedUnbounded_periodize` and
`periodize_tsupport_on_fundamentalCube` (delegated to child B) and confirming the `1/4 < 1/2`
separation at `:102` really prevents overlap of the translated supports.

**E-5 (rank 5) — The single real analytic load-bearing step for (C).**
`R3/CandidateBreakdown.lean:43 no_global_solution_one` reduces the entire whole-space
non-existence claim to `WholeSpaceUniqueness.candidate_global_agrees_before_one`.
Everything else in the R3 branch is a compactness/boundedness argument I verified by reading.
*Question:* does that uniqueness theorem need — and legitimately obtain — finite energy of
BOTH fields on `[0,t]`, and is its Grönwall/energy argument valid without any support
assumption on the competitor (as claimed at `R3/ProblemStatement.lean:122-124`)?
*What would settle it:* child A's report on the `WholeSpaceUniqueness` chain.

**E-6 (rank 6, from the periodic-branch child, corroborated) — no in-repo certificate that
the shipped PERIODIC force is nonzero.** The R3 branch has one
(`R3/CandidateBreakdown.lean:53` + `R3/ProblemStatement.lean:189`); the viscosity-one periodic
statement has one (`MaximalLifespan.lean:275`, but for
`ProblemStatement.CandidateProperties u p f`, not for the shipped
`PeriodicPaper.CandidateProperties ν u p f K`). There is no analogue of
`zero_force_has_global_solution` for `PeriodicPaper.GlobalSmoothSolution`.
*Question for an expert:* add and check
`example (ν : ℝ) : Nonempty (PeriodicPaper.GlobalSmoothSolution ν (fun _ => 0))` (zero fields);
together with `PeriodicPaperTheorem.lean:65` this yields `f ≠ fun _ => 0` for the shipped
force, and turns the audit-level argument above into a machine-checked one. If instead that
example fails to typecheck, the periodic competitor class is not inhabited for the zero force
and the whole (D) exclusion needs re-reading.
*What would settle it:* one 10-line Lean example in a scratch file, once a build exists.

## Corroboration from the two delegated children (and a scope refinement)

Both children reported. Their reports:
`workers/ns-spine-r3branch.md` (14 OK / 2 UNCLEAR / 0 KERNEL-RISK / 0 SUSPICIOUS) and
`workers/ns-spine-periodicbranch.md` (9 OK / 1 UNCLEAR / 1 SUSPICIOUS / 0 KERNEL-RISK).

**Independent confirmation of the central check.** Both children independently re-derived that
`NavierStokes/ComparatorDefinitions.lean` is character-identical to the challenge definitions
and that `ComparatorChallenges/` is not in the import closure. Three independent diffs, three
agreements. I consider Q2 settled at source level (E-1 remains the only residual).

**Scope refinement — 609 vs 753 modules (reconciled, not a conflict).** Child A cites a
609-file closure; I cite 753. Recomputed:
* closure of `NavierStokes.ComparatorSolution` (the **deliverable** path) = **609** local modules;
* closure of `NavierStokes.PaperResults` = 744, contributing **143 files not on the deliverable
  path**;
* closure of the root `NavierStokes.lean` = **753** (the union).
So 144 of the 753 files are compiled by the root but are **not needed for the two comparator
theorems**. Re-partitioning my kernel-risk census across that boundary:

| site | in the 609 deliverable closure? |
|---|---|
| `FlatKernelBounds.lean:76 inductive Expr`, `NaturalAxisCoefficients.lean:116 Field`, `ReservedPatches.lean:22 Slot`, `StressActivation.lean:539 HistoryRow`, `TorusInverse.lean:190 Direction` | **yes** |
| `ClosedIntervalJetAlgebra.lean:244`, `GenericDifferentialPolynomial.lean:185`, `GenericFactorSupport.lean:14` and `:106` (the indexed family) | no — `PaperResults` only |
| `ActivationContinuation.lean:517,520` (`HistoryRow.rec`), `WeightedODEJets.lean:177,187` (`List.rec`) | **yes — all 4** |
| `VolterraAnalyticBounds.lean:164,184` (`termination_by`), `GlobalSlowProfiles.lean:910`, `SlowRecursion.lean:953,964` (`WellFounded.fix_eq`) | **yes — all 5** |
| `Classical.propDecidable` at `ActualSignedPhysicalData.lean:22`, `InitialPhysicalData.lean:28`, `PositiveTimeSignedData.lean:24` | **yes — all 3** |
| `decide` | 86 of 90 in the 609 |
| largest literal `1152000` (`AxisModelBounds.lean:25,41,47,56,57`) | no — `PaperResults` only |
| largest literal on the deliverable path: `1000000` (`ExponentLedger.lean:276`, hypothesis `κ < 1/1000000`) | **yes** |

This reconciles child A's "max numeral 1/10^6" with my closure-wide `1152000`: both are right,
at different scopes. **Vectors (1) and (2) are therefore genuinely present on the deliverable
path** (5 inductives, 4 explicit recursor applications, 5 well-founded-recursion sites), even
though none of them is in the 19 spine files. Vector (3) remains at zero in both scopes.

**New load-bearing fact from child A — the force is DEFINED as the residual.**
`CandidateFromLimits.lean:82`:
`def force := SpacetimeGluing.smoothExtension 1 (tracedResidual u p L) (tracedResidual_smooth …)`,
with the docstring at `:80-81` stating "No force is an input to this definition."
Consequence for my table: `CandidateProperties.navier_stokes` (`R3/ProblemStatement.lean:106`)
is **satisfied by construction / definitionally**, not by an analytic estimate. This is the
classic shape of "a hypothesis that makes a claim trivially true", but here it is a *legitimate*
and standard move for a forced-blowup construction: the PDE is free once `f` is *defined* as the
residual, and the entire mathematical burden shifts to the two properties of `f` that are NOT
free —
`force_smooth : ContDiff ℝ ∞ f` (`CandidateFromLimits.lean:87`) and
`force_support : CompactPositiveTimeSupport f` (`R3/ProblemStatement.lean:102`), i.e. that the
residual extends smoothly *through the singular time* `t = 1` and vanishes near `t = 0` —
together with `speed_unbounded`. **Verdict [OK, but re-ranked]:** not a defect, and I flag it
so no reader mistakes `navier_stokes` for verified content. It makes E-5/child A's top
escalation (convergence of the residual jets as `t → 1⁻`, `VanishingJointJets` /
`GermCandidateAssembly.lean:169`) the single most important remaining item in the whole audit.

**Child A on blow-up and on the exclusion (both strengthen my UNCLEAR rows #49, #53):**
* `speed_unbounded` is backed by an explicit divergent profile,
  `u (t,0) = ((1-t)^(-A h) * j) • e₂` with `A h > 0`, `j > 0`
  (`FinalSlowBase.lean:361,372`, `BaseResidual.lean:104`), transported to the compact R3 field
  by a lattice shift (`R3CompactCandidate.lean:162`), and the viscosity rescaling is
  **space-only**, so the singular time stays exactly `t = 1` (`ViscosityScaling.lean:93`).
  Combined with `ProblemStatement.lean:151`, the degenerate-collapse worry of my E-3 is
  answered for the *velocity*: it is provably not the zero field, with an explicit rate.
* `no_global_solution_one` (my row #53) is a real theorem: weak–strong uniqueness by localized
  energy + `L⁶` Sobolev + Young with the dissipation retained + Grönwall + `R → ∞`
  (`R3/WholeSpaceComparisonClosure.lean:32`), and the competitor's pressure is pinned by Riesz
  recovery plus an `H^{-3}` harmonic Liouville argument (`R3/PressureRecovery.lean:407`,
  `R3/HarmonicTestFunctionals.lean:100`) rather than assumed. Upgrade row #53 from UNCLEAR to
  OK-by-delegation; the internals of the Grönwall closure remain unread by me.

**Child B's correction is already folded in above** (E-6): no in-repo certificate that the
shipped *periodic* force is nonzero, and `option_D_of_candidate` /
`MaximalLifespan.candidate_excludes_global_solution` are dead on (D) — which matches my
Finding S2. Child B also confirms `pressure_periodic` of the competitor is consumed all the way
down: `PeriodicViscosity.lean:65` → `PeriodicViscosityUniqueness.lean:89` →
`PeriodicUniqueness.lean:652` → `energy_balance:499` → `:533`
`cubeIntegral_pressure_energy_zero (:435)`. That makes E-2 concrete: the periodic pressure
hypothesis is used in the *energy balance* step, so a non-periodic-pressure competitor really
would escape this argument.

**Revised verdict counts including delegation:** OK 62, UNCLEAR 8, KERNEL-RISK 0, SUSPICIOUS 0
in my own 70-row table; across all three reports: OK 85, UNCLEAR 11, SUSPICIOUS 1,
KERNEL-RISK 0.

## Residue — what I could NOT check and why

1. **Nothing was compiled.** No built Mathlib on this box (disk full), so I could not run
   `lake build`, could not see the output of the two `#print axioms` commands at
   `ComparatorSolution.lean:31-32`, and could not confirm that the identical source text of
   the two structure copies elaborates to identical terms (E-1). All type-correctness claims
   here are source-level readings, not machine checks. In particular I cannot exclude an
   elaboration-level mismatch between the copy and the reference, nor a `simp`/`norm_num`
   call that silently fails to close a goal (that would surface only as a build error).
2. **The construction itself.** `ActualCandidate.selected_candidate_one_with_initial_rest`,
   `ViscosityScaling.*`, `WholeSpaceUniqueness.*`, `ParabolicScaling.compressedCandidate`,
   `PeriodicLocalization.*` and `PeriodicViscosityUniqueness.*` — the real mathematics —
   were delegated to two read-only children (`ns-spine-r3branch.md`,
   `ns-spine-periodicbranch.md`) and are marked UNCLEAR in my table (#49, #53, #58, #60,
   #61, #67).
3. **`CandidateConsequences.lean:136-217`** (`Consequences`, `consequences_of_candidate`,
   `h3_tendsto_of_speed_tendsto`, `mixed_*`) was skimmed only; none of it is reached by the
   two deliverable theorems.
4. **Closure-wide reading.** I read 19 files fully out of 753 local modules in the closure
   (404 520 lines). My kernel-risk statements about the other 734 files are grep-census
   statements, not readings: a risky construct hidden behind an unusual spelling (e.g. a
   recursor applied via `open`ed namespace abbreviation, or `Nat` arithmetic produced by
   `decide` on a compound `Decidable` instance) could have escaped the regexes. I did check
   the obvious spellings and found the counts reported above.
5. **`ComparatorChallenges/NavierStokes.json`** and `formalization.yaml` (the harness metadata)
   were not audited; whether they point the Comparator at the declarations I inspected is
   outside what I could verify.
