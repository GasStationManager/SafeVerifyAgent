
# Worker _sub-read-struct-4 — structural files (READ-ONLY, commit f9e8bc5)

## FILE 1: NavierStokes/VolterraRegularity.lean (869 lines, 47 decls)

Content: radial smoothness of the regular Volterra inverse `regularPrimitive c f ξ = ξ • weightedMean c f ξ`
(NilpotentVolterra.lean:36,40), a scale bootstrap on nested complex disks, and the mixed-regularity capstones
for `IsSymmetricIntegralSolution`. The analysis is real and non-trivial (differentiation under the integral
with compact domination at :127-198, induction on the derivative order at :202, disk-gap Cauchy operators).

VERDICT: substantially CLEAN mathematics; the findings are reachability/deadness, not falsity.

### SETTLED: `SmoothCoefficientData` (:660) IS CONSTRUCTED — not an unsupplied hypothesis
- Declared :660-664 (3 fields: `forcing`, `zeroth`, `first`, all joint `ContDiffOn ℝ ∞ ... (radialDomain R ×ˢ U)`).
- CONSTRUCTED as a field of a constructed parent: `SmoothHolomorphicSystem` (PositiveAxisExistence.lean:173,
  field `smooth : SmoothCoefficientData T U A₀ A₁ f` at :174) is CONCLUDED by
  `LowerInputRegularity.system` (PositiveAxisExistence.lean:341-345), whose proof builds the anonymous
  constructor `smooth := { forcing := ..., zeroth := ..., first := ... }` at :348-356 from
  `LowerInputRegularity` (:333, whose `denominator : ∀ z ∈ U, ell h z ≠ 0` at :339 is a real non-degeneracy).
  A second construction: `SmoothHolomorphicSystem.restrict` (PositiveAxisExistence.lean:188-200) rebuilds
  the `smooth` field by `.mono`.
- It is really consumed: `symmetric_solution_parameterJets_radial_contDiffOn_local` (:750) is applied at
  PositiveAxisExistence.lean:55 and :59 (jets k=0, k=1), and `.smooth` is fed in at
  PositiveAxisExistence.lean:396 / :419.
- `LowerInputRegularity` itself is concluded at SlowRecursion.lean:633, so the whole chain has a supplier.
  => OK (the candidate is retired).

### NOTE 1 (dead leaves, safe): :830 `symmetricSolution_mixed_contDiffOn` and :848
`symmetricSolution_mixed_contDiffAt_zero` demand
`SmoothCoefficientData R U (VolterraParity.symmetricRawCoefficient hR A₀) ... (symmetricRawField hR f)`
(:838-839, :856-857). Grep over all of `NavierStokes/`: nothing anywhere concludes a
`SmoothCoefficientData` whose arguments are the `symmetricRaw*` wrappers (the only supplier gives it for
`coefficient0/coefficient1/sourceField`), and neither theorem is cited anywhere outside this file.
So these two are unreachable specializations — safe in direction, but they are the *statement shape* the
file's docstring advertises ("no regularity of that output is an input", :828). The live path is the
generic :767/:750 pair, which is supplied.
Also unused outside the file: :767, :790, :802 (only the `_local` variant :750 is consumed).

### NOTE 2 (degenerate-parameter windows, generic-in-R so not vacuous):
`radialDomain R = Metric.ball 0 R` (:28) is EMPTY for `R ≤ 0`, and `Disk center ρ = closedBall center ρ`
is empty for `ρ < 0`. Many theorems take only `hR : 0 ≤ R` (:406, :461, :668, :767, :790, :802, :830), so
at `R = 0` every `ContDiffOn ... (radialDomain R)` conclusion is vacuously true; likewise `hρ : ∀ j, ρ j <
ρ (j+1)` (:464) never forces `ρ j ≥ 0`, so an all-negative radius sequence makes the disk-curve conclusions
statements about maps out of `∅`. WITNESS that the interesting regime is reached, so this is only a NOTE:
take `R = 1 > 0`, `δ = 1`, `ρ = interiorRadii 1` (:723) giving `ρ j = 1 - 1/(j+2)`, i.e. `ρ 0 = 1/2 > 0`,
`ρ 1 = 2/3`; `interiorRadii_pos` (:725) gives `0 < ρ j`, `interiorRadii_increasing` (:734) gives `hρ`, and
`interiorRadii_subset` (:742) gives `hDisk` inside any `U ⊇ ball center 1`. The strict capstone
`symmetric_solution_mixed_contDiffAt_zero` (:779) does demand `0 < R`. So the nondegenerate case is real,
and it is exactly the one used at :758-762.

### JUNK-VALUE SWEEP (grep `/` and `⁻¹` in statements): three divisions only —
:133 `δ := (R - |r|)/2` (proof-local, denominator literal 2), :723 `δ - δ/((j:ℝ)+2)` and :736 the same,
denominator `(j:ℝ)+2 ≥ 2 ≠ 0` always. NO unconstrained denominator, NO `⁻¹` anywhere. Clean.

### KERNEL-RISK SWEEP: no `inductive`, no `class`, no `deriving`, no `decide`, no `Acc.rec`, no
`termination_by`, no metaprogramming. One structural recursion, `cauchyJetCurve` (:533-539), recursing on
a `ℕ` argument with a `k+1 => derivativeCLM (... k (j+1) ...)` step — plain structural, accepted without a
termination hint; its equation lemmas are used via `simpa only [cauchyJetCurve]` (:573, :577). Largest
numeral in the file: `6` (`Fin 6`, e.g. :410, :433) and `4`/`2`/`1` in radius arithmetic. No big-numeral
arithmetic. => no kernel risk.

### Spot checks that came out clean
- :87 `regularPrimitive_hasDerivAt_on` clips to `[-a,a]` with `a` strictly between `|r|` and `R` (:93-95) and
  transfers back with `EqOn` (:111-121): the clip is genuinely eliminated, the claim is about the original `f`.
- :202/:224 the gain-one-derivative induction really uses `weightedMean_hasDerivAt_on` (:213), whose
  domination constant `K` comes from compactness of `closedBall 0 b` with `b < R` (:133-143) — no global bound smuggled in.
- :461 the bootstrap's `heq` obligation is discharged from `hW.integral_equation` (:518) and the value
  identities `hbval/ha₀val/ha₁val` (:471-475), i.e. the disk-valued surrogates are pinned to the actual
  coefficients on the radial domain, not free.
- :660 `SmoothCoefficientData` is `Prop`-valued with three `ContDiffOn` fields; it does NOT assume anything
  about `W`, so it is not a disguised conclusion.

FILE 1 TALLY: 47 decls read — OK 44 / NOTE 3 (:830+:848 unreachable specialization counted once, :406/:464
degenerate-window, plus the unused-generic remark) / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## FILE 2: NavierStokes/WaveStateRegularity.lean (304 lines, 28 decls)

Content: smoothness + annular support ("Regular", GaugeDebtIncrement.lean:26) of angular covariances of the
harmonic wave state. Live and consumed: `bilinearCovariance_regular` (:166) and `covarianceIncrement_regular`
(:179) are used at CorrectionStep.lean:8749,8761,8765, ActualInitialMean.lean:264,
ActualInitialCoherence.lean:490, with `WaveSupport` supplied by `fieldSum_support` (:226) at
ActualWaveRegularity.lean:484 / ActualInitialMean.lean:253 and by ActualWaveRegularity.lean:445.

### SETTLED — ESCALATE 1: `CoefficientSupport` (:197) IS NEVER CONSTRUCTED, and it is the STRONGER
### member of a stronger/weaker twin pair whose WEAKER member carries all the live traffic.
- `noncomputable def CoefficientSupport ... : Prop` at :197-201: for every active label, every harmonic
  index `j` and every point, `(blocks l).velocity n i j x ≠ 0 → x.1 ∈ Icc (qLength coord x.2.1 * a)
  (qLength coord x.2.1 * b)` — support control at the level of the *complex Fourier coefficients*.
- Exhaustive grep over `NavierStokes/`: the ONLY occurrences are the definition :197 and the six
  hypothesis positions :211, :250, :261, :272, :282, :293-294. NOTHING concludes it: no theorem, no
  anonymous constructor, no instance, no field of any constructed structure (it is a `def`, so it has no
  fields and no `.mk`). (`LabelSupportPreservation.lean:322/450` are a `section CoefficientSupport` name
  only, not the predicate.) => UNSUPPLIED HYPOTHESIS, shape 1.
- Consequence: the entire tail of the file is DEAD — :209 `fieldSum_support_of_coefficients`,
  :248 `fieldSum_covariance_regular`, :258 `fieldSum_covarianceIncrement_regular`,
  :269 `state_covariance_regular`, :278 `state_covarianceIncrement_regular`, and the file's capstone
  :288 `waveStage_covariance_regular` — 6 in-cone theorems, none of them cited anywhere outside this file.
- SAME-NAMED TWIN TRAP (confirmed, do not misread the grep): the `waveStage_covariance_regular` that
  CorrectionStep.lean:7549 and GaugeDebtIncrement.lean:372,394 actually use is
  `GaugeDebtIncrement.waveStage_covariance_regular` (GaugeDebtIncrement.lean:360), a DIFFERENT theorem.
  WaveStateRegularity's :288 has zero consumers.
- SHAPE 6 (stronger hypothesis beside a weaker used twin) — this is a candidate THIRD instance of the
  named pattern: coefficient-level `CoefficientSupport` (:197, unused, unconstructed) sits next to
  oscillation-level `fieldSum_support` (:226, hypothesis = per-label `SupportedGauge` of the assembled
  oscillation), which is weaker, IS constructed (ActualWaveRegularity.lean:445, :483) and carries every
  live application. :209 is precisely the bridge from the strong form to the weak form and is the dead one.
- Direction: safe (unreachable, not false); cost: the "state / waveStage" adapter layer of this file
  proves nothing about any object the artifact ever builds.

### NOTE 3: the file-local `structure LocalData` (:97-104) IS constructed, but only by
`LocalData.of_global` (:111-117, with `C := fun _ _ => univ`), and `of_global` has NO caller anywhere;
`LocalData` appears outside :97-130 only in the dead block :249-291. (Again a same-named twin: the
`LocalData` used by CorrectionStep/CrossBasedMeanComposition is `SignedMeanGain.LocalData`,
SignedMeanGain.lean:820, constructed at MeanStateRegularity.lean:444.) So `block_smooth` (:119) and
`fieldSum_smooth` (:127) are reachable in principle (via :111) but have no live consumer either.

### VACUITY WITNESS for the live route (so :166/:179 are not empty statements):
`SupportedGauge a b ell U f` (VariableGaugeMean.lean:67-69) says `f z ≠ 0 → z.1 ∈ Icc (ell z.2.1 * a)
(ell z.2.1 * b)`. This DEGENERATES to "f = 0 on U" if `b < a` or if `ell ≡ 0`, and `a b : ℝ` are
unconstrained in :166, :179, :226. But the nondegenerate regime exists and is the one used:
`ell = VariableGaugeMean.qLength coord` and `qLength_pos` (VariableGaugeMean.lean:174) gives
`0 < qLength coord s` whenever `0 < coord`, `coord < 1`, `0 < s.1`. WITNESS: `coord = 1/2`, `s.1 = 1`,
so `q := qLength (1/2) s > 0`; take `a = 1`, `b = 2`; then `Icc (q*1) (q*2)` is a nonempty interval of
positive length `q`, so a wave with `f z ≠ 0` at `z.1 = 3q/2` satisfies `SupportedGauge` — the hypothesis
does not force the field to vanish. Consistent with `angularAverage_supported` (:152), which needs the
integrand nonzero for *some* θ. => not vacuous.

### JUNK-VALUE SWEEP: the only division in the file is `angularAverage` (CorrectionState.lean:73-74),
`(∫ θ in 0..2π, f n (x,θ)) / (2 * Real.pi)`, and :54 `.div_const (2 * Real.pi)` — the denominator is the
literal `2 * Real.pi ≠ 0`, never a free variable. No `⁻¹` in any statement of this file. (For the record,
the neighbouring `VariableGaugeMean.density` (VariableGaugeMean.lean:64) does invert an unconstrained
`ell z.2.1`, but that is outside my three files.) Clean here.

### KERNEL-RISK SWEEP: no `inductive`, no `class`, no `deriving`, no `decide`, no `termination_by`, no
`.rec`, no metaprogramming; one `classical` (:87). Finiteness comes from `Finsupp.support` sums
(`field_expansion`, HarmonicFields.lean:112) and `Finset.sum_eq_zero`. Largest numeral: `3` (`Fin 3`) and
`2` in `2 * Real.pi`. => no kernel risk.

FILE 2 TALLY: 28 decls read — OK 21 / NOTE 1 (:97/:111 constructed-but-unconsumed) / UNCLEAR 0 /
ESCALATE 6 (:209, :248, :258, :269, :278, :288 — all dead behind the never-constructed `CoefficientSupport`
:197) / KERNEL-RISK 0.

## FILE 3: NavierStokes/AxisCoefficientSpace.lean (460 lines, 52 decls)

Content: the Banach space of the manuscript's weighted axis coefficients — normalized bounded-continuous
jets `((ℕ×ℕ) × I.interval) →ᵇ ℝ` (:49) cut down by the closed linear FTC identity `Compatible` (:92-95),
so that a point really does determine smooth functions whose stored higher coordinates ARE their
derivatives (:142 `hasDerivWithinAt_jet`, :164 `iteratedDerivWithin_jet`, :180 `contDiffOn_jet`).

VERDICT: CLEAN, and it is the positive control for two of the rubric's defect shapes.

### It is LIVE, and both directions are constructed (no unsupplied hypothesis here)
- `Window` (:28) is constructed: `ActivationHolomorphic.parameterWindow` (ActivationHolomorphic.lean:699-702,
  `nondegenerate := by norm_num`).
- Elements of the space are constructed: `ofJetFamily` (:330) is used at AnalyticCoefficientBounds.lean:222,
  AxisOperators.lean:138 and :213, AxisInverseFactors.lean:107 — always as
  `ofJetFamily I (weight ε) (weight_pos hε) ...`, i.e. with strictly positive weights.
- Consumed downstream: `coefficient_ext` (:263) at AxisOperators.lean:160,172,236,247,256,267,
  AxisInverseFactors.lean:136, AxisEvaluationAlgebra.lean:249; `hasDerivAt_jet_interior` (:156) at
  AxisEvaluation.lean:186,455 and AxisAnalyticCoefficients.lean:22; `abs_jet_sub_le` (:217) at
  AxisContraction.lean:675,687; `axisSpace_norm_le_iff` (:450) at AxisResolvent.lean:316.
  (Twin warning: `ShapeTransition.lean:1248` declares an unrelated `abs_jet_sub_le`.)

### JUNK-VALUE SWEEP — PASSES, unlike the two known defects. Every statement that divides by the weight
carries the nonvanishing hypothesis IN ITS OWN SIGNATURE:
:224 `normalized_derivative` has `hw : ∀ n m, w n m ≠ 0`; :233 `quotient_abs_derivative` and
:245 `norm_le_iff_derivative_bound` have `hw : ∀ n m, 0 < w n m`; :276 `rawOfJetFamily` and :330
`ofJetFamily`, :387 `ofSmoothFamily` all take `hw : ∀ n m, 0 < w n m` before the `/ w` in their bodies
(:280, :293); the ε-level statements :442 and :450 take `hε : 0 < ε` and route through
`AxisWeightEstimates.weight_pos` (AxisWeightEstimates.lean:55). The unweighted bound statements use
`|w n m|` (:205, :212, :219) so they are correct even for a signed weight. NO unguarded division found.

### NOTE 4 (shape 3, mitigated but real): `AxisSpace I ε` (:430) is a TYPE that does not certify `0 < ε`.
Concretely, `weight ε n m = (1/20)^n * (ε⁻¹)^m * m! * (n+m).choose m / (((n:ℝ)+1)^2 * ((m:ℝ)+1)^2)`
(AxisWeightEstimates.lean:28-30). At `ε = 0`, Mathlib gives `(0:ℝ)⁻¹ = 0`, so
`weight 0 n 0 = (1/20)^n / ((n+1)^2) > 0` but `weight 0 n m = 0` for every `m ≥ 1`. WITNESS of the
degeneracy: in `AxisSpace I 0` every jet with `m ≥ 1` is identically `0` (by `jet` :52-53), so
`Compatible` (:92) at `m = 0` reads `jet A n 0 x = jet A n 0 I.left + ∫ 0`, i.e. the coefficient functions
are forced CONSTANT. The two ε-statements that carry no `hε` — `axisSpace_complete` (:434) and
`axisSpace_smooth` (:437) — are therefore true but content-free at `ε = 0` (constants are smooth). This
is only a NOTE, not an escalation: the two quantitative ε-statements (:442, :450) DO take `hε : 0 < ε`,
and every downstream construction supplies `weight_pos hε`. Similarly `w : ℕ → ℕ → ℝ` is unconstrained in
the generic half of the file (:52-:220): with `w ≡ 0` every `jet` is `0`, `Compatible` holds for all `A`,
and `CoefficientSpace I 0 = RawJets I` — the smoothness/bound theorems then say nothing. The file is
honest about this: exactly the statements whose content needs nonvanishing (`normalized_derivative` :224,
`coefficient_ext` :263, and all constructors) demand it.
COUNTER-PATTERN worth recording: `Window.nondegenerate : left < right` (:31) certifies nondegeneracy IN
THE TYPE, and that is what feeds `uniqueDiffOn_Icc I.nondegenerate` (:153, :382, :395) — without it
`iteratedDerivWithin` on `Icc` would be junk. This is the artifact doing shape 3 the RIGHT way.

### NOTE 5 (dead but harmless): the `ofSmoothFamily` block (:387 def, :398, :409, :419) has no caller
anywhere outside this file; only the `ofJetFamily` route is used. Also with no external caller:
`quotient_abs_derivative` (:233), `axisSpace_complete` (:434), `axisSpace_smooth` (:437),
`axisSpace_derivative_bound` (:442), `contDiffAt_coefficient_interior` (:195). These are presentation
lemmas; `ofSmoothFamily` is proved correctly (its jets are the genuine `iteratedDerivWithin`, :404-405).

### KERNEL-RISK SWEEP: one `structure Window` (:28, three fields, no recursion), one `Submodule` bundle
(:98), one `instance coefficientSpace_complete` (:132, from `IsClosed.completeSpace_coe`), three
`abbrev`s (:49, :130, :430 — reducible, no `decide`). No `inductive`, no `deriving`, no `termination_by`,
no `.rec`, no `decide`, no metaprogramming. The only induction is `iteratedDerivWithin_jet` (:167, plain
`Nat` recursion). Largest numeral in this file: `2` (in `Nat` exponents / index arithmetic); the numeral
`20` and the `factorial`/`choose` numerals live in AxisWeightEstimates.lean:28-30, outside my files, and
appear here only symbolically. => no kernel risk.

FILE 3 TALLY: 52 decls read — OK 50 / NOTE 2 (:430/:434/:437 ε-degeneracy; :387 dead `ofSmoothFamily`
block) / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## OVERALL (worker _sub-read-struct-4)
The one thing to carry forward: `WaveStateRegularity.CoefficientSupport` (WaveStateRegularity.lean:197) is
NEVER constructed anywhere in the artifact, killing 6 in-cone theorems (:209, :248, :258, :269, :278, :288)
including that file's `waveStage_covariance_regular` capstone — whose name collides with the LIVE
`GaugeDebtIncrement.waveStage_covariance_regular` (GaugeDebtIncrement.lean:360) that CorrectionStep.lean:7549
actually uses. By contrast `VolterraRegularity.SmoothCoefficientData` (VolterraRegularity.lean:660) IS
constructed (PositiveAxisExistence.lean:348-356, via `LowerInputRegularity.system` :341) and IS consumed
(PositiveAxisExistence.lean:55,59), so it should come off the unsupplied-hypothesis candidate list.
