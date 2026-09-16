# Worker `_sub-read-struct-1` — structural files audit (NSE @ f9e8bc5, READ-ONLY, no build)

## FILE 1: NavierStokes/IntegratedMeanBalances.lean (949 lines, 106 decls, 2 structures)

Scope: full read, lines 1-949. Cross-file greps over all `NavierStokes/*.lean`.

### What the file does
`moment n f = ∫ r, r^n * f r` (line 22) — a FULL-LINE Bochner integral, not `∫_(0,∞)`.
On top: integration-by-parts identity `moment_deriv_succ` (66), the two radial divergence /
viscosity operators (83-90), their vanishing weighted moments (122,134,196,211), parameter
(slow-variable) differentiation under the integral (237-335), a unit-square torus average
(345-531), then the two "line (32)/(34)" chart balances `angularBalance` (619) /
`axialBalance` (629) and their integrated forms (639, 674, 735, 833, 843, 931).

### Math spot-checks (all pass)
* `moment_deriv_succ` (66): ∫r^{n+1}f' = -(n+1)∫r^n f. Correct; both endpoint terms killed by
  `HasCompactSupport`.
* `moment_angular_viscosity` (196): ∫(r²f''+rf'-f) = 2∫f - ∫f - ∫f = 0. Correct.
* `moment_axial_viscosity` (211): ∫(rf''+f') = -∫f' + ∫f' = 0. Correct.
* `pressure_moment` (146): p'=g ⟹ moment 1 p = -(1/2)moment 2 g. Correct.
* `weighted_*_ae` (92,99,166,173): the `r ≠ 0` a.e. set (55) is used correctly; the 1/r and 1/r²
  singularities are removed only a.e., which is legitimate for the Bochner integral. OK.

### Findings

**F1-1 (NOTE, unsupplied-hypothesis, weak form). `structure SmoothShell` (line 582) has exactly
three producers in the whole 641k-line artifact, and NONE of them is a velocity or flux field.**
Producers: `averagedRadialSource_shell` (899), `reconstructedMeanPressure_shell` (904),
`normalizedMeanDensity_shell` (912) — i.e. only the pressure, the averaged radial source and the
normalized density. `SmoothShell.partial` (586) and `SmoothShell.add` (590) are closure lemmas
(assume it to conclude it), so they do not count. Grep over `--include=*.lean` for any decl
CONCLUDING `SmoothShell` returns only these five lines. Consequence: every consumer that needs
`SmoothShell a b v` / `γ` / `radialFlux` / `axialFlux` / `virtualFlux` — i.e.
`integrated_angular_balance` (639), `integrated_axial_balance` (674),
`integrated_axial_reconstructed` (735), `integrated_angular_positive` (833),
`integrated_axial_positive` (843), `integrated_axial_constructed_pressure` (931), and downstream
`SignedStressPrimitive.angular_bump_identity` (SignedStressPrimitive.lean:991),
`axial_bump_identity` (:1014), `axial_bump_constructed_pressure_identity` (:1030),
`angular_bump_improvedClass` (:1047), `axial_bump_improvedClass` (:1066) — can only ever be
instantiated by a caller who supplies these shells by hand. Direction is safe (the hypotheses are
satisfiable: they are true of e.g. any smooth bump field), so this is NOT falsity; it is deadness.

**F1-2 (NOTE, dead terminal theorems).** The file's own physically-meaningful endpoints — the ones
that convert the full-line `moment` into the physical half-line integral `∫ r in Ioi 0` — have NO
consumer anywhere: grep finds `integrated_angular_positive` (833) and
`integrated_axial_constructed_pressure` (931) only at their own definition site;
`integrated_axial_positive` (843) is used only internally at line 944. Likewise the two
`SignedStressPrimitive` class-improvement theorems that consume this file's balances
(`angular_bump_improvedClass` :1047, `axial_bump_improvedClass` :1066) have no consumer; the live
chain that reaches `SignedMeanGain.lean:794-797` goes through the *same-named twins*
`StateMomentBalances.state_*_bump_improvedClass` (StateMomentBalances.lean:1081,1096) and
`GaugeMomentBalances.state_*_bump_improvedClass` (GaugeMomentBalances.lean:816,869), which are
built on `StateMomentBalances.angularBalanceAlong/axialBalanceAlong`
(StateMomentBalances.lean:630,666) — a different balance operator. So this file's `angularBalance`
/`axialBalance` branch is a parallel, currently unused copy. Beware of name collision when
attributing credit to `state_angular_bump_improvedClass`: there are two of them
(SignedStressPrimitive-based and GaugeMomentBalances-based).

**F1-3 (NOTE, half-line vs full-line).** `moment` (22) integrates over all of ℝ, so `radialMoment`
is only the physical radial moment when the shell is genuinely to the right of 0. Only
`positive_integral_eq_integral` (224) / `positive_radialMoment` (826) supply that bridge and they
DO require `0 < a` (826) — correct as stated. But the three main identities (639, 674, 735) do NOT
assume `0 < a`, nor `a < b`. With `b < a`, `RadiallySupported a b F` forces `F ≡ 0` (support ⊆
`Icc a b = ∅`), so those identities have a degenerate instance in which every field vanishes; they
are still non-vacuous for good `a b` because `a b` are universally quantified. NOTE, not ESCALATE.

**F1-4 (OK, checked and clean). `structure TorusPeriodic` (line 360) IS genuinely constructed.**
`StateMomentBalances.lean:52` (`pullback_periodic`) builds it from
`PressureStream.TorusPeriodicLift`, and it is then consumed by `average_torusDerivative`
(StateMomentBalances.lean ~74-86). Its two closure lemmas (368, 492) are not the only source. Note
the same-name twin `FourierAlias.TorusPeriodic` (FourierAlias.lean:31, a Prop-valued `def` over
integer `Frequency` translations) which is the widely used one — the two are distinct predicates
(unit translations of two named coordinates vs all integer translations); the artifact keeps them
straight, `pullback_periodic` is the only bridge.

**F1-5 (OK, kernel risk: none).** No `inductive`, no `.rec`/`Acc.rec`, no `termination_by`, no
`deriving`, no `decide`, no metaprogramming, no `native_decide`. Both `structure`s are
`Prop`-valued with non-recursive fields. Largest numeral in the file: `2` (exponents `r ^ 2`,
`1 / 2`, `pow_one`). Zero big-numeral arithmetic.

**Verdict FILE 1: 106 decls read. OK 101 / NOTE 5 (F1-1, F1-2 counts 2 statements: 833+931 dead,
F1-3, plus the parallel-copy note) / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.**
The mathematics is correct and the integration-by-parts core is genuinely load-bearing (used from
`SignedStressPrimitive`, `DefectIncrementBounds`, `StateMomentBalances`, `LocalSignedRequest`).
What is defective is only reachability: the `SmoothShell`-gated chart balances and their half-line
("physical") corollaries are a dead parallel branch, and no flux field in the artifact ever gets a
`SmoothShell`.

## FILE 2: NavierStokes/MeanStateRegularity.lean (491 lines, 67 decls = 56 theorems + 5 structures + 2 Prop-defs + 4 abbrevs)

Scope: full read, lines 1-491. Cross-file greps for every structure's producers and consumers.

### What the file does
A pure *closure/assembly* file. It defines two Prop-defs (`Periodic` 26, `PositivePeriodic` 30) and
five structures (`OperatorData` 81, `BaseData` 213, `PeriodicTriple` 219, `MovingTriple` 228,
`PrimitiveData` 339), and shows that the nonlinear fluxes, residuals and source `gr` of a mean state
inherit smooth + moving-support + torus-periodicity from the *individual* input fields. It ends in
`localData` (435), which builds `SignedMeanGain.LocalData` — a live, load-bearing record: consumed at
`CorrectionStep.lean:8547` and `CrossBasedMeanComposition.lean:466`.

### Findings

**F2-1 (ESCALATE-lead, vacuity, cross-file; the single most important thing in either file).
The only unconditional producer of `PrimitiveData` (line 339) proves its `mean` field with three
copies of `MovingField.zero`, i.e. it is instantiated at an IDENTICALLY ZERO mean triple.**
Chain: `ActualInitialization.initial_primitive` (ActualInitialization.lean:670) =
`ActualInitialCoherence.initialized_primitive` (ActualInitialCoherence.lean:715) =
`initialized_primitive_of_seed ... (seed_primitive B N0)`, and `seed_primitive`
(ActualInitialCoherence.lean:644) discharges the `mean : MovingTriple U a b u.mean` field by
`exact ⟨MovingField.zero, MovingField.zero, MovingField.zero⟩` (ActualInitialCoherence.lean:649),
which typechecks only because `(seed B N0).mean.radial/.angular/.axial` are DEFINITIONALLY `0`.
`MovingField.zero` is this file's line 112 (via `Periodic.zero` line 41 and
`GaugeDebtIncrement.Regular.zero`). The seed's covariance is NOT zero
(`seed_covariance_regular`/`_periodic`, ActualInitialCoherence.lean:640-642), so `PrimitiveData` is
not wholly trivial — but the *mean velocity* of the artifact's base state is zero, and this file's
entire `MovingTriple`→flux/residual closure (253-333) is exercised at `m = 0` at the base case,
where `thetaRadial`, `axialAxial`, `radialRadial`, ... are all identically 0 and every `gr`,
`thetaResidual`, `axialResidual` reduces to its virtual/covariance part. Reinforcing evidence that
the mean is *never* changed by the wave stage: `PrimitiveData.waveStage` (this file, 408) proves the
mean field by `rw [SignedMeanGain.waveStage_mean]; exact H.mean` (414-415) — the wave stage adds only
covariance. Whether `temporalBands`/`rankBands` (ActualInitialCoherence.lean:41-46, via
`MeanStageRegularity.rankStage_primitive`) ever make `u.mean` nonzero is OUTSIDE my two files and is
the exact question to hand to the initialization/cycle worker. Matches the established precedent
(`InitialPhysicalData.lean`, 177 theorems surviving `cartesianPotential = 0`).

**F2-2 (NOTE, pattern 6 candidate — stronger hypothesis next to a weaker used twin, in the SAME
file). `Periodic` (26, all radii R) vs `PositivePeriodic` (30, only `0 < R`).**
`PositivePeriodic` exists nowhere else in the artifact (grep: only MeanStateRegularity.lean:30, 38,
83, 89, 151, 163, 215-217) and is used exactly where it must be — the base coefficients and the
graph/radial profile, which are genuinely not smooth or periodic through the axis (`BaseData` 213,
`coefficient_mul` 148). But the mean/covariance fields are required to satisfy the STRONGER
`Periodic` (through `GaugeMomentBalances.MovingField.periodic`,
GaugeMomentBalances.lean:466, which `MeanStateRegularity.Periodic` is a definitional alias of). For a
`MovingField` with `0 < a`, the two are provably EQUIVALENT: `Regular.zero_of_nonpositive`
(GaugeDebtIncrement.lean:277) gives `f n z = 0` for `z.1 ≤ 0` on the slow domain, and this file's
own line 156-158 uses exactly that argument. Only the easy direction is provided
(`Periodic.positive` 38); no `Periodic.of_positive` exists anywhere (grep). So callers must supply
periodicity at radii where the field is provably zero. Harmless in direction, and NOT dead (a
producer exists, F2-1), so NOTE, not ESCALATE. Flagged as a possible third instance of the
artifact's "stronger hypothesis beside a used weaker twin" pattern, with the caveat that here the
strengthening is provably equivalent rather than genuinely stronger.

**F2-3 (NOTE, one dead wrapper).** `localData_of_regular` (475) has no consumer anywhere (grep:
only its own definition); the live entry point is `localData` (435). Similarly
`MovingTriple.updated` (248) and `PrimitiveData.waveStage_of_regular` (420) have no external
consumer. Small, harmless.

**F2-4 (OK, checked).** All five structures are genuinely constructed, not hypothesis-only:
`OperatorData` by `OperatorData.native` (94, `refine ⟨⟨rfl, ?_⟩, fun _ _ _ _ _ _ _ => rfl⟩` — the
`radius = Prod.fst` normalization is `rfl` for `StateMomentBalances.nativeOperators`, and the
profile is Y-independent); `BaseData`, `PeriodicTriple`, `MovingTriple` and `PrimitiveData` all
through `seed_primitive`/`initialized_primitive` (F2-1). `PrimitiveData` is consumed as a hypothesis
in at least 10 files (ActualSignedNativeBounds, ActualSignedCoherence, ActualCycleCoherence,
ActualSignedOutputBounds, ActualIntermediateDebtBounds, SignedCrossDefectClass, ...), so this file is
on the live spine — unlike file 1's `SmoothShell` branch.

**F2-5 (OK, proof spot-checks).**
* `Periodic.directional` (64): the local-in-slow-parameter argument is correct — `he` is an
  eventual equality on the open slow domain (69-70), `EventuallyEq.fderiv_eq` + `fderiv_comp_add_right`
  is the right route, and `IsOpen U` is genuinely needed and genuinely supplied (`U.isOpen` at 144).
* `MovingField.coefficient_mul` (148): the axis case split (154-158) is exactly the honest argument —
  for `R ≤ 0` the supported factor vanishes by `zero_of_nonpositive`, so no periodicity of the base
  is needed there. Requires `0 < a`; `0 < a` is supplied at every call site
  (`G.patch.a_pos`/`ha`). Good.
* `OperatorData.inv_periodic` (89): closes by `simp only [Operators.invRadius, radius_eq]` since
  `invRadius = fun _ x => (x.1)⁻¹` (MeanIncrementBounds.lean:48 + LocalRankDefect.lean:127) is
  Y-independent. The `0 < R` hypothesis is intro'd and unused — correct, because `0⁻¹ = 0` in Lean
  is still Y-independent. Junk value present but never load-bearing: every consumer
  (`inv_mul` 182 → `coefficient_mul`) restricts to `positiveDomain`.
* `movingSupport` (201): the division by `qLength` uses `qLength_pos` (205) — the non-degeneracy IS
  certified, not assumed.

**F2-6 (OK, kernel risk: none).** No `inductive`, no `.rec`/`Acc.rec`, no `termination_by`, no
`deriving`, no `decide`/`native_decide`, no metaprogramming. Five `Prop`-valued structures, all
non-recursive. Largest numeral: `2` (`Fin 3` indices `0 1 2`, `smul ... 2`). No big-numeral
arithmetic. Both `Periodic` and `PositivePeriodic` are marked `noncomputable def ... : Prop`
(harmless, but `def` for a `Prop` means no structure eta/anonymous-constructor sugar; the file relies
on definitional unfolding into `MovingField.periodic`, which does typecheck at 110).

**Verdict FILE 2: 67 decls read. OK 63 / NOTE 3 (F2-2, F2-3 counts 1, plus the Prop-def alias
remark) / UNCLEAR 0 / ESCALATE 1 (F2-1) / KERNEL-RISK 0.**
The file itself is correct and is genuinely load-bearing. Its defect is not internal: the state it
is applied to has an identically zero mean triple at the base case.

### Global note (no `sorry` in the audited cone)
`grep -rn 'sorry|admit|native_decide' --include=*.lean .` finds `sorry` only in
`ComparatorChallenges/Euler.lean:88,184` and `ComparatorChallenges/NavierStokes.lean:277,284`,
which are self-documented intentional challenge placeholders outside `NavierStokes/`. Neither of my
files contains any.
