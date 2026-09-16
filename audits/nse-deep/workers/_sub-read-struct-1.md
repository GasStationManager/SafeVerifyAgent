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
