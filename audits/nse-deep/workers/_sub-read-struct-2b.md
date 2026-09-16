
# sub-read-struct-2b — structural files (READ-ONLY, commit f9e8bc5)

## FILE 1: NavierStokes/PulseCovariance.lean (829 lines, 91 decls, 3 structures)

Content: Gaussian pulse column concentration. `gaussian` (:40), `weight`/`mass`/`centeredMoment`
(:121-126), structures `PulseBounds` (:130), `CutoffBounds` (:145), `TangentPulse` (:637),
`abbrev SignedPulsePair` (:677), terminal theorems `compact_actual_positive_inverse` (:747) and
`compact_actual_positive_inverse_of_scalar_cone` (:801).

Verdict counts (91 decls): OK 84 / NOTE 4 / UNCLEAR 1 / ESCALATE 2 / KERNEL-RISK 0.

### ESCALATE-1 (shape 1 UNSUPPLIED HYPOTHESIS, whole-branch): `structure TangentPulse`
PulseCovariance.lean:637 is NEVER CONSTRUCTED ANYWHERE IN THE ARTIFACT.
Repo-wide grep for `TangentPulse` gives only argument/hypothesis positions:
  - PulseCovariance.lean:678 (`SignedPulsePair` = `(j : Fin 2) -> TangentPulse ...`),
    :681,:685,:689,:696,:702,:707,:716 (defs/theorems taking `pulses` as an argument),
    :756 and :809 (`forall pulses : SignedPulsePair ...` inside the two terminal theorems),
  - PartitionedCovariance.lean:345,:350,:354,:359,:369,:379,:393,:407,:418,:981,:1004 — all
    `(P : PulseCovariance.TangentPulse ...)` parameters.
Grep for the field names confirms it: `tangent_model` occurs at exactly two lines in the whole
artifact — its declaration (PulseCovariance.lean:643) and its projection use
(PulseCovariance.lean:711). There is no `TangentPulse.mk`, no `... : TangentPulse ... where`,
no field assignment `tangent_model := ...` anywhere.
Consequence: every statement whose only nontrivial input is a `TangentPulse`/`SignedPulsePair`
is DEAD (true but with no inhabitant ever produced). That covers PulseCovariance.lean:696
(`actualMatrix_factorization`), :701, :706, :715, :747, :801, and downstream
PartitionedCovariance.lean:979 (`PairData.ofSignedPulses`) and :995
(`compact_actual_pair_strictCone`).
Direction: SAFE (unreachable, not false). But the advertised payload of this file — "the actual
pulse pair has a nonsingular covariance matrix with positive inverse weights" — is never
instantiated for any actual object.
Contrast, and this is what makes the finding sharp: the OTHER structure of the same file,
`PulseBounds` (:130), IS genuinely constructed — PrimaryCovarianceBounds.lean:573 via
`PulseCovariance.pulseBounds_of_envelope` (:153), and used at PrimaryCovarianceBounds.lean:695
and PrimaryTargetBounds.lean:543; `CutoffBounds` (:145) is discharged at
PrimaryCovarianceBounds.lean:143 for `GaussianTailFlat.slotCutoff`. So the mass/moment half of
the file is live; exactly the three extra `TangentPulse` fields (`tangent` :640,
`tangent_continuous` :642, `tangent_model` :643 — i.e. the pointwise ODE tangent-direction
estimate `|t v i / x v - modelDirection c0 (affineSlope s0 slope r v) i| <= E/r^2`) are what
nobody ever certifies.

### ESCALATE-2 (dead leaves): the two terminal theorems are consumed by nothing outside their
own subtree. `compact_actual_positive_inverse` (:747) is used only at :821 by
`compact_actual_positive_inverse_of_scalar_cone` (:801), which is used only at
PartitionedCovariance.lean:1008 by `compact_actual_pair_strictCone` (:995), and grep shows
`compact_actual_pair_strictCone` and `PairData.ofSignedPulses` have ZERO further uses in the
artifact. Also `normalizedColumn_error_of_outer_scale` (:618) has zero uses. This branch does
not reach any main theorem.

### NOTES
- NOTE (shape 3, non-degeneracy not typed): `TangentPulse` (:637) carries `E` with NO sign
  hypothesis; `E < 0` makes `tangent_model` (:643) unsatisfiable. The consumers repair it by a
  separate `hE : 0 <= E` (:603, :707, :753, :807). Harmless but the type does not certify it.
- NOTE (coupling): `SignedPulsePair` (:677-678) instantiates `TangentPulse ... c0
  (signedSlopes u j) (signedSlopes u j) E`, i.e. the affine DRIFT slope is forced EQUAL to the
  base slope `s0 = +/-u` (:496,:515). Nothing justifies that identification here; it is what
  makes `|slope| = |u|` in :709 work (`signedSlopes_abs` :692). If the real ODE drift differs
  from `s0`, no pulse can ever be built — reinforcing ESCALATE-1.
- NOTE (junk-value-free, positive result): `mass psi x` is never divided by without proof —
  `mass_pos` (:310) is derived from `core_weight_lower` (:264) + `mass_lower` (:292), i.e. from a
  real interval of length `r/3` where `psi = 1` (`cutoff_one` :140 vs core interval :247). So
  `averagedDirection` (:361) is not a 0/0 junk value under `PulseBounds`. Clean.
- NOTE: `concentrationConstant` (:364) contains `firstGaussianMoment (2*b)` (:43), an unevaluated
  integral; only `>= 0` (:86) and finiteness (:81) are proved. The estimates are therefore
  qualitative in the constant, never numeric. Not a defect, but no explicit constant exists.
- UNCLEAR: `PulseBounds` two-sided Gaussian sandwich (:141-142) needs `B >= b` (roughly) for
  `a*gaussian B <= x <= A*gaussian b` to be jointly satisfiable on the whole slot; the structure
  does not relate `b` and `B` (only `0 < b`, `0 < B`). Satisfiable in practice (it IS constructed
  at PrimaryCovarianceBounds.lean:573), so I record it as UNCLEAR, not a defect.
- KERNEL RISK: none. No `inductive`, no `.rec`, no `decide`, no `termination_by`, no `deriving`.
  Largest numeral in the file: 36 (`core_scaled_sq` :255, `1/36`) and 18 (`exp (-B/18)` :266/:285).
  Two `local instance`s at :738 and :741 are `inferInstanceAs` on `Fin 2 -> Fin 2 -> R` — benign,
  and `local`.

## FILE 2: NavierStokes/ActualPhysicalPrefixFields.lean (493 lines, 43 decls, 1 structure, 1 Prop-def)

Content: converts per-stage polar chart identities into cylindrical germs. Prop-def
`AngularPeriodic` (:42), `structure StageRealizations` (:342), terminal theorems
`physicalFields_of_stages` (:438) and `physicalFields_all` (:475) producing
`ActualCycleResidualBounds.PhysicalData`.

Verdict counts (43 decls): OK 39 / NOTE 3 / UNCLEAR 1 / ESCALATE 0 / KERNEL-RISK 0.

### LIVE AND INSTANTIATED — the opposite of File 1 (this is the important positive result)
- `StageRealizations` (:342) IS constructed: ActualCandidateAssembly.lean:1059-1077
  (`stageRealizations B N0 hN`, all three fields discharged by `zerothPotential_on_chart` /
  `positivePotential_on_chart` / `direct_on_chart` / `zeroth+positivePressure_on_chart`).
- `physicalFields_all` (:475) IS applied: ActualCandidateAssembly.lean:1085 with EVERY hypothesis
  supplied, including `Hrep` from `ActualCandidateConstruction.cycle_representation B N0` (:1088)
  and `hfloor` from `twice_residual_scale` (:1086).
- Its output feeds real estimates: `ActualCandidateAssembly.physicalData` (:1079) -> `estimates`
  (:1090) -> and the `PhysicalData` consumer is
  `ActualCycleResidualBounds.Invariant.residual_jetRate` (ActualCycleResidualBounds.lean:1158-1171)
  / `finite_residual_rates` (:1190), i.e. an actual residual JetRate. Not dead.
- Non-vacuity of the germ side-conditions is certified elsewhere: the germ obligations are
  conditional on `z in source n` (:267, unfolding to `{p | 0 < p.2 0 and graphMapTZ G p in U}`,
  PhysicalResidualTZ.lean:388-389), and a CONCRETE such `z` with its membership is built at
  PhysicalResidualJetBounds.lean:933-948 (`z := ResidualPolarGraph.cylindricalPoint a j n w`,
  `hzU : z in graphSourceTZ ...` at :943-944). So this is not an empty-set theorem.

### NOTES
- NOTE (shape 6 CANDIDATE — stronger hypothesis beside the weaker twin actually used):
  `StageRealizations.velocity_prefix` (:358) assumes
  `hA : forall k, ContDiffOn R inf (A k) (physicalSublevel h qbig)` (:362) but uses it ONLY as
  `((hA k).mono _).differentiableOn` (:370); the callee `mixedVelocity_eqOn` (:211) takes exactly
  the weaker twin `hA : forall k, DifferentiableOn R (A k) V` (:214). Same pattern again at
  `physicalFields_of_stages` (:446 `hP : ContDiffOn R inf`) whose only use for pressure is
  `differentiableAt` (:465) (and `ContDiffOn.sum` at :464). Harmless (the caller has C-infinity from
  `stages_smooth`), but if the artifact already has 2 confirmed instances of this pattern, this is a
  third and fourth, and it is in a LIVE file.
- NOTE (same-named twin predicate — the trap the rubric warns about): `AngularPeriodic` is defined
  TWICE in the artifact with DIFFERENT bodies: here at :42
  (`forall z, Function.Periodic (fun theta => f (replaceAngle z theta)) (2*pi)`, angle REPLACEMENT)
  and at MeanResidual.lean:56 (`forall q, f (angularShift q period) = f q`, angle SHIFT). They are
  mathematically equivalent but not definitionally interchangeable. This file does not `open
  MeanResidual` (:19), so no capture occurs, and the local one is really proved
  (`velocityTZ_periodic` :182, `pressureTZ_periodic` :193 from `represented_*_periodic` :137-174).
  Anyone cross-reading the two namespaces must not treat the names as one predicate.
- NOTE (strong-but-supplied hypothesis): `StageRealizations` fields (:344,:348,:352) quantify over
  ALL chart scales `forall a, 0 < a -> forall i k`, whereas `exists_cartesianChart` (:251-263) only
  ever produces the single point-dependent scale `a := z.2 0` (:261). The strong form is genuinely
  discharged (ActualCandidateAssembly.lean:1065,:1070,:1073 all `intro n hn a ha i k`), so this is
  a NOTE only.
- UNCLEAR: `cartesianChartDomain` (:271) is a triple intersection whose third factor is a preimage
  under `polarCoordinates a i`; nothing in this file shows it is nonempty for a GIVEN `(qbig,n,a,i)`,
  only that a valid chart EXISTS for each `z in source n` (`exists_validChart` :320). Fine for the
  germ arguments as written (they start from a point), recorded only for completeness.
- KERNEL RISK: none. No `inductive`, no `.rec`, no `decide`, no `termination_by`, no `deriving`.
  Largest numerals: `4` (:262), `2 * Real.pi` throughout, `2 * ChartScales.Q Nr` (:302). One
  smoothness-order coercion `WithTop.coe_le_coe.mpr le_top` (:460) — benign.

## FILE 3: NavierStokes/ClosedNativeWaveIdentities.lean (674 lines, 44 decls, 4 structures)

Content: pointwise (no-openness) wave identities. Structures `GeometryAt` (:360), `ExactAt` (:472),
`AngularData` (:527), `RawJetsAt` (:540); terminal theorems `native_realizes_curl_at` (:645) and
`native_divergence_zero_at` (:657).

Verdict counts (44 decls): OK 38 / NOTE 5 / UNCLEAR 1 / ESCALATE 0 / KERNEL-RISK 0.

### ALL FOUR STRUCTURES ARE CONSTRUCTED (checked repo-wide; opposite of File 1)
- `RawJetsAt` (:540): built here at :621 (`rawJets_of_localInput`) and outside at
  ActualSignedCommonDynamics.lean:110-126 and ActualParticularDynamics.lean:650,:873.
- `GeometryAt` (:360): built at ActualSignedCommonDynamics.lean:92-102 (from
  `CurlClassBounds.CylindricalGeometry`, itself built at :84-90) and ActualParticularDynamics.lean:492,
  :504 (plus a transport lemma at :465-466).
- `AngularData` (:527): built at ActualSignedCommonDynamics.lean:75-82 and
  ActualParticularDynamics.lean:530.
- `ExactAt` (:472): built at :573-593 (`RawJetsAt.corrected_exact`).
- Terminal theorems consumed: `native_realizes_curl_at` (:645) and `native_divergence_zero_at` (:657)
  at ActualSignedCommonDynamics.lean:208-210 and ActualParticularDynamics.lean:926,:945.
- Non-degeneracy is really certified in one place: `RawJetsAt.normal_ne` (:552) is discharged at
  ActualSignedCommonDynamics.lean:121-126 by contradiction against a strictly positive
  `ActualPrimaryBounds.normalFloor_pos`. That is a genuine certificate, not an assumption.

### NOTES
- NOTE (shape 3, non-degeneracy NOT certified by the type, ruled out one layer up): NONE of the four
  structures constrains `s.epsilon n` or `d.radialScale n`, and both silently degenerate the
  identities:
  `GraphDirections.axialField d s n _ = s.epsilon n . d.axial` (LinearWaveBounds.lean:109-110) is a
  CONSTANT field, so at `s.epsilon n = 0` the axial direction is the ZERO field: every
  `along Vz f x` vanishes, `GeometryAt.axial_radius` (:368) becomes `0 = 0`, and
  `cylindricalLaplacian`/`cylindricalDivergence` in :109, :152, :375 silently lose their axial term
  while all statements stay TRUE but weaker. Likewise `radialField d n x = d.radial +
  radialScale n . (radialProfile x . d.auxiliary)` (LinearWaveBounds.lean:106-107): at
  `radialScale n = 0` the radial field is constant too, and then `GeometryAt.radial_angular` (:369)
  and `radial_axial` (:370) become `0 = 0`. Positivity of epsilon does exist ONE LAYER UP
  (`ChartScales.epsilon_pos`, used e.g. BasePhaseGeometry.lean:86,:1018), so direction is safe.
  Contrast: the frequency non-degeneracy IS demanded in the type where it is needed
  (`hK : K <> 0` at :303, :330, :647, :660, used for `inverseCarrier_phaseFactor` at :323-324).
- NOTE (partly redundant field): with `Vtheta = fun _ => d.angular` (:649, :662) and `Vz =
  d.axialField s n` both CONSTANT maps in every actual application (both are supplied as
  `contDiffAt_const` at :500 and :653), `GeometryAt.angular_axial` (:371)
  `fderiv Vz x (Vtheta x) = fderiv Vtheta x (Vz x)` is `0 = 0` and carries no information in any
  instantiation that exists in this artifact. It is still discharged honestly
  (ActualSignedCommonDynamics.lean:102), so this is bookkeeping, not a defect.
- NOTE (phantom parameter): `ExactAt a s d n x` (:472) has NO field mentioning `s` (:474-489), and
  `AngularData a s d psi n` (:527) has no field mentioning `s` (:529-537), yet the conclusions they
  feed (`harmonicResidual_eq_at` :491, using `s.epsilon n` at :498) depend on `s`. So neither record
  constrains the strip data at all; every `s`-dependence of the identity is carried by the
  conclusion. Combined with the previous note, nothing in the hypothesis records excludes a
  degenerate strip.
- NOTE (same-named twins, exactly the trap the rubric warns about): FOUR distinct structures named
  `AngularData` exist: this one (:527), `DirectAngularDiagonal.AngularData`
  (DirectAngularDiagonal.lean:139, a DATA structure, not a Prop), `PrimaryResidualClass.AngularData`
  (PrimaryResidualClass.lean:71), `ActualInitialMeanEquation.AngularData`
  (ActualInitialMeanEquation.lean:41). Most `AngularData` hits in a repo-wide grep are the
  `DirectAngularDiagonal` one; do not read them as evidence for or against this one. The
  construction sites relevant to THIS record are only ActualSignedCommonDynamics.lean:78 and
  ActualParticularDynamics.lean:530.
- NOTE (interface widening is honest): `cylindricalCurl_vectorPotential_of_differentiable` (:302)
  keeps the minimal `DifferentiableAt` hypotheses and the C-infinity variants (:330, :343) are proved
  ON TOP of it; the C-infinity hypotheses are needed there for `phaseNormal_contDiffAt` (:226). This
  is the correct direction of the shape-6 pattern (weak core, strong wrapper) — unlike File 2.
- UNCLEAR: `vectorLaplacian_mode_split_at` (:165) and `linearResidual_mode_split_at` (:182) carry an
  implicit `pTheta : R` used ONLY through `hPhiTheta : along Vtheta Phi =f[nhds x] fun _ => pTheta`
  (:170, :192) and it never appears in the conclusion; the sole consequence used is
  `along Vtheta (along Vtheta Phi) x = 0` (`along_along_const_germ` :98). So the hypothesis is
  strictly stronger than what is used (locally-constant angular derivative, versus vanishing second
  angular derivative). Harmless and it is supplied honestly
  (`ExactAt.phase_angular` :488 is itself an existential), but a weaker twin hypothesis would do.
- KERNEL RISK: none. No `inductive` beyond the four `structure ... : Prop`, no `.rec`, no `decide`,
  no `termination_by`, no `deriving`, no metaprogramming. Only `fin_cases` on `Fin 3` and
  `Matrix.cons_val_*` simp lemmas (:396). Largest numeral: 2 (indices / `pow_two`, e.g. :129, :152).
  One `omit [NormedSpace R D] in` at :433 — benign.
