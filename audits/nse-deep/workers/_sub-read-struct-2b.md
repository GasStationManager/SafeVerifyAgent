
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
