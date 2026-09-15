# Worker notes — Euler comparator→Evolution audit, SLICE: compact-vorticity-support propagation

Repo: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @f9e8bc5). READ-ONLY; no `lake build`
(no Mathlib artifacts, disk full). Instrument: line-by-line reading with python/grep. Every claim below is a
source reading, not a kernel check; where I depend on elaboration/defeq I say so.

Slice: the input `h.local_compact_vorticity_of_truncationFamily h.finiteEnergyTruncationFamily hc`
consumed at `Euler/ComparatorLocalEvolution.lean:94`.

## 0. Bottom line

Nothing in this slice is an assumption on the competitor. The whole chain
(truncation family → global Picard flow of the truncation → backward-transport + energy-escape → one
compact ball for a positive time) is *constructed* from the challenge-class fields
(`velocity_smooth`, `div_free`, `initial_condition`, `euler`, `integrable`, `globally_bounded_energy`)
plus the claimant-chosen datum hypothesis `hc : HasCompactSupport (vectorCurl u₀)`.
No lemma in the slice runs Evolution → challenge. No junk-value/vacuity trick is load-bearing.
No kernel-risk constructs at all (no `decide`, no big numerals, no recursor tricks, no macro/axiom/unsafe/partial).

Verdicts per declaration below. Summary: all **OK**, with two OK-with-caveat items
(§4 `nonnegative_time_square_smooth`, §11 clamped/junk conventions) and one scope caution (§12).

---

## 1. `Euler.EulerExistenceAndSmoothnessR3.exists_local_trapping_constants` — ComparatorLocalCompactVorticity.lean:32-58
**Statement (mine).** Given `hc` (compact support of the initial curl), there exist `A,M,δ>0`, `δ≤1`,
`δ*M<1`, with `tsupport (vectorCurl u₀) ⊆ ball A` and `‖v x t‖ ≤ M` for all `t∈[0,1]`, `‖x‖ ≤ A+1`.

**Mechanism.** `hc.isBounded.exists_pos_norm_le` gives `A`. `M` = sup of `‖v‖` on the *compact* cylinder
`Icc 0 1 ×ˢ closedBall 0 (A+1)`, from `h.velocity_joint_contDiffOn.continuousOn` (Euler/ScalarEulerVorticity.lean:63,
itself `h.velocity_smooth` composed with coordinate swap) + `IsCompact.image_of_continuousOn`. Then
`δ := min 1 (1/(2M))`, so `δ*M ≤ 1/2 < 1`. All inputs are challenge-class fields.

**Verdict: OK.** Note `δ` depends on `M` = local sup speed, hence on `v` and on the support radius `A`.
That is legitimate for an ∃-statement and is exactly the shape the caller consumes.

## 2. `truncation_realField_agrees` (private) — ComparatorLocalCompactVorticity.lean:62-69
Says: the endpoint-clamped `realField` of `F.coefficient R` at time `r∈[0,1]` equals `v · r` where `‖x‖<R`.
Proof = unfold `realField`/`projIcc_of_mem` + `F.agrees`. **OK** (pure bookkeeping; `omit h`).

## 3. `locallyTrappedBackwardFlows` — ComparatorLocalCompactVorticity.lean:73-155
**Statement (mine).** For `T ∈ [0,δ]`, builds a `ComparatorBridge.BackwardVorticityFlows T F.energy (A+1)
(tsupport (vectorCurl u₀)) (vectorCurl u₀) (vectorCurl (v · T))` record, i.e. an R-indexed family of
global backward flows with uniform energy `F.energy`, plus the two nontrivial fields
`transport_nonzero` and `forward_trap`.

**Mechanism, field by field** (radius inflation `ρ R := max R (A+2)`, coefficient `C R := F.coefficient (ρ R)`):
- `flow/velocity`: `TruncatedBackwardFlow.homeomorph/velocity` of `C R` = the *actual Picard flow* of the
  time-reversed truncation (TruncatedBackwardFlow.lean:39-47 → `EulerSmoothBanachFlow.flowData`
  (SmoothBanachFlow.lean:40) → `EulerBoundedLipschitzFlow.Data` (BoundedLipschitzFlow.lean:21-63) →
  `EulerPacketExistence.exists_global_solution` (EulerProof.lean:18264), a *proved* global Picard theorem
  glued from finite intervals with ODE uniqueness). Boundedness + global Lipschitz constant come free from
  `SmoothTimeField` (field and jets are `→ᵇ`, so `‖fderiv‖ ≤ ‖A.derivative.field‖`,
  SmoothBanachFlow.lean:30-38). **This is why the truncation is needed at all**: the untruncated `v` has no
  global bound, so no global flow; the truncation is bounded and Lipschitz, hence has a genuine global flow.
- `preserves_volume`: `homeomorph_measurePreserving` (TruncatedBackwardFlow.lean:173) ← Jacobian
  determinant ≡ 1 from trace-free derivative (SmoothFlowVolume.lean:19-43). Fed by `F.divergence`.
  Note `EulerSmoothLimit.divergence` (EulerProof.lean:5216) *is* `LinearMap.trace ℝ Space (fderiv …)`,
  so the `exact` is a defeq match; I could not elaborate it, so this is "as written it type-checks" trust.
- `velocity_memLp`, `energy_bound`: from `F.memLp`, `F.energy_bound` at radius `ρ R` — **uniform in R and s**.
- `curve_continuous / speed_continuous / curve_derivative`: flow regularity lemmas of the Picard flow.
- `initial_support`: `subset_tsupport`.
- `transport_nonzero` (:121-138): the real content. If the backward trajectory stays inside `R`, then
  `‖X R s x‖ < R ≤ ρ R`, so the truncated velocity *equals* `v` along the path (`truncation_realField_agrees`),
  hence the path is a genuine reverse-time Euler particle path and
  `h.vorticity_ne_zero_along_reverse_trajectory` (ReversedVorticityTransport.lean:21) applies. That lemma
  reduces to `h.vorticity_eq_zero_along_trajectory` (ScalarEulerVorticity.lean:83), which is the vorticity
  transport law derived from the challenge Euler equation: curl of the equation
  (`vorticity_hasDerivAt` :30, using `h.pointwise_euler`, `h.div_free`, scalar pressure) + material
  derivative identity (:47) + a Grönwall/linear-ODE zero-propagation lemma
  (`ComparatorBridge.transport_eq_zero_along_trajectory`, VorticityTransport.lean:73 → `linearODE_eq_zero`).
  Boundary time `t=0` is covered by `vorticity_continuousOn` (:76), also from `h`.
  **So the "transport bound" is not assumed anywhere: it is the curl of the challenge equation.**
- `forward_trap` (:139-155): traces the *forward* path `endpointPath` from `a ∈ tsupport (vectorCurl u₀)`
  (so `‖a‖ ≤ A`) and applies `EulerComparatorLocalFlow.norm_lt_of_local_speed_bound` (LocalFlowTrap.lean:38),
  a clean first-exit-time mean-value argument: with `‖X 0‖ ≤ A`, speed `≤ M` *only while* `‖x‖ ≤ A+1`,
  and `T*M < (A+1)-A = 1` (from `T ≤ δ`, `δ*M<1`), the path never reaches radius `A+1`. The speed bound
  for the truncated field is transferred from `hspeed` by agreement, valid since `A+1 < A+2 ≤ ρ R`.

**Verdict: OK.** Extra arguments (`F`, `A`, `M`, `δ`, `T`, `hAbound`, `hspeed`) are all *supplied* at the
call site from `h` (§5, §1); none of them is a hypothesis about a competitor solution.

## 4. `BackwardVorticityFlows` + its consequences — NoIncomingVorticity.lean:48-151
**Structure (:48-68).** Data record; it is *not* used as an assumption on the competitor: the only place it
is instantiated in this chain is §3, where every field is discharged.

**`escapes` (:79)**, **`measure_nonzero_outside_le` (:94)**, **`measure_nonzero_outside_eq_zero` (:114)**,
**`zero_outside` (:131)**, **`support_subset_closedBall` (:142)**: the argument is
"finite kinetic action ⇒ nothing arrives from infinity":
- if `w x ≠ 0` with `‖x‖ > supportRadius`, the backward path from `x` must leave every ball of radius `R`
  (else `transport_nonzero` + `forward_trap` bound `‖x‖ ≤ supportRadius`);
- `flow_escape_measure_le` (FlowEscapeBound.lean:171) then bounds
  `volume S ≤ energy·T²/(R-K₀)²` for any bounded measurable set `S` of such points — via Cauchy–Schwarz on
  the displacement (`curve_escape_sq_le_action` :70), measure-preservation to convert Eulerian energy into
  Lagrangian action (`flow_action_integrable_and_bound` :99, Fubini + `MeasurePreserving.integral_comp`),
  and Markov (`escape_measure_le_of_action` :142);
- `R → ∞` kills the measure; continuity of `w` upgrades a.e. to pointwise (`positive_volume_set_of_nonzero_outside` :28).
I read all of FlowEscapeBound.lean; the estimates are ordinary and correct-looking. `nlinarith` at :166 with
small rational constants only.

**Verdict: OK.** Crucially the *same* `energy` works for all `R` — which is what §5 supplies.

## 5. `finiteEnergyTruncationFamily` — ComparatorTruncationFamily.lean:69-103
**Statement (mine).** A `def` producing `FiniteEnergyTruncationFamily v` (TruncationFamily.lean:16-25:
fields `coefficient : ℝ → SmoothTimeField (Icc 0 1) Space Space`, `energy : ℝ`, and the Props
`divergence`, `memLp`, `energy_bound`, `agrees`) from `h` alone.

**Mechanism.** `coefficient R := h.finiteEnergyTruncationTimeField R hR` for `0<R`, else the `R=1` field
(`dite` fallback — junk branch, see §11). The four Prop fields are discharged:
- `divergence` ← `finiteEnergyTruncation_divergence` (curl of anything is divergence-free);
- `memLp` / `energy_bound` ← `finiteEnergyTruncation_energy_bound` with
  `energy := truncationEnergyConstant * h.globally_bounded_energy.choose` (fixed multiple of the challenge
  class's own uniform energy bound; independent of `R` and `t` — exactly what §4 needs);
- `agrees` ← `finiteEnergyTruncation_eq` (equality with `v` on `‖x‖<R`).
Inputs used: `h.velocity_smooth`, `h.velocity_contDiff` (ClassicalBridge.lean:21), `h.div_free`,
`h.velocity_memLp` (ClassicalBridge.lean:29, from the challenge field `integrable : MemLp (‖v·t‖) 2` via
`memLp_norm_iff`), `h.globally_bounded_energy`.

**Verdict: OK — no assumed field, no `sorry`, no extra hypothesis.** It is a total `def` in
`Prop`-obligation-free form: all four obligations are closed inside the same declaration.

## 6. `finiteEnergyTruncationSquareTimeField` / `finiteEnergyTruncationTimeField` — ComparatorTruncationFamily.lean:36-64
Builds the `SmoothTimeField` on `Icc 0 1` for the *square* time `t ↦ v(·,t²)` via
`SmoothTimeField.ofContDiffOnCompactSupport` (CompactSmoothTimeField.lean:125), then reparametrizes by
`unitSqrtTime` (continuous, :19). `_apply` (:52) shows the composite field at `t` is literally
`finiteEnergyTruncation (v · t) R`. Requirements met: joint smoothness (§7), common compact support
`closedBall 0 (2R)` (`finiteEnergyTruncation_support`, needs `0<R`), compactness of `Icc 0 1`.
**Verdict: OK.** `SmoothTimeField` (SmoothTimeField.lean:13-19) ties `jet n t x` to the *actual*
`iteratedFDeriv` (`jet_eq`), so nothing here is a formal placeholder.

## 7. `nonnegative_time_square_smooth` — TruncationFamilySmooth.lean:78-84 (and :88 wrapper)
**Statement.** `ContDiffOn ℝ ∞ v (univ ×ˢ Ici 0)` ⇒ `ContDiff ℝ ∞ (fun (x,t) ↦ v (x, t²))`.
**Mechanism.** `contDiffOn_univ.mp` + `ContDiffOn.comp` with `MapsTo` into `univ ×ˢ Ici 0` (since `t² ≥ 0`).
This is exactly Mathlib's `ContDiffOn.comp`, so the boundary-time smoothness is obtained *without* any
Whitney-type extension theorem and without strengthening the hypothesis.
**Verdict: OK (caveat).** This is the one place where a reader may suspect "smooth up to the boundary" is
being silently upgraded. It is not: the conclusion is a `ContDiff` of the *even reparametrisation*, which is
a legitimate consequence of Mathlib's `ContDiffOn.comp` on a set with nonempty interior. Everything
downstream only uses the square-time field plus a *continuous* sqrt reparametrisation, so no time-derivative
of `v` at `t=0` is ever claimed. I could not elaborate it (no build), so I flag it as
OK-modulo-`ContDiffOn.comp` semantics.

## 8. `FiniteEnergyTruncation.lean` — definitions and exported statements
Read in full; I **skimmed the inner algebra** of the purely computational estimates (`nlinarith` steps at
:268, :301, :316, :345, :356) and of `curl_negativeCrossPotential` (:54, `fin_cases`+`ring`).
- `negativeCrossPotential` (:25), `radialAverage` (:73) `= ∫₀¹ t·u(tx) dt`, `radialPotential` (:179).
- `curl_radialPotential` (:187): the radial homotopy formula `2A + (x·∇)A = u` (:136) plus
  `divergence_radialAverage = 0` (:121, needs `div u = 0`) gives `curl (radialPotential u) = u`.
  So the potential is *constructed*, not assumed.
- `potentialTruncation u χ := curl (χ · radialPotential u)` (:196): automatically divergence-free (:204)
  and supported in `tsupport χ` (:209).
- `potentialTruncation_eq` (:218): equals `u` where `χ ≡ 1` near `x`.
- `potentialTruncation_error_bound` (:272) / `_norm_bound` (:304) / `_energy_bound` (:320):
  `‖trunc‖² ≤ 2‖u‖² + 288C²‖radialAverage u‖²` and `∫‖trunc‖² ≤ (2+1152C²)∫‖u‖²`, using
  `radial_average_memLp_and_energy` (imported: `∫‖radialAverage u‖² ≤ 4∫‖u‖²`, i.e. a Hardy-type bound).
  Only zeroth-order data of `u` enters — no derivative of `u` in the bound. That matters: the challenge class
  gives no global control of `∇v`, so a bound needing `∇v` would have been a smuggled hypothesis. It does not.
- `scaledCutoff` (:360) + `truncationCutoff R := scaledCutoff bump R` (:402): `‖∇χ‖·‖x‖ ≤ C` is
  *scale-invariant* (:370), so `truncationEnergyConstant` (:474) is one fixed number independent of `R`.
- `finiteEnergyTruncation` (:442) and its five exported lemmas (:445-467, :482).
**Verdict: OK.** Numerals are tiny (`2, 4, 12, 288, 1152`); no `decide`, no numeric kernel work.

## 9. `local_compact_vorticity_of_truncationFamily` — ComparatorLocalCompactVorticity.lean:159-171
**Statement (mine).** From `h`, *some* truncation family `F`, and `hc`: there are `δ>0` and `B` with
`tsupport (vectorCurl (v·t)) ⊆ closedBall 0 B` for **all** `t ∈ [0,δ]`.
**Mechanism.** `δ, A, M` from §1 (`δ ≤ 1`, needed because `F` lives on `Icc 0 1`); `B := A+1`; for each
`t ∈ [0,δ]` instantiate §3 at `T := t` and apply `support_subset_closedBall` (§4) to
`w := vectorCurl (v·t)`, continuous by `vectorCurl_smooth (h.velocity_contDiff t ht.1)`; `closure_minimal`
upgrades `Function.support ⊆` to `tsupport ⊆`.
**Verdict: OK.** Note the ball `A+1` and `δ` are chosen *once, before* `t`, so the conclusion is genuinely
uniform on `[0,δ]` — which is what `exists_evolution_of_commonCompactCurl` needs (one compact `K`).
`local_compact_vorticity` (:177) is the same statement with `F := h.finiteEnergyTruncationFamily`.

## 10. Caller fit — ComparatorLocalEvolution.lean:91-97
`compactCurlLocalUpgrade` consumes exactly `⟨δ, B, hδ, hsupport⟩` and passes
`K := closedBall 0 B`, `hK := isCompact_closedBall`, `T := δ`, `hT := hδ` to
`exists_evolution_of_commonCompactCurl`. **Uniformity is sufficient**: single `δ>0`, single compact ball,
all `t ∈ Icc 0 δ`. Nothing in the caller asks for `δ` independent of `v`, nor for `δ` bounded below by a
universal constant.

## (a) Assumed vs proved
**Nothing in this slice is an assumption on the competitor.** Concretely:
- `local_compact_vorticity_of_truncationFamily` takes `F : FiniteEnergyTruncationFamily v` as an *argument*,
  which looks like a hypothesis — but the only instantiation is `h.finiteEnergyTruncationFamily`
  (ComparatorTruncationFamily.lean:69), a `def` that builds all 4 Prop fields from `h`. So the family is
  a construction, not an assumption.
- The only non-`h` hypothesis in the slice is `hc : HasCompactSupport (vectorCurl u₀)`, a property of the
  *claimant's own* initial datum, not of the competitor solution.
- No `Prop`-valued `def` obligation is left open in the slice; `compactCurlLocalUpgrade`
  (ComparatorLocalEvolution.lean:91) is a proved instance of the `CompactCurlLocalUpgrade` interface.

## (b) Direction
No lemma in the slice needs Evolution-class data. All arrows are challenge → construction:
`h` → truncation family → global flows → transport/escape → compact support. `BackwardVorticityFlows`
(NoIncomingVorticity.lean:48) is the only record that *could* have been used as a "nice-solution" hypothesis,
and it is discharged in §3 rather than assumed.

## (c) Junk values / vacuity
Three conventions, none load-bearing:
1. `coefficient R` for `R ≤ 0` falls back to the `R=1` field (ComparatorTruncationFamily.lean:72-73, `dite`).
   All Prop fields of the structure are guarded by `0 < R`, and every consumer uses `ρ R = max R (A+2) > 0`.
   No vacuity is exploited (the guard is never the reason a claim holds).
2. `SmoothTimeField.realField` / `TruncatedBackwardFlow.velocity` clamp time by `projIcc`
   (TruncatedBackwardFlow.lean:44-59): outside `[0,T]` the velocity is frozen at the endpoint value, so the
   flow is globally defined. Every use is inside `[0,T]` via `velocity_eq_realField`'s `hs : s ∈ Icc 0 T`.
   This is an *extension*, not a `0`-junk fallback, and the ODE facts used hold on `Ioo 0 T`.
3. No `toL2`-style "= 0 when not MemLp" fallback appears in the slice; `SmoothTimeField.field` is a genuine
   `→ᵇ` bounded function and `jet_eq` pins jets to real `iteratedFDeriv`. No `fderiv = 0` junk is used:
   every derivative statement carries a `HasDerivAt`/`HasFDerivAt` witness or a `ContDiff` hypothesis.
Also checked for vacuity of the *conclusion*: `tsupport (vectorCurl (v·t)) ⊆ closedBall 0 B` is a nontrivial
claim (no hypothesis forces the curl to vanish; `hc` only bounds its support at `t=0`).

## (d) Kernel-risk scan of the slice (18 files read)
Scanned `ComparatorLocalCompactVorticity`, `ComparatorTruncationFamily`, `FiniteEnergyTruncation`,
`TruncationFamilySmooth`, `TruncationFamily`, `SmoothTimeField`, `CompactSmoothTimeField`,
`TruncatedBackwardFlow`, `NoIncomingVorticity`, `FlowEscapeBound`, `LocalFlowTrap`,
`ReversedVorticityTransport`, `ScalarEulerVorticity`, `ClassicalBridge`, `BoundedLipschitzFlow`,
`SmoothBanachFlow`, `SmoothFlowVolume`, `ComparatorLocalEvolution`:
- `decide` / `native_decide`: **0 hits**. `axiom` / `sorry` / `unsafe` / `partial` / `macro` / `elab` /
  `syntax` / `set_option`: **0 hits**. `Acc.rec` / `WellFounded` / `termination_by`: **0 hits**.
- Numeral arithmetic: only `norm_num` (10 sites) and `positivity` (5) on trivial goals (`0<1`, `1<2`,
  `2*M>0`), and `nlinarith` (7 sites) with small integer coefficients (`2, 4, 12, 288, 1152`). No numeral
  larger than 4 digits anywhere in the slice; nothing that forces a bignum kernel reduction.
- Choice usage is ordinary: `classical` + `.choose` on `h.globally_bounded_energy`,
  `unitTruncationBump_derivative_bound`, and `Data.curve_exists` (Picard) — all existentials proved first.

## 12. Scope caution (outside my slice, but implied by it)
The support statement is *local in time*: `δ` is produced from the sup speed of `v` near the initial
vorticity support and is not bounded below by anything universal. So the whole conversion delivers an
`Evolution T hT` only for `T = δ`. Whoever audits the final contradiction must confirm it works for
*arbitrarily small* `T` (and that `Evolution`'s own extra fields are proved there, not assumed);
otherwise the local nature of this slice would become the weak link. Nothing in my slice hides that.
