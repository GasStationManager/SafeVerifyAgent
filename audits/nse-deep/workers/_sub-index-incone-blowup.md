# NSE deep audit — BLOWUP / DIVERGENCE mechanism (read-only)

Repo `/home/gsm/.openclaw/workspace/repos/NSE`, commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
No files modified, no build run (grep + reading only). Every claim below carries file:line.

## 0. Bottom line

**The blow-up is LABEL-FREE.** The `speed_unbounded` field of the headline
`CandidateProperties` is produced from ONE scalar lower bound,

    0 < W.axis.j        (`NavierStokes/NominalProfile.lean:63-64` field + `NavierStokes/NaturalAxisData.lean:44` `j_pos`)

on the axis datum `j` of the *slow / nominal profile* `W = ActualPrimary.nominal`.
The axis norm equals exactly `(1-t)^(-A h) * W.axis.j`
(`NavierStokes/BaseResidual.lean:90-101`), where `A h = 1/2 + h > 0`
(`NavierStokes/CoordinateAlgebra.lean:18`).
`j` is a *numeral-capped real*: `j := min (jcap/2) (1/2000)` with
`0 < j` by `lt_min (by positivity) (by norm_num)`
(`NavierStokes/MatchingConeBounds.lean:982-988`; a second, unused path at
`NavierStokes/PreparedOutgoing.lean:95-101`).
It is **not** a `Finset.sum` over wave labels, not `LabelSumBounds.fieldSum`,
not `activeLabels`, not `oscillation`, not `tangentSum`.

Consequence: an EMPTY wave-label type `Index B N0` would **not** falsify the
headline. It would instead make the entire label/wave/covariance layer
non-load-bearing for the singularity (see §5 for why that is still a serious
finding, in the opposite direction from "inhabitance gap").

## 1. Chain from the headline `speed_unbounded` down to the lower bound

Hop A — headline witness asks for `CandidateProperties …` (which contains
`speed_unbounded : SpeedUnboundedAtOne u`, `NavierStokes/R3CompactCandidate.lean:37`,
`NavierStokes/ProblemStatement.lean:114`; def of `SpeedUnboundedAtOne` at
`NavierStokes/ProblemStatement.lean:94-96`):
  `ActualCandidateAssembly.Witness` `NavierStokes/ActualCandidateAssembly.lean:1121-1158`
  proved by `ActualCandidateAssembly.witness` :1153-1163 =
  `GermCandidateAssembly.exists_candidate_witness_of_finite_stages …`
  (call site `NavierStokes/ActualCandidateAssembly.lean:1155`).

Hop B — inside that theorem the ONLY blow-up input is `haxis`:
  `NavierStokes/GermCandidateAssembly.lean:298`
    `have haxis := origin_blowup H v upper bandFloor hqbig initial stages D hInitialAxis hStagesAxis hat`
  then `:300-306`
    `exact CandidateConsequences.mixed_exists_force_with_consequences … hcut hz ea eb ep haxis`.
  (Note `hcut` at `:296` is `LocalAngularDiagonal.spatialCut_angularSum_divergence`,
  `NavierStokes/LocalAngularDiagonal.lean:183-195` — that is `spatialDivergence … = 0`,
  i.e. divergence-FREEness, NOT a divergence/blow-up statement. Name trap.)

Hop C — `CandidateConsequences.mixed_exists_force_with_consequences`
  `NavierStokes/CandidateConsequences.lean:185-215`, hypothesis
  `haxis : Tendsto (fun t => ‖MixedPeriodicAssembly.velocity A v (t,0)‖) (𝓝[<] 1) atTop`
  (`:194-195`), used at `:212` via `MixedPeriodicAssembly.exists_candidate_force`
  (`NavierStokes/MixedPeriodicAssembly.lean:338-368`), which discharges the
  `speed_unbounded` field with
  `periodicVelocity_speed_unbounded haxis` (`NavierStokes/MixedPeriodicAssembly.lean:366`,
  theorem at `:322-335`, which only needs `periodicVelocity_origin`
  `NavierStokes/MixedPeriodicAssembly.lean:87-89`; the time-activation step is
  `CandidateConsequences.mixed_activated_speed_tendsto` `:170-181` +
  `TimeLocalization.activatedVelocity_speed_unbounded_iff` `NavierStokes/TimeLocalization.lean:187`).

Hop D — `GermCandidateAssembly.origin_blowup` `NavierStokes/GermCandidateAssembly.lean:147-159`:
    `apply (FinalSlowBase.axis_tendsto H v upper bandFloor).congr'`   (:157)
    `exact (origin_eventually_base … hs).symm.mono (fun _ ht => congrArg norm ht)`  (:158-159)
  i.e. the mixed three-sum origin trace is *transported* onto the base field's
  divergence. The three stage sums contribute NOTHING; see §3.

Hop E — `FinalSlowBase.axis_tendsto` `NavierStokes/FinalSlowBase.lean:372-379`:
    `apply BaseResidual.baseVelocity_axis_tendsto_atTop (scales_strictMono …) h_pos h_lt_half
       (coefficients_smooth H v) W.axis.normalization (fun _ hn => (EntranceAlignedBase.modulated_positive_axis H v hn …).2.1)`
    `rw [leading_origin]; exact W.axis.small.j_pos`      (:377-379)
  where `FinalSlowBase.leading_origin` `:356-360` proves
  `(coefficients H v).axial 0 (0,0) = W.axis.j`
  from `EntranceAlignedBase.modulated_leading_axis`
  (`NavierStokes/EntranceAlignedBase.lean:861-863`:
   `(modulatedCoefficients H v).axial 0 (0,eta) = 4*eta + W.axis.j`).

Hop F — the actual divergence engine,
  `BaseResidual.baseVelocity_axis_tendsto_atTop` `NavierStokes/BaseResidual.lean:104-116`:
    `(BlowupImplication.negative_power_tendsto_atTop hA (BlowupImplication.remaining_time_tendsto 1)).atTop_mul_pos h0 tendsto_const_nhds`
  with `hA : 0 < CoordinateAlgebra.A h` (`:110`, `A h = 1/2+h`) and
  `h0 : 0 < d.axial 0 (0,0)`; congr'd onto
  `BaseResidual.baseVelocity_norm_at_origin` `NavierStokes/BaseResidual.lean:90-101`:
    `‖baseVelocity a h C d (t,0)‖ = (1-t)^(-A h) * d.axial 0 (0,0)`.
  Base velocity itself: `FinalSlowBase.velocity = SlowBorelBase.baseVelocity (scales) h W.axis.normalization (coefficients H v)`
  (`NavierStokes/FinalSlowBase.lean:274-275`, def `NavierStokes/SlowBorelBase.lean:1179-1181`).

(The same engine, label-free, exists in the "core" layer:
`NaturalCore.coreVelocity_norm_at_origin` / `coreVelocity_axis_tendsto_atTop`
`NavierStokes/NaturalCore.lean:419-443` with `hj : 0 < j`;
`NaturalCore.speedUnbounded_of_axis_tendsto` `:443-456` is the generic
`Tendsto ‖u(t,0)‖ → SpeedUnboundedAtOne u` converter.)

## 2. The LOWER BOUND, verbatim and by object

Statement carrying the positivity (quoted, `NavierStokes/BaseResidual.lean:90-95`):

    theorem baseVelocity_norm_at_origin {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
        (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients}
        (hd : SmoothCoefficients d) (C : ℝ)
        (hz : ∀ j, 0 < j → d.axial j (0, 0) = 0) (h0 : 0 < d.axial 0 (0, 0))
        {t : ℝ} (ht : t < 1) :
        ‖baseVelocity a h C d (t, 0)‖ =
          (1 - t) ^ (-CoordinateAlgebra.A h) * d.axial 0 (0, 0)

The bounded-below object is the **leading axial coefficient of the slow
(Borel) expansion, evaluated at the axis point `(X,η) = (0,0)`**:
`d.axial 0 (0,0)`, with `d = FinalSlowBase.coefficients H v = EntranceAlignedBase.modulatedCoefficients H v`
(`NavierStokes/FinalSlowBase.lean:99`). Its value is pinned to the profile's
axis datum: `= W.axis.j` (`NavierStokes/FinalSlowBase.lean:356-360`), positive by
`W.axis.small.j_pos` (`NavierStokes/FinalSlowBase.lean:379`).

Supporting label-free facts consumed at the axis:
* higher slow orders vanish on the axis: `hz` supplied by
  `EntranceAlignedBase.modulated_positive_axis` `NavierStokes/EntranceAlignedBase.lean:866-870`
  (`.axial n (0,eta) = 0` for `0 < n`), used through
  `BaseResidual.slowSum_eq_leading_of_positive_zero` `NavierStokes/BaseResidual.lean:36`
  (call at `:81`) and `ProfileHistories.average_at_axis` `NavierStokes/ProfileHistories.lean:169`.
* `AxisymmetricFields.velocity_on_axis` reduces the curl to the axial component
  (`NavierStokes/BaseResidual.lean:76-79`).
* the schedule `a : ℕ → ℕ` enters only as `StrictMono a` (cut-off bookkeeping);
  no divergence claim is made about a sum over `a`.

## 3. WHY the label-indexed sums cannot contribute (this is the decisive part)

`GermCandidateAssembly.origin_eventually_base` `NavierStokes/GermCandidateAssembly.lean:107-145`
proves that at the ORIGIN, eventually as `t → 1⁻`,

    MixedPeriodicAssembly.velocity (potentialSum … A) (potentialSum … B) (t,0)
      = FinalSlowBase.velocity H v upper bandFloor (t,0)

with three ingredients:
1. `potentialSum_eq_base_germ` `NavierStokes/GermCandidateAssembly.lean:76-96`:
   near a point where `initial` and every `stages j` has a ZERO GERM, the whole
   potential diagonal equals the base field `TailGaugePotential.finalPotential`
   (uses `AxisPreservation.potentialSum_eq_first_near` `NavierStokes/AxisPreservation.lean:65`
   and `SmoothCutoffs.scaledCutoff_eventually_one`).
   The zero-germ input is `AxisZeroOn` (`NavierStokes/GermCandidateAssembly.lean:23-25`).
2. the direct/angular sum is EXACTLY zero on the axis:
   `DirectAngularDiagonal.angularSum_axis` `NavierStokes/DirectAngularDiagonal.lean:315-319`
   (`angularSum a q b (t,x) = 0` when `x 0 = x 1 = 0`), applied at
   `NavierStokes/GermCandidateAssembly.lean:138-141`.
3. `TailGaugePotential.finalPotential_sameCurl` `NavierStokes/TailGaugePotential.lean:448-450`:
   `spatialCurl (finalPotential …) w = FinalSlowBase.velocity … w` for `w.1 < 1`.

And the `AxisZeroOn` obligations for the *wave-carrying* stages are discharged
in the actual assembly, i.e. **every label-indexed field is identically zero in a
neighbourhood of the axis**:
* `ActualCandidateAssembly.axis_not_active` `NavierStokes/ActualCandidateAssembly.lean:643-648`:
  a preterminal point with `radialProjection w = 0` is NOT in
  `ActualPolarCoverage.active`, because
  `ActualCurrentWaveSupport.profileRadius_zero_of_axis` `NavierStokes/ActualCurrentWaveSupport.lean:42-44`
  gives radius `0`, while `PrimaryTargetBounds.leftRadius_pos nominal > 0`
  (annulus test `profileRadius_mem_iff_active` `NavierStokes/ActualCurrentWaveSupport.lean:61-67`).
* hence `particular_axisZeroOn` `:592-599`, `signed_axisZeroOn` `:649-654`,
  `stream_axisZeroOn` `:466-472`, combined into
  `positivePotential_axisZeroOn` `:680-686`, and `initialPotential_axisZeroOn` `:144-149`;
  these are precisely the arguments passed at `NavierStokes/ActualCandidateAssembly.lean:1161`.

So the wave layer (labels, covariance, oscillation, `LabelSumBounds.fieldSum`,
`tangentSum`) lives in an ANNULUS bounded away from the axis and is *switched off*
exactly where the singularity is measured.

## 4. Vacuity check on the strict positivity (task item 4)

* `0 < W.axis.j`: field `j_pos` of `NaturalAxisData.SmallParameters`
  (`NavierStokes/NaturalAxisData.lean:41-45`: `h_pos, h_le ≤ 1/1000, j_pos, j_le ≤ 1/1000`).
  Instantiated with a concrete numeral-capped `j`:
  `MatchingConeBounds.preparedWitness_exists` `NavierStokes/MatchingConeBounds.lean:976-996`,
    `let j := min (jcap / 2) (1 / 2000)`, `hjpos : 0 < j := lt_min (by positivity) (by norm_num)` (:982-983),
    `hj : SmallParameters F.data.h j := ⟨F.data.h_pos, hh, hjpos, (min_le_right _ _).trans (by norm_num)⟩` (:987-988),
    `A := NominalProfile.AxisStage.ofEntrance hj prep Λ0 C0 …` (:995, def `NavierStokes/NominalProfile.lean:1759-1764`, stores `j` and `hj` verbatim).
  `jcap` itself is a *proved* positive real from
  `MatchingConeBounds.exists_ordered_prepared_continuation` `NavierStokes/MatchingConeBounds.lean:852-854`
  (`∃ rho, 0 < rho ∧ ∃ jcap, 0 < jcap ∧ jcap ≤ 1 ∧ …`) — a slow-profile matching-debt
  quantity on `Icc (-1) 1`, with no label index anywhere in its type.
  The choice reaches the headline through
  `NominalConeAssembly.Assembly.witness` = `G.assemblePrepared … A.matching …`
  (`NavierStokes/NominalConeAssembly.lean:1403-1405`, `:1058-1064`) with
  `assemble_axis : (G.assemble … A c …).axis = A` (`:992-996`, `rfl`), then
  `exists_certificate`/`exists_nominal_cone` `:1500-1521`,
  `FinalSlowBase.ProfileData`/`actualProfile` `NavierStokes/FinalSlowBase.lean:619-634`,
  `CorrectionInitialization.ActualPrimary.nominal` `NavierStokes/CorrectionInitialization.lean:3888`.
  Also re-exported as an axis-parameter bundle at `NavierStokes/BaseWitnessClosure.lean:43-47`.
* No hypothesis of the form `0 < c` with `c` a label sum appears anywhere on the
  divergence path. The only sums on that path are (a) the slow-order sum in `j`
  (`SlowBorelBase.slowSum` `NavierStokes/SlowBorelBase.lean:254-255`), whose positive
  orders vanish on the axis, and (b) the cut-off diagonal `tsum` over stages, killed by
  the zero germs. Both are indexed by ℕ (asymptotic order / stage), NOT by wave labels.
* `A h = 1/2 + h > 0` needs only `h > 0` (`NavierStokes/BaseResidual.lean:110`,
  `NavierStokes/CoordinateAlgebra.lean:18`).

## 5. Adversarial reading of this result

The parent's suspicion (an inhabitance-dependent headline) does **not** hold for
the blow-up. The inverse finding is worth stating loudly:

* If `Index B N0` were empty, then by the artifact's own empty branch
  (`NavierStokes/ActualInitialMean.lean:318-331`: `activeLabels … = ∅`,
  `(seed B N0).oscillation = 0`, `tangentSum B N0 = 0`) the whole oscillation field
  is identically zero, and **the headline `speed_unbounded` would still be proved**,
  because it is carried by `W.axis.j` alone (§1-§2). No contradiction with
  `ProblemStatement.lean:151` `zero_velocity_not_unbounded`, since the velocity is
  the base curl + zero, not zero.
* There is NO `Nonempty (Index W N)` instance in the repo — only
  `PrimaryGeometryAssembly.indexCountable (N) : Countable (Index W N)`
  (`NavierStokes/PrimaryGeometryAssembly.lean:141`). Grep for
  `Nonempty (Index …)` returns nothing (only `sourceIndex_nonempty` for a different
  type, `NavierStokes/ActualParticularPhysicalData.lean:615`). The artifact never needs
  labels to exist.
* Therefore the singularity is *prescribed*, not *produced*: the velocity's axis
  trace is the self-similar profile `(1-t)^(-(1/2+h)) * j` by construction of the
  slow base, and `CandidateProperties.navier_stokes`
  (`NavierStokes/ProblemStatement.lean:112-113`) only says the residual EQUALS the
  force `f`. The wave/label machinery is spent on regularity of that residual at
  `t = 1` (`VanishingJointJets`, `boundaryLimits`, force jets), not on the blow-up.
  The audit weight should therefore move to: (i) is the force genuinely constrained
  (it is smooth, spatially periodic, `CompactFutureTimeSupport`, decaying as
  `t → ∞`, and must match `boundaryLimits` at `t = 1`) and (ii) does anything force
  the force to be non-trivial / physically admissible on `(0,1)`? That is where a
  triviality objection, if any, must live — not at `speed_unbounded`.

## 6. Gaps in my own trace (explicit)

1. No compilation was performed (no `.olean`, toolchain mismatch by instruction), so
   all typing/defeq steps are read, not machine-checked. In particular
   `FinalSlowBase.velocity = SlowBorelBase.baseVelocity …` is a `def` (`:274-275`) and the
   `change`/`rw` steps in `FinalSlowBase.origin` `:362-370` are assumed to typecheck.
2. `origin_eventually_base` also needs `MixedAxisPreservation.origin_eventually_localDomain`
   (`NavierStokes/MixedAxisPreservation.lean:458`) and
   `radialProjection_origin` (`:309`); I read their statements/names but did not expand
   `MixedAxisPreservation.localDomain` (`:448`) to re-verify that the origin is inside it
   for all `t` near 1 — if that failed, the germ argument would fail, but the failure
   direction is "no blow-up transport", not "hidden label dependence".
3. I did not audit `hz : VanishingJointJets`, the residual bounds, or the force
   construction. Those are exactly the parts where the labels ARE used, and where an
   emptiness collapse would matter for SIGNIFICANCE (if all label sums are provably
   controllable when empty, the wave layer proves nothing) — flagged, not verified here.
4. I did not check the R3 / whole-space repackaging beyond noting
   `R3/ActualCandidate.lean:115` `speed_unbounded := hc.speed_unbounded` and
   `PeriodicSobolev.candidate_derivativeH3_unbounded`
   (`NavierStokes/PeriodicSobolev.lean:332-355`), both of which merely relay the same field.
