# Worker report — question (A): does `no_euler_evolution_of_initial_H3` EARN its conclusion?

Repo under audit: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5).
Read-only. No `lake build` (no Mathlib on disk): every claim below is a source read, not an elaboration check.
Threat model per parent brief. Every claim carries file:line.

## Scope

READ IN FULL, line by line, every declaration:
- `Euler/PacketStageContradiction.lean` (73 lines, 2 decls: `false_of_evolution`, `no_euler_evolution_of_initial_H3`) — the target file.
- `Euler/PacketStageGrowth.lean` (95 lines, 5 decls) — divergence side.
- `Euler/PacketInductionStage.lean` (145 lines, 1 structure + 15 decls) — `Stage` invariant.
- `Euler/OrdinaryEulerDifference.lean` (150 lines, 1 structure + 12 decls) — `Evolution` = the notion of "Euler evolution".
- `Euler/OrdinaryEulerVaryingHorizon.lean` (109 lines, 4 decls) — the a-priori/no-escape side actually invoked.
- `Euler/OrdinaryEulerRestriction.lean` (44 lines, 4 decls).
- `Euler/OrdinaryH3Envelope.lean` (145 lines, 10 decls) — Gronwall envelope + `h3_stability`.
- `Euler/OrdinaryQuadraticStability.lean` (46 lines, 1 decl) — scalar comparison lemma.
- `Euler/ParentOrdinaryEvolution.lean` (58 lines, 2 decls) — how a stage supplies an `Evolution`.
- `Euler/PacketStageLocalExistence.lean` (86 lines, 2 decls) — the counterpart local-existence theorem (used for the vacuity question).

READ AT DECLARATION LEVEL + PROOF BODY OF THE CITED LEMMA (one level deep, targeted):
- `Euler/OrdinaryEulerStability.lean:17-47` (`referenceNormPath`, `referenceSize`, `referenceWordBound`, `gradient_continuous`).
- `Euler/OrdinaryH3Energy.lean:34-51` (`differenceRhs_pairing`), `:105-130` (`energyProduction`, `difference_energy_bound`).
- `Euler/OrdinaryH3Norms.lean:12-40` (`tensorNorm`, comparisons).
- `Euler/OrdinaryWordTime.lean:87-97` (`wordEnergy_hasDerivWithinAt`).
- `Euler/EulerProof.lean:12522-12542` (`no_escape_near_compact_trajectory`), `:8375-8383` (`real_smooth_fderiv_le_H3`), `:5202` (`Space := EuclideanSpace ℝ (Fin 3)`).
- `Euler/LpSmoothField.lean:31-54` (`SmoothL2Field`), `Euler/SmoothL2Series.lean:19-24`, `Euler/PacketFieldPhysicalSobolev.lean:18-20` (`derivativeSum`).
- `Euler/SmoothCoefficientTimeRestriction.lean:84-86` (`initialInclusion`), `Euler/VolterraConvolution.lean:20-25` (`extendPath`).
- `Euler/PacketBaseGuardScales.lean:14,22-26` (`baseHorizon`, `baseHorizon_pos`).
- `Euler/OrdinaryEulerLocalCauchy.lean:29-84` (`short_uniform_h3`, `exists_local_evolution_of_cauchy`).
- `Euler/PacketInductionScales.lean:83-113,123-143` (`Scales`, `exists_scales`), `Euler/PacketInfiniteConstruction.lean:1-77`, `Euler/BaseInductionStage.lean:22-40` (`firstStage`).
- `Euler/PacketStageInitialLimit.lean:84-114` (the sole consumer, and where `hinit` is discharged).
- `Euler/ParentEulerParity.lean:38-40` (`strain_origin`).

SKIMMED / NOT READ: everything under the successor constructions (`PacketForwardSuccessor`,
`PacketJoinedSuccessor`), `EulerPacketCommonScaleChoice.exists_common_guards`, the transport-commutator
estimates behind `differenceRhs_word_bound`, and the `ParentFrame` structure body
(`Euler/PacketSourceGeometryData.lean:25`). These are named as escalations, not audited here.

## Per-declaration findings

### 1. `EulerPacketInduction.Stage.no_euler_evolution_of_initial_H3` — Euler/PacketStageContradiction.lean:67 — [OK]
Exact statement (:67-69), with the section variables at :19-23 in force
(`{c B : ℝ} {S : Scales c B}`, `(P : ∀ n, Stage S n)`, `(u₀ : Space → Space)`, and
`hinit : Tendsto (fun n => derivativeSum 3 ((fun x => (P n).state.evolution.velocity (0,x))-u₀)) atTop (𝓝 0)`):

    theorem no_euler_evolution_of_initial_H3 :
        ¬ ∃ U : Evolution (baseHorizon S.J S.X) (baseHorizon_pos S.J S.j_one S.x_pos).le,
          (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field=u₀ := by
      rintro ⟨U,hU⟩
      exact false_of_evolution P u₀ hinit U hU

Mechanism: pure destructuring; all content is in `false_of_evolution`. Name matches statement:
it claims non-existence of an `EulerOrdinarySobolev.Evolution` on `[0, baseHorizon S.J S.X]` whose
time-0 velocity FIELD equals `u₀` — nothing stronger. It is a CONDITIONAL statement: `P` (an actual
stage family) and `hinit` (H³ convergence of stage initial data to `u₀`) are hypotheses.

### 2. `EulerPacketInduction.Stage.false_of_evolution` — Euler/PacketStageContradiction.lean:25-65 — [OK]
Statement: given the stage family `P` and `hinit`, plus a base-horizon `U : Evolution (baseHorizon S.J S.X) _`
with `(U.velocity 0).field = u₀`, derive `False`.
Actual proof mechanism, step by step:
- :29-35 sets `durations n := (P n).parent.T` (positive, `:30` from `parent.T_pos`), `durations n ≤ baseHorizon`
  from the STRUCTURE FIELD `(P n).horizon_le` (PacketInductionStage.lean:32); `V n :=
  (P n).state.regularity.ordinaryEvolution` (the stage's OWN Euler evolution on its own horizon);
  `times n := ⟨(P n).time, …⟩ ∈ Icc 0 (durations n)`.
- :36-44 `hfield`: the time-0 difference field of `U|[0,durations n]` versus `V n` is exactly
  `(fun x => (P n).state.evolution.velocity (0,x)) - u₀`. Uses `Evolution.difference` (:81-82 of
  OrdinaryEulerDifference.lean, `fieldSub (V.velocity t) (U.velocity t)` — V minus U, sign correct),
  `hU₀`, and `velocity_match` (the Sobolev record's field agrees with the classical velocity).
- :45-49 `hnorm`: `tensorNorm 3 (difference …) = derivativeSum 3 (…)` via
  `tensorNorm_eq_derivativeSum` (SmoothL2Series.lean:19). So `hinit` becomes an H³ statement about
  genuine L² jets (`hlim`, :50-53).
- :54-55 applies `U.no_gradient_escape_of_initial_tendsto_varying` (OrdinaryEulerVaryingHorizon.lean:96)
  to get `¬ Tendsto (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) atTop atTop`, then
  `apply hno` — i.e. the remaining goal is to PROVE that divergence.
- :56-65 identifies that sequence with `(P n).activationGradient` (`velocity_match` + `rfl`, since
  `activationGradient` is by definition `‖fderiv ℝ (fun x => state.evolution.velocity (P.time,x)) 0‖`,
  PacketStageGrowth.lean:49-50) and closes with `gradient_atTop P` (PacketStageGrowth.lean:83).
Verdict: the contradiction is exactly "PROVED divergence + PROVED a-priori comparison". No
`Classical.choose`, no extra hypothesis, no `sorry` in this file (0 occurrences).

### 3. `Evolution.no_gradient_escape_of_initial_tendsto_varying` — Euler/OrdinaryEulerVaryingHorizon.lean:96-107 — [OK]
Wraps `no_gradient_escape_varying` by taking `ε n := tensorNorm 3 (initial difference) + 1/(n+1)` (strictly
positive, still → 0). Legitimate.

### 4. `Evolution.no_gradient_escape_varying` — Euler/OrdinaryEulerVaryingHorizon.lean:61-94 — [OK]
This is the a-priori-bound side, and it is DERIVED, not assumed:
- :72-73 `hc`: `fderiv ℝ (U.velocity ·).field 0` is continuous in t (from `gradient_continuous`,
  OrdinaryEulerStability.lean:35-47, which is built from the structure field `velocity_continuous`).
- :74-78 applies `EulerBreakdownCriterion.no_escape_near_compact_trajectory` (EulerProof.lean:12522-12542),
  whose proof is: `isCompact_Icc.exists_bound_of_continuousOn` gives a bound `C` on the reference
  gradient over the COMPACT `Icc 0 T`; if samples → ∞ while staying within `errors n → 0` of the
  reference, pick n with `‖samples n‖ ≥ C+2` and `errors n < 1`, then `linarith`. Correct and elementary.
- :81-94 the "errors" are `9*smoothEmbeddingConstant * tensorNorm 3 (difference)`, justified by the real
  H³ → C¹ Sobolev embedding `real_smooth_fderiv_le_H3` (EulerProof.lean:8375-8383) applied to the
  difference field, plus `fderiv_sub`. So the compactness bound is transported to the stage gradients.
KEY POINT for the parent's question 3: there is NO BKM criterion and NO assumed energy inequality on the
putative `U`. The a-priori control on `U` is: (i) `U` lives on the CLOSED base horizon, (ii) all its L² jets
are continuous in t by structure field, hence (iii) `referenceSize := ‖U.referenceNormPath‖` (sup over the
compact `Icc 0 T` of `tensorNorm 4 (U.velocity t)`, OrdinaryEulerStability.lean:17-33) is finite, and
(iv) its gradient at the origin is bounded on `Icc 0 T`. That is a theorem about the structure, not a hypothesis.

### 5. `Evolution.eventually_h3_bound_varying` / `sampled_h3_tendsto_zero_varying` — :28-48 / :50-59 — [OK]
`h3_stability` is applied to the RESTRICTION `U.restrictTime (durations n)` with `M := U.referenceSize`
and the smallness condition `640 ε n exp(3 C T) ≤ 1/2` obtained EVENTUALLY from `ε n → 0` (:38-40).
The exponent uses the full base horizon `T`, dominating `durations n` (:21-26). Squeeze to 0. Sound.
Note the honest structure: each stage is compared only on its OWN horizon `durations n = (P n).parent.T`
(matching the file docstring at PacketStageContradiction.lean:6-8), and `restrictTime`
(OrdinaryEulerRestriction.lean:18-32) is a genuine restriction — `initialInclusion` is `t ↦ ⟨t,…⟩`
(SmoothCoefficientTimeRestriction.lean:84-86), i.e. the identity on the underlying real, not a clamp or junk map.

### 6. `Evolution.h3_stability` — Euler/OrdinaryH3Envelope.lean:119-142 — [OK]
`tensorNorm 3 (U.difference V t) ≤ 640 ε exp(3 · stabilityConstant M · T)` given
`hM : ∀ t, WordBound 4 M (U.velocity t)`, `hinit ≤ ε`, and smallness. Mechanism: regularized envelope
`40√(energy+δ²)` (:60-62), its one-sided derivative (:75-90), the differential inequality
`X' ≤ C(X+X²)` (:92-97), and the scalar comparison lemma. Genuine Gronwall, no circularity.

### 7. `quadratic_stability_within` — Euler/OrdinaryQuadraticStability.lean:11-44 — [OK]
Uses `image_le_of_deriv_right_lt_deriv_boundary` against the barrier `F t = 2ε exp(3Ct)`; the strict
inequality at contact is earned from `F t ≤ 1/2` so `C(F+F²) ≤ 2CF < 3CF` (needs `C>0`, `F>0`: both present).
Correct; the smallness hypothesis is genuinely needed and is genuinely supplied.

### 8. `difference_energy_bound` — Euler/OrdinaryH3Energy.lean:108-130 — [OK, one level deep]
`energyProduction W (differenceRhs U W P) ≤ 3600 h3ProductConstant (M+√E) E` with
`hU : WordBound 4 M U` on the REFERENCE only. The pressure difference is eliminated by orthogonality of
`solenoidalSpace` and `gradientSpace` (`differenceRhs_pairing`, :34-51, incl. `word_pressure_pairing_zero`
and `advection_inner_zero` for the divergence-free transport term). This is the honest H³ difference
estimate: only the reference needs H⁴ control; the perturbation is quadratic. NOT audited deeper:
`differenceRhs_word_bound` (:53-103) and the commutator estimates it calls.

### 9. `structure EulerOrdinarySobolev.Evolution` — Euler/OrdinaryEulerDifference.lean:21-32 — [OK, with a meaning caveat]
Fields: `velocity, pressureForce : Icc 0 T → SmoothL2Field Space`; `velocity_continuous`/`pressure_continuous`
for EVERY jet order n; `solenoidal` (velocity in `solenoidalSpace`); `gradient` (pressure force in
`gradientSpace`); `time_law`: for every interior `t ∈ Ioo 0 T` and every x, the pointwise Euler equation as a
`HasDerivAt` for `r ↦ velocity (projIcc … r) x` with derivative `-Du·u - ∇p`. `SmoothL2Field`
(LpSmoothField.lean:31-34) = a genuine `ContDiff ℝ ∞` function on `Space = EuclideanSpace ℝ (Fin 3)`
(EulerProof.lean:5202) with EVERY iterated derivative in `L²(volume)`.
CAVEAT (interpretive, not a defect): because continuity of ALL jets on the CLOSED interval is a field,
"∃ Evolution on [0,T]" means "a solution that stays H^∞-with-continuous-L²-jets up to and including T".
So the theorem's real content is "no solution survives to the base horizon in that class", i.e. blowup
before `baseHorizon S.J S.X`. It does NOT claim non-existence of weak/short-time solutions — and indeed
the repo proves the opposite for short time (finding 11). The pressure force is a supplied field
constrained to `gradientSpace`, not defined by a Riesz projection; a putative solution must produce it.

### 10. `SobolevData.ordinaryEvolution` — Euler/ParentOrdinaryEvolution.lean:42-56 — [OK]
Builds an `Evolution A.T` from the packet parent's own Euler state, with `solenoidal` at the endpoints
obtained by L²-continuity/closure from the interior (`velocity_solenoidal`, :18-40) and `time_law` from
`pointwise_time_derivative_of_classical`. So the stage evolutions are real `Evolution`s: the type is inhabited.

### 11. `Stage.exists_local_evolution` — Euler/PacketStageLocalExistence.lean:39-86 — [OK] (decisive anti-vacuity evidence)
With the same `P` and (all-order) `hinit`, it PROVES `∃ L > 0, L ≤ baseHorizon/12 ∧ ∃ E : Evolution L _,
(E.velocity 0).field = u₀.field`, via `exists_local_evolution_of_cauchy` (OrdinaryEulerLocalCauchy.lean:68+)
and the same `h3_stability`. Consequence: the `Evolution` type is NOT empty for this very datum, and the
`.field` equality with `u₀` IS achievable (:84-86 upgrades a.e. equality to equality using continuity).
So `no_euler_evolution_of_initial_H3` is not "trivially true because the type is empty or the equality is
unreachable"; it is a genuine time-horizon statement (local yes, base horizon no).

### 12. `Stage.gradient_atTop` — Euler/PacketStageGrowth.lean:83-93 — [OK]
`Tendsto (fun n => (P n).activationGradient) atTop atTop`, from `gradient_lower` plus
`Scales.previousShear_ge_index` (:25-34, induction from the `Scales` fields `previousShear_one` and
`shear_separation`). Real proof, not an assumed field.

### 13. `Stage.gradient_lower` — Euler/PacketStageGrowth.lean:52-81 — [UNCLEAR-by-scope, mechanism OK]
`previousShear S.J S.X n / 2 ≤ P.activationGradient` for `n ≠ 0`. Mechanism: the frame decomposition
`M = B + Q + remainder` with `‖Q‖ = previousShear` (rank-one term, `frame_shear`), `‖remainder‖ ≤ frame.error`,
`‖B‖ ≤ frame.G`, and `G + error ≤ previousShear/2` from `frame_bound`, `frame_error`, `S.activation_small`;
`‖M‖ = activationGradient` via `strain_origin` (ParentEulerParity.lean:38-40, using the oddness field).
This is a real reverse-triangle argument. BUT every ingredient is a FIELD of `Stage`/`ParentFrame`/`Scales`.
So: the divergence is proved from the invariant, and the entire burden moves to whether the invariant is
INHABITED. That burden is discharged elsewhere: `Scales.firstStage : Stage S 0` is CONSTRUCTED
(BaseInductionStage.lean:22), `stages` by recursion (PacketInfiniteConstruction.lean:41-43), and
`constructionScales := Classical.choice (exists_scales …)` (PacketInfiniteConstruction.lean:68-70) with
`exists_scales : Nonempty (Scales c B)` PROVED at PacketInductionScales.lean:123-…  This is the
`Classical.choice` the brief anticipated; the existence proof is real (it chooses D, J, X₀, δ from
`exists_base_power` and `exists_common_guards`), but I did not audit `exists_common_guards` — see Escalations.

### 14. `structure Stage` — Euler/PacketInductionStage.lean:23-55 — [OK as an invariant; not audited for satisfiability]
28 fields. Note `gradient_bound` (:35-37) is an UPPER bound `≤ gradientConstant * previousShear`, consistent
with (not contradicting) the lower bound `previousShear/2` used for divergence — the two only pin the
activation gradient to a band around `previousShear`, so no field is self-contradictory in an obvious way.
Remaining decls in the file (`coupling_bounds` :61, `sigma_pos` :68, `time_lt` :75, `horizon_lower` :81,
`horizon_reciprocal` :91, `time_pos` :96, `exterior_cap` :104, `core_cap` :110, `pressure_cap` :116,
`source_stage` :123, `normalized_sigma` :127, `strain_bound` :133, `curvature_bound` :138) are short
`linarith`/`nlinarith` consequences of fields — all [OK], none used to smuggle content.

### 15. Consumer `Stage.initialDataLimit_no_euler` — Euler/PacketStageInitialLimit.lean:105-113 — [OK]
The only consumer. It discharges `hinit` with the PROVED `initialDataLimit_Hm P hq hB hstep 3` (:84-104),
not with an assumption. So downstream the H³ convergence is earned too (given the packet-series machinery).

## Kernel-risk (over the ten files read in full plus the two partially read)
- `decide`: 1 — PacketInductionStage.lean:72, `(by decide : 2 ≠ 0)` on ℕ. Trivial, kernel-safe.
- `native_decide`: 0. `axiom`: 0. `sorry`: 0. `macro`/`elab`/`syntax`/`set_option`/`unsafe`/`partial`: 0.
  (Confirms the repo-wide scan; no custom metaprogramming anywhere in this chain.)
- `.rec`/`.brecOn`/`.recOn`/`Acc.rec`: 0. `termination_by`: 0. `WellFounded`: 0.
  Recursion in this chain is structural only: `PacketInfiniteConstruction.lean:41-43` (`stages`),
  `SmoothL2Series.lean:39-41` (`partialSum`), `PacketStageGrowth.lean:27-34` (`induction n`).
- `rfl` occurrences: PacketStageContradiction.lean:44, :63; OrdinaryEulerRestriction.lean:32, :35, :38;
  SmoothL2Series.lean:46; PacketInfiniteConstruction.lean:44, :47. None is `rfl` on recursive numeral data;
  :35/:38 are structure-projection/eta `rfl` on `restrictTime` (definitional unfold of a structure instance),
  :44/:63 unfold `Evolution.difference`/`activationGradient` defs. Kernel work is proj/beta, not bignum.
  MILD note: `restrictTime_initial` (:38) relies on `Subtype`/structure eta — standard Lean 4 kernel feature.
- `norm_num`: 20 in the full-read set (e.g. PacketInductionStage.lean:73,77,92,97,100;
  OrdinaryEulerVaryingHorizon.lean:26,40,45; OrdinaryH3Envelope.lean:42,103; OrdinaryEulerStability.lean:60).
  All on tiny rational goals (`0 < 12`, `0 ≤ 40`, `0 < 1/2`).
- Numerals ≥ 3 digits: 30 occurrences, all ≤ 3600 and all ℝ constants inside inequalities
  (`640`, `320`, `1800`, `3600`, `1000` as an exponent in `S.X^1000` at PacketInductionStage.lean:42,110).
  `baseHorizon = 6*J^2*X^(-498:ℝ)` (PacketBaseGuardScales.lean:14) uses REAL rpow exponents, so the kernel
  never computes a bignum. NO GMP-heavy `Nat.pow/div/mod/gcd/beq/ble` site in this chain.
- `Classical.*`: 0 in the files read in full; the single relevant use is
  `Classical.choice (exists_scales …)` at PacketInfiniteConstruction.lean:69 (outside this theorem's proof;
  it only picks the scale parameters for the concrete `packets`, and its existence lemma is proved).

## Escalations (ranked; each with the exact question an expert must answer)
1. Satisfiability of the `Stage` invariant is the whole ballgame. My theorem is conditional on
   `P : ∀ n, Stage S n`; the divergence comes from `Stage`/`ParentFrame`/`Scales` FIELDS
   (PacketStageGrowth.lean:52-81). QUESTION: do `Stage.forwardNext` / `Stage.joinedNext`
   (`Euler/PacketForwardSuccessor.lean`, `Euler/PacketJoinedSuccessor.lean`, used at
   PacketInfiniteConstruction.lean:22-25) really produce all 28 fields of `Stage S (n+1)` — in particular
   `frame_bound`, `frame_error`, `compression`, and `horizon_le : parent.T ≤ baseHorizon` — from a stage at n,
   with no hypothesis that already encodes the blowup? If any successor lemma assumes an unproved bound,
   the divergence is smuggled one level down.
2. Faithfulness of `EulerOrdinarySobolev.Evolution` (OrdinaryEulerDifference.lean:21-32) as "an Euler
   evolution on [0,T]". QUESTION: is any field STRONGER than what a genuine smooth finite-energy Euler
   solution on `ℝ³` must satisfy — specifically, (a) `∀ n, MemLp (iteratedFDeriv ℝ n field) 2` at EVERY
   order, and (b) `pressureForce t ∈ gradientSpace` with `pressureForce` itself an all-order-L² field?
   If (a)/(b) can fail for a real solution that is otherwise perfectly regular on `[0,T]`, then the
   non-existence theorem is weaker than the blowup claim it is used for.
3. `exists_common_guards` (called at PacketInductionScales.lean:125) feeding
   `exists_scales : Nonempty (Scales c B)` (:123). QUESTION: is that existence proof free of hidden
   `sorry`-equivalents/circularity, and does it really deliver the FOUR `SmallSeries` summability fields
   (:99-109) plus `localized` (:111) simultaneously for one `(J,D,X,δ)`?
4. `differenceRhs_word_bound` (OrdinaryH3Energy.lean:53-103) and the transport-commutator estimates it uses.
   QUESTION: is the commutator bound `≤ 24 h3ProductConstant X M` correct with `WordBound 4 M` on the
   reference only (no H⁴ control on the perturbation)?
5. `PacketStageInitialLimit.initialDataLimit_Hm` (:84-104). QUESTION: does `fullInitialLimit_Hm` really give
   H^s convergence for EVERY s of the stage initial data to `initialDataLimit`, with the index shift at
   :96-103 handled correctly?

## Residue
- Not settled here: whether the successor constructions preserve `Stage` (escalation 1) — outside my scope.
- Not settled here: soundness of `exists_local_evolution_of_cauchy`'s limit construction
  (OrdinaryEulerLocalCauchy.lean:68+) beyond its statement; I used it only as anti-vacuity evidence.
- `derivativeSum` (PacketFieldPhysicalSobolev.lean:18-20) is a sum of `lpNorm`s, so it takes the JUNK value 0
  on a non-L² argument. This does NOT weaken the theorem: the proof only uses `hinit` after rewriting through
  `tensorNorm_eq_derivativeSum` for a bona fide `SmoothL2Field` difference (PacketStageContradiction.lean:45-53),
  and if a `U` existed then `u₀` would be an `L²` smooth field anyway. Flagged only so a reader does not
  mistake `hinit` for a strong hypothesis when `u₀` is wild.
- What would settle vacuity completely: exhibit ONE `Evolution T hT` for some `T>0` independent of the packet
  machinery (e.g. a stationary/shear-flow example), and check `Evolution`'s `time_law` against Mathlib's
  own Euler formulation. The repo's `evolutionOfClassical` (OrdinaryEulerDifference.lean:34-54) plus
  `Stage.exists_local_evolution` already gets most of the way.

## Bottom line for question (A)
The conclusion is EARNED as a conditional theorem, by the intended mechanism:
PROVED divergence (`gradient_atTop`, from the stage invariant) + PROVED comparison
(H³ Gronwall stability `h3_stability` + Sobolev H³→C¹ + compactness bound on the reference gradient,
`no_escape_near_compact_trajectory`). No BKM criterion is invoked and none is needed; no energy inequality
is assumed on the putative `U`; no `Classical.choose` appears in the proof; nothing in the two declarations
of PacketStageContradiction.lean is vacuous or circular. The unaudited risk sits entirely in (a) whether the
`Stage` invariant is inhabited for all n (successor constructions) and (b) whether `Evolution` is a faithful
notion of Euler solution.
