# NSE deep audit — worker slice: SPATIAL all-order L² JET recovery (`SmoothL2Field` membership)

Repo: /home/gsm/.openclaw/workspace/repos/NSE (openai/NavierStokesAndEuler @ f9e8bc5), READ-ONLY.
No Mathlib build available (disk full) => NO `lake build`. Instrument: line-by-line reading + grep.
Mathlib cross-check: an independent Mathlib source tree was used to verify the *statements* of the
external lemmas cited by these files:
`/home/gsm/.openclaw/workspace/lean-eval-house-with-two-rooms/.lake/packages/mathlib` (v4.33.0;
NSE pins v4.34.0-rc2, so names could have drifted, but every load-bearing lemma I checked exists
and means what the repo needs).

## 0. Bottom line (answers to (a)-(d))

(a) NOTHING in this slice is an unproved assumption or an extra regularity hypothesis imposed on the
    competitor. Every `SmoothL2Field` field (ContDiff ∞ + `MemLp (iteratedFDeriv ℝ n ·) 2` for ALL n)
    is *derived* from the challenge data: `h.velocity_smooth`, `h.integrable` (via a genuine Mathlib
    iff, see §7), `h.div_free`, `h.globally_bounded_energy` — PLUS one further input,
    `hsupport : ∀ t ∈ Icc 0 T, tsupport (vectorCurl (v · t)) ⊆ K` with `K` compact.
    That `hsupport` is *threaded as a hypothesis through my whole slice* and is discharged OUTSIDE it
    (Euler/ComparatorLocalEvolution.lean:91-97 from `hc : HasCompactSupport (vectorCurl u₀)` via
    `Euler/ComparatorLocalCompactVorticity.lean:159` `local_compact_vorticity_of_truncationFamily`).
    It is *not* a smoothness/decay assumption on the competitor's solution: it is a claimed
    propagation of a property of the CHOSEN initial datum. I did NOT audit that propagation.
    => LOUD FLAG: the entire all-order L² jet recovery is CONDITIONAL on compact vorticity support of
    `v(·,t)` for every t in [0,δ]. All of the load of "no NICE solution vs no solution" that could
    still hide in the spatial direction sits in that unaudited transport theorem
    (`exists_local_trapping_constants`, `locallyTrappedBackwardFlows`), not in the recovery itself.

(b) NO lemma in this slice runs the wrong way. Every declaration consumes `h`
    (`EulerExistenceAndSmoothnessR3`) / raw smoothness+L²+div-free+compact-curl and PRODUCES
    `SmoothL2Field` / `MemLp` / uniform jet bounds. `Euler/ClassicalBridge.lean` only *weakens* `h`.
    Crucially `recoveredVelocity_field` (ComparatorLocalEvolution.lean:41-45) is `rfl`: the produced
    Evolution's velocity slice IS literally `(v · t)`, so no nicer surrogate object is substituted.

(c) NO junk-value or vacuity trick in this slice.
    - `SmoothL2Field.toLp` / `jetLp` (LpSmoothField.lean:42,46) use `MemLp.toLp` WITH the proof term
      `A.integrable n`. They do NOT use the total fallback `Euler.toL2`
      (SolutionDefinitions.lean:87-90, `if h : MemLp … then h.toLp f else 0`). The `= 0` fallback
      cannot be exploited here.
    - `partialDerivative`/`gradient`/`Δ` are `fderiv`-based (junk 0 where not differentiable), but
      every single use in this slice is under an explicit `ContDiff ℝ ∞` hypothesis, so no vacuity.
    - `Δ` is Mathlib's `Laplacian` (`ContDiffAt.laplacian_CLM_comp_left`,
      `laplacian_eq_iteratedFDeriv_orthonormalBasis` both exist in Mathlib), not a home-made stub.
    - The cutoffs are a genuine Mathlib `ContDiffBump` (`spatialBump`, EulerProof.lean:3735) rescaled
      by `cutoffScale n = ((n:ℝ)+1)⁻¹`; `0 ≤ cutoff ≤ 1`, compact support, `→ 1` pointwise, and
      `‖∇cutoff n‖ ≤ M·cutoffScale n`. Nothing degenerate.
    - The structure `SmoothL2Field` is NOT cheaply satisfiable (it excludes e.g. a nonzero constant
      field), so the target class is genuinely stronger and the recovery does real work.

(d) KERNEL-RISK: NONE found in this slice. A grep over the 8 files I read for
    `sorry|admit|axiom|native_decide|decide|set_option|macro|elab|notation|unsafe|partial |Acc.rec|
    WellFounded|termination_by` returned only:
      * `Euler/ClassicalBridge.lean:14  local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` (harmless
        local abbreviation, no new syntax category, no elab),
      * two `@[simp]` lemmas in `Euler/LpFiniteTensorReconstruction.lean:62,83` (harmless).
    No big-numeral arithmetic (the only constants are existentially quantified reals: bump-derivative
    bound `M`, `C = M^2+1`, and the operator norm `‖tensorReassembly n‖`). All recursions are plain
    STRUCTURAL recursion on `List (Fin 3)` (`wordDerivative`, `wordEnergyBound`) or `Nat.rec`
    inductions inside tactic proofs — no well-founded recursion, no `termination_by`, no `Acc.rec`.

---

## 1. `EulerLpTranslation.SmoothL2Field` — Euler/LpSmoothField.lean:31-34

Statement (my words): a *structure* (data, not Prop) carrying
`field : Space → V`, `smooth : ContDiff ℝ ∞ field`, and
`integrable : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n field) 2 volume`.
So membership demands: ordinary C^∞ smoothness AND global square-integrability of EVERY iterated
Fréchet derivative (order 0 included, via `norm_iteratedFDeriv_zero` at :38-40). This is exactly
"all-order spatial L² jets" — much stronger than the challenge's single `MemLp (‖v·t‖) 2`.

Mechanism of the derived API: `memLp` (:38) re-reads order 0 through `congr_norm`;
`toLp` (:42) and `jetLp` (:46) are `MemLp.toLp` applications, i.e. the L² class is built from the
supplied integrability proof; `derivative` (:49) shifts the index by one using
`norm_iteratedFDeriv_fderiv`. `translation_contDiff` (:85) then upgrades to smoothness of the
translation orbit in L² by a `Nat`-structural induction (:68-82) with `contDiff_succ_iff_fderiv`,
and `norm_iteratedFDeriv_translation_le` (:119) bounds orbit jets by `‖jetLp n‖` with constant 1.
Nothing here is assumed: it all consumes the `integrable` field.

Verdict: **OK**. (The strength of the target class is real; that is precisely why §2-§6 matter.)

## 2. `EulerComparatorRecovery.iteratedFDeriv_memLp_of_curl_compact` — Euler/DivCurlTensorRecovery.lean:66-75
and `smoothL2Field_of_curl_compact` — :79-85

Statement: for `u : Space → Space` with `ContDiff ℝ ∞ u`, `MemLp u 2 volume`,
`∀ x, divergence u x = 0`, `HasCompactSupport (vectorCurl u)`: for every `n`,
`MemLp (iteratedFDeriv ℝ n u) 2 volume`; hence a `SmoothL2Field Space` with `field := u`.

Mechanism (honest, and *not* an induction on the tensor order):
1. Scalarize: for each word `w : Fin n → Fin 3` and component `j`,
   `iteratedFDeriv ℝ n u x (fun i => direction (w i)) j = wordDerivative (List.ofFn w) (u · j) x`
   — proved by `iteratedFDeriv_coordinate_word` (:23-38, structural `Nat` induction using the genuine
   Mathlib `DifferentiableAt.iteratedFDeriv_succ_apply_left'`, verified to exist,
   Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:834) and `iteratedFDeriv_component` (:41-46,
   `ContinuousLinearMap.iteratedFDeriv_comp_left` with `EuclideanSpace.proj j`).
2. Each scalar word derivative is L² by `component_wordDerivative_memLp` (§3).
3. Lift back to the tensor with the genuine iff `MemLp.of_eval_piLp` / `MemLp.of_eval`
   (Mathlib aliases of `memLp_piLp_iff` / `memLp_pi_iff` — both verified present) over the FINITE
   index `(Fin n → Fin 3)`, then post-compose with the fixed bounded map
   `tensorReassembly n` (`ContinuousLinearMap.comp_memLp'`) and rewrite by
   `tensorReassembly_coordinates`.
So the full tensor's L² membership is genuinely reconstructed from 3^n·3 scalar facts, with no
extra hypothesis and no circular use of "derivatives are already L²".

Verdict: **OK**. Note the four hypotheses are the *only* inputs; `hL2` here is `MemLp u 2` (not of
its derivatives), so there is no self-reference.

## 3. `component_wordDerivative_memLp` — Euler/DivCurlRecovery.lean:317-331 (core of §2)

Statement: same hypotheses, conclusion `MemLp (wordDerivative word (u · j)) 2` for every finite
coordinate word and component.

Mechanism: (i) componentwise smoothness/L² by `contDiff_piLp` and `PiLp.norm_apply_le`;
(ii) `Δ (u · j)` has compact support because `laplacian_compact_of_curl_compact` (:198-210) proves
`Δ u = -curl curl u` from `vectorCurl_vectorCurl` (MeanVectorIdentities.lean:105,
`curl curl f = grad div f - Δ f`) plus `div u = 0`, and curl of a compactly supported field is
compactly supported; (iii) then the real engine
`wordDerivative_memLp_of_laplacian_compact` (:234-249): structural List induction where the step
uses `gradient_memLp_of_laplacian_compact` applied to `wordDerivative word h`, whose Laplacian is
`wordDerivative word (Δ h)` (`laplacian_wordDerivative` :213-224) and hence compactly supported.
The induction is HONEST: at each step it re-establishes the two premises (`MemLp` of the current
word derivative from `ih`, compact support of its Laplacian from commutation), it does not assume
the conclusion at higher order.

Verdict: **OK**.

## 4. The elliptic first-derivative estimate — Euler/DivCurlRecovery.lean:53-194

This is the only genuinely analytic step, and it is real Caccioppoli/Fatou, not hand-waving.
- `localized_dirichlet_identity` (:53-74):
  `∫‖∇(ηh)‖² = ∫ h²‖∇η‖² − ∫ η²·(h·Δh)` for compactly supported smooth η.
  Built from the pointwise algebraic identity `localized_gradient_identity`
  (MeanHarmonicEnergy.lean:32) — which I checked by hand:
  `|∇(ηh)|² = ⟪∇(η²h),∇h⟫ + h²|∇η|²`, correct — and classical integration by parts against the
  compactly supported test `η²h` (`gradient_test_integration_by_parts`, MeanSolenoidalSpace.lean:137,
  itself proved coordinatewise from Mathlib's
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`). All integrability side conditions are
  discharged from compact support. No decay of `h` is assumed — the cutoff carries the boundary.
- `gradient_energy_recovery` (:87-150): applies the identity to `η = cutoff n`
  (bump at scale `n+1`, so `‖∇cutoff n‖ ≤ M` uniformly, LpSpatialCutoff.lean:33-52), gets
  `∫‖∇(cutoff n · h)‖² ≤ M²∫h² + ∫|hΔh|` uniformly in n, and then Fatou
  (`integrable_and_integral_le_of_nonneg_limit`, :24-50, via `lintegral_liminf_le'`) with the
  pointwise limit `∇(cutoff n · h)(x) → ∇h(x)` (`cutoffField_fderiv_tendsto`,
  LpSpatialCutoff.lean:79) to conclude `MemLp (gradient h) 2` AND the quantitative bound.
  This is the step that would be circular if it assumed `∇h ∈ L²`; it does not — it localizes first.
- `exists_gradient_energy_square_bound` (:174-194): converts `∫|hΔh|` into `∫h² + ∫(Δh)²` (Cauchy /
  `nlinarith` on `(h ± Δh)² ≥ 0`), giving a FIELD-INDEPENDENT constant `C = M²+1`. This constant
  independence is what makes the uniform-in-time bootstrap (§5) legitimate.

Verdict: **OK**.

## 5. `wordDerivative_energy_uniform` / `component_wordDerivative_energy_uniform`
— Euler/DivCurlRecovery.lean:251-313 and :335-365

`wordEnergyBound C h : List (Fin 3) → ℝ` (:253) is a plain structural recursion
`[] ↦ ∫h²`, `i::word ↦ C·bound(word) + ∫ (D^word Δh)²`.
`wordDerivative_energy_le` (:258) proves `∫ (D^word h)² ≤ wordEnergyBound C h word` by List
induction, each step being `∫(∂_i f)² ≤ ∫‖∇f‖² ≤ C∫f² + ∫(Δf)²` with `Δ(D^word h) = D^word(Δh)`.
`wordDerivative_energy_uniform` (:291) then makes the bound uniform over an ARBITRARY parameter set ι
given (a) a uniform bound on `∫ h_t²` and (b) uniform bounds on the compactly supported Laplacian
word energies. Both recursions are structural and the constant `C` is fixed once for all fields, so
there is no hidden per-t choice.

Verdict: **OK**. Uniformity is bought exactly by the field-independent `C` of §4.

## 6. `jetLp_norm_uniform_of_coordinate_energy` — Euler/DivCurlTensorRecovery.lean:126-152
(with :89 `tensor_integral_norm_sq_le_coordinate_energy`, :117 `jetLp_norm_sq_eq_integral`)

Statement: for a family `A : ι → SmoothL2Field Space`, if for every component `j` and word there is a
uniform bound `B` on `∫ (D^word (A t).field ·_j)²`, then for every order `n` there is `M` with
`‖(A t).jetLp n‖ ≤ M` for all t.

Mechanism: `‖jetLp n‖² = ∫‖iteratedFDeriv n field‖²` (`Lp` 2-norm identity
`EulerLpBochnerRealization.norm_sq_eq_integral`, LpBochnerRealization.lean:20, correct: `Lp.norm_def`
+ `eLpNorm_eq_integral_rpow_norm`), then the pointwise finite-dimensional inequality
`‖A‖² ≤ ‖tensorReassembly n‖² · Σ_w Σ_j (A(direction∘w) j)²`
(TensorCoordinateEnergyBound.lean:41, from `le_opNorm` of the reassembly composed with the
coordinate map, plus `tuple_norm_sq_le_coordinate_energy` :19), integrated with `integral_mono`.
`tensorReassembly` (LpFiniteTensorReconstruction.lean:79) is `LinearMap.leftInverse` of the
coordinate evaluation map, which is INJECTIVE (`tensorCoordinates_injective` :65, via
`Module.Basis.ext_multilinear` on the standard basis) and lives between finite-dimensional spaces —
so `tensorReassembly_coordinates` (:83, `LinearMap.leftInverse_apply_of_inj`, verified present in
Mathlib/LinearAlgebra/Basis/VectorSpace.lean:276) is a real left-inverse identity and
`‖tensorReassembly n‖` is a finite operator norm. Order-dependent constants only; each `n` handled
separately, which is all that `SmoothL2Field`/`jetLp` uniformity needs here.

Verdict: **OK**. Mild remark (not a defect): no attempt is made to control the growth of
`‖tensorReassembly n‖` in n; the consumers only ever need one order at a time.

## 7. `Euler/ClassicalBridge.lean` — weakening the challenge hypothesis

- `velocity_contDiff` (:21-23) / `pressure_contDiff` (:25): from
  `h.velocity_smooth : ContDiffOn ℝ ∞ (uncurry v) (univ ×ˢ Ici 0)` compose with
  `x ↦ (x,t)` using the genuine Mathlib `ContDiffOn.comp_contDiff`
  (verified: Mathlib/Analysis/Calculus/ContDiff/Comp.lean:145; hypotheses are exactly
  `ContDiffOn g s`, `ContDiff f`, `∀ x, f x ∈ s`), with `⟨mem_univ x, ht⟩` supplying membership.
  Valid also at the boundary `t = 0` because `ContDiffOn` is a local-Taylor-series condition that
  restricts along the slice; this is Mathlib's own composition lemma, no unique-differentiability
  side condition is being dodged by the authors.
- `velocity_memLp` (:29-31): THE ONE I WAS ASKED TO DOUBT. The challenge only gives
  `integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2` (SolutionDefinitions.lean:79) — note the cdot expands at
  the enclosing parentheses, so this is `MemLp (fun x => ‖v x t‖) 2 volume`, the NORM function.
  The conversion is `(memLp_norm_iff hAESM).mp (h.integrable t ht)`, where
  `memLp_norm_iff` is genuine Mathlib
  (Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:745):
  `AEStronglyMeasurable f μ → (MemLp (fun x => ‖f x‖) p μ ↔ MemLp f p μ)`.
  The measurability side condition is supplied from smoothness (`velocity_contDiff … .continuous`),
  which itself comes from `h`. `.mp` is used in the correct direction. Since `eLpNorm` only sees
  `‖f x‖`, the iff is a triviality about the seminorm, not a smuggled regularity gain.
  => LEGITIMATE, not assumed.
- `pointwise_euler` (:33-47): converts the challenge `derivWithin … (Ici 0)` equation at `t > 0`
  into `HasDerivAt`, using `derivWithin_of_mem_nhds (Ici_mem_nhds ht)` — only valid for `t > 0`,
  and indeed the statement requires `0 < t`. Honest (endpoint `t = 0` deliberately excluded).

Verdict: **OK**.

## 8. `Euler/ComparatorUniformSpatialJets.lean` — supplying the uniform scalar energies from `h`

- `velocity_laplacian_eq_neg_curl_curl` (:25-34): `Δ(v·t) = -curl curl (v·t)` from `h.div_free` and
  the curl-curl identity. **OK**.
- `velocity_laplacian_tsupport_subset` (:37-40): `tsupport (Δ(v·t)) ⊆ tsupport (vectorCurl (v·t))`.
  **OK** — this is the reason a *vorticity* support hypothesis suffices.
- `velocity_laplacian_component_joint_contDiffOn` (:44-52): joint (space-time) smoothness of each
  component of `Δ(v·t)` on `Ici 0 ×ˢ univ`, obtained from `h.velocity_joint_contDiffOn` by
  differentiating twice in space inside the set (`joint_scalar_laplacian_contDiffOn`,
  CompactSpatialJets.lean:48, built from `ContDiffWithinAt.fderivWithin` with `uniqueDiffOn_univ`
  in the SPATIAL variable only — the time variable is never differentiated, so the `Ici 0` boundary
  is not an issue). **OK**.
- `laplacian_component_word_energy_uniform_of_commonCompactCurl` (:56-68): uniform-in-t bounds for
  `∫ (D^word (Δ(v·t))_j)²` on `Icc 0 T`, from joint continuity on the compact set `Icc 0 T ×ˢ K`
  plus vanishing off `K` (`wordDerivative_energy_uniform_of_compact_support`,
  CompactSpatialJets.lean:94, which is a sup-bound-times-`volume K` estimate,
  `uniform_energy_of_compact_support` :71). **OK** — genuinely uses compactness of `K` and of
  `Icc 0 T`; nothing is assumed about the competitor beyond `h` + `hsupport`.
- `component_word_energy_uniform_of_commonCompactCurl` (:72-94): assembles the above with
  `h.velocity_contDiff`, `h.velocity_memLp`, `h.div_free`, `h.globally_bounded_energy` and the
  compact-curl hypothesis, and calls §5. Every argument is a projection of `h` or of `hsupport`.
  **OK**.

## 9. Where the slice plugs in — Euler/ComparatorLocalEvolution.lean:31-97 (read for direction only)

`recoveredVelocity` (:31-39) = `smoothL2Field_of_curl_compact (v · t) …` — the Evolution velocity is
DEFINITIONALLY the challenge velocity (`recoveredVelocity_field` :41 is `rfl`).
`recoveredVelocity_jetLp_uniform` (:49-60) = §6 + §8. `exists_evolution_of_commonCompactCurl` (:64)
consumes these plus solenoidality/time-law inputs (other slices).
`compactCurlLocalUpgrade` (:91) discharges the Prop-valued `def CompactCurlLocalUpgrade`
(ComparatorEvolutionIdentification.lean:37-41) — so that obligation is NOT left open; its antecedent
`hc : HasCompactSupport (vectorCurl u₀)` is a property of the chosen initial datum, and the
propagation `hc ⟹ hsupport` is `local_compact_vorticity` (ComparatorLocalCompactVorticity.lean:177).

=> **UNCLEAR (outside my slice, flagged for the decider)**: `local_compact_vorticity` /
`exists_local_trapping_constants` / `locallyTrappedBackwardFlows`. If that transport argument is
weak, then the spatial jet recovery silently applies to fewer competitors than claimed, and the
headline degrades. Inside my slice nothing else can degrade it.
