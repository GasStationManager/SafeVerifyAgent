# CONE_JOIN — the 64 alignment citations that are out of the headline cone

Input: `alignment/CONE_JOIN_input.csv` (64 rows) joined against `CONE.csv` (seeds `NavierStokesR3.theorem_1_1` at `NavierStokes/R3/Theorem.lean:46` and `Euler.euler_breakdown_R3` at `ComparatorChallenges/Euler.lean:85`). Artifact read-only at commit f9e8bc5; nothing was compiled.

## Summary

All 64 rows resolve. **58 are `WRAPPER`, 2 `DEAD`, 2 `ABOVE_SEED`, 1 `CENSUS_MISS`, 1 `OTHER`.**
**29 of the 64 classifications change** against the in-cone carrier.

The dominant structure is not subtle and it is architectural: **33 of the 64 cited declarations are
not even in the seeds' import closure**, and **32 of those 33 live in files reachable only through
`NavierStokes/PaperResults.lean` → `NavierStokes/PaperAdditionalResults.lean`** — a 4-line and a
30-line module that declare nothing and are imported by `NavierStokes.lean` *beside*
`NavierStokes.ComparatorSolution`, not below it. That is a literal paper-facing layer: 30 modules'
worth of manuscript restatements hanging off the root, structurally incapable of reaching the
headline theorem. (The 33rd, `NavierStokes/BaseWitnessClosure.lean`, is imported by **no file at
all** — it is outside even the display layer.)

The remaining 31 rows are in scope but unreferenced. Almost all are **existential repackagings**:
the construction is carried out *definitionally* on the headline route (`FinalSlowBase.ProfileData`
+ `Classical.choice profileData_nonempty`, `NavierStokes/FinalSlowBase.lean:619,627,634`), and the
`exists_actual_base` / `exists_modulated_profile` / `exists_weighted_profile` / `exists_nominal_witness`
family restates the same content as `∃ …` for the paper. Those are harmless: the carrier is as strong.

**What is not harmless** is the residue. In several places the *paper's clause* lives only in the
out-of-cone layer while the in-cone twin proves something strictly weaker. The nine rows that matter
are listed under *Findings worth an expert*; the sharpest is that both the **all-order flatness of the
excluded slot error** (Prop 9.1/9.3) and the **exact-curl identity** (Lemma 7.7) sit in the same
structure `ParticularWaveAssembly.LocalControl` as two out-of-cone fields (`gaussian_flat` at
`NavierStokes/ParticularWaveAssembly.lean:1547`, `exact_curl` at `:1565`) while **25 other field
lemmas of that same structure are in cone**. Whatever the headline route uses `LocalControl` for, it
does not use those two.

Two rows genuinely improve on re-classification: Prop 5.3 (row 8) is **LEAN STRONGER** against its
in-cone carrier, not weaker, and Lemma 4.5(2nd) (row 62) is carried by the stronger additive-gap form.


## Table

| # | slice | paper stmt | cited (wrapper) | why out of cone | in-cone carrier(s) | carrier vs paper | changed? |
|---|---|---|---|---|---|---|---|
| 1 | B | A.6 (Lemma) | `NavierStokes/AppendixHeatResults.lean:66` endpoint_derivatives | WRAPPER | NavierStokes/RadialHeatProfile.lean:216 iteratedDerivWithin_profile; :624 radial_heat_equation; :441 profile_logSlope_lt; NavierStokes/HeatProfileExtension.lean:70 extension, :73 extension_contDiff | EXACT on A.6's ODE / log-slope / smoothness clauses; NO IN-CONE COUNTERPART for the explicit endpoint display (A.35) and the explicit (A.36) constant | CHANGED (LEAN STRONGER -> EXACT, partial) |
| 2 | A | 4.10 (Proposition) | `NavierStokes/AppendixJoiningResults.lean:17` axis_initial_margin | WRAPPER | NavierStokes/NominalConeAssembly.lean:1517 exists_nominal_cone; NavierStokes/NaturalAxisData.lean:79 neg_W_formula | EXACT on 4.10's existence substance; NO IN-CONE COUNTERPART for the printed numeric axis margin `14/5 < -W` | SAME (EXACT) with a new gap flagged |
| 3 | B | B.4 (Lemma) | `NavierStokes/AppendixJoiningResults.lean:67` reference_first_gt_three | WRAPPER | NavierStokes/ReferenceBounds.lean:1004 ReferenceBoundsOnHold; :1180 exists_reference_bounds | EXACT on B.4's four uniform families and the hold-region source bound; NO IN-CONE COUNTERPART for the `p1 > 3 on [100,110]` clause | SAME (EXACT) with the p1>3 clause newly flagged as out of cone |
| 4 | B | B.6 (Cor) | `NavierStokes/AxisHolomorphic.lean:539` exists_common_holomorphic_extension | WRAPPER | NavierStokes/AxisHolomorphic.lean:401 complexProfile_analytic; :414 complexProfile_bound; :513 exists_parameterTube_subset; NavierStokes/ActivationHolomorphic.lean:1108 exists_initialTube | EXACT - the wrapper is a pure existential repackaging of exactly these in-cone lemmas (same tube, same bound, same jet identities) | SAME |
| 5 | B | B.6 (Cor) | `NavierStokes/AxisHolomorphicJoint.lean:202` exists_common_joint_extension | WRAPPER | NavierStokes/AxisHolomorphic.lean:401 complexProfile_analytic; :414 complexProfile_bound; :513 exists_parameterTube_subset; NavierStokes/AxisHolomorphicJoint.lean:177 complexProfile_joint_smooth_tube | EXACT - same repackaging plus the joint-smoothness field, which its proof takes from the in-cone tube lemmas | SAME |
| 6 | B | B.2 (Prop) | `NavierStokes/AxisJointAnalytic.lean:101` profile_analyticOnNhd | WRAPPER | NavierStokes/AxisContraction.lean:753 natural_axis_profiles; NavierStokes/AnalyticCoefficientBounds.lean:315 uniform_normalizedExp_axisData; NavierStokes/AxisHolomorphic.lean:401 complexProfile_analytic | EXACT - real-strip analyticity is the real slice of the in-cone complex-tube analyticity | SAME |
| 7 | B | B.2 (Prop) | `NavierStokes/AxisProfile.lean:48` profileCoeff | WRAPPER | NavierStokes/AxisSeries.lean:174 profile; :302 profile_gt_quarter; :347 bessel_one_le_one | EXACT (one numeric constant weaker) - the comparison-series bound the paper's B.2 needs is in cone; only the explicit quartic/cubic truncation identities are not | SAME |
| 8 | B | 5.3 (Prop) | `NavierStokes/BaseResidual.lean:1439` truncationResidual_rate | WRAPPER | NavierStokes/BaseResidual.lean:2514 baseResidual_jetRate_axis; :1513 FiniteIdentities | LEAN STRONGER - the carrier proves `JetRate ... m n` for EVERY real n >= 0 (arbitrary flatness order, and up to the axis), strictly beating the paper's single rate 2h(N+1) - K_m | CHANGED (LEAN WEAKER (trivially) -> LEAN STRONGER) |
| 9 | D | (prose, line 250) | `NavierStokes/BaseWitnessClosure.lean:22` actual_profile_eq | OTHER: orphan module | NavierStokes/FinalSlowBase.lean:627 profileData_nonempty; :634 actualProfile | EXACT - the cited `rfl` identity is definitional and the in-cone `actualProfile` is the object it names | SAME |
| 10 | A | 4.7 (2nd) (Lemma) | `NavierStokes/ClosedIntervalCk.lean:23` I | WRAPPER | NavierStokes/MomentRepair.lean:206 exists_unique_small_correction; NavierStokes/UniformAngularReset.lean:273 exists_smooth_solver_on_ball | LEAN WEAKER - the in-cone route has the C0 unique small correction and a C-infinity solver in the datum on a ball, but no C^k norm estimate and no statement over the closed interval I = Icc (-1) 1 | CHANGED (LEAN STRONGER -> LEAN WEAKER) |
| 11 | B | A.2 (Lemma) | `NavierStokes/ClosedIntervalMomentRepair.lean:16` Data | WRAPPER | NavierStokes/MomentRepair.lean:206 exists_unique_small_correction; NavierStokes/UniformAngularReset.lean:273 exists_smooth_solver_on_ball; :364 uniform_reset_branch | LEAN WEAKER - existence, uniqueness in the ball and the 2*beta*||d|| bound are in cone; A.2's C^k bound ||c||_{C^k} <= 2 beta_k ||d||_{C^k} and the `Small k` hypothesis family are not | CHANGED (EXACT -> LEAN WEAKER) |
| 12 | A | 4.7 (2nd) (Lemma) | `NavierStokes/ClosedIntervalMomentRepair.lean:151` exists_smooth_same_branch | WRAPPER | NavierStokes/MomentRepair.lean:206 exists_unique_small_correction; NavierStokes/UniformAngularReset.lean:273 exists_smooth_solver_on_ball | LEAN WEAKER - the `same branch` identification and the C^k bound that made the first pass call it stronger are both display-only | CHANGED (LEAN STRONGER -> LEAN WEAKER) |
| 13 | B | 5.5 (Prop) ; B.10 (Cor) | `NavierStokes/ConstructedSlowBase.lean:932` exists_actual_base | WRAPPER | NavierStokes/FinalSlowBase.lean:619 ProfileData; :627 profileData_nonempty; NavierStokes/ConstructedSlowBase.lean:906 Modulated.residual_identity; :919 Modulated.weighted_bound | EXACT - the in-cone route builds the same object constructively (ProfileData + Classical.choice) and proves the same per-field conclusions; the wrapper only re-packages them existentially | SAME |
| 14 | D | 9.6 (Proposition) | `NavierStokes/ExponentLedger.lean:63` wave_increment | WRAPPER | NavierStokes/ExponentLedger.lean:291 stage_parameter_succ; NavierStokes/ActualCyclePreservation.lean:826 state_runInvariant | EXACT in shape - the +1/10 per cycle and the induction that chains it are in cone; the ledger's gain-margin arithmetic (wave_increment and the ~40 margin lemmas) is not | SAME |
| 15 | B | A.1 (Lemma) | `NavierStokes/ExponentialMomentMatrix.lean:72` expBumpMomentMatrix_det_ne_zero | WRAPPER | NavierStokes/PowerMomentMatrix.lean:261 bumpMomentMatrix_det_ne_zero; :143 powerEvaluationMatrix_det_ne_zero | EXACT on A.1's invertibility for the power family; NO IN-CONE COUNTERPART for the exponential/log variant | CHANGED (LEAN STRONGER -> EXACT, partial) |
| 16 | D | (prose, line 139) ; (prose, line 643) | `NavierStokes/FinalSlowBase.lean:361` origin | WRAPPER | NavierStokes/FinalSlowBase.lean:356 leading_origin; NavierStokes/BaseResidual.lean:61 baseVelocity_at_origin | EXACT - `origin` is one rewrite of the two in-cone lemmas; the closed form the prose quotes follows from them | SAME |
| 17 | B | 5.2 (Lemma) | `NavierStokes/FiveRowRank.lean:311` exists_five_row_repair | WRAPPER | NavierStokes/GlobalSlowProfiles.lean:799 exists_step; :786 StepProperties; :758 Admissible; NavierStokes/PositiveOrderMoments.lean:77 rowDensity | EXACT - the five moment rows and the step construction are in cone; only the finite-rank repair packaging is not | SAME |
| 18 | B | A.9 (Lemma) | `NavierStokes/FlatPrimitivePaper.lean:76` exists_factor_on_rectangle | WRAPPER | NavierStokes/ParametricFlatFactor.lean:222 factor_contDiff; NavierStokes/FlatPrimitiveFactor.lean:255 factor_contDiff | LEAN WEAKER - the in-cone machinery gives the smooth parametric factor, but the paper's A.9 identity on the rectangle, B(p,0)=b(p,0)/c and the uniform jet bounds on K x [0,delta0] are stated only in the display file | CHANGED (LEAN STRONGER -> LEAN WEAKER) |
| 19 | A | 4.8 (Lemma) | `NavierStokes/HeatedOutgoing.lean:875` exists_heated_profile | WRAPPER | NavierStokes/ExtendedHeatedOutgoing.lean:81 exists_witness; NavierStokes/OutgoingProfile.lean:557 Specification | EXACT - the in-cone `exists_witness` supplies exactly the compensation witness the wrapper re-exports | SAME |
| 20 | C | 8.4 (Proposition (integrated equations)) | `NavierStokes/IntegratedMeanBalances.lean:639` integrated_angular_balance | WRAPPER | NavierStokes/StateMomentBalances.lean:626 integrated_angular_along; :661 integrated_axial_along; :767 state_angular_moment; :980 state_axial_moment | LEAN STRONGER - the in-cone twin proves the same balance for an ARBITRARY direction pair (z,t) rather than the fixed coordinate direction (0,1), by the same proof | SAME (EXACT/LEAN STRONGER) |
| 21 | C | 6.3 (Lemma (number of relevant labels)) | `NavierStokes/LabelCounting.lean:231` pointwise_count | WRAPPER | (none found) | NO IN-CONE COUNTERPART - no in-cone declaration counts relevant labels | SAME (align-C already flagged `off the headline path`) |
| 22 | A | 3.2 (Definition) | `NavierStokes/LeadingStress.lean:372` physicalVelocity | WRAPPER | NavierStokes/AxisymmetricFields.lean:27 radialEnergy; :29 profilePoint; NavierStokes/ProfileHistories.lean:303 Profiles | NO IN-CONE COUNTERPART for the leading-stress physical velocity itself; the paper's 3.2 is routed around structurally, exactly as the first pass said | SAME (NO COUNTERPART - routed around) |
| 23 | B | (prose, line 461) | `NavierStokes/LeadingStress.lean:458` theta_transport_stress | WRAPPER | NavierStokes/LeadingStress.lean:193 theta_transport_coefficient; :309 radialDivergence_pullback | NO IN-CONE COUNTERPART for the prose identity; the in-cone content is the coefficient/pullback algebra it is assembled from | SAME |
| 24 | A | 4.2 (Proposition) | `NavierStokes/LeadingStress.lean:571` navierStokesResidual_tangential | WRAPPER | NavierStokes/ConstructedSlowBase.lean:906 Modulated.residual_identity; NavierStokes/FinalSlowBase.lean:330 residual_identity | NO IN-CONE COUNTERPART as stated - Proposition 4.2's identity (Cartesian NS residual = minus the weighted radial divergences of q^{-A-1/2} T0) has no in-cone statement; the in-cone residual identity is the different, coarser `navierStokesResidual = stressForce + error` | CHANGED (EXACT -> NO IN-CONE COUNTERPART) |
| 25 | A | 4.6 (Theorem) ; C.3 (Proposition) | `NavierStokes/LeadingStressWeights.lean:1154` exists_weighted_profile | WRAPPER | NavierStokes/FinalSlowBase.lean:619 ProfileData; :627 profileData_nonempty; NavierStokes/LeadingStressWeights.lean:1067 stress_zero_before; :1089 zeta; NavierStokes/ReservedPatches.lean:333 heated_fields | EXACT on 4.6/C.3's substance - the FullTrueCone + WeightedBounds + edge-factor package is a field of the in-cone ProfileData; only the existential restatement is out of cone | SAME |
| 26 | D | 9.1 (Proposition) ; 9.3 (Proposition) | `NavierStokes/LinearWaveBounds.lean:898` constructed_linear_wave_with_flat_error | DEAD | NavierStokes/LinearWaveBounds.lean:833 constructed_linear_wave_with_excluded (5 consumers) | LEAN WEAKER - the carrier proves the WaveClass bound and the constructedGood/excludedSlotError decomposition, but NOT the paper's all-order flat error `forall N, UnweightedClass s N (excludedSlotError ...)`, which exists only behind the unsupplied `GaussianTailFlat.FlatEdges` | CHANGED (EXACT (partial) -> LEAN WEAKER) |
| 27 | D | 10.1 (Proposition) | `NavierStokes/LocalAngularGrowth.lean:60` localized_eq_raw | WRAPPER | NavierStokes/SpatialLocalization.lean:49 spatialCutoff; NavierStokes/TimeLocalization.lean:74 activatedVelocity_eq_late; NavierStokes/R3/ActualCandidate.lean:40 localized_residual_zero_early | EXACT - split; the in-cone half of 10.1 is intact, the cited `localized_eq_raw` is a display-layer restatement of the same plateau identity | SAME |
| 28 | D | (prose, line 84) | `NavierStokes/LocalAngularGrowth.lean:238` selected_candidate_one_with_angular_growth | WRAPPER | NavierStokes/R3/ActualCandidate.lean:143 selected_candidate_one_with_initial_rest; NavierStokes/R3/ProblemStatement.lean:~111 CandidateProperties.speed_unbounded | LEAN WEAKER - the in-cone candidate carries only the qualitative `SpeedUnboundedAtOne`; the quantitative `AngularGrowth` rate (NavierStokes/LocalAngularGrowth.lean:180) has no in-cone counterpart | CHANGED (quantitative rate -> NO IN-CONE COUNTERPART) |
| 29 | A | 3.1 (Theorem) | `NavierStokes/LocalPaperHeat.lean:22` exterior_profile_smooth | WRAPPER | NavierStokes/R3CompactCandidate.lean:24 Properties; :248 of_localized_fields | NO IN-CONE COUNTERPART for the exterior heat-profile clauses of Theorem 3.1 (exterior_profile_smooth and the four sibling exterior lemmas) | CHANGED (LEAN STRONGER -> partial: exterior clauses have no in-cone counterpart) |
| 30 | AD | 3.1 (Theorem) ; 9.9 (Proposition) | `NavierStokes/LocalPaperTheorem.lean:53` Properties | WRAPPER | NavierStokes/R3CompactCandidate.lean:24 Properties; :248 of_localized_fields; :179 of_periodic_local_model | LEAN WEAKER - `LocalPaper.Properties` bundles more (AwayExtensions, UniformJetsOnScaleStrips, all-order residual flatness, the exterior clause) than the in-cone `R3CompactCandidate.Properties` used on the headline route | CHANGED (LEAN STRONGER / EXACT -> LEAN WEAKER against the carrier) |
| 31 | D | (prose, line 596) | `NavierStokes/LocalPaperTheorem.lean:179` local_theorem | WRAPPER | NavierStokes/R3/ActualCandidate.lean:143 selected_candidate_one_with_initial_rest; NavierStokes/R3CompactCandidate.lean:248 of_localized_fields | EXACT on what the headline needs; the full `local_theorem` bundle is display-only | SAME |
| 32 | A | 4.10 (Proposition) | `NavierStokes/MatchingDebtBounds.lean:887` exists_nominal_witness | WRAPPER | NavierStokes/NominalConeAssembly.lean:1517 exists_nominal_cone; NavierStokes/NominalProfile.lean:2481 Witness; :2536 Witness.five_moments | EXACT - the in-cone route obtains the same `NominalProfile.Witness` (with the five-moment certificate) constructively | SAME |
| 33 | B | B.10 (Cor) | `NavierStokes/MatchingDebtBounds.lean:928` nominal_witness_exists | WRAPPER | NavierStokes/NominalConeAssembly.lean:1517 exists_nominal_cone; NavierStokes/NominalProfile.lean:2481 Witness | EXACT - B.10's inhabitation is supplied in cone by exists_nominal_cone rather than by this `Nonempty` wrapper | SAME |
| 34 | A | 4.6 (Theorem) ; C.2 (Proposition) | `NavierStokes/ModulatedProfileAssembly.lean:1126` exists_modulated_profile | WRAPPER | NavierStokes/NominalConeAssembly.lean:1517 exists_nominal_cone; NavierStokes/ModulatedProfileAssembly.lean:1101 exists_of_certificate; :661 Witness.true_cone_from_nominal; NavierStokes/FinalSlowBase.lean:627 profileData_nonempty | EXACT - `exists_modulated_profile` is the two-line composition of two in-cone theorems, and `profileData_nonempty` performs exactly that composition on the headline route | SAME |
| 35 | A | C.2 (Proposition) | `NavierStokes/ModulatedProfileJetRates.lean:347` exists_with_moment_repair_all_jets | WRAPPER | NavierStokes/ModulatedProfileAssembly.lean:619 Witness.rows_outside; :627 Witness.stocks_outside; :641 Witness.shears_outside; :661 Witness.true_cone_from_nominal | EXACT in substance - the four clauses C.2 needs are in-cone fields of the in-cone `Witness`; only the O(1/n) jet-rate packaging is display-only | SAME, with the C/n jet bound newly flagged as out of cone |
| 36 | A | 4.7 (2nd) (Lemma) | `NavierStokes/MomentRepairPicardConvergence.lean:21` exists_small_solution_with_iterates | WRAPPER | NavierStokes/MomentRepair.lean:206 exists_unique_small_correction; :154 correctionIteration_norm_le; :173 correctionIteration_sub_le | EXACT on existence/uniqueness/bound; the Picard-limit `Tendsto` clause has no in-cone statement (the in-cone theorem concludes `ExistsUnique`, not convergence of the iterates) | CHANGED (LEAN STRONGER -> EXACT, one clause out of cone) |
| 37 | B | B.2 (Prop) | `NavierStokes/NaturalAxisJointAnalytic.lean:87` natural_analytic | WRAPPER | NavierStokes/AxisContraction.lean:753 natural_axis_profiles; :731 coefficient_fixedPoint; NavierStokes/AnalyticCoefficientBounds.lean:315 uniform_normalizedExp_axisData | EXACT - the fixed-point construction and its analytic coefficient bounds are in cone; only the packaged analyticity of the four named profile fields is not | SAME |
| 38 | B | B.3 (Prop) | `NavierStokes/NaturalExitBounds.lean:130` Estimates | WRAPPER | (none found) | NO IN-CONE COUNTERPART - none of B.3's exit estimates (phi_lower, source_lower, p1_lower, ns_error, cone_margin, parameter_jets) has an in-cone statement | CHANGED (LEAN STRONGER -> NO IN-CONE COUNTERPART) |
| 39 | A | 4.10 (Proposition) | `NavierStokes/NominalProfile.lean:2637` exists_assembly_threshold | WRAPPER | NavierStokes/NominalConeAssembly.lean:1517 exists_nominal_cone; NavierStokes/ExtendedHeatedOutgoing.lean:81 exists_witness | EXACT - the assembly threshold is supplied in cone by exists_witness inside exists_nominal_cone | SAME |
| 40 | C | 7.7 (Lemma (exact curls)) | `NavierStokes/OscillatoryCurl.lean:160` wave_eq | WRAPPER | NavierStokes/CurlClassBounds.lean:758 curlRemainder_waveClass | LEAN WEAKER - the in-cone carrier gives the class bound on the curl remainder, but Lemma 7.7's EXACT curl identity and exact divergence-freeness have no in-cone statement | CHANGED (EXACT -> LEAN WEAKER) |
| 41 | A | 3.3 (Definition) | `NavierStokes/OutgoingProfile.lean:640` exists_outgoing_profile | WRAPPER | NavierStokes/OutgoingProfile.lean:557 Specification; NavierStokes/ExtendedHeatedOutgoing.lean:81 exists_witness | EXACT - 3.3 is a prose convention; the nested-existential ordering the first pass pointed at is reproduced in cone by the same Specification/witness pair | SAME (NO COUNTERPART - routed around) |
| 42 | B | 5.1 (Lemma) | `NavierStokes/PositiveAxisDifferential.lean:257` positive_solution_unique | WRAPPER | NavierStokes/SlowRecursion.lean:1272 buildLocalHierarchy; :1256 LocalHierarchy; NavierStokes/ActualSlowAxis.lean:287 hierarchy | EXACT on 5.1's existence/regularity; NO IN-CONE COUNTERPART for the uniqueness clause in the larger competitor class | CHANGED (LEAN STRONGER -> EXACT, uniqueness out of cone) |
| 43 | B | A.2 (Lemma) | `NavierStokes/QuadraticLinearization.lean:12` isInvertible | WRAPPER | NavierStokes/UniformAngularReset.lean:223 tangent_invertible; :273 exists_smooth_solver_on_ball | EXACT - the linearization-invertibility step is in cone in the reset-solver form | SAME |
| 44 | D | 10.4 (Lemma) | `NavierStokes/R3/IntegratedDissipation.lean:143` candidate_l2Norm_le_cumulativeForceNorm | ABOVE_SEED | NavierStokes/R3/ProblemStatement.lean:108 CandidateProperties.energy_bounded (UniformFiniteEnergy (Ico 0 1) u) | LEAN WEAKER - the only in-cone energy statement is the plain uniform L2 bound; Lemma 10.4's dissipation inequality (10.13), the L2-norm/force comparison and the integrability clauses are reached only above the seed | CHANGED (LEAN STRONGER -> LEAN WEAKER / NO IN-CONE COUNTERPART for (10.13)) |
| 45 | D | 10.4 (Lemma) | `NavierStokes/R3/Theorem.lean:66` theorem_1_1_with_dissipation | ABOVE_SEED | NavierStokes/R3/Theorem.lean:46 theorem_1_1 (the seed itself) | LEAN STRONGER than the seed but irrelevant to it - `theorem_1_1_with_dissipation` is `theorem_1_1` plus CompactEnergy.candidate_energy_estimates, so it implies the seed and cannot be below it | SAME (legitimately above the seed) |
| 46 | B | B.7 (Lemma) | `NavierStokes/ReferenceEndpointRate.lean:275` exists_entrance_envelope | WRAPPER | (none found) | NO IN-CONE COUNTERPART - the entrance-envelope constants of B.7 have no in-cone statement | CHANGED (EXACT -> NO IN-CONE COUNTERPART) |
| 47 | B | B.4 (Lemma) | `NavierStokes/ReferenceUniformStocks.lean:414` uniform_reference_quantities | WRAPPER | NavierStokes/ReferenceBounds.lean:1004 ReferenceBoundsOnHold; :1180 exists_reference_bounds | EXACT on the bounds half of B.4; NO IN-CONE COUNTERPART for the four `Uniform k` C^k families | CHANGED (EXACT -> EXACT on bounds, C^k half out of cone) |
| 48 | A | 4.8 (Lemma) | `NavierStokes/SchedulePressure.lean:175` axisPressure_even | CENSUS_MISS (attribute blind spot) | NavierStokes/SchedulePressure.lean:155 axisPressure_eq; :171 axisPressure_contDiff; NavierStokes/PressureDatum.lean:62 pressure_neg | EXACT - evenness holds definitionally for the in-cone `axisPressure` through `axisPressure_eq` + `PressureDatum.pressure_neg` | SAME, but the cone verdict for this row is not decidable at name level |
| 49 | A | 4.3 (Lemma) | `NavierStokes/SeedHandbackJets.lean:94` stocks_formulas | WRAPPER | NavierStokes/StressAlgebra.lean:238 angular_integrated_lag; :255 axial_integrated_lag | EXACT - both displayed formulas of (4.16) are in cone in the StressAlgebra rendering; only the second, definitional SeedHandbackJets rendering is not | SAME |
| 50 | A | 4.4(ii) (Lemma) | `NavierStokes/SeedHandbackJets.lean:354` profile_comparison_norm | WRAPPER | (none found) | NO IN-CONE COUNTERPART - the profile-comparison estimate (4.17) has no in-cone statement | CHANGED (EXACT -> NO IN-CONE COUNTERPART) |
| 51 | C | 7.8 (Corollary (covariance expansion)) | `NavierStokes/SignedCovariance.lean:409` physical_signed_cross_covariance | DEAD | NavierStokes/SignedCovariance.lean:312 cross_reconstruct_component; :623 increment_wave_class; :569 signed_quotient_class | EXACT in substance / NO SINGLE COUNTERPART - the pointwise reconstruction (7.41) and the class bounds (7.42) are in cone separately; the assembled and physical covariance identities are not | SAME (the first pass already said `no one declaration states (7.41)+(7.42) together`) |
| 52 | C | 8.5 (Corollary (covariance targets)) | `NavierStokes/SignedStressPrimitive.lean:1014` axial_bump_identity | WRAPPER | NavierStokes/SignedStressPrimitive.lean:506 bump_improvedClass_of_moment_identity; NavierStokes/StateMomentBalances.lean:1081 state_angular_bump_improvedClass; :1096 state_axial_bump_improvedClass | EXACT - the generic bump-order lemma and the state-level angular/axial improved-class theorems in cone carry 8.5's content | SAME |
| 53 | B | A.1 (Lemma) | `NavierStokes/SmoothExponentialMomentMatrix.lean:80` matrix_inverse_contDiffOn | WRAPPER | NavierStokes/PowerMomentMatrix.lean:261 bumpMomentMatrix_det_ne_zero | NO IN-CONE COUNTERPART for the smooth-inverse half of A.1 (matrix inverse ContDiffOn in the parameter) | CHANGED (LEAN STRONGER -> invertibility EXACT, smooth-inverse half out of cone) |
| 54 | B | A.1 (Lemma) | `NavierStokes/SmoothPowerMomentMatrix.lean:178` matrix_inverse_contDiffOn | WRAPPER | NavierStokes/PowerMomentMatrix.lean:261 bumpMomentMatrix_det_ne_zero | NO IN-CONE COUNTERPART for the smooth-inverse half of A.1 | CHANGED (as row 53) |
| 55 | A | 4.7 (1st) (Lemma) | `NavierStokes/SmoothPowerMomentMatrix.lean:197` compact_inverse_jets_bound | WRAPPER | NavierStokes/PowerMomentMatrix.lean:261 bumpMomentMatrix_det_ne_zero; :29 expSum | NO IN-CONE COUNTERPART for 4.7(1st)'s `inverse and every fixed parameter jet bounded on a compact family` clause | CHANGED (LEAN STRONGER -> NO IN-CONE COUNTERPART for the jet-bound clause) |
| 56 | A | 4.2 (Proposition) | `NavierStokes/StressAlgebra.lean:316` stressFree_angular_lag_algebra | WRAPPER | (none found) | NO IN-CONE COUNTERPART - the stress-free substitution algebra of (7)->(8) has no in-cone statement, and neither does the 4.2 residual identity it feeds (row 24) | CHANGED (EXACT -> NO IN-CONE COUNTERPART) |
| 57 | B | A.10 (Prop) | `NavierStokes/TerminalEdgeFactor.lean:1595` physicalStress_factorization | WRAPPER | NavierStokes/TerminalEdgeFactor.lean:1467 profile_uniform_cone; :1562 profile_relative_cone; :1440 profileConeGap_zero; NavierStokes/TerminalCone.lean:398 profile_cone_margin; :452 profile_full_true_cone | EXACT on A.10's cone/margin content (including the closed endpoint delta = 0); NO IN-CONE COUNTERPART for the physical (q-scaled) stress factorization (A.48)-(A.50) and the (A.51) jet bound | CHANGED (EXACT -> EXACT on the cone half, factorization half out of cone) |
| 58 | B | A.10 (Prop) | `NavierStokes/TerminalEdgePaper.lean:16` profileStress_lower_bound | WRAPPER | NavierStokes/TerminalEdgeFactor.lean:1467 profile_uniform_cone | EXACT - the (A.51) lower bound is literally `obtain := profile_uniform_cone` and that in-cone theorem already carries it | SAME |
| 59 | C | 6.2 (Lemma (common torus)) | `NavierStokes/TorusCoverDegree.lean:208` card_fiber | WRAPPER | NavierStokes/TorusAverages.lean:94 integral_torusCovering_iterate | NO IN-CONE COUNTERPART for the 14^d fibre count and the sheetwise bijection; the in-cone half is only the Haar-agreement (6.19) | CHANGED (LEAN STRONGER / partly routed around -> NO IN-CONE COUNTERPART for the counting half) |
| 60 | C | 6.2 (Lemma (common torus)) | `NavierStokes/TorusCoverLattice.lean:59` indexHom_range_index | WRAPPER | NavierStokes/TorusAverages.lean:94 integral_torusCovering_iterate | NO IN-CONE COUNTERPART - the lattice index 14 is used only by the counting half, which is out of cone | CHANGED (as row 59) |
| 61 | A | 4.11 (Lemma) | `NavierStokes/TrueConeLoop.lean:765` exists_compact_trueCone_family_with_margin | WRAPPER | NavierStokes/TrueConeLoop.lean:658 family_pointwise_properties; :714 family_joint_contDiffOn; :459 exists_family_choices; :372 constructed_trueCone; :346 constructed_means | LEAN WEAKER - the in-cone carrier gives periodicity, the two prescribed means, joint smoothness and the strict `InTrueCone` at every phase, but NOT the uniform cone margin: `HasConeMargin` (:283) occurs nowhere in cone | CHANGED (LEAN WEAKER (hypothesis only) -> LEAN WEAKER, and now on the conclusion too) |
| 62 | A | 4.5 (2nd) (Lemma) | `NavierStokes/UniformCone.lean:148` compact_equation_eleven | WRAPPER | NavierStokes/UniformCone.lean:176 compact_equation_eleven_gap; :62 compact_normalized_cone | LEAN STRONGER - the in-cone `_gap` version is the additive-gap strengthening the first pass called the extra, so the strong form is the one on the headline route | SAME (LEAN STRONGER) |
| 63 | C | 8.2 (Lemma (compact radial primitive)) | `NavierStokes/UniformFourierAlias.lean:1134` meanClass_alias_superflat | WRAPPER | NavierStokes/UniformFourierAlias.lean:1193 real_exactAlias_finiteJets | EXACT - the carrier gives, for every jet order m and every gain order p, the bound K*C*|M|^{-p} with no uniformity in p, which is exactly (8.8) as the paper states it; only the epsilon^N `superflat` repackaging is out of cone | SAME |
| 64 | B | A.2 (Lemma) | `NavierStokes/UniformQuadraticBranch.lean:131` exists_smooth_small_branch | WRAPPER | NavierStokes/UniformAngularReset.lean:273 exists_smooth_solver_on_ball | LEAN WEAKER - the in-cone smooth solver is on a ball in the datum with a C0 bound; the uniform-over-S smooth branch with the ||c|| <= 2*nu*delta bound and ball uniqueness is display-only | CHANGED (EXACT -> LEAN WEAKER) |

## Findings worth an expert (ranked)

**1. Prop 9.1 / 9.3 — the all-order flat error is not on the headline route.**
Cited wrapper `NavierStokes/LinearWaveBounds.lean:898 constructed_linear_wave_with_flat_error`
(zero consumers, takes the unsupplied `GaussianTailFlat.FlatEdges`). Its in-cone twin
`NavierStokes/LinearWaveBounds.lean:833 constructed_linear_wave_with_excluded` (5 consumers) proves
the `WaveClass s P (α + 1/2 − 3κ)` bound and the `constructedGood + excludedSlotError` decomposition
— but **not** `∀ N, UnweightedClass s N (excludedSlotError …)`. That clause exists only in
`NavierStokes/LinearWaveBounds.lean:868 excludedSlotError_all_gains`, whose single use is
`NavierStokes/ParticularWaveAssembly.lean:1547 LocalControl.gaussian_flat`, **out of cone**, inside a
structure whose other 25 field lemmas (`:1488`–`:1679`) are in cone. So the headline construction
carries the wave bound and the decomposition but, at name level, never the flatness of the retained
error. Carrier vs paper: **LEAN WEAKER**.

**2. Lemma 7.7 — the exact-curl identity has no in-cone statement.**
`NavierStokes/OscillatoryCurl.lean:160 wave_eq`, `:188 wave_divergence_free`, `:224 wave_tsupport_subset`
and `:274 wave_eq_stripped` are all out of cone; only the definitions (`:129 coefficient`, `:133 potential`,
`:136 wave`, `:109 carrier`, `:122 phaseNormal`) and two periodicity lemmas are in. The one in-cone
carrier, `NavierStokes/CurlClassBounds.lean:758 curlRemainder_waveClass`, is a *class bound on the
remainder*, not an identity, and says nothing about exact divergence-freeness. The exact-curl clause
enters only at `NavierStokes/ParticularWaveAssembly.lean:1565 LocalControl.exact_curl`, also out of
cone. Carrier vs paper: **LEAN WEAKER**. (Rows 1 and 2 are the same two fields of the same structure.)

**3. Lemma 4.11 — the uniform cone margin is nowhere in cone.**
`NavierStokes/TrueConeLoop.lean:283 HasConeMargin` occurs in exactly four places in the repository:
its own definition, `:298` and `:784` (both out of cone) and `NavierStokes/TrueConeLoopPaper.lean:39`
(display layer). The in-cone carrier `NavierStokes/TrueConeLoop.lean:658 family_pointwise_properties`
(with `:346 constructed_means`, `:372 constructed_trueCone`, `:714 family_joint_contDiffOn`) gives
periodicity, both prescribed means, joint smoothness and strict `InTrueCone` at every phase — but no
`ε`-margin. The first pass called 4.11 "LEAN WEAKER (hypothesis only)"; against the carrier the
weakening is **on the conclusion as well**.

**4. Proposition 4.2 — no in-cone counterpart at all.**
Both declarations align-A cites (`NavierStokes/LeadingStress.lean:571 navierStokesResidual_tangential`,
zero consumers, and `NavierStokes/StressAlgebra.lean:316 stressFree_angular_lag_algebra`, zero
consumers) are out of cone, and so is the whole chain feeding them (`:458 theta_transport_stress`,
`:499 axial_transport_stress`, `:392`/`:409 radialDivergence_physicalStress*`, `:372 physicalVelocity`).
The in-cone residual identity is the coarser `navierStokesResidual = stressForce + error`
(`NavierStokes/ConstructedSlowBase.lean:906`, `NavierStokes/FinalSlowBase.lean:330`), which is a
different statement: it does not say the leading residual equals minus the weighted radial divergences
of `q^{−A−1/2}T₀`. **CHANGED: EXACT → NO IN-CONE COUNTERPART.** Note `LeadingStress.physicalPressure`
(`:376`) is in cone while `physicalVelocity` (`:372`) is not, which is worth an eyeball.

**5. Lemma 10.4 is genuinely above the seed, and the in-cone energy statement is much weaker.**
`NavierStokes/R3/Theorem.lean:66 theorem_1_1_with_dissipation` = `theorem_1_1` + energy estimates, so
it is legitimately `ABOVE_SEED`; `NavierStokes/R3/IntegratedDissipation.lean` is 0/8 in cone and feeds
only it. The only in-cone energy clause is
`NavierStokes/R3/ProblemStatement.lean:108 energy_bounded : UniformFiniteEnergy (Ico 0 1) u` — a bare
`∃E, kineticEnergy ≤ E`. The paper's (10.13) dissipation inequality, the `l2Norm ≤ cumulativeForceNorm`
comparison and the integrability statements are **not below the headline theorem**. This is not a
defect in Theorem 1.1 (which does not need them) but it does mean the "LEAN STRONGER for every ν>0
with 2ν in front" verdict describes a statement the headline does not use.

**6. Lemma A.2 / Lemma 4.7(2nd) — the C^k half of the moment repair is display-only.**
`ClosedIntervalCk.lean` (0/48), `ClosedIntervalMomentRepair.lean` (0/24), `UniformQuadraticBranch.lean`
(0/4), `QuadraticLinearization.lean` (0/1), `MomentRepairPicardConvergence.lean` (0/1) are *all* outside
the seeds' import closure. The in-cone carriers are
`NavierStokes/MomentRepair.lean:206 exists_unique_small_correction` (C⁰ `ExistsUnique`, no convergence
clause) and `NavierStokes/UniformAngularReset.lean:273 exists_smooth_solver_on_ball` (a C^∞ solver on a
ball, with `‖g d‖ ≤ 2β‖d‖`). Neither states `‖c‖_{C^k} ≤ 2β_k‖d‖_{C^k}` over `I = Icc (-1) 1`, nor the
"same branch" identification, nor the Picard limit. **CHANGED: EXACT / LEAN STRONGER → LEAN WEAKER**
for rows 10, 11, 12, 36, 64 (and row 43 is fine).

**7. Proposition B.3 and Lemma B.7 — no in-cone counterpart found.**
`NavierStokes/NaturalExitBounds.lean` (0/8) and `NavierStokes/ReferenceEndpointRate.lean` (0/17) are
display-only and I located nothing in cone stating the exit estimates (`phi_lower`, `source_lower`,
`p1_lower`, `ns_error`, `cone_margin`, `parameter_jets`) or the entrance envelope (`endpointLog`,
`endpointU`, `Cjoin`). Searched: those field names, `coneSize`, `exists_exit`, `ideal_prefix_exit`,
`exists_linear_Ck_constants`, and the `NaturalEntrance` / `ReferenceBounds` namespaces. Both were
first-pass **LEAN STRONGER**; against the cone they are **NO IN-CONE COUNTERPART**.

**8. Lemma 4.4(ii) and Lemma 6.2's counting half — no in-cone counterpart.**
`NavierStokes/SeedHandbackJets.lean` is 0/40 and outside the import closure; `outputDifference`,
`fieldDifference`, `historyDifference` and `parameterNorm` occur nowhere else in the repository, so
(4.17) has no in-cone statement. For 6.2, `TorusCoverDegree.lean` (0/35) and `TorusCoverLattice.lean`
(0/17) are display-only; the only in-cone piece is the Haar agreement
`NavierStokes/TorusAverages.lean:94 integral_torusCovering_iterate`. The `14^Δ` count, the sheetwise
bijection and the lattice index are not below the headline.

**9. One row the cone census cannot decide, and it is the documented blind spot.**
Row 48, `NavierStokes/SchedulePressure.lean:175 axisPressure_even`, is the **only** one of the 64 that
carries an implicit-use attribute: it is `@[simp]`. `simp` can fire it anywhere in the cone without
naming it, so "out of cone" here is a limitation of the name-level census, not evidence of dead code —
`axisPressure` itself is in cone (`:29`, with `:155 axisPressure_eq` and `:171 axisPressure_contDiff`)
and is used across roughly eight in-cone files. Classified `CENSUS_MISS (attribute blind spot)`. **No
other row required a CENSUS_MISS**: every zero-consumer wrapper was confirmed unreferenced by a
repository-wide `grep -rnw` restricted to files that actually import the declaring module.

### Two rows that get *better*

- **Row 8, Prop 5.3.** The first pass said "LEAN WEAKER (trivially)" because
  `NavierStokes/BaseResidual.lean:1439 truncationResidual_rate` has exponent `2Nh − 2 − m` against the
  paper's `2h(N+1) − K_m`. But that theorem's whole chain (`:1521 baseResidual_jetRate` →
  `:1614 baseResidual_allJetsFlat`) is out of cone. The in-cone carrier is
  `NavierStokes/BaseResidual.lean:2514 baseResidual_jetRate_axis`, which proves
  `JetRate … m n` for **every** real `n ≥ 0` — arbitrary flatness order, and up to the symmetry axis.
  **CHANGED: LEAN WEAKER → LEAN STRONGER.**
- **Row 62, Lemma 4.5(2nd).** `NavierStokes/UniformCone.lean:148 compact_equation_eleven` is out of
  cone but `:176 compact_equation_eleven_gap` — the additive-gap strengthening — is in. The strong
  form is the one on the headline route.

### One structural observation the first pass could not have made

Proposition 8.4 and Corollary 8.5 look out of cone in `IntegratedMeanBalances.lean` and
`SignedStressPrimitive.lean`, but they are **not** missing: there is a full in-cone twin in
`NavierStokes/StateMomentBalances.lean` — `:626 integrated_angular_along` and `:661 integrated_axial_along`
prove the same balances for an **arbitrary direction pair `(z,t)`** by a line-for-line identical proof
(same `moment_balance_algebra`, same `zero_mass_parameterPartial`), and `:1081`/`:1096
state_*_bump_improvedClass` carry 8.5. That is the "live twin" pattern of the calibration example, and
here the twin is *stronger*, not weaker. The same pattern holds for Lemma 8.2, where the in-cone
carrier `NavierStokes/UniformFourierAlias.lean:1193 real_exactAlias_finiteJets` sits one rung below
the five out-of-cone `*_alias_superflat` variants and states (8.8) in exactly the paper's
"no estimate uniform in p" form.

## What I did not check

- **I did not re-derive the four slice reports.** Where a row's paper-side reading is inherited
  (e.g. what Prop 9.3 (ii)/(iii) actually say), I took the first pass at its word and only moved the
  Lean side from wrapper to carrier.
- **Instances, the `@[simp]` set, `gcongr`/`positivity`/`aesop` extensions.** `cone.py` cannot see
  them and neither can I without a build. Row 48 is the one place this bit; for the other 63 rows no
  implicit-use attribute is present on the cited declaration, but a *carrier* could still be reached
  implicitly, so "no in-cone counterpart" always means "no **named** in-cone counterpart".
- **I did not verify that any in-cone carrier is correct.** This pass is about reachability and
  statement strength, not about whether the carriers' proofs are sound. In particular I did not look
  at `sorry`, `native_decide`, `Classical.choice` misuse or axiom leakage in any carrier.
- **The 108 alignment citations that are already in cone** were not re-examined; nor were the 33
  display-layer modules' other declarations beyond the cited ones.
- **Consumer search method.** I used `grep -rnw <short name>` filtered by the declaring module's
  import closure, and flagged short-name ambiguity. Three names in the set are ambiguous enough that
  raw grep badly overcounts (`ClosedIntervalCk.I`, `FinalSlowBase.origin`,
  `PositiveAxisDifferential.positive_solution_unique` — the last has a same-named sibling at
  `NavierStokes/SimilarityCoordinates.lean:103`); those three I resolved by hand. I did not do a
  whole-repo elaboration-level reference check.
- **The Euler half.** All 64 rows are Navier–Stokes; `Euler.euler_breakdown_R3` is a seed but no row
  cites an Euler declaration, so the Euler side of the cone was used only as part of the denominator.
- **I did not check whether `ParticularWaveAssembly.LocalControl` is ever constructed.** The prior
  pass lists it as one of the 43 confirmed-unsupplied predicates; findings 1 and 2 above would be
  sharper still if that is right, since then even the 25 in-cone field lemmas are vacuous.

