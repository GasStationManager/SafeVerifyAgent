# Alignment audit — slice B: paper §5, Appendix A (A.1–A.10), Appendix B (B.1–B.10)

Paper: `ns-paper.txt` (text extraction of the published PDF, not committed)
Lean:  `/home/user/openai/navierstokesandeuler` (`NavierStokes/`, 816 files)

Scope reminder: this is a **specification** pass, not a soundness pass. I compared the
paper's *intermediate statements* with the Lean *statements* that carry the same
mathematical content. Docstrings were used only as search hints.

---

## 1. Summary table

| # | kind | page | Lean counterpart(s) `file:line` | class | how |
|---|---|---|---|---|---|
| 5.1 | Lemma | p47 | `NavierStokes/SlowRecursion.lean:1256` (`LocalHierarchy`), `:1272` (`buildLocalHierarchy`), `:1283` (`exists_local_slow_hierarchy`), `:1298` (`equations_on_window`); uniqueness `NavierStokes/PositiveAxisDifferential.lean:257` (`positive_solution_unique`), `:211`; instantiation `NavierStokes/ActualSlowAxis.lean:287` | **LEAN STRONGER** *(revised in the addendum)* | one radius `core` **and one complex η-neighborhood `U`** serve *every* order and *every* radial derivative; paper allows both to shrink with order/derivative. Uniqueness proved in a *larger* competitor class (continuous radial + holomorphic slices, no uniform bounds). Placement `X_keep < X_cut < a² < inf I_pos` is **proved** about the real witness (`AssembledSlowBase.lean:1083`,`:1098`,`:1102`); see Addendum §A. |
| 5.2 | Lemma | p50 | `NavierStokes/GlobalSlowProfiles.lean:730` (`Scheme`), `:758` (`Admissible`), `:786` (`StepProperties`), `:799` (`exists_step`), `:1925`–`:1965` (support/smoothness); moments `NavierStokes/PositiveOrderMoments.lean:77,84`; matrix rank `NavierStokes/FiveRowRank.lean:311`; stress support `NavierStokes/SlowStressSupport.lean` | **EXACT** (weighted bound (5.13) only partly verified) | radii `a < b ≤ B` are fields of `Scheme`, fixed before `n` (matches "independent of n"); the five moment rows `rowDensity` are literally (5.10)–(5.11); `exists_step` returns `mn = 0` plus exterior vanishing. See §2.2 for what I could not close on (5.13). |
| 5.3 | Prop | p55 | `NavierStokes/BaseResidual.lean:1439` (`truncationResidual_rate`), `:1513` (`FiniteIdentities`), `:1521`/`:2514` (`baseResidual_jetRate`, `…_axis`) | **LEAN WEAKER (trivially)** | Lean exponent is `2·N·h − 2 − m`; paper (5.25) is `2h(N+1) − K_m`. Same shape (`K_m = m+2`, independent of `N`), Lean is short by exactly one slow order `2h`. Harmless: `N` is universally quantified. |
| 5.4 | Lemma | p57 | `NavierStokes/SlowBorelBase.lean` (cutoff-schedule Borel summation), `NavierStokes/BorelExtension.lean`, `NavierStokes/ConstructedSlowBase.lean:839` (`scales`), `:842` (`scales_spec`) | **EXACT** | `aj+1 ≥ 2aj` / `a₁⁻¹ < q₀` is `AdmissibleScales` + `StrictMono a` + `B ≤ a 0`; the cutoff `χ` is the schedule's. |
| 5.5 | Prop | p60 | `NavierStokes/ConstructedSlowBase.lean:932` (`exists_actual_base`), `:885`, `:906` (`residual_identity`), `:911` (`error_allJetsFlat`), `:919` (`weighted_bound`) | **EXACT** | `div u = 0`, `R(u,p) = stressForce + error`, `AllJetsFlat` ⇒ `\|∂^α E_B\| ≤ C_{α,M} q^M` for every `M`, uniform on the compact carrier (see §2.3 on the filter formulation). |
| A.1 | Lemma | p126 | `NavierStokes/PowerMomentMatrix.lean:261` (`bumpMomentMatrix_det_ne_zero`), `:143`, `:192`; log version `NavierStokes/ExponentialMomentMatrix.lean:72`; parameter part `NavierStokes/SmoothPowerMomentMatrix.lean:178,184,197`, `NavierStokes/SmoothExponentialMomentMatrix.lean:80,86,98` | **LEAN STRONGER** | continuity of the bumps suffices (paper assumes smooth); proved for general finite positive measures; inverse + *all* fixed parameter jets bounded uniformly on an arbitrary compact parameter set. |
| A.2 | Lemma | p127 | `NavierStokes/ClosedIntervalMomentRepair.lean:16` (`Data`), `:45` (`Small`), `:151` (`exists_smooth_same_branch`), `:210` (`linear_solution`); `NavierStokes/UniformQuadraticBranch.lean:131`; `NavierStokes/QuadraticLinearization.lean:12` | **EXACT** | `I = Icc (-1) 1 = K`; `Small k` is literally `8 β_k² κ_k ‖d‖_{C^k} ≤ 1`; conclusion `‖c‖_{C^k} ≤ 2 β_k ‖d‖_{C^k}` on the **same** branch; uniqueness in the C⁰ ball; selection by iteration from zero is the `Tendsto … correctionIteration^[n] 0` clause; `Q = 0` case needs no smallness. |
| A.3 | Cor | p128 | `NavierStokes/FiveProfileMoments.lean:263` (`GoodExponent`), `:273`–`:274` (`axialPowers`,`angularPowers`), `:265`,`:267`, `:300`,`:336`; `NavierStokes/FiveRowRank.lean:81,84,88,311` | **EXACT** | `GoodExponent b := b ≠ −1/2 ∧ b ≠ 1/2 ∧ b ≠ 3/2` and the two weight blocks `![0, b+1/2]`, `![1/2, b, b−1]` are the paper's verbatim; both uses (`α = 1/10`, `α = −1/2−λ`) discharged as `good_initial`, `good_outgoing`; quadratic form via `quadraticCLM` + `normalizedMap`. |
| A.4 | Prop | p130 | `NavierStokes/OutgoingProfile.lean:557` (`Specification`), `:594` (`exists_profile_for_data`); schedule `NavierStokes/OutgoingSchedule.lean`; amplitude `NavierStokes/CorrectedPulseAmplitude.lean`, `NavierStokes/PulseAmplitude.lean`; patches `NavierStokes/ReservedPatches.lean`; cone `NavierStokes/OutgoingCone.lean`, `…/OutgoingEntranceCone.lean`, `…/OutgoingNegativeSlopeCone.lean`, `…/PulseCone.lean`, `…/TailCone.lean` | **EXACT for the analytic content; cone clause only partly traced** | `Specification` carries smoothness, `E > 0`, `ideal_prefix` = (A.7) verbatim, all four moment identities of (A.8) (`mass_total_zero`, `angular_total_zero`, `energy_zero`, `renormalized_zero`), `after_pulse` (U=M=J=0), `eventual_power` (E=Epow). The cone assertions of A.4 live in separate files that I located but did not read line-by-line (§4). |
| A.5 | Lemma | p133 | `NavierStokes/PressureDatum.lean:18` (`pressure`), `:62` (even), `:95` (`pressure_translate`, XR-independence), `:243` (smooth), `:213` (`complexPressure_analytic`), `:348`,`:360` (sign of `Π₀′`), `:425` (`pressure_le_of_ideal_prefix`); instantiated on the real schedule at `NavierStokes/SchedulePressure.lean:147` (`admissible`), `:157` (`axisPressure_eq`), `:175` (`axisPressure_even`), `:180` (`axisPressure_lower_bound`) | **EXACT** | `axisPressure_lower_bound : axisPressure d η ≤ −(5/2)·P²·shape η ^ 2` is (A.22) with `shape η = (1+η²)⁻¹ = f`; analyticity is on the *explicit* strip `{\|Im z\| < 1/2}` ⊇ [−1,1]. The instantiation uses the *uncorrected* schedule `finalAngular`, matching the paper's "azimuthal corrections … omitted". |
| A.6 | Lemma | p138 | `NavierStokes/RadialHeatProfile.lean:29` (`profile`), `:121`,`:124`,`:320` (`moment_ode` = (A.37)), `:624`,`:635` (`radial_heat_equation`), `:660` (`radialProfile_derivative_neg` = `K_r<0`), `:441` (`profile_logSlope_lt` = `−ZH′/H < h`), `:666`,`:680` (joint smoothness); jets `NavierStokes/HeatProfileExtension.lean:24`–`:99`; (A.35)/(A.36) `NavierStokes/AppendixHeatResults.lean:66` (`endpoint_derivatives` = (A.35)), `:76`, `:89`, `:143` (`small_argument_remainder`), `:166` (`uniform_small_argument`) | **LEAN STRONGER** | every claim of A.6 is present, plus: `HeatProfileExtension.extension` is a **globally smooth** extension of `H` past `Z = 0` (Borel-glued), which is more than the paper's "η-derivatives extend continuously to η = ±1 from the interior"; (A.36)'s constant is explicit: `uniform_small_argument` (`AppendixHeatResults.lean:166`) gives `\|H−1\| + \|Z H′\| ≤ 2(1+h₀)·h·Z`. |
| A.7 | Prop | p139 | `NavierStokes/HeatTailEdit.lean`, `NavierStokes/HeatSwitchCone.lean`, `NavierStokes/HeatedOutgoing.lean`, `NavierStokes/ExtendedHeatedOutgoing.lean`, `NavierStokes/RenormalizedHeatMoment.lean`, `NavierStokes/TerminalCompensation.lean`, `NavierStokes/ParametricTerminalCompensation.lean`, `NavierStokes/ReservedPatches.lean`; consumed as `ExtendedHeatedOutgoing.Witness` in `NavierStokes/NominalProfile.lean:2487` | **UNRESOLVED (structural mapping only)** | I located the files and confirmed the edit + three-bump compensation is carried by a constructed `ExtendedHeatedOutgoing.Witness` that the assembled `NominalProfile.Witness` holds, and that `NominalProfile.Witness` **is** constructed (`MatchingDebtBounds.nominal_witness_exists`). I did not read the per-clause statements (M, J, S(∞), C_p(∞), renormalized angular moment preserved *pointwise on* [−1,1]). (Partly relieved by the addendum: `FiveMomentCertificate` is proved for the *post-edit* assembled profile, `NominalProfile.lean:2536`.) |
| A.8 | Lemma | p140 | `NavierStokes/NominalProfile.lean:2079` (`FiveMomentCertificate`), `:2536` (`Witness.five_moments`), `:2543` (`pressure_canonical`); representation `NavierStokes/TerminalStress.lean:36` (`backwardStress`), `:725` (`terminalStress_formula` = (A.54)), `:754`, `:778`; vanishing past `X_b` `NavierStokes/TerminalEdgeFactor.lean:1627`, `:1631`; forward↔backward at order 1 `NavierStokes/FirstOrderBaseEdge.lean:248`, applied `:377` | **EXACT** *(revised in the addendum)* | hypotheses are the exact pointwise-in-η `FiveMomentCertificate` plus `Π(X) = −½∫_X^∞E²/x`; (A.46) is `backwardStress R r = (∫_{Ioi r} u²R)/r²` verbatim, positive sign; "stresses vanish for `X ≥ X_b`" is an **identity** (`δ = 3−y ≤ 0`), stronger than derived. Residue: the zeroth-order forward↔backward identification not located; the order-1 analogue is proved. |
| A.9 | Lemma | p141 | `NavierStokes/FlatPrimitivePaper.lean:76` (`exists_factor_on_rectangle`); machinery `NavierStokes/FlatPrimitive.lean`, `NavierStokes/FlatPrimitiveFactor.lean`, `NavierStokes/ParametricFlatFactor.lean` | **LEAN STRONGER** | identity `∫₀^δ e^{−c/u²}u^{−j} b(p,u) du = ½ e^{−c/δ²} δ^{3−j} B(p,δ)` verbatim, with `B` **globally** `ContDiff ℝ ∞`, `B(p,0) = b(p,0)/c`, and *every* mixed jet bounded on `K × [0,δ₀]`; the parameter lives in an arbitrary normed space, not just a compact interval of η. |
| A.10 | Prop | p142 | `NavierStokes/TerminalEdgeFactor.lean:1595` (`physicalStress_factorization`), `:1607` (`physicalStress_jets` = (A.51) upper), `:1467` (`profile_uniform_cone`), `:1562` (`profile_relative_cone`), `:1659` (`profile_true_cone`), `:1440` (`profileConeGap_zero = 2`); full interval `NavierStokes/TerminalCone.lean:398` (`profile_cone_margin`), `:422` (`profile_relative_cone`), `:452` (`profile_full_true_cone`); lower bound `NavierStokes/TerminalEdgePaper.lean:16` (`profileStress_lower_bound` = (A.51) lower) | **EXACT** | `δ ∈ (0, 5/2]` is exactly the paper's `.5 ≤ y < 3`; `T₀ = (edge 4 δ / δ³) • (angularFactor, δ⁶·axialFactor)` is (A.48)–(A.50) with the same constants `e^{−4/δ²}`, `δ^{−3}`, `δ^{3}`; `profile_cone_margin` gives `2 + h < a ≤ 2 + 2h` (= (A.56)) and the explicit uniform gap `3/2 ≤ 2 − (a−2)(T_z/T_θ)²` **including the closed endpoint δ = 0**. |
| B.1 | Lemma | p145 | weights `NavierStokes/AxisWeightEstimates.lean:28` (`weight`); space `NavierStokes/AxisCoefficientSpace.lean`; operators `NavierStokes/AxisOperators.lean:326`,`:330` (`norm_product_le ≤ 64`), `:380`,`:384`; identities `NavierStokes/AxisEvaluationAlgebra.lean:135` (`regularInverse_equation` = (B.5)), `:167`,`:176`,`:184`,`:191`, `:336` (`inverseMixed_equation` = (B.6)) | **EXACT** | `weight ε n m = (1/20)^n ε^{−m} m! C(n+m,m) / ((n+1)²(m+1)²)` is `a_{αβ}` of (B.4) character-for-character (`ε = ρ`); all six boundedness claims and the mixed estimate (B.6) present, with explicit constants. |
| B.2 | Prop | p146 | `NavierStokes/AxisContraction.lean:753` (`natural_axis_profiles`), `:731` (`coefficient_fixedPoint`), `:587` (`uniform_natural_fixedPoint`), `:536`; comparison series `NavierStokes/AxisSeries.lean:174` (`profile`), `:302` (`profile_gt_quarter`), `:347` (`bessel_one_le_one`), `NavierStokes/AxisProfile.lean:48` (`profileCoeff`); g-bound on the complex neighborhood `NavierStokes/AnalyticCoefficientBounds.lean:255`,`:260`,`:315`; analyticity `NavierStokes/AxisJointAnalytic.lean:101`, `NavierStokes/NaturalAxisJointAnalytic.lean:87`,`:126` | **EXACT (one numeric constant weaker)** | quantifier order `∃Λ₀ ∀Λ≥Λ₀ ∃C₀(Λ) ∀C≥C₀` is reproduced exactly (`Λ₀` is chosen before `a = φ*/C`); `x₀ = (S 1, −½ J₁(Z*/L))` is `(f₀(Yχ), −YZ*/(2L))`; (B.13) is the `Bρ`-norm bound `‖x − x₀‖ ≤ B/(2Λ)`, which is *stronger* than the stated sup-of-fixed-jets form. **Only numeric difference:** Lean proves `f₀ > 1/4` on `[0,4.1]` where the paper claims `≥ .265`. |
| B.3 | Prop | p148 | `NavierStokes/NaturalExitBounds.lean:130` (`Estimates`), `:155` (`exists_exit`), `:230` (`ideal_prefix_exit`) | **LEAN STRONGER** | `source_lower : (19/20)·L·Λ·χ + 5/2 < S_q` is (B.17) verbatim (.95 / 2.5); `phi_lower` gives the explicit `c₀ = 1/8`; `p1_lower/p1_positive_upper` are (B.18); `ns_error` is the `O(Λ⁻¹)`; `cone_margin : 2 + 1/4 < coneSize` at `X = 4/Λ` is (B.19) with an explicit margin; plus all fixed parameter jets bounded by a constant chosen before Λ and C. |
| B.4 | Lemma | p150 | `NavierStokes/ReferenceBounds.lean:1004` (`ReferenceBoundsOnHold`), `:1180` (`exists_reference_bounds`); C^k half `NavierStokes/ReferenceUniformStocks.lean:414` (`uniform_reference_quantities`); `p1 > 3` on [100,110] `NavierStokes/AppendixJoiningResults.lean:67` (`reference_first_gt_three`) | **EXACT** | `(47/50)·L·Λ·χ + 12/5 < S_q` = `.94LΛχ + 2.4`; `logSlope ≤ 1` = `l_r ≤ 1`; `9/4 < coneSize` = `v_r > 2 + c` with `c = 1/4`; `p1 > 3` on `X ∈ [100,110] = [X_b, X_i]`; the four `Uniform k` families are `CE_r`, its reciprocal, `p_{1,r}`, `n_{s,r}` with the bound quantified **before** `C` and the cutoff width. |
| B.5 | Prop | p151 | `NavierStokes/ActivationContinuation.lean:1925` (`ContinuationWitness`), `:1945` (`exists_activation_continuation`); flat factorization `NavierStokes/ActivationCone.lean:908` (`natural_activation_direction`), `:489` (`exists_actual_stress_direction`); first-collar cone `NavierStokes/ActivationCone.lean:838` (`natural_initial_activation`) | **EXACT** | continuation to `X = 110 = X_i` with `relaxed` on `[startRadius,110]` and `2 < p1` on `[holdRadius,110]`; `T₀ = activation(1,κ,u)·D(…)` with `D` smooth and `ε ≤ D.1` at `u = 0` is exactly `T₀ = e^a B₀` with `e^a` flat at `X₀` and `B₀ ≠ 0` there; parameter order Λ → C → small cutoff/activation/ramp widths matches the paper. `a = .8`, `D_X U = 0` at `X_i` sit in `RampParameters`/`ShapeTransition`, which I did not read. |
| B.6 | Cor | p153 | `NavierStokes/ActivationHolomorphic.lean:1108` (`exists_initialTube`), `:1240` (`InitialTube.natural_all_radial_jets`), `:1250` (`…reference_all_radial_jets`), `:1227` (`natural_regular`), `:1260`; `NavierStokes/AxisHolomorphic.lean:539` (`exists_common_holomorphic_extension`); `NavierStokes/AxisHolomorphicJoint.lean:202` | **EXACT** | the "one complex neighborhood for *every* fixed radial derivative" clause is literally the `all_radial_jets` form (one `InitialTube` serving all radial jets), which is the strong reading. |
| B.7 | Lemma | p154 | `NavierStokes/ReferenceEndpointRate.lean:275` (`exists_entrance_envelope`), `:226` (`exists_endpointLog_bound`), `:156` (`exists_linear_Ck_constants`), `:293`,`:299` (identification with the fields at `X_i = 110`) | **EXACT** | `∃Cnat, ∀Λ, ∃B, Cjoin, ∀q(=C,δ), ∀T,κ,w₁,w₂` reproduces (B.32)'s exact dependence chain: `Cnat_k` independent of Λ and C, `B_k`/`Cjoin_k(Λ)` may depend on Λ but not on C or the transition widths. |
| B.8 | Prop | p155 | `NavierStokes/NominalProfile.lean:2536` (`five_moments`), `:2557` (`seed_agreement`), `:2564` (`heat_agreement`), `:2576`,`:2589`,`:2594`,`:2609`,`:2616`; solver input `NavierStokes/MatchingDebtBounds.lean:578` (`MatchingBounds`), `:652`,`:753`,`:805`,`:853`,`:887`,`:928`; five-row solve `FiveProfileMoments`/`FiveRowRank`; cone `NavierStokes/MatchingConeBounds.lean:852`,`:976` | **EXACT** *(revised in the addendum)* | all five moments vanish **exactly and pointwise in η**; "agree exactly with the reference" is a field **identity** on each side of the join (`seed_agreement` below `Xi`, `heat_agreement` past `heatJoin`); `separation < exp(-8)` is the paper's `x_sep < e^{−8}`. Smallness (`MatchingBounds`) is the solver's input, not a substitute for the conclusion. |
| B.9 | Remark | p156 | (no Lean counterpart expected) | **NO COUNTERPART — routed around** | B.9 is a *Remark* fixing the order of the finitely many η-derivative orders. Lean makes the same point structurally by quantifying the derivative order `N`/`k` before the parameters in `exists_entrance_envelope`, `exists_nominal_witness (… N …)`, `uniform_reference_quantities (k)`. |
| B.10 | Cor | p157 | `NavierStokes/NominalProfile.lean:2481` (`Witness`), `:2511` (`exists_parameter_interval`), `:2523` (`fields_smooth`), `:2530` (`E_positive`), `:2536`, `:2543`, `:2661`; inhabited by `NavierStokes/MatchingDebtBounds.lean:928`; consumed by `NavierStokes/ConstructedSlowBase.lean:932` | **EXACT** *(revised in the addendum)* | every clause has a counterpart; `exists_parameter_interval` gives **one** common open η-interval `(-a,a)`, `1 < a < 3/2`, valid at **every** nonnegative radius — the strong, radius-uniform reading of "analytic in η on one complex neighborhood". |

---

## 2. Per-statement notes (non-EXACT rows and rows with caveats)

### 2.1 Lemma 5.1 — **LEAN STRONGER**

Paper (p47): *"There exists an interval 0 ≤ ξ ≤ a … on which every positive order has a unique
solution … The profiles are smooth in X and, for each fixed radial derivative, holomorphic on a
neighborhood of [−1,1] in the parameter η. **That neighborhood and its bounds may depend on the
order and the radial derivative; a does not.**"*

Lean (`SlowRecursion.lean:1256`):

```
structure LocalHierarchy (R : ℝ) (U : Set ℂ) (h C : ℝ)
    (base : Fin 5 → SimilarityProfile.InnerProfile) where
  coefficients : ℕ → Coefficient R U
  zero_axis : ∀ n, 0 < n → ∀ i : Fin 5, ∀ z ∈ U, coefficients n i (0, z) = 0
  equations : ∀ n, 0 < n → ∀ X ∈ Ioo (0 : ℝ) (R ^ 2), ∀ eta : ℝ, (eta : ℂ) ∈ U →
    OrderEquations h C coefficients n (X, eta)
  …
```

`Coefficient R U = Fin 5 → AxisFunction R U`, and membership in `AxisFunction R U` requires
(`:23`) `ContDiffOn ℝ ∞ F (Ioo (-R) R ×ˢ U)` **and** `∀ r, DifferentiableOn ℂ (fun z => F (r, z)) U`.
So a **single** `U` and a **single** `R` serve all orders and all radial derivatives — strictly
stronger than the paper's hedged form. `equations_on_window` (`:1298`) makes the point explicitly:
*"Any fixed real parameter window contained in the input neighborhood is retained at every slow
order; the recursion consumes no further strip width."*

Uniqueness is also stronger. Paper: *"Uniqueness holds among solutions whose profiles extend
holomorphically in η … with bounds uniform for 0 ≤ ξ ≤ a."* Lean
(`PositiveAxisDifferential.lean:257`) proves uniqueness against any `IsDifferentialSolution`
(`:250`): jointly continuous, holomorphic parameter slices, zero axis data, genuine radial
derivative — **no** uniform-bound hypothesis and no integral-equation hypothesis. The docstring
at `:208` says the same, and here the statement backs it.

Supply check: `ActualSlowAxis.lean:287` builds `hierarchy` from `buildLocalHierarchy` with a real
base (`base E hT hδ hδT κ hP0 C …`) read off the constructed leading profile, and
`ActualSlowAxis.lean:299`–`:302` identify `A.coefficients 0 i` with `P.f, P.U, P.Ubar − P.U,
P.pressure`. So this is not an unconstructed predicate.

**What I could not close.** The paper's Lemma 5.1 also asserts *where* the interval sits:
"extending from the axis into the inner collar of Theorem 4.6(i), **where the stress cone
inequalities hold with a uniform positive margin**". `LocalHierarchy` carries no cone data; that
placement is handled elsewhere (`ReservedPatches.lean`, `ActivationCone.lean`, the `Scheme`
radii `a < b ≤ B`). I did not verify that the radius used to instantiate `LocalHierarchy` is
proved to lie inside the margin-positive collar.

### 2.2 Lemma 5.2 — **EXACT**, with (5.13) only partly verified

The five moment rows are literally the paper's. `PositiveOrderMoments.lean:77`:

```
noncomputable def rowDensity (n : ℕ) (u e : History) (omega : Profile) (R : ℝ) : Debt :=
  ![R * u n R, R ^ 2 * e n R, pressureGradient n e omega R,
    R ^ 2 * cauchy n u e R,
    R * cauchy n u u R - R ^ 2 / 2 * pressureGradient n e omega R]
```

compared with (5.10)–(5.11): `∫R U_n`, `∫R²E_n`, `∫∂_RΠ_n`, `∫R²Σ_{i+j=n}U_iE_j`,
`∫(RΣU_iU_j − ½R²∂_RΠ_n)`. Identical, row for row.

"There are radii `X_a < X_− < X_+ < X_b`, **independent of n**" is structural in Lean: `a`, `b`,
`B` are *fields of `Scheme`* (`GlobalSlowProfiles.lean:735`–`:740`), fixed before the recursion
`recursionStep` (`:884`) runs, and `Admissible s n` (`:758`) states `inner_axial/inner_phi` on
`|R| ≤ s.a`, `outer_axial/outer_phi` on `s.b ≤ R`, and `Exterior s.B` for all four components —
with the same `a, b, B` at every `n`. `exists_step` (`:799`) returns `StepProperties`, whose third
conjunct is `moments n … = 0` (all five rows) for every `eta ∈ S`.

**Unverified:** (5.13), `|∂^I T_n(X,η)| ≤ C_{n,I} ζ(X) δ(X)^{−N_{n,I}}` with the refinement
"for `n ≥ 2` one may take `N_{n,I} = 0`". The matching Lean shape exists —
`BaseResidual.PolynomialEdgeJets` (`:1640`) is exactly `∀m ∃C ∃N ∀w∈W, ‖∂^m f‖ ≤ C ζ(w) δ(w)^{−N}`,
`ConstructedSlowBase.firstStress_edgeJets` (`:468`) supplies it for the *order-1* stress via
`SlowFirstOrderEdge.stressX`, and `BaseResidual.HigherInteriorSupport` (`:2638`) gives orders `≥ 2`
compact support strictly inside the annulus (which is how `N = 0` is realized). I read the
definitions but did not trace the per-order estimate back to `SlowStressSupport`.

### 2.3 Proposition 5.3 — **LEAN WEAKER (by one slow order; not load-bearing)**

Paper (5.25), p55: `|F_slow(U^[N])|_m ≤ C_{N,m} q^{2h(N+1) − K_m}`, `K_m` independent of `N`.

Lean (`BaseResidual.lean:1439`):

```
theorem truncationResidual_rate … (N : ℕ) … (M : ℕ) :
    FiniteJetRate l (fun z => (cartesianChart h z).1)
      (fun z => truncationResidual N h C f z.1 z.2) M (2 * (N : ℝ) * h - 2 - M)
```

with `FiniteJetRate l q f M r := ∃ C ≥ 0, ∀ᶠ x in l, ∀ m ≤ M, ‖iteratedFDeriv ℝ m f x‖ ≤ C * (q x)^r`
(`DiagonalResidual.lean:37`).

So Lean's exponent is `2Nh − 2 − m`, the paper's is `2h(N+1) − K_m`. The essential quantifier
claim — that the loss `K_m` is independent of `N` — is reproduced exactly (`−2 − M` contains no
`N`). Lean is short by exactly `2h`, i.e. it proves the estimate at truncation index `N` that the
paper proves at index `N−1`. Since `N` is universally quantified and the consumer
(`ConstructedSlowBase.error_allJetsFlat`) takes `N → ∞`, this is not load-bearing.

**On the "compact profile range" wording.** The paper states (5.25) on `0 ≤ X ≤ X_max`,
`−1 ≤ η ≤ 1`. Lean's `truncationResidual_rate` requires `PhysicalApproach l h lo hi` with
`hlo : 0 < lo`, i.e. it **excludes** a neighborhood of the axis. That looked like a gap, but it is
not: the axis case is a separate theorem, `BaseResidual.baseResidual_jetRate_axis` (`:2514`) and
`baseResidual_allJetsFlat_axis` (`:2608`), which take `PhysicalApproach l h 0 hi` (`lo = 0`) with
the extra input `StressZeroCore d r` — the stress vanishing in the core. Both regimes are covered.

**On the filter formulation.** `PhysicalApproach l h lo hi` (`BaseResidual.lean:350`) asks for a
compact carrier eventually containing the filter, `z.1 < 1` eventually, the radial coordinate in
`Icc lo hi` eventually, and `q → 0`. Quantifying over *all* such filters and reading off the
neighborhood filter of the `q = 0` end of a fixed compact set recovers the paper's
"uniformly on the profile rectangle … as `q ↓ 0`". I consider this equivalent, not weaker.

### 2.4 Proposition B.2 — **EXACT**, one numeric constant weaker

Paper (B.11), p146: `f₀(z) ≥ 305719/1152000 > .265` on `[0, 4.1]`.
Lean (`AxisSeries.lean:302`): `profile_gt_quarter : 1 / 4 < profile χ Y` for `0 ≤ χ ≤ 1`,
`0 ≤ Y ≤ 41/10`.

`1/4 < .265`, so Lean proves strictly less. The role of the bound in the paper's proof is only
"`Φ > 0` for large Λ, hence `ϕ > 0`, hence division by `ϕ` in (B.15) is valid" — positivity with
a fixed margin. `1/4` serves that role identically. Not load-bearing; recorded for completeness.

The rest of B.2 is exact or stronger. In particular the delicate quantifier order is reproduced:
`natural_axis_profiles` (`AxisContraction.lean:753`) returns `∃ Λ₀ > 0, ∀ Λ ≥ Λ₀, ∀ a, ‖a‖ ≤ M → ∃ x …`,
where `a = φ*/C`; `Λ₀` does **not** depend on `a`, matching "there are `Λ₀` and, for each `Λ ≥ Λ₀`,
an amplitude threshold `C₀(Λ)`". The paper's own emphasis — *"It is essential here that the bound
on `g` holds on a complex neighborhood, since `ϕ*` itself can grow exponentially with Λ"* — is the
Lean file `AnalyticCoefficientBounds.lean` (`normalizedExp_unitHolomorphic`, `:260`;
`uniform_normalizedExp_axisData`, `:315`), which is exactly that step.

Analyticity: `natural_axis_profiles` itself concludes only `ContDiffOn ℝ ∞ … (strip I 20)`, but
joint **real analyticity** is proved separately and for the same object:
`AxisJointAnalytic.profile_analyticOnNhd` (`:101`) and
`NaturalAxisJointAnalytic.CoefficientProfile.natural_analytic` (`:87`) /
`exists_common_joint_analytic_profiles` (`:126`). So the paper's "analytic in Y and in η on a
common neighborhood" is met.

### 2.5 A.7, A.8, B.8, B.10 — **UNRESOLVED**

For each of these I established the file-level mapping and confirmed the relevant Lean object is
*constructed* rather than assumed, but ran out of budget before comparing clause by clause.
Specifically:

- **A.7**: `ExtendedHeatedOutgoing.Witness F controls.radius heatBound` is a field of
  `NominalProfile.Witness` (`NominalProfile.lean:2487`), and `NominalProfile.Witness F` is
  inhabited by `MatchingDebtBounds.nominal_witness_exists` (`:928`). The clauses I did not check
  are "preserves `M, J, S(∞), C_p(∞)` and `∫₀^∞(H − H_pow)dX` **pointwise on [−1,1]**" and
  "the original axis pressure datum … unchanged".
- **A.8**: `TerminalPressure.axialBackwardStress` (`:1049`) is the from-`r`-to-∞ representation
  (A.46); `axialBackwardStress_divergence` (`:1477`) is the identity it satisfies. The clause
  "the leading tangential stresses vanish for `X ≥ X_b`" I did not locate.
- **B.8/B.10**: `MatchingDebtBounds.exists_ordered_matching_continuation` (`:753`),
  `exists_ordered_assembled_profile` (`:805`), `exists_nominal_witness` (`:887`) are the chain.
  The clause "agree **exactly** with … the reference inner profile (A.7)" at `log x = −5` I did
  not verify; `NominalProfile.Witness.separated : controls.separation ≤ Real.exp (-8)` (`:2488`)
  is the corresponding numeric constraint and is consistent with the paper's `x_sep < e^{−8}`.

---

## 3. Findings worth an expert

> **Superseded in part.** Findings 1 and 2 below were closed on a second pass and are withdrawn; see the Addendum at the end for the revised ranked list.

Ranked. **There are no cases in this slice where Lean proves a materially weaker statement than
a load-bearing paper claim, and no outright gaps that I could establish.** What follows is the
honest residue: two items an expert could close cheaply, and three "unresolved" items that are
the real risk surface because I could not read them, not because I found anything wrong.

1. **(Unresolved, highest value) A.8 / B.8 / B.10 — the three exact-matching claims.**
   These are the statements that say the inner and outer halves of the leading profile *agree
   exactly* (five radial moment functions, pressure datum, `Q_s`, `N_s`) and that the stress
   therefore vanishes outside the annulus. They are the load-bearing junction between Appendix A
   and Appendix B, and they are the only statements in my slice where I could not compare clauses.
   The Lean objects exist and are constructed (`NominalProfile.Witness`,
   `MatchingDebtBounds.nominal_witness_exists`, `TerminalPressure.axialBackwardStress`), so a
   reviewer should read `NavierStokes/MatchingDebtBounds.lean:753–930`,
   `NavierStokes/NominalProfile.lean:2481–2679` and `NavierStokes/LeadingStress.lean` against
   p140–141 and p155–157. Suggested concrete question: does any Lean statement assert the
   *pointwise-in-η* equality of all five normalized moment functions at `log x = −5`, or only
   smallness of the five-row debt plus a repair?

2. **(Cheap to close) Lemma 5.1's geometric placement clause.**
   Lean's `LocalHierarchy` is stronger than the paper on every analytic count, but it says nothing
   about *where* the radius `core` sits. The paper's Lemma 5.1 asserts the inner interval
   "extend[s] from the axis into the inner collar of Theorem 4.6(i), where the stress cone
   inequalities hold with a uniform positive margin", and Lemma 5.2 then chooses
   `X_− < X_keep < X_cut < a² < inf I_pos` relative to that collar. In Lean the corresponding
   radii are fields of `GlobalSlowProfiles.Scheme` (`:735`–`:740`) and of `ReservedPatches`.
   Question for an expert: is the radius used in `ActualSlowAxis.hierarchy` (`:287`) proved to lie
   inside the margin-positive collar, or is the collar relation only imposed at the `Scheme` level
   (`base_axial_patch`, `base_angular_patch`, `GlobalSlowProfiles.lean:747–749`) where it is a
   *hypothesis* of the structure rather than a theorem about the constructed base? If the latter,
   check that `nominalScheme` (`AssembledSlowBase.lean:1117`) discharges it from the real profile.

3. **(Unresolved) Lemma 5.2's weighted stress bound (5.13).**
   `BaseResidual.PolynomialEdgeJets` has exactly the right shape and is supplied for order 1
   (`ConstructedSlowBase.firstStress_edgeJets`) and, via `HigherInteriorSupport`, for orders `≥ 2`.
   But the paper's (5.13) is a bound on `T_n` for **each** `n` with constants `C_{n,I}, N_{n,I}`,
   and what reaches the summed level (`WeightedStressBound`, `ConstructedSlowBase.lean:438`) is a
   bound on the *normalized tensor minus the order-0 stress pair*, i.e. a single aggregated
   statement. An expert should confirm these are the same content and not an aggregation that
   quietly drops a per-order claim.

4. **(Benign, record only) Proposition 5.3's exponent is one slow order short.**
   `2Nh − 2 − m` vs `2h(N+1) − K_m`. See §2.3. Non-load-bearing because `N` is free.

5. **(Benign, record only) `f₀ ≥ .265` vs Lean's `f₀ > 1/4`.**
   See §2.4. Non-load-bearing; only positivity with a fixed margin is used.

Two positive findings worth stating, since the brief asked whether Lean might be *weaker*:

- **A.1, A.2, A.9, A.6 and B.3 are all formalized at least as strongly as stated**, and in several
  cases with explicit constants where the paper writes `C` or `c` (`A.6`'s `(A.36)` constant is
  `2(1+h₀)`; `B.3`'s `c₀` is `1/8`; `B.4`'s `c` is `1/4`; `A.10`'s cone gap is `3/2`). A formalization
  that had quietly weakened these would show up here as an existential where the paper has a number;
  it does not.
- **A.10's cone is proved on the paper's full interval**, not only on a collar. The collar-only
  version (`TerminalEdgeFactor.profile_uniform_cone`, `:1467`) exists and is the obvious place a
  weakening would hide, but `TerminalCone.profile_full_true_cone` (`:452`) covers `0 < δ ≤ 5/2`,
  which is exactly `.5 ≤ y < 3`, and `TerminalCone.profile_cone_margin` (`:398`) covers the closed
  interval `0 ≤ δ ≤ 5/2` including the endpoint the paper reaches only "through this extension".

---

## 4. What I did not check

- **A.7, A.8, B.8, B.10 at clause level** (see §2.5 and finding 1). I read the paper text, located
  the Lean files, and confirmed the relevant witnesses are constructed, nothing more.
- **A.4's cone clauses.** `OutgoingProfile.Specification` (`:557`) carries the smoothness, positivity,
  moment and ideal-prefix content of A.4 exactly, but carries **no cone field**. A.4's second half
  ("satisfies the admissible stress cone throughout the intermediate power-law interval, axial pulse,
  profile interpolation, and exterior transition … strict relaxed cone from `x = x_−`") must live in
  `OutgoingCone.lean`, `OutgoingEntranceCone.lean`, `OutgoingNegativeSlopeCone.lean`, `PulseCone.lean`,
  `TailCone.lean`, `ProfileSpectralCone.lean`, `NominalConeAssembly.lean`, `TrueConeLoop(Paper).lean`
  — all of which exist and which `ConstructedSlowBase.exists_actual_base` consumes through
  `TrueConeLoop.InTrueCone` — but I did not read them.
- **B.5's endpoint numerics** `a = .8`, `D_X U = 0` at `X_i`. `ContinuationWitness` gives
  `2 < p1` on `[holdRadius, 110]` but I did not find the `a = .8` / `D_X U = 0` statements; they
  should be in `ShapeTransition.lean` or `ActivationContinuation.RampParameters`.
- **§5's constants (5.17)** `max_{k+ℓ≤m} sup |∂^k_X ∂^ℓ_η P_n| ≤ C_{n,m}`. Present in spirit
  (`GlobalSlowProfiles.profiles_compactSupport` + smoothness on a compact box) but not located as
  a statement.
- **Whether `autoImplicit` has silently generalized any statement in my slice.** The prior audit
  (A4 in `nse-deep/FINDINGS.md`) records that the `NavierStokes` library builds with
  `autoImplicit := true`. I read statements as written; a mistyped identifier bound as a fresh
  implicit would make a statement *harder*, not easier, but would also make my content matching
  wrong. I did not re-elaborate anything with `-DautoImplicit=false`.
- **Proofs.** By instruction, no proof was audited for correctness, and no kernel-trust question
  was re-derived.
- **§5.4's Lemma statement text** is truncated in the paper dump at (5.34); I matched it on the
  visible content (`a_{j+1} ≥ 2a_j`, `a_1^{-1} < q_0`, cutoff `χ` equal to 1 on [0,1/2] and 0 on
  [1,∞)) against `AdmissibleScales`/`SlowBorelBase` without reading the surrounding prose on p57–58.

---

## 5. Draft → published numbering correspondences established for this slice

The Lean cites a candidate manuscript whose numbering differs from the published PDF. Established
by mathematical content:

| Lean docstring citation / label | published statement | evidence |
|---|---|---|
| draft **"Proposition 5.1"** (`AxisProfile.lean:14,46`, `AxisSeries.lean:10,300`) | **Proposition B.2** (p146) | `profileCoeff χ n = (−χ/2)^n/(n!(n+1)!)` is the paper's `f₀` coefficient verbatim; `profile_gt_quarter` is stated on `Y ≤ 41/10 = 4.1`, B.2's interval; `leadingAxial Z L Y = −YZ/(2L)` is B.2's `u₀`. |
| draft **"Lemma 5.2"** (`ReferenceBounds.lean:1176`) | **Lemma B.4** (p150) | `ReferenceBoundsOnHold` fields are `.94LΛχ + 2.4`, `l_r ≤ 1`, `v_r > 2 + 1/4`, `p1 > 3`, i.e. (B.23) line for line. |
| draft "Lemma 4.7"-shaped exponential-sum material | **Lemma A.1** (p126) | `PowerMomentMatrix`/`ExponentialMomentMatrix`: distinct real exponents, nonneg nonzero bumps on ordered disjoint compact intervals, invertible moment matrix, plus the logarithmic/exponential variant A.1 states. |
| label `` `axis:exit` `` (`NaturalExitBounds.lean:153`) | **Proposition B.3** (p148) | `source_lower` is (B.17); `p1_lower`/`p1_positive_upper`/`ns_error` are (B.18). |
| label `` `axis:model-series` ``, `` `axis:model-positive` `` (`AxisModelBounds.lean`) | **Proposition B.2 / B.3** support | same `f₀`/`Φ` material. |
| label `` `join:reference` `` (`ReferenceUniformStocks.lean:413`) | **Lemma B.4**, second half (p150) | "the parameter norms of `CE_r`, its reciprocal, `p_{1,r}`, and `n_{s,r}` on `[X₀,X_i]`" ↔ the four `Uniform k` families. |
| label `` `join:scale-envelope` `` (`ReferenceEndpointRate.lean:273`) | **Lemma B.7**, (B.32) (p154) | `‖ℓ_i‖_{C^k} ≤ B_k` and `‖G_i − U*‖_{C^k} ≤ C^nat_k/Λ + C^join_k(Λ)(t₁+κ₀+ω_fin)`. |
| label `` `heat:exterior` `` (`AppendixHeatResults.lean:3`) | **Lemma A.6** (p138) | the gamma-integral heat factor `H` and its endpoint jets. |
| label `` `heat:small-argument` `` (`AppendixHeatResults.lean:150`) | **(A.36)** inside Lemma A.6 | `|H(Z)−1| + |ZH′(Z)| ≤ C_h Z`, uniform for `0 < h ≤ h₀`. |
| label `` `heat:flat-primitive` `` (`FlatPrimitivePaper.lean:74`) | **Lemma A.9** (p141) | `∫₀^δ e^{−c/u²}u^{−j}b du = ½e^{−c/δ²}δ^{3−j}B(δ,η)`. |
| label `` `outgoing:moment-rank` `` | **Corollary A.3** (p128) / Lemma A.1 applied | the two weight blocks and `GoodExponent`. |
| `X_i = 110`, `X_b = 100`, `X₀ = 4/Λ` | B.3–B.5, B.7 radii | `ReferenceBoundsOnHold.at_hundred`, `AppendixJoiningResults.reference_first_gt_three` on `Icc 100 110`, `ReferenceEndpointRate.endpointU_eq_physical` at `110`, `NaturalExitBounds` on `0 < X ≤ 4.1/Λ`. |
| `Xi` in `NominalProfile` / `δ = 3 − y` in `TerminalEdgeFactor` | A.10's terminal interval | `profile_full_true_cone` on `0 < δ ≤ 5/2` ↔ `.5 ≤ y < 3`. |

Note: `Scaling.lean:14` cites draft "Proposition A.2 and Remark 8.6" and `PulseGrowth.lean:10`
cites draft "Proposition A.4"; neither corresponds to this PDF's A.2/A.4 (both are scalar
inequalities about `(1+u²)^{3/2}`-type denominators). Treat those two citations as noise.

---

# ADDENDUM (second pass) — items 1 and 2 closed

Two of the "unresolved" items from §3 were closed on a follow-up pass. Both resolve **in the
formalization's favour**: the Lean statements are the exact ones, not weaker substitutes.

## A. Item 2 — Lemma 5.1's placement clause: **PROVED, not assumed**

The chain the paper writes as `X_− < X_keep < X_cut < a² < inf I_pos` (p50) is, in Lean, the three
explicit arguments of the `Scheme` constructor:

`NavierStokes/GlobalSlowProfiles.lean:1092` (`schemeFromHierarchy`) takes
```
    (his : inner < stop) (hsrho : stop < rho ^ 2) (hsa : stop < a ^ 2 / 2)
```
and `NavierStokes/AssembledSlowBase.lean:1117` (`nominalScheme`) supplies all three with
**theorems about the actual constructed witness `W : NominalProfile.Witness F`**, not hypotheses:

| paper | Lean value | discharged by |
|---|---|---|
| `X_keep` | `nominalInner W = (4/Λ)/4` (`AssembledSlowBase.lean:1076`) | — |
| `X_cut` | `nominalStop W = (4/Λ)/2` (`:1077`) | — |
| `X_keep < X_cut` | `inner < stop` | `nominalInner_lt_stop` (`:1083`) |
| `X_cut < a²` (analytic radius) | `stop < rho^2` | `nominalStop_lt_radius` (`:1098`), via `nominalStop_lt_initial` (`:1088`) → `nominalInitial_le_collar` (`:1093`) → `ActualSlowAxis.collar_lt_square` |
| `a² < inf I_pos` | `stop < a^2/2` with `a = ReservedPatches.radialLeft F … .positive` | `nominalStop_lt_patch` (`:1102`) |

The `Scheme` fields `base_axial_patch` / `base_angular_patch` (`GlobalSlowProfiles.lean:747–749`),
which I had flagged as possibly-free hypotheses, are **also discharged from the real profile**:
`schemeFromHierarchy` fills them from `B0 : BaseData` (`:1115–1116`), and `B0` is
`nominalBaseData` (`AssembledSlowBase.lean:1000`), built by `baseDataOfProfile` out of
`W.profiles` with the proofs `nominal_positive_patch`, `nominal_axial_exterior`,
`nominal_mass_exterior` (`:1006`, `:1010`, `:1011–1015`). So nothing in this row is an
unconstructed predicate.

**But Lean makes a different placement choice than the paper, and a cleaner one.** The paper puts
`X_−` *in the inner collar of Theorem 4.6(i), where the stress cone inequalities have a uniform
positive margin*. Lean puts the whole cutoff window at `X ∈ [(4/Λ)/4, (4/Λ)/2]`, i.e. at
`Y = ΛX ∈ [1, 2]` — strictly **inside** the analytic-axis interval `0 ≤ Y ≤ 4.1` of Proposition B.2,
where the leading residual stress **vanishes identically**, rather than in the margin-positive
collar (which in Lean begins at `X = 4/Λ`, where `NaturalExitBounds.Estimates.cone_margin`
(`:143`) gives `2 + 1/4 < coneSize` and `ReferenceBounds.ReferenceBoundsOnHold.cone_margin`
(`:1015`) continues it for `X ≥ 4/Λ`). `nominalStop_lt_initial` (`:1088`) is exactly the statement
that the cutoff stops before that collar starts.

Placing the cutoff where `T₀ ≡ 0` is at least as good as placing it where `T₀` satisfies the cone
with a margin, so this is not a weakening — but it does mean **there is no Lean statement
corresponding to the words "where the stress cone inequalities hold with a uniform positive
margin" in Lemma 5.1**, because the Lean construction does not need one. `Scheme` has no cone
field at all; the cone enters only on the assembled base, via `TrueConeLoop.InTrueCone` in
`ConstructedSlowBase.exists_actual_base` (`:936–941`).

**Revised class for 5.1: LEAN STRONGER**, caveat withdrawn. The only residue is descriptive, not a
gap: Lean's inner interval is positioned by a different (stronger) criterion than the paper's.

## B. Item 1 — the A.8 / B.8 / B.10 exact-matching junction

**My question was: "does any Lean statement assert pointwise-in-η equality of all five normalized
moment functions at log x = −5, or only smallness of the five-row debt plus a repair?"**

**Answer: yes, exactly and pointwise in η.** `NavierStokes/NominalProfile.lean:2079`:

```
structure FiveMomentCertificate (U E : Field) (powerH : ℝ → ℝ) (P0 eta : ℝ) : Prop where
  …
  mass_zero      : (∫ x in Ioi 0, U (x, eta)) = 0
  transport_zero : (∫ x in Ioi 0, U (x, eta) * Real.sqrt (2 * x) * E (x, eta)) = 0
  energy_zero    : (∫ x in Ioi 0, U (x, eta) ^ 2 - E (x, eta) ^ 2 / 2) = 0
  angular_zero   : (∫ x in Ioi 0, Real.sqrt (2 * x) * E (x, eta) - powerH x) = 0
  pressure_datum : P0 = -(∫ x in Ioi 0, halfKernel E eta x)
```

These are `M(∞) = 0`, `J(∞) = 0`, `S(∞) = ∫(U² − E²/2) = 0`, `∫(H − H_pow) dX = 0` and the axis
pressure datum — A.8's hypothesis list verbatim, each an **equation**, one per `eta`, with the
matching integrability side conditions.

And it is **established for the assembled profile**, not assumed:
`NominalProfile.Witness.five_moments` (`:2536`)
```
theorem five_moments {eta : ℝ} (hη : eta ∈ HeatedOutgoing.parameterDomain) :
    FiveMomentCertificate W.U W.E (OutgoingDilation.powerH F W.controls.radius) (F.axisDatum eta) eta
```
with the fifth of A.8's hypotheses, `Π(X) = −½∫_X^∞ E(x)²/x dx`, as
`Witness.pressure_canonical` (`:2543`).

So the smallness objects I had worried about — `MatchingDebtBounds.MatchingBounds` (`:578`),
`NominalProfile.SmallDebt` — are the **input to the repair solver**, and the solver's **output** is
the exact certificate. That is precisely the paper's own logic on p155–156 (choose `X_R` so the
normalized discrepancies are small, then solve them away exactly by Lemma A.2). `MatchingBounds.separation : c.separation < Real.exp (-8)` (`:580`) is the paper's `x_sep < e^{−8}`.

The "agree exactly with … the reference outer profile" clause is likewise a **field identity**, on
each side of the join:
- `Witness.seed_agreement` (`:2557`): for `X ≤ Xi`, `W.f`, `W.U`, `W.Pi` **equal** the seed (axis) profiles;
- `Witness.heat_agreement` (`:2564`): for `X > heatJoin`, `W.U`, `W.E`, `W.Pi` **equal**
  `HeatedOutgoing.U / E / Pi` — the reference outer fields;
- `Witness.U_outgoing` (`:2589`), `mass_outgoing` (`:2594`), `moments_after` (`:2576`),
  `E_outgoing_before_patch` (`:2616`), `E_extended_after_radius` (`:2609`) for the remaining fields
  and histories.

**A.8's "stress vanishes for X ≥ X_b".** Found, and it is an identity rather than a derived
vanishing: `NavierStokes/TerminalEdgeFactor.lean:1627`
```
theorem profileStress_of_nonpos (C : ℝ) (d : TailData) (y0 : ℝ)
    {y : ℝ × ℝ} (hy : y.2 ≤ 0) : profileStress C d y0 y = 0
```
and `physicalStress_of_nonpos` (`:1631`), both by `FlatCutoff.edge_of_nonpos`
(`NavierStokes/FlatCutoff.lean:29`). The edge coordinate is `y.2 = δ = 3 − y`, so `δ ≤ 0` ⟺
`y ≥ 3` ⟺ `X ≥ X_b = e³ X_tail`, which is exactly the paper's range.

**A.8's representation (A.46) with the positive integration sign.**
`NavierStokes/TerminalStress.lean:36`
```
noncomputable def backwardStress (R : ℝ → ℝ) (r : ℝ) : ℝ := (∫ u in Ioi r, u ^ 2 * R u) / r ^ 2
```
is literally `T_θ(r) = r^{-2}∫_r^∞ r'² R_θ^{(0)}(r') dr'`, and `terminalStress_formula` (`:725`) is
(A.54)'s three-term decomposition, with `terminalStress_ge_boundary` (`:754`) giving
`K f_r ≤ T_θ` and `terminalStress_nonneg` (`:778`) giving `0 ≤ T_θ` — the paper's "all three terms
are nonnegative".

**One narrowed residue, worth an expert.** A.8's *content* is that the forward, axis-based stress
of Proposition 4.2 (`T_θ(r) = −r^{-2}∫_0^r s²R_θ ds`) **equals** the backward integral (A.46) —
that is what the zero total moments buy. In Lean the backward object is a *definition*, and the
`TerminalStress` module docstring says so: *"The backward stress is defined independently of the
separate global moment condition that identifies it with an axis-based stress primitive."* I found
that identification proved — but **at the first slow order**, not the zeroth:
`NavierStokes/FirstOrderBaseEdge.lean:248`
```
/-- The forward first-order primitive equals the backward terminal one.
The total viscosity moment is derived from the same original reset row. -/
theorem first_angular_eq_backward … :
    SlowStressSupport.stress 2 (…thetaDensity F.data.h C (asSlowProfiles s) 1) (R, eta) =
      SlowFirstOrderEdge.radialStress … eta R
```
(applied to the real data at `FirstOrderBaseEdge.lean:377`), whose proof unfolds
`TerminalStress.backwardStress` and consumes the vanishing total moment `hreset`. The **zeroth**-order
forward primitives exist (`NavierStokes/ZerothStressIdentity.lean:71,76`, `weightedTheta` /
`weightedAxial`, built from `ProfileHistories.primitive` of the sources, i.e. forward from the axis),
but I did not find a zeroth-order `forward = backward` theorem. Candidates I did not read:
`NavierStokes/TerminalCone.lean:487` (`E_eq_profileAngularVelocity`), `:566`
(`same_witness_full_cone`), `NavierStokes/LeadingStress.lean:458,499`
(`theta_transport_stress`, `axial_transport_stress`).

### Revised classes

- **A.8 — EXACT** (hypotheses and both conclusions present; one narrowed residue: the zeroth-order
  forward↔backward identification, proved at order 1, not located at order 0).
- **B.8 — EXACT** (exact pointwise-in-η moment vanishing plus field identities on both sides of the
  join; the smallness objects are the solver's input, not a substitute for the conclusion).
- **B.10 — EXACT** (`NominalProfile.Witness`, `:2481`, inhabited by
  `MatchingDebtBounds.nominal_witness_exists`, `:928`; its clauses are `five_moments` (`:2536`),
  `pressure_canonical` (`:2543`), `E_positive` (`:2530`), `fields_smooth` (`:2523`), and
  `exists_parameter_interval` (`:2511`), the last giving **one common open η-interval `(-a,a)` with
  `1 < a < 3/2` valid at every nonnegative radius** — B.10's "analytic in η on one complex
  neighborhood" clause in its strong, radius-uniform form).

### Revised ranked findings

Former findings 1 and 2 are **withdrawn**. The ranked list becomes:

1. **(Unresolved, narrowed) The zeroth-order forward↔backward stress identification for A.8.**
   Ask: is there a Lean theorem saying the order-0 axis-based stress primitive
   (`ZerothStressIdentity.weightedTheta` / `weightedAxial`) equals `TerminalStress.backwardStress`
   of the order-0 residual, derived from `FiveMomentCertificate`? The order-1 analogue exists
   (`FirstOrderBaseEdge.first_angular_eq_backward:248`) and shows the authors prove this shape when
   they need it, which is mild evidence the order-0 case is either present elsewhere or genuinely
   not needed on the headline route (the terminal cone results consume `profileStress` directly).
   Cheap to settle: grep `ZerothStressIdentity.weightedTheta` consumers and read
   `LeadingStress.lean:458,499`.
2. **(Unresolved) Lemma 5.2's weighted stress bound (5.13)** — unchanged, see §2.2 and former
   finding 3.
3. **(Benign) Prop 5.3's exponent is one slow order short** — unchanged.
4. **(Benign) `f₀ ≥ .265` vs Lean's `f₀ > 1/4`** — unchanged.
5. **(Descriptive, not a defect) Lemma 5.1's inner interval is positioned by a different criterion
   than the paper's** — Lean puts the cutoff where `T₀ ≡ 0` (Prop B.2's interval) rather than in the
   margin-positive collar. Stronger, but it means the paper's cone-margin wording has no Lean
   counterpart, and a reader matching statement to statement will not find one.
