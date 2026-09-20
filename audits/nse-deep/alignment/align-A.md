# Alignment audit A — paper §3, §4, Appendix C vs the Lean formalization

Scope: Theorem 3.1, Definitions 3.2/3.3, Lemmas/Propositions 4.1–4.11, Lemma C.1,
Propositions C.2/C.3. Read-only pass over `/home/user/openai/navierstokesandeuler`
(`NavierStokes/`, `.lake/` skipped) against
`ns-paper.txt` (text extraction of the published PDF, not committed) (page markers `<<<PAGE n>>>`).

Headline result of this slice: **I found no case where Lean proves a materially
weaker statement than the paper claims.** The dominant pattern is the opposite —
Lean's §3/§4/App-C layer is *equal or stronger* (larger domains, weaker
hypotheses, explicit constants where the paper says "there exists"). The residue
is (a) two places where Lean's *hypotheses* are stronger than the paper's in a
benign, formalization-driven way (global/open-domain smoothness where the paper
says "smooth on a closed rectangle"), (b) one place where an auditor reading only
one file would wrongly report a quantifier-order weakening that a second file
repairs, and (c) three conclusion clauses I could not locate as stated Lean
assertions inside my time budget.

---

## 1. Summary table

| # | kind | page | Lean counterpart(s) `file:line` | class | one-line how |
|---|---|---|---|---|---|
| 3.1 | Theorem | p15 | `NavierStokes/LocalPaperTheorem.lean:53` (`Properties`), `:179` (`local_theorem`); `NavierStokes/LocalPaperHeat.lean:22–74` | **LEAN STRONGER** | all four clauses present and unconditional; smoothness/jet bounds hold on `{t<1}` (whole space, across the axis) rather than only on Ω∗={τ>0,q<q∗}, and the scale-strip jet bound carries no `c' < q∗` restriction |
| 3.2 | Definition | p18 | no named definition; realized by `NavierStokes/AxisymmetricFields.lean:27` (`radialEnergy = (x₀²+x₁²)/2`), `:29` (`profilePoint`), `NavierStokes/ProfileHistories.lean:303` (`Profiles`), `NavierStokes/LeadingStress.lean:372–379` | **NO COUNTERPART — routed around** | Lean never states "regular at the axis"; instead *every* field is built as a smooth function of `(t, s=r²/2, z)`, which is (4.4)/(4.5) made structural, so the property is definitional rather than assumed |
| 3.3 | Definition | p18 | none | **NO COUNTERPART — routed around** | a prose convention (`α ≪ β`, right-to-left choice order); Lean encodes the same ordering as nested explicit existentials, e.g. `NavierStokes/OutgoingProfile.lean:640` (`∃ lam₀ C, ∀ lam < lam₀, ∀ h with 2h < lam, ∃ F …`) |
| 4.1 | Lemma | p25 | `NavierStokes/SimilarityProfile.lean:160` (`hasDerivAt_pullback_time`), `:180` (`hasDerivAt_pullback_z`), `:39–43` (`T`,`Z`); coefficient algebra `NavierStokes/CoordinateAlgebra.lean:180,184,190,200`; rates `:138–143` | **EXACT** | genuine `HasDerivAt` statements `∂ₜ(q^b f)=q^{b−1}T_b f`, `∂_z(q^b f)=q^{b−D}Z_b f` with `T_b,Z_b` literally (4.2); the six coordinate rates match term for term |
| 4.2 | Proposition | p27 | `NavierStokes/LeadingStress.lean:571` (`navierStokesResidual_tangential`); (4.13) algebra `NavierStokes/StressAlgebra.lean:316,324` | **EXACT** | the *Cartesian* NS residual's θ- and z-components plus the explicit axial-viscosity terms equal minus the `∂_r+2/r`, `∂_r+1/r` divergences of `q^{−A−1/2}T₀` |
| 4.3 | Lemma | p28 | `NavierStokes/StressAlgebra.lean:238` (`angular_integrated_lag`), `:255` (`axial_integrated_lag`); second, definitional rendering `NavierStokes/SeedHandbackJets.lean:94` (`stocks_formulas`) | **EXACT** | both displayed formulas of (4.16), coefficient by coefficient; see note §2.1 on the two renderings |
| 4.4(i) | Lemma | p28–29 | not located as a single statement; nearest: `NavierStokes/ModulatedProfileAssembly.lean:619` (`rows_outside`), `:627` (`stocks_outside`), `:641` (`shears_outside`), `:589` (`rows_before`) | **UNRESOLVED (partial)** | the exact-agreement conclusion is available in the form actually used (agreement of rows/stocks/shears outside a modulation window), not as the abstract "two profiles + equal moments at X_h" lemma |
| 4.4(ii) | Lemma | p29 | `NavierStokes/SeedHandbackJets.lean:354` (`profile_comparison_norm`), `:269` (`profile_comparison`) | **EXACT** | literally (4.17), same norm, same constant dependence (`k,h,X₀,X₁,μ,B,B₀`), correct `∃C ∀P,Q` order, and no radial derivative of a difference appears |
| 4.5 (1st) | Lemma | p31 | `NavierStokes/ConeAlgebra.lean:69` (`true_cone_iff`) | **EXACT** | `(2<P ∧ v<coneBound P J) ↔ (v<P ∧ (v−2)J² < 2(P−v)²)` under `2<v` |
| 4.5 (2nd) | Lemma | p31 | `NavierStokes/UniformCone.lean:148` (`compact_equation_eleven`), `:176` (`compact_equation_eleven_gap`); pointwise core `NavierStokes/ConeAlgebra.lean:155` (`equation_eleven_sufficient`) | **LEAN STRONGER** | the uniform-over-compact-K threshold `P_K` is proved, plus uniform normalized margins and an additive-gap version the paper does not state; see §2.2 — reading `ConeAlgebra.lean` alone is misleading |
| 4.6 | Theorem | p32–34 | no single statement; (i)–(vi) distributed: `NavierStokes/LeadingStressWeights.lean:1154` (`exists_weighted_profile`), `:1121` (`stress_lower_bound`), `:1137` (`physical_jet_bound`), `:1067` (`stress_zero_before`), `:1089` (`zeta`); `NavierStokes/ModulatedProfileAssembly.lean:1126` (`exists_modulated_profile`), `:196` (`repairPatch_before_positive`); `NavierStokes/OutgoingProfile.lean:557,640`; exterior `NavierStokes/RadialHeatProfile.lean`; **(vi)** `NavierStokes/ReservedPatches.lean:22` (`Slot`), `:29,35` (offsets), `:90,254` (disjointness), `:120,157` (containment), `:274,282` (`xAmplitude_pos`, `xAmplitude_shape`), `:333,342` (`heated_fields`, `_on_closedPatch`), `:546` (`radial_heated_fields`), `:634,645,678,689` (preservation) | **LEAN STRONGER on (iii)/(iv), EXACT on (vi)** | all six clauses appear, unconditionally and with explicit constants. (vi) closed on evidence (see §2.9): `Slot` names four disjoint log-windows, of which `.positive` = `(−14,−9)` and `.mean` = `(−8,−3)` give `sup I_pos < inf I_mean`; `heated_fields` concludes `U = 0` and `E = xAmplitude F XR η · X^{−(1/2+λ)}` with `xAmplitude F XR η = xAmplitude F XR 0/(1+η²) > 0`, i.e. (4.30) verbatim |
| 4.7 (1st) | Lemma | p34 | `NavierStokes/PowerMomentMatrix.lean:261` (`bumpMomentMatrix_det_ne_zero`), `:29,74` (`expSum`); inverse jets `NavierStokes/SmoothPowerMomentMatrix.lean:197` (`compact_inverse_jets_bound`), `:184` (`compact_inverse_jet_bound`) | **LEAN STRONGER** | invertibility proved assuming only *continuity* of the bumps (paper says smooth), arbitrary real exponents, any finite size; the "inverse and every fixed parameter derivative bounded on a smooth compact family" clause is proved with moving intervals and an arbitrary normed parameter space — but see §2.3 (open-domain hypothesis) |
| 4.7 (2nd) | Lemma | p34 | `NavierStokes/ClosedIntervalMomentRepair.lean:151` (`exists_smooth_same_branch`), `:88` (`exists_continuous_branch`); core `NavierStokes/MomentRepair.lean:206` (`exists_unique_small_correction`), `:154`, `:173`; same-branch identification `NavierStokes/MomentRepairPicard.lean`, `NavierStokes/MomentRepairPicardConvergence.lean:21` | **LEAN STRONGER** | `I = Icc (−1) 1` (`NavierStokes/ClosedIntervalCk.lean:23`); smoothness of the solution needs only `Small 0`, whereas the paper demands `8ν_j²q_j‖d‖_{C^j} ≤ 1` for `j=0,k`; the C⁰ and C^k solutions are proved to be the *same* branch (both zero-started Picard limits), which the paper asserts in one sentence of proof |
| 4.8 | Lemma | p35–36 | `NavierStokes/OutgoingProfile.lean:557` (`Specification`), `:594` (`exists_profile_for_data`), `:640` (`exists_outgoing_profile`), `:656` (`exists_fixed_lambda`); pressure datum `NavierStokes/SchedulePressure.lean:175,180,206,211,236`; heat tail `NavierStokes/HeatedOutgoing.lean:875`, `NavierStokes/RadialHeatProfile.lean` | **EXACT ((i),(ii) verified; (iii) partial)** | (i): `Uo=4η`, `Eo=P∗f(η)x^{1/10}` on `0<x≤1` (`ideal_prefix`), canonical pressure, analytic axis datum, even, `Π₀ ≤ −(5/2)P∗²f²`, `ηΠ₀'>0` for `η≠0` — all four pressure clauses proved. (ii): the four moment identities (4.28) are exactly `mass_total_zero`/`angular_total_zero`/`energy_zero`/`renormalized_zero`, and `after_pulse` gives `Uo=Mo=Jo=0` beyond the pulse. Clause (ii)'s four intervals are `ReservedPatches.Slot` with offsets `(−25,−20)`, `(−20,−15)`, `(−14,−9)`, `(−8,−3)`, and `heated_fields:333` gives `Eo = c_patch f(η) X^{−1/2−λ}`, `Uo = 0` on the three non-heat ones — exactly 4.8(ii)'s `I₁,I₃,I₄` (§2.9) |
| 4.9 | Lemma | p36 | `NavierStokes/TerminalCone.lean:398` (`profile_cone_margin`), `:184` (`profileSpeed_bounds`); edge factorization `NavierStokes/TerminalEdgeFactor.lean:876`, `:971`; lower bound `NavierStokes/TerminalEdgePaper.lean:15`; backward primitive `NavierStokes/TerminalPressure.lean:1049` (`axialBackwardStress`) | **LEAN STRONGER on the cone clause; partial on the primitives** | `2+h < v_s ≤ 2+2h` and a cone gap `≥ 3/2` (an *explicit* `κ_o`, where the paper says only `κ_o>0`), on `0 ≤ y_b ≤ 5/2` — exactly the paper's `e^{1/2}X_tail ≤ X < X_b` with `X_b=e³X_tail`, and including the closed edge `y_b=0`. (4.32) matches to the letter: `T_{0,θ}=e^{−4/y_b²}y_b^{−3}b_θ`, `T_{0,z}=e^{−4/y_b²}y_b^{3}b_z`. The angular backward primitive `T_θ(r)=r^{−2}∫_r^∞ r'²R_θ` I did not locate |
| 4.10 | Proposition | p36–38 | `NavierStokes/MatchingDebtBounds.lean:887` (`exists_nominal_witness`), `:928` (`nominal_witness_exists`), `:905` (`exists_nominal_with_small_coefficients`); `NavierStokes/NominalProfile.lean:2637`; axis data `NavierStokes/AppendixJoiningResults.lean:17,46`; analyticity `NavierStokes/AxisJointAnalytic.lean:102`, `NavierStokes/NaturalAxisCoefficients.lean` | **EXACT in substance (spot-checked)** | an inner profile matching all five cumulative moments to the reference outer pair exists unconditionally given an outer `Specification`; the printed numerical axis margins of the proof (`> 14/5`, `> 29/10`, `L ≥ 4879/5000`) are proved literally. I did not re-verify clause (ii)'s first-collar factorization (4.33) |
| 4.11 | Lemma | p38–39 | `NavierStokes/TrueConeLoop.lean:765` (`exists_compact_trueCone_family_with_margin`), `:732` (`exists_compact_trueCone_family`), `:277` (`InTrueCone`), `:283` (`HasConeMargin`), `:289` (`compact_periodic_trueCone_margins`) | **LEAN WEAKER (hypothesis only) — see §2.4** | the period-one loop with the prescribed mean, uniform cone margin, and nominal behaviour near the radial endpoints is all there and jointly C∞ on an open neighbourhood; but Lean requires the input `a, m, p₁, p₂` to be `ContDiff ℝ ∞` **globally on the ambient space**, where the paper assumes smoothness only on the closed rectangle `I × [−1,1]` with one-sided η-derivatives. Margin is stated on an equivalent-but-different 4-tuple |
| C.1 | Lemma | p158–160 | `NavierStokes/LoopVariance.lean:152` (`baseVariance`), `:842,847,850` (`solvedTilt`, `_mean`, `_variance`); `NavierStokes/TrueConeLoop.lean:22–24,196–235` (`lowSpeed`,`highSpeed`,`targetSpeed`,`seedRho`,`seedSpeed`,`seedTilt`,`seedTilt_mean`,`seedTilt_variance`,`seedTilt_nominal_of_inactive`), `:236` (`seed_cone`); reparametrisation `NavierStokes/ParametricRephase.lean` | **EXACT** | the paper's own witness, not a substitute: `baseVariance s = M_e(2s)/M_e(s)²−1` is literally the bracket of (C.4)–(C.5), `solvedTilt` is the exponential tilt `t(θ';µ)` solved for the prescribed variance (C.10), and `lowSpeed/highSpeed/targetSpeed = 2+δ/8, 2+δ/4, 2+δ/2` are literally (C.9)'s three cutoff thresholds |
| C.1 (moment layer) | Lemma | p158–160 | `NavierStokes/LoopMoments.lean:30` (`avg`), `:59` (`variance_identity`), `:73` (`energy_moment`), `:100` (`phaseDensity`), `:103,106` (`loopA`,`loopC`), `:181` (`rephased_moments`), `:155,168` (`rephased_meanA/C`), `:304` (`corrected_speed_bounds`) | **EXACT** (plus one clause with no paper counterpart) | *draft "Lemma 6.1" = published Lemma C.1.* `loopA v t = v/(1+t²)`, `loopC v t = v·t/(1+t²)` is the paper's `(a_L,−b_L) = v(1,t)/(1+t²)`; `phaseDensity a v t = a(1+t²)/v` is `dφ/dθ' = a(1+t²)/(2πv)`; `energy_moment` is `a⟨1+t²⟩ = v_s+aV = v`; `rephased_moments` is `∫₀¹a_L dφ = a`, `∫₀¹(−b_L)dφ = a t_s = −b_s`; `corrected_speed_bounds` is (C.9)'s three-regime conclusion. See §2.8 for the extra two-point-law clause |
| C.2 (analytic core) | Proposition | p161 | `NavierStokes/RadialModulation.lean:34` (`phasePoint`), `:39,42` (`modulatedE`,`modulatedU`), `:136,152` (`angular_shear_exact`,`axial_shear_exact`), `:168,188` (value bounds), `:222,241,257` (`zeroMeanPrimitive`, `exists_smooth_periodic_zeroMean_primitive`, `exists_primitive_of_prescribed_mean`), `:372,398` (`uniform_modulatedE/U_eta_jets`) | **EXACT** | *draft "Prop 6.2" = published Proposition C.2.* `modulatedE n E A X η = E X η · exp(A(X,η,n·log X)/n)` and `modulatedU n U B X η = U X η + B(X,η,n·log X)/n` are character-for-character the proof's `E_N`, `U_N`; `exists_primitive_of_prescribed_mean` is (C.11)'s zero-mean periodic antiderivatives; `uniform_modulated*_eta_jets` is the `O(N^{-1})` closeness in every fixed η-derivative; frequencies are arbitrary positive reals, so positive integers are a special case (LEAN STRONGER on that point) |
| C.2 | Proposition | p161 | `NavierStokes/ModulatedProfileJetRates.lean:347` (`exists_with_moment_repair_all_jets`), `:12` (`SmoothRepairFamily`); assembly `NavierStokes/ModulatedProfileAssembly.lean:1126`, `:619`, `:627`, `:641`, `:661` | **EXACT** | for all large integer frequencies: admissible cone throughout `[W.left, patch.right] × J`; `profileRows R = profileRows Q` for `X ≥ patch.right` (exact restoration of `m,Π,Q_s,N_s` beyond the first correction patch); `R = P` outside the patch; and for every fixed η-derivative order `q` a bound `C/n` — the paper's `O(N^{-1})`, with the constant allowed to depend on `q` exactly as the paper allows |
| C.3 | Proposition | p163 | `NavierStokes/LeadingStressWeights.lean:1154` (`exists_weighted_profile`), `:1089` (`zeta`), `:1121`, `:1137`, `:736`, `:761`, `:1067`; `NavierStokes/ActiveAnnulusWeight.lean:1186`; `NavierStokes/FlatCutoff.lean:26` | **EXACT in substance** | the weight is `radialWeight (activationTime²) (leftEdge) (rightEdge)`, i.e. (C.18) with `t₁²` at the inner edge and `4` at the outer; `|T₀| ≥ cζ`, `|∂^α T₀| ≤ Cζ/δ^N`, smooth unit direction with strict margin at both closed edges, stress zero for `X ≤ X_a` |

---

## 2. Per-statement notes (every non-EXACT row, plus two that need a caveat)

### 2.1 Lemma 4.3 — two renderings, one of them conditional in form

Paper (p28): "For the solutions of (4.9) with `C_Q = C_N = 0`,
`Q_s = −W + ((1−h)I − DηI_η − dJ_η + 2(h−D)ηJ)/(XH)`, `N_s = −WU + (D(M−ηM_η) + 4hηS − dS_η)/X + 4AηΠ − dΠ_η`."

`StressAlgebra.lean:238` (`angular_integrated_lag`) concludes

> `∫₀^X angularSource … / (X * p.H X) = -p.W X + ((1 - h) * p.I X - axialExponent h * η * p.Iη X - coordinateFactor η * p.Jη X + 2 * (h - axialExponent h) * η * p.J X) / (X * p.H X)`

with `axialExponent h = 1/2 − h = D`, `coordinateFactor η = 1 − η² = d`. Term for term
identical. Same for `axial_integrated_lag:247`.

Caveat worth recording for the final report: in this file the η-derivatives
(`Iη, Jη, Uη, Hη, Pη`) are **independent function fields** of the
`AngularMomentData`/`AxialMomentData` structures (`:128`, `:178`), constrained only by
radial-derivative compatibility (`Iη_deriv : HasDerivAt Iη (Hη x) x`, etc.), and the
theorems additionally assume `IntervalIntegrable` of the source, `X ≠ 0`, `H X ≠ 0`.
Nothing in *this* file proves those fields are the genuine η-partials. That would be a
weakening if it stood alone — it does not: `ProfileHistories.lean:303` defines
`Profiles` from just two smooth fields `f, U` and *derives* `H, M, I, J, S, W, pressure`
and the balance `W_balance:390` as theorems, and `SeedHandbackJets.lean:94`
(`stocks_formulas`) states the same two formulas over genuine
`derivWithin … J` η-derivatives of actual Lebesgue integrals. Classification stays EXACT.

### 2.2 Lemma 4.5, second assertion — the quantifier order is repaired in a second file

`ConeAlgebra.lean:153` (`equation_eleven_sufficient`) is **pointwise**:
`∀ (a,b,w) …, ∃ p₀, ∀ p > p₀, …`. The paper (p31) claims the opposite order:
"For every nonempty compact set K … *there exists* `P_K > 0` … For every `(a,b_s,w) ∈ K`
and every `p_{s,1} ≥ P_K` …", and its proof explicitly says "Thus one threshold works
throughout K, including points with `v_s = 2`."

`UniformCone.lean:148` (`compact_equation_eleven`) supplies exactly the paper's order:

> `∃ ε p₀, 0 < ε ∧ 0 ≤ p₀ ∧ (∀ x ∈ K, ε ≤ 1 - b x * w x / a x ∧ …) ∧ ∀ p, p₀ < p → ∀ x ∈ K, 2 < p * (1 - b x * w x / a x) ∧ a x * (1 + (b x / a x)^2) < coneBound (…) (…)`

and it makes no `v_s > 2` assumption, so `v_s = 2` points are included, as the paper
requires. `compact_equation_eleven_gap:176` goes further with a common additive gap `η`
in both inequalities, which the paper does not state. Lean also generalises `K ⊂ ℝ³` to a
compact subset of any topological space with `ContinuousOn` data.

**Flag for the other auditors:** anyone grading `ConeAlgebra.lean` in isolation will
report a `∀∃ / ∃∀` weakening here. It is not one.

### 2.3 Lemma 4.7, first assertion — open parameter domain

`SmoothPowerMomentMatrix.Family` (`:93`) carries `U : Set E` and every smoothness field is
`ContDiffOn ℝ ∞ … U`; `compact_inverse_jets_bound:192` takes `hU : IsOpen U` and
`K ⊆ U` compact. The paper's family is over `η ∈ [−1,1]`, a *closed* interval, with
"smooth" meaning one-sided derivatives at `η = ±1` (stated on p34 and again in
Lemma 4.4). So the Lean user must supply the data on an open neighbourhood of `[−1,1]`.
Benign — every family actually built in the repo is defined on a strip — but it is a
genuine hypothesis strengthening, i.e. the Lean lemma does not literally apply to
"smooth on `[−1,1]`" data without an extension step that is neither stated nor supplied here.
Contrast: `ClosedIntervalMomentRepair` (the *second* assertion of 4.7) does work on
`I = Icc (−1) 1` directly, via a `C^k`-on-a-closed-interval Banach space. The two halves
of one paper lemma therefore use different conventions.

### 2.4 Lemma 4.11 / Lemma C.1 — the one real hypothesis gap in this slice

Paper, Lemma 4.11 (p38): "Let `I = [X₋,X₊] ⋐ (0,∞)`, and let `a, b_s, p_s` be **smooth on
`I × [−1,1]`**, with `a > 0`. … Smoothness includes one-sided derivatives at `η = ±1`."

Lean, `TrueConeLoop.lean:765`:

> `(a m p₁ p₂ : E → ℝ) {K B : Set E} (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂) (haK : ∀ x ∈ K, 0 < a x) (hPK : ∀ x ∈ K, 2 < p₁ x + p₂ x * m x) (hrelaxed : ∀ x ∈ K, nominalSpeed (a x) (m x) < coneBound (p₁ x + p₂ x * m x) (p₂ x - p₁ x * m x)) (htrueB : ∀ x ∈ B, 2 < nominalSpeed (a x) (m x))`

`ContDiff ℝ ∞ a` is smoothness on **all of `E`**, not `ContDiffOn … K`. The paper's
hypothesis (smooth on a closed rectangle, one-sided at the η-boundary) is strictly weaker;
passing from it to Lean's requires a Whitney/Seeley extension that the Lean statement
neither assumes nor provides. Everything else matches or exceeds the paper:

* mean: `(∫ φ in 0..1, A (x,φ)) = a x` and `(∫ φ in 0..1, C (x,φ)) = a x * m x`, i.e.
  `∫₀¹(a_L, −b_L) dφ = (a, −b_s)` — ✔ (`C` is the `−b_L` slot since `a·m = a·t_s = −b_s`);
* period one in `φ` — ✔ (`Function.Periodic … 1`);
* admissible cone at every `φ` with one positive margin `ε` uniform in `x ∈ K` and `φ` — ✔;
* "near both radial endpoints the loop is independent of `φ` and equals `(a,−b_s)`" — ✔,
  as an **open** `N ⊇ B` on which `A(x,φ)=a x`, `C(x,φ)=a x·m x` for all `φ`;
* smoothness of the loop: `ContDiffOn ℝ ∞ A (U ×ˢ univ)` for an open `U ⊇ K` — stronger
  than the paper's "smooth on `I×[−1,1]×(ℝ/ℤ)`".

Second, smaller difference: the paper's margin is on `Ψ` of (4.35),
`Ψ = (a, v−2, c−v, 2(c−v)² − (v−2)j²)`. Lean's `HasConeMargin` (`:283`) is
`ε ≤ A`, `ε ≤ v−2`, `ε ≤ P_c − 2`, `ε ≤ coneBound(P_c,J_c) − v`. The two 4-tuples have the
same positivity set (by `true_cone_iff`), and on a compact set a positive margin for one
gives a positive margin for the other — the identity
`Ψ₄ = 2(coneBound − v)(P_c + J_c²/4 − v + rootTerm)` is immediate from
`ConeAlgebra.square_difference:38` — but the literal statement `Ψⱼ ≥ κ_L` of (C.2) is not
what Lean proves. Substantively equivalent; formally different.

### 2.5 Theorem 4.6 — distributed across files

There is no Lean declaration whose statement is "Theorem 4.6". The six clauses appear as:

* (i) positivity/smoothness of `F,U,Π,V₀/X` across the axis: structural
  (`ProfileHistories.Profiles`, `ModulatedProfileAssembly.positive_f:987`, `positive_E:996`);
  η-analyticity on a complex neighbourhood: `AxisJointAnalytic.lean:102`,
  `NaturalAxisCoefficients.lean:109,175`, `SchedulePressure.lean:236`. Canonical pressure
  (4.25): `OutgoingProfile.Specification.pressure_canonical:557ff`.
* (ii) exact radial balance and residual identity: `LeadingStress.lean:571`;
  `T₀ = 0` for `X ≤ X_a`: `LeadingStressWeights.lean:1067` (`stress_zero_before`).
* (iii) positive lower bounds and the unit-direction margin at the closed edges:
  `LeadingStressWeights.lean:738` (`inner_direction`), `:761` (`outer_direction`),
  `:946`, `:968`, packaged in `:1154`.
* (iv) the weight `ζ` and (4.27): `LeadingStressWeights.lean:1089` (`zeta`), `:1121`
  (`c * zeta ≤ ‖stress‖`), `:1137` (`‖D^n stress‖ ≤ C * zeta / distance^N`). Note the
  paper's `(4.27)` has `C_α ζ δ^{−m_α}`; Lean's is `C * zeta v X / distance v X ^ N`,
  the same shape with `N` depending on the order — ✔.
* (v) `M(∞)=J(∞)=S(∞)=0`, `∫(H−H_pow)=0`, and the exterior formula (4.29):
  `OutgoingProfile.lean:557` fields `mass_total_zero`, `angular_total_zero`,
  `energy_zero`, `renormalized_zero`; `RadialHeatProfile.lean` defines
  `profile a z = Γ(a)⁻¹ ∫_{(0,∞)} e^{−v} v^{a−1}(1+zv)^{1−a} dv` with `a = 1+h`, i.e.
  literally `H(Z)` of (4.29), and proves positivity, `C∞` on the closed half-line
  including `Z=0` (`profile_contDiffOn:226`), a uniform bound for every fixed derivative
  (`profile_derivative_bound:234`), the radial swirl heat equation
  (`radial_heat_equation`, `forward_radial_heat_equation`) and `K_r < 0`
  (`radialProfile_derivative_neg`).
* **(vi) — located after a follow-up; see §2.9.** `NavierStokes/ReservedPatches.lean`
  names the four slots (`Slot.modulation/heat/positive/mean`), proves them disjoint and
  correctly ordered (`.positive` before `.mean`), and proves `U = 0`,
  `E = c_patch(1+η²)^{-1}X^{-1/2-λ}` on the two reserved ones as a conclusion
  (`heated_fields:333`). My first-pass "not located" was a grep miss.

### 2.6 Theorem 3.1 — Lean's version is on a larger domain

Paper: "smooth fields on `Ω∗ = {(x,t) : τ>0, q<q∗}`". Lean's smoothness domain is
`PhysicalWaveSum.preterminal = {w | w.1 < 1}` (`PhysicalWaveSum.lean:386`) — all of space
at every `t<1`, including the axis and including `q ≥ q∗`. Clause (ii)'s Lean form
(`UniformJetsOnScaleStrips`, `LocalPaperTheorem.lean:34`) quantifies over **all** `c'`
with no `c' < q∗` side condition. Clause (iii)'s Lean form (`residual_flatness`,
`:73`) uses a **real** exponent `r ≥ 0` rather than an integer `N`. Clause (iv)
(`AngularRayGrowth`, `:42`) is literally (3.6) with `ray Xin τ = √(2·X_in·τ)·e₀`
(`BaseAngularGrowth.lean:19`), `A h = 1/2+h`, and the error `≤ C τ^{2h}`.
`LocalPaperHeat.lean` then supplies (3.5) exactly: `r^{−1−2h}H_ext(τ/r²)`, `H_ext`
smooth on `[0,∞)` with every derivative bounded, the radial swirl heat equation with the
paper's sign, `p = −∫_{(r,∞)} K(ρ)²/ρ dρ` **with its integrability**, and `A = 0`.
Classification: LEAN STRONGER.

### 2.7 Lemma 4.9 — explicit constants, one primitive not located

`TerminalCone.lean:398` proves, on `0 ≤ δ ≤ 5/2` and `η ∈ [−1,1]`:
`2 + h < profileSpeed … ≤ 2 + 2h` and `3/2 ≤ profileConeGap …`. Two things to note.

1. The paper writes the middle inequality for `a` ("`2 + h < a ≤ 2 + 2h`") while Lean
   states it for the speed `v_s`. These coincide because the same lemma asserts `b_s = 0`
   on that range, whence `v_s = a + b_s²/a = a`. Not a discrepancy.
2. `κ_o` is `3/2`, an explicit numeral, where the paper says only `κ_o > 0`. LEAN STRONGER.
3. The radial range matches exactly: `X_b = e³X_tail` and `e^{1/2}X_tail ≤ X < X_b` give
   `y_b = log(X_b/X) ∈ (0, 5/2]`; Lean's `0 ≤ δ ≤ 5/2` also covers the closed edge.
4. The backward primitives: the axial one is
   `TerminalPressure.axialBackwardStress:1049` = `(∫_{(r²/2,∞)} ∂_z(canonical pressure) ds)/r`,
   which under `ds = r dr` is the paper's `T_z(r) = r^{−1}∫_r^∞ r' R_z^{(0)}(r') dr'` — ✔
   (with integrability proved, `axialBackwardStress_bound:1067`). The **angular**
   primitive `T_θ(r) = r^{−2}∫_r^∞ r'² R_θ^{(0)}(r') dr'` I did not locate; see §3 item 4.

### 2.8 `LoopMoments`, `LoopVariance`, `RadialModulation` (late addition; draft §6 numbering)

Added after the §6–8 auditor established that the draft's §6 is published §4/Appendix-C
material. Two points beyond the table rows.

*The paper's C.1 witness is formalized, and `LoopMoments`' two-point laws are not it.*
The paper realizes a prescribed variance with the exponential-tilt family
`t(θ';µ) = t_s + d₀(e^{µp_{s,2}sinθ'}/M_e(µp_{s,2}) − 1)/p_{s,2}` and the monotonicity
argument (C.4)–(C.7). That is exactly `LoopVariance.lean` (`expNormalizer`,
`baseVariance:152 = M_e(2s)/M_e(s)² − 1`, `extendedExpTilt`, `solvedTilt:842`), built on
`exp(s·cos θ)` rather than `exp(z·sin θ')` — a rotation of the angle, immaterial — and it
is what `TrueConeLoop.seedTilt:199` actually uses. Separately, `LoopMoments.lean:198–300`
(`TwoPoint`, `symmetricPair`, `oneSidedPair`, `exists_projected_twoPoint`) proves finite
two-point realizability of any prescribed variance with the projection bound `P_c(t) > 2`
preserved. **That clause has no counterpart in the paper**; it is a supplementary
feasibility result, and nothing in the chain to Lemma 4.11 consumes it. Flagged so that
no one hunts for it in §4 or Appendix C. Class: LEAN EXTRA, harmless.

*Frequency type.* Proposition C.2 says "a sufficiently large finite **integer** `N`".
`RadialModulation` states everything for positive **real** `n` (`:18` "Frequencies are
positive real numbers; hence the results apply in particular to positive integer
frequencies"), and `ModulatedProfileJetRates.lean:347` then instantiates at `n : ℕ`.
Strictly stronger, and the integer form the paper needs is recovered.

### 2.9 Theorem 4.6(vi) — closed on evidence (`NavierStokes/ReservedPatches.lean`)

My first pass reported (vi) as not located. That was a grep miss, not an absence: the
namespace is `ReservedPatches`, and the exponent is written `X ^ (-(1 / 2 + F.data.core.lam))`,
which none of my patterns (`Ipos`, `Imean`, `cpatch`, `patchExponent`, `X ^ (-(1/2 + lam))`)
matched. All three questions answer yes.

**(a) Two disjoint patches with the paper's ordering.** `ReservedPatches.lean:22`:
`inductive Slot | modulation | heat | positive | mean`, with log-offsets relative to the
pulse entrance `(−25,−20)`, `(−20,−15)`, `(−14,−9)`, `(−8,−3)` (`:29,35`). These are
Lemma 4.8(ii)'s four intervals `I₁..I₄` (`.heat` is the one the heat compensation uses;
the file's own header says so), and `.positive`/`.mean` are Theorem 4.6(vi)'s
`I_pos`/`I_mean`. Disjointness: `offsets_separated:48`, `windows_disjoint:90`,
`closedPatches_disjoint:254`, `radial_windows_disjoint:505`. Ordering:
`rightOffset .positive = −9 < −8 = leftOffset .mean`, so `sup I_pos < inf I_mean` — the
paper's orientation, not merely disjointness. Containment: `clock_inside_wait:114` and
`window_inside_wait:120` place every window strictly inside the outer profile's shaped
wait, and `right_before_switch:157` before the heat switch — the Lean form of "both
intervals lie in `(X_a, X_v)`". (There is no theorem whose statement is literally
`I_pos, I_mean ⊆ (X_a, X_v)`; the containment is expressed in the clock coordinate.)

**(b) (4.30) as a conclusion, not a hypothesis.** `heated_fields:333`, for every slot
`s ≠ .heat` (hence for `.positive` and `.mean`) and every `η`:

> `HeatedOutgoing.U F XR (X, eta) = 0 ∧ HeatedOutgoing.E F XR c (X, eta) = xAmplitude F XR eta * X ^ (-(1 / 2 + F.data.core.lam))`

with `xAmplitude_pos:274` (`0 < xAmplitude F XR eta`) and `xAmplitude_shape:282`
(`xAmplitude F XR eta = xAmplitude F XR 0 / (1 + eta ^ 2)`). Setting
`c_patch := xAmplitude F XR 0 > 0`, independent of `X` and `η`, this is
`U = 0`, `E = c_patch (1+η²)^{-1} X^{-1/2-λ}` — (4.30) verbatim, exponent included.
`heated_fields_on_closedPatch:342` gives it on the closed sub-patch;
`radial_heated_fields:546` is the same statement in the physical radius `R` with
`radialAmplitude_pos:521`, `radialAmplitude_shape:529`.

**(c) The §5/§8 consumers discharge against it.** `.mean` (Lemma 8.7, averaged-flow
corrections): `MeanRankUpdate.lean:1391–1430` builds `reservedAngularBase`/
`reservedAxialBase` from `radialSupportLeft/Right … .mean`, `radialAmplitude`, and
`radial_heated_fields`, and proves `reserved_five_rows:1399`;
`CorrectionInitialization.lean:4335–4384` does the same. `.positive` (Lemma 5.2,
positive-order background corrections): `AssembledSlowBase.lean:848–960`
(`nominalOuterX_gt_patch:871`, `radialWindow … .positive` at `:953`) and
`ModulatedExterior.lean:330`.

**"Left unchanged by the construction."** Two mechanisms, both proved:
`ModulatedProfileAssembly.repairPatch_before_positive:196` shows the Proposition C.2
moment-repair patch (which sits in the `.modulation` slot) ends strictly *before* `I_pos`
begins; and `ReservedPatches.Supported:576`/`RadialSupported:657` with
`supported_updates_preserve_fields:634`, `finite_updates_eqOn:645`,
`radial_supported_updates_preserve_fields:678`, `radial_finite_updates_eqOn:689` show that
any finite family of updates supported in other slots leaves `U = 0` and the `E` power law
on this slot intact. `heat_increment_support:393`/`heat_increment_tsupport:412` confine the
heat correction to `.heat`.

**One honest caveat.** These are statements about `HeatedOutgoing.E/U` — the outer profile
after the heat tail — together with preservation lemmas. The transfer to the *finished*
leading profile goes through `repairPatch_before_positive:196`, the `Supported` preservation
lemmas above, and `ModulatedProfileAssembly.rows_outside:619`/`stocks_outside:627`. Each
piece is a theorem; I verified the pieces, and there is no single declaration that composes
them into "the finished profile satisfies (4.30) on `I_pos` and `I_mean`". That is a
packaging observation, not a gap.

*Instrument lesson, for the other auditors.* A "not located" verdict in this repo is cheap
to get wrong: identifiers are English compounds in namespaces that do not echo the paper's
notation (`ReservedPatches`, `Slot.positive`, `xAmplitude`), and numeric exponents are
spelled with Lean's spacing and field accessors (`-(1 / 2 + F.data.core.lam)`, not
`-1/2-λ`). Grep for the *structure* (`inductive Slot`, `namespace …Patches`) or for a
consumer, not for the paper's symbol.

---

## 3. Findings worth an expert

Ranked. Nothing here is a soundness finding; the first two are gaps in coverage that
an expert should either close or explicitly declare out of scope, the rest are
formalization-convention notes that the final report should carry so that other
auditors do not double-count them.

**~~1. Theorem 4.6(vi) — no located Lean statement of the reserved intervals.~~ CLOSED
on evidence; no expert needed.**
`NavierStokes/ReservedPatches.lean` supplies all of clause (vi): two disjoint reserved
windows with the paper's ordering `sup I_pos < inf I_mean`, `U = 0` and
`E = c_patch(1+η²)^{-1}X^{-1/2-λ}` proved as a **conclusion** (`heated_fields:333` with
`xAmplitude_pos:274`, `xAmplitude_shape:282`), and preservation under corrections supported
in the other slots. Both consumers discharge against it: `.mean` in
`MeanRankUpdate.lean:1391–1430` and `CorrectionInitialization.lean:4335–4384` (§8's
Lemma 8.7), `.positive` in `AssembledSlowBase.lean:848–960` (§5's Lemma 5.2). Full evidence
in §2.9. My original verdict was a grep miss; the residual observation is only that no
single declaration composes the pieces for the *finished* profile, which is packaging, not
a gap. **This was my rank-1 item; the slice now has no NO-COUNTERPART gap.**

**2. Lemma 4.9's angular backward primitive.**
`T_θ(r) = r^{−2}∫_r^∞ r'²R_θ^{(0)}(r')dr'` — the axial twin is proved
(`TerminalPressure.axialBackwardStress:1049`) but I did not find the angular one. The
paper derives both from the four moment identities ("The four moment identities cancel the
total residual integrals, giving the backward primitives above"), and the four identities
*are* proved (`OutgoingProfile.Specification`). So this is most likely present under a name
I did not hit rather than absent; an expert can settle it in minutes.
**Rank 2** (likely present; unresolved by me).

**3. Lemma 4.11 / C.1 requires globally smooth input data.**
`TrueConeLoop.lean:765` takes `ContDiff ℝ ∞ a` (on all of `E`) where the paper assumes
smoothness only on `I × [−1,1]` with one-sided η-derivatives. The Lean lemma is therefore
*not* directly applicable to data given only on the closed rectangle; a global extension
must be produced first, and neither the statement nor (as far as I saw) its callers state
that step. In practice the repo's data is built from globally smooth pieces, so this is
almost certainly harmless — but it is the only place in my slice where Lean's **hypothesis**
is strictly stronger than the paper's in a way that is not obviously discharged. The same
convention issue, milder, appears at `SmoothPowerMomentMatrix.Family` (`hU : IsOpen U`,
`K ⊆ U`) for Lemma 4.7's first assertion — and notably *not* at
`ClosedIntervalMomentRepair` for its second assertion, which works on `Icc (−1) 1`
directly. Worth asking why the two halves of one paper lemma use different conventions.
**Rank 3** (hypothesis strengthening, benign-looking).

**4. `ConeAlgebra.lean` in isolation reads as a quantifier-order weakening. It is not.**
Raised here defensively: `equation_eleven_sufficient:153` is `∀(a,b,w) ∃p₀`, the paper is
`∃P_K ∀(a,b,w)∈K`. `UniformCone.compact_equation_eleven:148` proves the paper's form
(and more). No action needed beyond making sure the final report does not list this as a
finding. **Rank 4** (anti-finding).

**5. Lemma 4.11's margin is on a different 4-tuple than (4.35)'s `Ψ`.**
`HasConeMargin` bounds `(a, v−2, P_c−2, coneBound−v)`; the paper bounds
`Ψ = (a, v−2, P_c−v, 2(P_c−v)²−(v−2)J_c²)`. Equivalent on a compact set — the bridge is
`ConeAlgebra.square_difference:38` plus `true_cone_iff:69` — but the literal (C.2) is not a
Lean theorem. Only matters if some downstream consumer needs `Ψ₄ ≥ κ_L` in that exact form.
**Rank 5** (cosmetic unless consumed literally).

---

## 4. What I did not check

* **Proofs.** Per instructions, I compared *statements* only; no proof was audited for
  correctness, and I did not re-derive any kernel-trust finding. I did not check whether
  `#print axioms` is clean for any declaration cited here (the prior kernel-trust pass
  covers that for the headline).
* **`autoImplicit`.** The prior audit's A4 notes the `NavierStokes` library builds with
  `autoImplicit := true`, so a mistyped identifier in an intermediate *statement* binds a
  fresh implicit instead of erroring. Every declaration I quote was read as text; I did
  **not** elaborate any of them, so I cannot rule out that a variable I read as (say) `h`
  is auto-bound rather than the intended one. For the statements in this slice that is
  most worth re-checking on `TrueConeLoop.lean`, `TerminalCone.lean` and
  `ModulatedProfileJetRates.lean`, whose statements carry many loose parameters.
* **Proposition 4.10 clause (ii)** — the first-collar factorization (4.33)
  `T₀ = e^{−t₁²/y_a²}g_a(y_a)B_a(y_a,η)` with `g_a(0)>0`, `B_a(0,η)=F(X_a,η)s(X_a,η) ≠ 0`,
  and the jet bounds `|T₀| ≥ c e^{−t₁²/y_a²}`, `|∂^α T₀| ≤ C_α e^{−t₁²/y_a²}y_a^{−N_α}`.
  I confirmed the *outer* twin in full (`TerminalEdgeFactor:876,971`,
  `TerminalEdgePaper:15`) and saw the inner one referenced
  (`LeadingStressWeights.inner_direction:738`, `zeta` built from `activationTime²`), but
  did not read the inner factorization statement itself.
* **Proposition 4.10 clause (iii)** — the explicit reference integrals (4.34)
  (`M̂₀=4ηx`, `Î₀=(5√2/8)P∗fx^{8/5}`, `Ĵ₀=4ηÎ₀`, `Ŝ₀=16η²x−(5/12)P∗²f²x^{6/5}`,
  `Ĉ_{p,0}=(5/2)P∗²f²x^{1/5}`) and the matching tolerances
  (`Q_s ≥ Q_min/2`, `.7 ≤ a ≤ .9`, `|b_s| ≤ .1/(1+w∗)`, `v_s < 1`).
* **Lemma 4.8 clause (iii)'s cone ranges** (relaxed on `[e^{−5}X_R, e^{1/2}X_tail]`,
  admissible on `[X_good, e^{1/2}X_tail]`). Clause (ii)'s four intervals are now confirmed
  (`ReservedPatches.Slot`, §2.9), and I verified the pressure clauses of (i) and all four
  moment identities of (ii); the cone-range geometry I only saw as parameters
  (`OutgoingTail.TailData`, `HeatedOutgoing`, `TerminalCompensation`).
* **Lemma 4.4(i)** as an abstract statement (two profiles agreeing beyond `X_h` with
  `∆m(X_h)=0`). The specialised form actually used is present; the general one I did not
  find.
* **Whether the leading profile that the headline `theorem_1_1` construction actually
  uses is the one my §4 citations describe.** I traced
  `R3/Theorem.lean:27 → ActualCandidate.selected_candidate_one_with_initial_rest:143 →
  ActualCandidateAssembly.selected_witness:1177` and separately confirmed that
  `LeadingStressWeights.exists_weighted_profile:1154` and
  `ModulatedProfileAssembly.exists_modulated_profile:1126` are unconditional, but I did
  not verify that the *same* profile object flows into `selected_witness`. Auditor B/C/D
  covering §5–§10 should close that link.
* I did **not** read `.lake/`, and I did not build anything.

---

## 5. Draft → published numbering established for this slice

The Lean docstrings cite a draft with a different numbering. These are the
correspondences I established **by mathematical content**, with the evidence:

| draft citation in Lean | published | evidence |
|---|---|---|
| draft **Lemma 3.3** (`StressAlgebra.lean:155,241` "the first/second integral formula in the proof of Lemma 3.3") | published **Lemma 4.3** | `angularPrimitive`/`axialPrimitive` are term-for-term the numerators of (4.16) |
| draft **equations (6)–(9)** (`StressAlgebra.lean:10`) | published **(4.9)–(4.11), (4.16)** | (6) = lag equations (4.9); (7) = stress definition (4.11); (8) = stress-free equations (4.13); (9) = the integrated identity (4.16) |
| draft **Proposition 3.2** (`LeadingStress.lean:34,38` "the coefficient of the … radial stress in Proposition 3.2"; `:564–570` docstring above `navierStokesResidual_tangential:571`, "Proposition 3.2 for the actual Cartesian Navier–Stokes residual") | published **Proposition 4.2** | the residual-as-stress-divergence statement |
| draft **Lemma 3.5** (`ConeAlgebra.lean:9,69` "the square-root criterion and quadratic equivalence in Lemma 3.5") | published **Lemma 4.5** | `true_cone_iff` is (4.21)+(v_s>2) ⟺ (4.22) |
| draft **equation (10)** (`ConeAlgebra.lean:16–17`) | published **(4.21)** (the definition of `U(P_c,J_c)` and the relaxed cone) | `coneBound` is `U(P,J)` |
| draft **equation (11)** (`ConeAlgebra.lean:11,101,153`; `UniformCone.lean:36`) | published **Lemma 4.5's second assertion** (the two displayed inequalities on `K`) | `a − b_s w > 0`, `2b_s w + b_s²/a + (a−2)w² < 2` |
| draft **Lemma 3.6** (the exponential-sum / moment-matrix lemma; `PowerMomentMatrix.lean` `expSum`, `expSum_coefficients_zero`) | published **Lemma 4.7, first assertion** | distinct real exponents, ordered disjoint bump supports, `B_ij = ∫ x^{α_i}β_j` invertible |
| draft **Lemma 3.7** (`MomentRepair.lean:151` "The quantitative hypotheses in Lemma 3.7 make the correction ball invariant") | published **Lemma 4.7, second assertion** | `Bc + Q(c,c) = d` under `8ν²q‖d‖ ≤ 1` |
| draft **Lemma 4.4** (`RadialHeatProfile.lean:9,89` "the actual gamma-normalized improper integral in Lemma 4.4"; "exactly the displayed integral in Lemma 4.4") | published **Theorem 4.6(v), equation (4.29)** — and it also serves **Lemma 4.8(iii)** | `Γ(1+h)^{-1}∫₀^∞ e^{−v}v^h(1+Zv)^{−h}dv` |
| draft **§4.4** (`RadialSchedule.lean` header "the outgoing radial schedule … equation (13)") | published **Lemma 4.8(i)–(ii)** (the ideal prefix `U_o=4η`, `E_o=P∗f x^{1/10}`, and the moment rows) | `idealAxialVelocity η = 4η`; `logShapeDerivative` is `(log f)'` for `f=(1+η²)^{-1}` |
| draft **§4.6** (`FlatCutoff.lean:25` "the one-sided Gaussian-flat edge used as a scalar model in Section 4.6") | published **Theorem 4.6(iv) / (C.18)** — the weight `ζ` | `edge c x = exp(−c/x²)`; instantiated at `c = t₁²` (inner) and `c = 4` (outer) |
| draft **§3** generally (the `Profiles`/lag/stress layer) | published **§4.1–§4.3** | — |
| draft **Lemma 6.1** (`LoopMoments.lean:11` "the averaging and rephasing identities in Lemma 6.1"; `LoopVariance.lean:11` "the integral normalizer and variance used by Lemma 6.1") | published **Lemma C.1** | `loopA/loopC = v(1,t)/(1+t²)`, `phaseDensity = a(1+t²)/v`, `baseVariance = M_e(2s)/M_e(s)²−1`, cutoff thresholds `2+δ/8, 2+δ/4, 2+δ/2` = (C.9) |
| draft **Proposition 6.2** (`RadialModulation.lean:17` "the modulation in Proposition 6.2") | published **Proposition C.2** | `modulatedE = E·exp(A(X,η,n log X)/n)`, `modulatedU = U + B(X,η,n log X)/n` — the proof's `E_N`, `U_N` verbatim |
| draft **§11** (`Lemma 11.3`, `Prop 11.4/11.7`, cited elsewhere in the Lean) | **not in my slice**; no §11 exists in the published PDF | flagged for whoever audits §5–§10 |

**The draft→published shift is not uniform, so docstring citation numbers are unreliable
everywhere in this slice too.** Confirmed by the §6–8 auditor: draft §8 became published
§6+§7, while draft §6 became published Appendix C (rows above) and draft §3 became
published §4. Map by content, never by number.

Two further notes for the final report:

* The Lean's `axialExponent h = 1/2 − h` is the paper's `D`; `velocityExponent h = 1/2 + h`
  is the paper's `A`; `coordinateFactor η = 1 − η²` is `d`; `L h η = 1 − 2hη²` is `L`.
  `NaturalAxisData.{A,D,d,L}` and `CoordinateAlgebra.{A,D,d,L}` are duplicate copies of the
  same four definitions used in different files.
* Lean's `nominalSpeed a m = a(1+m²)` is `v_s`, `m` is `t_s`, `p₁,p₂` are `p_{s,1},p_{s,2}`,
  `coneBound P J` is `U(P_c,J_c)`, and `InTrueCone` is the *admissible* stress cone
  (including `v_s > 2`), not the relaxed one.
