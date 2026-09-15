# Deep audit: `NavierStokes/TerminalEdgeFactor.lean`

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (openai/NavierStokesAndEuler @ f9e8bc5).
Read-only, source-level (no Mathlib build available; **no `lake build` was run**).
All line numbers are `TerminalEdgeFactor.lean:<line>` unless another file is named.

## Scope

* File size: **1676 lines**, **235 top-level declarations** = **62** `def`/`abbrev` + **173**
  `theorem`. Of the theorems, **47** are pure smoothness plumbing (`*_contDiff*`).
* No `sorry`, no `axiom`, no `set_option`, no `macro`/`elab`/`syntax`, no `native_decide`,
  no `decide`, no `inductive`/`structure`, no `termination_by`, no `.rec`, no `Nat.pow`
  (machine scan, see Kernel-risk section). The only earlier "hits" of `partial` in a
  repo-wide scan are substrings of `SimilarityProfile.partialS` / `partialZ`.
* **Read line-by-line: the whole file** (every declaration statement, and every proof
  body except the interiors of the 47 `*_contDiff` combinator terms, which were read
  but only checked structurally — see sampling scheme).
* Sampling scheme for the long chains: I did not sample a prefix. I enumerated the
  distinct *proof patterns* and audited at least one full instance of each, plus every
  instance of the patterns that can hide a mathematical error:
  1. `nlinarith` — **4 sites total (739, 742, 774, 1414); all four audited by hand**.
  2. change-of-variables + improper FTC (`integral_Ioi_of_hasDerivAt_of_tendsto'`):
     2 instances (222–239, 603–620) — both audited, plus their 4 consumers.
  3. `convert! … using 1` + `field_simp; ring_nf; rw; ring` re-normalisation:
     10 sites; audited 86–93, 1404–1423, 1513–1534 fully (the three that carry
     content), structurally the rest.
  4. `edge`-weight factorisation (`X = (edge 4 x / x^3) * factor`): 6 instances
     (475, 876, 971, 1027, 1080, 1256, 1595) — all audited, including the
     `x^3` vs `x^6` bookkeeping.
  5. `normalizedParam` transfer dictionary (1088–1241): all 18 lemmas audited for the
     `η^2 < 1` (strict) side condition.
  6. Compactness/uniformity (1444–1489): audited in full.
* I also re-derived the key algebra numerically-symbolically by hand (exponent
  `spatialExponent (1+h) = 1/2-(1+h) = -1/2-h`, see finding **F1**).
* Consumers: I grepped the whole repo for every exported name of this file and audited
  the call sites in `TerminalCone.lean`, `TerminalEdgePaper.lean`,
  `TerminalHistoryBridge.lean:299`, `SlowFirstOrderEdge.lean:239/303`,
  `LeadingStressWeights.lean:443`.

## What the file is for

It builds the *terminal edge* stress objects in two charts and connects them.

* **Physical chart** (`EdgeParam = ℝ × ℝ`, `p.1` a log-time, `p.2 = z`):
  `timeOf p = 1 - exp p.1` (27), `radius` (36), `carrier`/`carrierRadial` = the actual
  radial heat amplitude and its radial derivative (105, 124), `angularStress` (455) =
  `TerminalStress.terminalStress` (a backward integral), `axialStress` (687) = an
  `∫_{s>r²/2}` of the canonical pressure `∂_z`.
* **Profile chart** (`(η, x)`, `η` the *time* parameter through `t = η²`, `x` the edge
  coordinate with `x = 0` the outer edge): `profileS y0 x = exp (y0+3-x)` (745),
  `profileRadius` (746), `profileZ = 2(1-η²)/profileS` (748), `profileCarrier` (776),
  `profileAngularStress` (860), `profileAxialStress` (944), `profileSpeed` (1351),
  `profileTilt` (1319), `profileConeGap` (1437).
* **Dictionary**: `normalizedParam η = (log (1-η²), η)` (1088) and 18 lemmas
  (1090–1241) proving physical = profile **for `η^2 < 1` (strict)**.
* **Headline exports**: `profileStress_jets` (1288), `physicalStress_jets` (1607),
  `profileAngularStress_edge_jets` / `profileAxialStress_edge_jets` (1299/1308),
  `profile_uniform_cone` (1467), `profile_relative_cone` (1562),
  `profile_true_cone` (1659), `profileSpeed_eq_log_deriv` (1548).

## Per-declaration findings

Verdicts: **OK** = statement matches its name/use and I reconstructed the proof
mechanism and, where numeric, the arithmetic; **UNCLEAR** = statement fine, closure of a
tactic (`field_simp`/`ring_nf`/`convert!`/`simp only`) not machine-checkable without a
build; **SUSPICIOUS** = a real mathematical/wording concern; **WEAK** = true but much
weaker than its docstring suggests.

### 1. Chart plumbing (25–104)

| decl | line | statement (my words) | mechanism | verdict |
|---|---|---|---|---|
| `EdgeParam`, `timeOf`, `axisPoint`, `chartQ`, `chartEta`, `outerRadius`, `radius`, `chartPoint` | 25–39 | definitions; `radius = outerRadius · exp(-x/2)`, `outerRadius = sqrt(2·q·exp(y0+3))` | defs | OK |
| `timeOf_lt_one` | 41 | `1 - exp a < 1` | `linarith [exp_pos]` | OK |
| `chartQ_pos` | 51 | `0 < q` at every edge param | `q_pos` + `timeOf_lt_one` | OK |
| `outerRadius_pos`, `radius_pos` | 66, 75 | positivity of both radii | `sqrt_pos` + `mul_pos` | OK |
| `radius_square` | 86 | `radius² = 2·q·exp(y0+3-x)` | `sq_sqrt`, `exp_add`; the `exp_nat_mul` step is the only fiddly one | OK (algebra re-derived by hand) |
| `chartX`, `chart_logX` | 95, 101 | `X = exp(y0+3-x)`, `log X = y0+3-x` | `change` to `(r²/2)/q`, `field_simp` | OK |
| `carrier*`, `denominator*` | 105–155 | carrier = `physicalHeat` at the chart point; `denominator = q·L` | `rfl`-level + `contDiff` combinators | OK |
| 8 `*_contDiff` here | 45–82,111–155 | smoothness of the above | combinator terms; every division/`sqrt`/`rpow` side goal is discharged by the matching positivity lemma | OK (structural) |

### 2. Edge coordinate and the radial→edge change of variables (158–240)

| decl | line | statement | mechanism | verdict |
|---|---|---|---|---|
| `edgeCoordinate R r = -2 log(r/R)` | 158 | log edge distance | def | OK |
| `edgeCoordinate_hasDerivAt` | 160 | derivative `-2/r` | chain rule; `field_simp` | OK |
| `edgeCoordinate_nonpos` | 166 | `R ≤ r ⇒ coord ≤ 0` | `log_nonneg` | OK — this is the sign convention that makes `edge 4 x = 0` outside the collar |
| `radius_edgeCoordinate`, `edgeCoordinate_radius` | 171, 179 | the two round-trips | `exp_log`/`log_exp` with `0 < r`, `0 < R` guards present | OK |
| `integrableOn_Ioi_of_eventually_zero` | 193 | continuous on `Ioi 0` + eventually `0` ⇒ integrable on `Ioi r` | indicator of `Icc r (max r b)` + a.e. congruence | OK; hypotheses are genuinely used |
| `radialFlatDensity` | 206 | `(2/u)·integrand 4 j a (edgeCoordinate R u)` | def; `2/u` is exactly the Jacobian `|d(edge)/dr|` | OK |
| `radialFlatDensity_integral` | 222 | `∫_{Ioi r} density = FlatPrimitive.primitive c j a (edgeCoordinate R r)` | improper FTC with antiderivative `-primitive∘edgeCoordinate`, tail `→ 0` because `primitive_of_nonpos` | OK — Jacobian sign and orientation both check out |
| `chart_tau_identity`, `physical_heat_argument` | 241, 249 | `1-t = q(1-η²)`; heat argument `2(1-t)/(r²/2) = 2(1-η²)/exp(y0+3-x)` | `tau_coordinate_identity`, `field_simp` | OK — this is what pins `profileZ` (see F2) |

### 3. Taper, coefficients, the angular stress factorisation (255–531)

| decl | line | statement | mechanism | verdict |
|---|---|---|---|---|
| `logTaper d y0 y = tailShape d (y-y0)` | 255 | taper in the log-`X` variable | def | OK |
| `logTaper_deriv_at_radius` | 267 | `d/dy logTaper` at `y = log X` equals `(edge 4 u/u³)·taperSlopeFactor u`, `u = edgeCoordinate` | `physical_logX` then `tailShapeDeriv_factorization` (`TerminalStress.lean:893`) | OK — the `y0+3-u-y0 = 3-u` bookkeeping is explicit at 274 |
| `radialTaper_deriv` | 285 | radial derivative gets the extra `2/r` | `flattening_radial_hasDerivAt` | OK; `2/r` matches `radialFlatDensity` |
| `radialTaper_plateau` | 297 | taper `= 1` eventually in `r` | `tailShape_late` | OK; used only for tail-vanishing |
| `boundaryCoefficient`, `timeCoefficient`, `correctionCoefficient` | 303–312 | the three coefficient fields | defs | OK |
| `time_weight_eq_density`, `correction_eq_density` | 345, 362 | the two residual densities equal `radialFlatDensity 4 3 (coeff)` | unfold + the two `_at_radius` lemmas; **345 splits on `edgeCoordinate = 0`** and closes that branch by `simp` | OK; the `he : … = 0` branch is the `x=0` junk case and both sides are `0` there |
| `time_weight_integral`, `correction_integral` | 394, 413 | the two backward integrals equal `ParametricFlatFactor.primitive 4 3 coeff` | a.e. congruence + `radialFlatDensity_integral` + `edgeCoordinate_radius` | OK |
| `viscous_weight_integrable` | 432 | `u²·viscousResidual` integrable on `Ioi r` | smoothness at each `u>0` + plateau ⇒ eventually 0 | OK |
| `angularStress_factorization` | 475 | `angularStress = (edge 4 x / x³)·angularFactor` | `terminalStress_formula` (`TerminalStress.lean:725`), then `primitive_eq_scale_mul_factor` twice and `ring` | OK — and the **missing viscous integral is not missing**: `terminalStress_formula` converts `∫u²V` into `boundary(r) + ∫correction` by parts (`boundary_hasDerivAt`, `TerminalStress.lean:39`), with `boundary → 0` supplied by `outgoing_boundary_tendsto_zero`. I re-derived the sign: `∫_r^∞ u²V = boundary(r) + ∫corr`, and `boundary(r)/r² = K(r)·g'(r)` — matches 484–491 exactly |
| `angularFactor_zero`, `angularFactor_zero_pos` | 499, 505 | at `x=0` the factor is `2K/r·taperSlopeFactor > 0` | `zero_pow 3` kills the primitive terms; `taperSlopeFactor_zero_pos` | OK |
| `angularStress_normalized` | 525 | dividing by `exp(-4/δ²)/δ³` recovers the factor, for `δ>0` | `mul_div_cancel_left₀` with a `positivity` non-vanishing side goal | OK; `0 < δ` needed and present |

### 4. `s = r²/2` chart and the pressure/axial primitives (534–690, 980–1084)

| decl | line | statement | mechanism | verdict |
|---|---|---|---|---|
| `logCoordinate S s = edgeCoordinate S s/2` | 534 | same coordinate in `s` | def; `d/ds = -1/s` (536) | OK |
| `radialS_eq`, `radialS_logCoordinate`, `logCoordinate_radialS` | 551–572 | round-trips `s ↔ x` with `s = outerS·exp(-x)` | `exp_log`/`log_exp` under `0 < s`, `0 < outerS` | OK |
| `scalarFlatDensity`, `_integrable`, `_integral` | 588–620 | same FTC lemma with Jacobian `1/s` | as §2 | OK — `1/s` is exactly `|d(logCoordinate)/ds|` |
| `chi` (622), `chi_eq_logScale` (636) | | `χ = 2η/(q^D·L)` equals `qAxial/q` | `field_simp` with three non-vanishing facts | OK |
| `pressureCoefficient` (643) | | `carrier² · tailShape(3-x) · taperSlopeFactor x` | def | OK |
| `pressure_density_eq` | 980 | physical density `K²·f·f'/s` equals `scalarFlatDensity 4 3 pressureCoefficient` | `carrier_at_s`, `physical_logX_s`, `tailShapeDeriv_factorization` | OK — I checked `f'` is replaced by `(edge/u³)·taperSlope` and the loose `1/s` lands in the density |
| `pressureGradient_eq_primitive` | 994 | `∂_z(canonicalPressure) = χ · primitive 4 3 pressureCoefficient` | 3-step `calc`; every step is an equality of the *same* quantity (no norm swap) | UNCLEAR (statement OK; depends on `TerminalPressure.outgoingPressure_partialZ`, off-file) |
| `pressureGradient_factorization` | 1027 | `= edge 4 x · pressureFactor` | `scale_three` (923): `scale c 3 x = edge c x`, incl. the `x=0` branch | OK |
| `axialCoefficient = (r²/2)·pressureFactor` | 663 | i.e. `s · pressureFactor` | def | OK |
| `axial_density_eq` | 1046 | `∂_z p` at `s` equals `scalarFlatDensity 4 0 axialCoefficient` | `field_simp [hs.ne']`; the `s` inside `axialCoefficient` cancels the `1/s` | OK |
| `axialStress_eq_primitive` (1058), `axialStress_factorization` (1080) | | `axialStress = edge 4 x · x³ · axialFactor` | FTC + `scale` with `j=0` | OK. Note the weight for the axial channel is `edge·x³`, **not** `edge/x³` |
| `profileAxialStress` (944) and `profileAxialStress_eq_primitive` (958) | | profile version uses `∫_0^{x} profileS u · profilePressureGradient` | `intervalIntegral.integral_congr` | OK — I checked the Jacobian: `s = profileS u`, `ds = -profileS u du`, and `∫_{s>s_x} = ∫_{-∞}^{x}`; the `∫_{-∞}^{0}` part is zero because the integrand carries `edge 4 u`. So `∫_0^x` is the correct truncation, not an off-by-domain error |

### 5. Profile chart, closed endpoints (700–900)

| decl | line | statement | mechanism | verdict |
|---|---|---|---|---|
| `positiveExtension m x` (700), `_pos` (708), `_eq` (718) | | smooth positive continuation that is the identity for `x ≥ m` | `OutgoingSchedule.sigma` cut-off; `sigma_zero`/`sigma_one` at the right thresholds | OK |
| `profileL` (725), `profileL_pos` (732), `profileL_eq` (735) | | `profileL = positiveExtension (1-2h) (L h η)`, `= L h η` when `η² ≤ 1` | `nlinarith [d.h_pos]` on `1-2h ≤ 1-2hη²`, i.e. `2h(1-η²) ≥ 0` | OK (arithmetic re-derived). See **F3** for the junk region `η²>1` |
| `eta_sq_le_one` | 741 | `η ∈ [-1,1] ⇒ η² ≤ 1` | `nlinarith` with the hint `(η+1)(1-η) ≥ 0` | OK |
| `profileS/profileRadius/profileZ` (+`_pos`,`_square`,`_nonneg`) | 745–774 | `radius² = 2·profileS`; `profileZ ≥ 0` iff `η² ≤ 1` | `sq_sqrt`, `div_nonneg` | OK |
| `profileCarrier` (776), `profileCarrierRadial` (780) | | `C·S^σ·H(z)` and `C·S^(σ-1)(σH - zH')·radius`, `σ = spatialExponent (1+h)`, `H = HeatProfileExtension.extension` | defs | OK — and they are *proved* equal to the physical ones at 1120/1132 |
| `profileCarrier_pos` | 807 | positive when `η² ≤ 1` | `rpow_pos` + `extension_pos` (needs `0 ≤ z`) | OK |
| `profileChi`, `profileBoundary/Time/CorrectionCoefficient` | 812–829 | profile mirrors of §3 | defs; mirror structure verified field by field against 303–312 | OK |
| `profileAngularFactor` (854), `profileAngularStress` (860), `_factorization` (876) | | same `(edge 4 x/x³)` factorisation | `primitive_eq_scale_mul_factor` + `ring` | OK; I re-derived the `x³/radius²` vs `primitive/radius²` matching |
| `profileAngularFactor_zero(_pos)` | 885, 891 | `>0` at `x=0` for `η ∈ [-1,1]` | as 499/505 | OK |
| 12 `*_contDiff` in this block | | smoothness of all profile coefficients | combinators; `profileL_pos`, `profileS_pos`, `profileRadius_pos` discharge every denominator | OK (structural) |

### 6. Dictionary physical ↔ profile (1088–1241)

| decl | line | statement | mechanism | verdict |
|---|---|---|---|---|
| `normalizedParam η = (log(1-η²), η)` | 1088 | the section `t = η²` | def | **SUSPICIOUS-adjacent junk**: at `η² = 1` this is `(Real.log 0, η) = (0, η)` and then `timeOf = 0`, i.e. time **0**, not the blow-up time 1. See **F2** |
| `timeOf_normalizedParam` … `axialStress_normalizedParam` (18 lemmas) | 1090–1241 | physical objects at `normalizedParam η` equal profile objects at `η` | each one carries `hη : η^2 < 1` **strictly**, used for `exp_log`/`sub_pos` | OK — the strictness is present in **all 18**, and all in-repo consumers (`TerminalCone.lean:204,215,225,234,247`) pass a strict `heta` |
| `carrier_normalizedParam` (1120) | | uses `extension_eq_profile` on `0 ≤ profileZ` | correct branch of the glued extension | OK |
| `carrierRadial_normalizedParam` (1132) | | uses `iteratedDeriv_extension_eq_profileJet … 1` | **order-1 jet, matched to `deriv`** via `iteratedDeriv_one` | OK — this is exactly the "off-by-one in derivative order" trap and the index is right (`1` ↔ first derivative ↔ `profileCarrierRadial`'s single `deriv`) |
| `factor_congr_slice` | 1189 | slice-wise equal coefficients give equal `factor` | `integral_congr_ae` with `filter_upwards with t` (everywhere) | OK |

### 7. Full stress, jets, tilt, speed, cone (1245–1673)

| decl | line | statement | mechanism | verdict |
|---|---|---|---|---|
| `profileStress` / `profileStressFactor` | 1245, 1248 | `(Tθ, Tz)` and `(angularFactor, x⁶·axialFactor)` | defs | OK — the `x⁶` is forced: `Tθ = (edge/x³)·A`, `Tz = edge·x³·B`, so `Tz = (edge/x³)·(x⁶B)`. **The power bookkeeping is consistent (3+3=6)** |
| `profileStress_factorization` | 1256 | `profileStress = (edge/x³) • factor` | `Prod.ext`; `by_cases x = 0` branch closed by `simp` | OK |
| `profileStress_jets` | 1288 | `∃ A>0, ∃ N, ∀ i ≤ n, ∀ η ∈ [-1,1], ∀ 0<x≤b: ‖iteratedFDeriv i profileStress (η,x)‖ ≤ A·edge 4 x/x^N` | `EdgeWeightJets.edge_smul_iteratedFDeriv_bound` | OK on quantifier order: `A, N` are chosen **before** `i, η, x` (constants uniform); they may depend on `n, b, C, d, y0`, which is legitimate |
| `physicalStress_jets` | 1607 | same on a compact `S ⊆ EdgeParam` | same lemma with `hS` | OK |
| `profileAngularStress_edge_jets`, `profileAxialStress_edge_jets` | 1299, 1308 | **all** jets of both stresses vanish at `x = 0` | `EdgeWeightJets.weighted_iteratedFDeriv_zero`; the axial one is re-cast as `weighted 4 0 (x³·B)` (1311) | OK — and this is the fact that makes the cone results cheap near `x=0` (**F4**) |
| `profileTilt` (1319), `profileTilt_eq_ratio` (1322), `_zero` (1333), `_contDiffAt` (1336), `_tendsto_zero` (1342) | | `tilt = x⁶B/A = Tz/Tθ` for `x>0`, `= 0` at `x=0`, smooth at `(η,0)` for `η ∈ [-1,1]` | `mul_div_mul_left` with `edge/x³ ≠ 0` for `x>0`; `div` smoothness needs `A(η,0) ≠ 0` | OK; the division guard is the *proved* positivity `profileAngularFactor_zero_pos`, not an assumption |
| `profileSpeed` | 1351 | `1 - r·K_r/K - 2 f'/f` | def | OK, and see next row |
| `profileSpeed_contDiffAt_of_ne` / `_contDiffAt` / `_contDiffOn` | 1355–1386 | smooth where `profileCarrier ≠ 0` (in particular for `η² ≤ 1`) | `ContDiffAt.div` with the two non-vanishing facts (`carrier ≠ 0`, `tailShape > 0`) | OK |
| `extended_heat_slope` | 1388 | for `z ≥ 0`: `-z·H'(z) < h·H(z)` | `z=0`: `extension_zero` + `h>0`; `z>0`: `iteratedDeriv_extension_eq_profileJet … 1` + `profile_h_logSlope_lt` | OK — order-1 jet again correct; the `div_lt_iff₀` uses `profile_pos` |
| `profileCarrier_radial_gap` | 1404 | `radius·K_r + K < 0` for `η² ≤ 1` | reduces to `hb` (1409) closed by `nlinarith` after `unfold spatialExponent` | **OK, and this is the load-bearing inequality.** I re-derived it exactly: with `σ = 1/2-(1+h) = -1/2-h`, `2(σH - zH') + H = -2hH - 2zH'`, so `hb` is *literally* `2 ×` the hypothesis `hlog : -zH' < hH`. Linear in the atoms `h·H` and `z·H'`, so `nlinarith` needs no sign of `H` — and there is **zero slack** |
| `profileSpeed_zero_gt_two` | 1425 | `2 < profileSpeed (η,0)` for `η ∈ [-1,1]` | `hdiv` from the gap + `hz : tailShapeDeriv d 3 = 0` (from `tailShapeDeriv_factorization` at `δ=0`, where `edge 4 0 = 0`) | OK — I checked `speed(η,0) = 2 + 2h - 2·heatSlope(z)` independently and it matches `TerminalCone.lean:167` |
| `profileConeGap` (1437), `_zero` (1440) | | `2 - (v-2)·tilt²`; `= 2` at `x=0` | `profileTilt_zero` | OK; constant `2` matches `ConeAlgebra.true_cone_iff`'s `2(P-v)²` after dividing by `(P-v)²` |
| `compact_positive_collar` | 1444 | `K` compact, `f` continuous at `(p,0)` and positive there ⇒ one `ε, m` uniform over `K` | `UniformCone.positive_uniform_margin` + `IsCompact.eventually_forall_of_forall_eventually` on `𝓝 0 ×ˢ 𝓝 p` + `Metric.mem_nhds_iff` | OK; genuinely uniform (`ε, m` before `∀ p`), conclusion for `|x| < ε` (both signs — harmless, see note) |
| `profile_uniform_cone` | 1467 | `∃ ε m > 0, ∀ η ∈ [-1,1], ∀ |x| < ε`: `m ≤ angularFactor`, `m ≤ speed-2`, `m ≤ coneGap` | `min` of the three + `compact_positive_collar` | OK / **WEAK** (F4) |
| `profileSpeed_eq_log_deriv` | 1548 | `speed = 1 + 2·(d/dx log(K f_o))` | `profileAngularVelocity_hasDerivAt_edge` then `field_simp; ring` | OK — I verified both terms: `dK/dx = -(r K_r)/2` (because `r = c·e^{-x/2}` ⇒ `dr/dx = -r/2`) and `d log f_o/dx = -f'/f`. The docstring's claim `1+2∂_δ log = 1 - r∂_r log` is the correct chain rule for `δ = Y - 2 log r` |
| `profile_relative_cone` | 1562 | on `0<x<ε`: `Tθ>0`, `v>2`, `(v-2)Tz² < 2Tθ²` | `profileTilt_eq_ratio` + `div_lt_iff₀` | OK / **WEAK** (F4) |
| `physicalStress*` (1585–1638) | | mirror of §7 in the physical chart; `physicalStress_normalizedParam` needs `η² < 1` | `Prod.ext` of the two dictionary lemmas | OK |
| `profileStress_of_nonpos`, `physicalStress_of_nonpos` | 1627, 1631 | stress `= 0` for `x ≤ 0` | `edge_of_nonpos` | OK |
| `profileSwirlCoefficient(_pos)` (1642), `profileP` (1651), `profileJ` (1654) | | `F = K f_o / r > 0`; `P = v + Tθ/F`; `J = Tz/F` | defs + `div_pos` | OK; `P - v = Tθ/F` holds by `add_sub_cancel_left`, exactly as the docstring says |
| `profile_true_cone` | 1659 | on `0<x<ε`: `2 < P` and `v < coneBound P J` | `ConeAlgebra.true_cone_iff hv` (an **iff**, `ConeAlgebra.lean:69`), `mpr` fed with `v<P` and the divided-by-`F²` form of the previous item | OK / **WEAK** (F4). The two `mpr` inputs match the iff's RHS literally |

**No declaration in this file is vacuous.** I specifically checked the candidates:
`0 < x` / `0 < r` / `0 < s` side conditions are all satisfiable and are used to rewrite
`exp_log`/`log_exp`; `η ∈ Icc (-1) 1` is non-empty; `η^2 < 1` is non-empty; the numeric
side goals are `0 < 4`, `3 ≠ 0`, `0 < 2` (all true); `d.h_pos`/`d.h_lt_half` give
`0 < h < 1/2`, a non-empty range, and `profileL_pos` needs exactly `1-2h > 0`.

## Kernel-risk assessment

**Kernel risk: essentially nil.** Machine scan of the file:

1. **Recursive inductives / recursors / `Acc.rec` / structure eta.** `inductive`: 0.
   `structure`: 0. `.rec`: 0 (the earlier repo-wide `partial` hits in this file are the
   substring inside `SimilarityProfile.partialS` / `partialZ`). `termination_by`: 0. No
   well-founded definition is introduced here; the only structural recursion the kernel
   sees is Mathlib's own `iteratedFDeriv`/`iteratedDeriv` on `ℕ`, applied to *variable*
   `n`/`i` (1288–1317, 1607) — never unfolded on a literal, so no recursor is reduced.
   `Fin`/`Finset` sums: 0 occurrences in this file.
2. **GMP `Nat` numeral arithmetic.** The largest numeric literal anywhere in the file is
   two digits; a regex for `\d{3,}` returns **zero** matches. All numerals are
   `1, 2, 3, 4, 6, 16, 1/2, 3/2, 5/2`-scale. `norm_num` appears 43× but only on goals of
   the shape `0 < 4`, `(3:ℕ) ≠ 0`, `0 < 2`, `(2:ℝ) ≠ 0`, and `2 - 0 > 0`. `decide`,
   `native_decide`, `Nat.pow`, `omega`: 0 occurrences. There is **no** numeral the kernel
   must recompute at any nontrivial width.
3. **Custom metaprogramming.** `macro`/`elab`/`syntax`/`set_option`/`attribute`
   declarations: **0**. `axiom`: 0. `sorry`: 0. `unsafe`/`partial def`: 0. Tactics used
   are stock (`linarith` 29, `norm_num` 43, `nlinarith` 4, `positivity` 9, `field_simp`
   14, `ring`/`ring_nf`, `simp only`, `convert!` 10). All of these emit ordinary proof
   terms; the kernel work is `Real`-field algebra with tiny rational coefficients.

Does the kernel have to perform any risky computation to accept this file? **No.** The
expensive part of checking this file is elaboration/unification of long `ContDiff`
combinator terms and `Real.rpow` rewriting, not kernel reduction. Nothing here can hide
a `decide`-style unsoundness or a numeral blow-up.

## Escalations

Ranked. None of these is a proof of a false statement inside this file; I could not find
a single incorrect statement here. They are the places where the *file's own claims are
weaker than the surrounding prose*, plus the two off-file dependencies that carry the
real weight.

**E1 (highest value). The three "cone" theorems are collar-continuity statements with a
non-quantified `ε`, and near `x = 0` they are almost tautological.**
`TerminalEdgeFactor.lean:1467` / `1562` / `1659`.
`profileAxialStress_edge_jets` (1308) proves that *every* jet of the axial stress
vanishes at `x = 0`, so `profileTilt → 0` (1342) and `profileConeGap(η,0) = 2` exactly
(1440). `profile_uniform_cone` then just runs continuity on a compact `η`-interval. So on
the collar the cone inequality `(v-2)Tz² < 2Tθ²` holds because `Tz` is *flat-zero*, not
because of any dynamical mechanism. The docstrings at 1464–1466 and 1560–1561 ("the
strict cone inequalities for the actual stress hold throughout one positive-width
terminal collar") invite over-reading.
*Precise question for an expert:* does the blow-up argument need the cone on a
**quantified** `x`-range (e.g. all `0 < δ ≤ 5/2`, which is what `TerminalCone.lean:398
profile_cone_margin` actually proves with the `3/2 ≤ coneGap` margin), or does an
unquantified `ε` from continuity suffice anywhere in the chain?
*What would settle it:* the consumer census. In this repo the ε-collar versions are used
**only** by `TerminalEdgePaper.lean:20` (a paper-facing lower bound), while the
load-bearing path uses the quantitative `TerminalCone.profile_cone_margin` /
`profile_relative_cone` / `profile_full_true_cone` (`TerminalCone.lean:398/422/452`). If
that census is right, this file's headline theorems are decorative and the audit weight
should move to `TerminalCone.lean` — which is *not* in my scope.

**E2. `normalizedParam` is junk-valued exactly at the blow-up endpoint `η² = 1`, and the
physical↔profile dictionary is only proved on the open set.**
`TerminalEdgeFactor.lean:1088`, and all 18 lemmas 1090–1241 (each with `hη : η^2 < 1`).
At `η² = 1`, `Real.log 0 = 0` in Mathlib, so `normalizedParam (±1) = (0, ±1)` and
`timeOf (0, ±1) = 1 - exp 0 = 0`: the *first* time, not the terminal time. The section
docstring 692–698 asserts "A profile chart including both endpoints `η = ±1` … No value
of the implicit coordinates at zero backward time is used." That is true only in the weak
sense that the endpoint statements are made *purely* in profile coordinates
(`profileCarrier`, `profileAngularStress`, …) and never routed through `normalizedParam`.
I verified that no lemma in this file, and no call site in `TerminalCone.lean`
(204, 215, 225, 234, 247), instantiates any `*_normalizedParam` lemma at `η² = 1`.
*Precise question:* does the final blow-up statement require the *physical* stress cone
at `t = 1` (i.e. `η² = 1`), or only the profile-chart cone plus a separate limit?
*What would settle it:* trace whether any theorem downstream of `TerminalCone.lean`
needs `normalized_angularStress`/`normalized_axialStress` (which need `η² < 1`) on a
closed `η`-interval. If it does, the endpoint is a genuine gap; if it only needs the
profile object, the closed-interval results here are sufficient and the docstring is
merely loose.

**E3. Two off-file inputs carry the real mathematical weight of this file.**
(a) `TerminalStress.terminalStress_formula` (`TerminalStress.lean:725`), used at
`TerminalEdgeFactor.lean:479`. My reconstruction of its integration-by-parts sign is
consistent, but its own hypotheses include
`outgoing_boundary_tendsto_zero` — a decay claim about the actual carrier/taper product.
(b) `RadialHeatProfile.profile_h_logSlope_lt` (`RadialHeatProfile.lean:708`), used at
`TerminalEdgeFactor.lean:1402`. Everything downstream — `profileCarrier_radial_gap`,
`profileSpeed_zero_gt_two`, and hence all three cone theorems — is exactly `2 ×` this
one inequality (see the `hb` computation in §7). *Precise question:* is
`profile_logSlope_lt` proved for the *same* profile normalization (`a = 1+h`,
`Real.Gamma a⁻¹ · moment a 0 z`) that `profileCarrier` uses, and does its proof hold at
all `z > 0` rather than only for small `z`? *What would settle it:* a line-by-line audit
of `RadialHeatProfile.lean:600–712` (out of my scope).

**E4. `spatialExponent (1+h) = -1/2-h` makes `profileCarrier_radial_gap` exactly tight.**
`TerminalEdgeFactor.lean:1409–1414` with `RadialHeatProfile.lean:476`.
`2(σH - zH') + H = -2hH - 2zH'`, so the strict inequality survives with **no slack**: it
is the hypothesis `-zH' < hH` doubled. Any later change of the exponent convention (e.g.
`spatialExponent a = 1/2 - a` vs a `-(1+a)/2` convention) silently turns `v > 2` into
`v ≥ 2` or worse. *Precise question:* is `spatialExponent a = 1/2 - a` the exponent that
the *physical* heat kernel scaling requires here (`K ~ s^{1/2-a}`)? *What would settle
it:* `RadialHeatProfile.radialProfile`'s own heat-equation lemma
(`scaled_forward_radial_heat_equation`, `RadialHeatProfile.lean:714`) checked against the
same `spatialExponent`.

**E5 (low). `N` in the jet bounds is existential and unbounded.**
`1288`, `1607`: `∃ A, ∃ N : ℕ, … ≤ A·edge 4 x / x^N`. Any `N` is allowed, so these are
qualitative "exponentially small with polynomial loss" bounds. *Question:* does
`SlowFirstOrderEdge.lean:239/303` (the consumer) need an explicit `N`, or does it also
quantify `N` existentially? A quick read of the consumer's statement suggests the latter,
but I did not audit that file.

## Residue (not checked, and why)

* **No build.** Nothing here is machine-checked. Every "OK" means: the statement says
  what its name/consumers assume, and I reconstructed the mathematical content and (for
  arithmetic) re-derived it by hand. I cannot certify that `field_simp`, `ring_nf`,
  `convert! … using 1`, or `simp only [...]` actually close their goals; the 10
  `convert!` sites (86, 160, 264, 1417, 1502, 1507, 1523, 1542 and 2 more) are the ones
  where a silent mismatch would show up as a build failure, not as a false theorem.
* **Off-file dependencies I read only at the statement level** (their proofs are out of
  scope): `TerminalStress.terminalStress_formula` / `boundary_hasDerivAt` /
  `tailShapeDeriv_factorization` / `taperSlopeFactor*`, `TerminalPressure.*`
  (`outgoingPressure_partialZ`, `canonicalPressure`, `swirlCoefficient`),
  `RadialHeatProfile.*` (`spatialExponent`, `profile_h_logSlope_lt`,
  `radialProfile_first_derivative`), `HeatProfileExtension.*` (glue, jets, positivity),
  `EdgeWeightJets.*` (both jet-bound lemmas — statements audited, proofs skimmed),
  `ParametricFlatFactor.*` / `FlatPrimitive.*` / `FlatPrimitiveFactor.*`
  (`primitive_eq_scale_mul_factor`, `factor_at_zero` — statements audited),
  `ConeAlgebra.true_cone_iff` (statement audited; it is a genuine iff),
  `UniformCone.positive_uniform_margin`, `CoordinateAlgebra.L`/`D`/`qAxial`,
  `OutgoingTail.tailShape*`, `OutgoingSchedule.sigma*`, `PhysicalHeatCoordinates.*`,
  `SimilarityProfile.*`, `SimilarityCoordinates.tau_coordinate_identity`.
* **Mathlib lemma signatures** (`IsCompact.eventually_forall_of_forall_eventually`,
  `integral_Ioi_of_hasDerivAt_of_tendsto'`, `norm_iteratedFDeriv_mul_le`,
  `div_lt_div_of_pos_right`, `Real.rpow_*`): assumed to have the shapes the proofs use.
  The compactness one is the least obvious; the proof feeds it a `𝓝 0 ×ˢ 𝓝 p`-style
  `eventually`, which is the shape I expect that lemma to want.
* **The 47 `*_contDiff` proof terms** were checked structurally (does each combinator's
  non-vanishing/positivity side goal have a matching in-file lemma?) rather than by
  reconstructing every implicit argument.
* **`TerminalCone.lean`, `TerminalEdgePaper.lean`, `SlowFirstOrderEdge.lean`,
  `TerminalHistoryBridge.lean`** — I read only the call sites of this file's exports, to
  check index/quantity agreement. Their own proofs are someone else's scope, and E1
  argues that is where the weight actually sits.

## Verdict counts

* Declarations examined: **235 / 235** (statements). Proof bodies read: **188** in full,
  **47** `*_contDiff` structurally.
* **OK: 233** — **UNCLEAR: 1** (`pressureGradient_eq_primitive`, 994: statement fine,
  content depends on an off-file `partialZ` identity) — **WEAK-but-true: 3**
  (`profile_uniform_cone` 1467, `profile_relative_cone` 1562, `profile_true_cone` 1659;
  counted as OK above, flagged in E1) — **KERNEL-RISK: 0** — **SUSPICIOUS: 0**.
* One junk-value site worth naming even though every consumer guards it:
  `normalizedParam` at `η² = 1` (E2).
