
# Worker _sub-read-struct-3 -- structural files (READ-ONLY, commit f9e8bc5)

Global pre-check over all 4 assigned files: grep for `sorry`, `axiom`, `native_decide`,
`decide`, `termination_by`, `deriving`, `.rec`, `partial def`, `unsafe`, `macro`, `elab`,
`inductive`, `class ` returns NOTHING. No metaprogramming, no recursion, no decidability
kernel work anywhere in the 2428 lines. KERNEL-RISK = 0 for all four files a priori;
largest numerals seen are single digits (2, 4, `-1/2`, `/ 2`).

## 1. NavierStokes/ParametricModulation.lean (612 lines, 49 decls, 2 structures)

Verdict: OK (substantive, non-vacuous, both structures ARE constructed). 44 OK / 5 NOTE / 0 UNCLEAR / 0 ESCALATE / 0 KERNEL-RISK.

Content: `primitiveFamily`/`normalizedPrimitiveFamily` (:23,:26) are REAL interval integrals
(`RadialModulation.periodicPrimitive`/`zeroMeanPrimitive` of the parameter slice), not
abstract fields with assumed properties -- so smoothness (:40,:57), periodicity (:84),
zero mean (:95) and the derivative law (:76) are all PROVED, not assumed. This is the
opposite of the unsupplied-hypothesis shape.

Structure census (defect shape 1 test -- is each structure CONSTRUCTED?):
- `CompactCutoff K U` (:110). CONSTRUCTED: `exists_compactCutoff` (:122) builds it for any
  compact K inside open U from `IsOpen.exists_contDiff_support_eq` + `Real.smoothTransition`
  + `UniformCone.positive_uniform_margin` (:130). Not a hypothesis-only object.
- `TrueConeRealization a m p₁ p₂ K B` (:300) = `TrueConeLoop.FamilyChoices` + a `CompactCutoff K {p | 0 < a p}`.
  CONSTRUCTED twice over: `exists_trueConeRealization` (:304), and instantiated downstream at
  `NavierStokes/ModulatedProfileAssembly.lean:355` (`exists_realization`). Consumed by
  ModulatedHistories.lean (30+ sites), ModulatedProfileJetRates.lean, ModulatedCone.lean.
  So the whole file is live, not dead.

Non-vacuity witness (defect shape 2 test) for the capstone `exists_modulated_trueCone_profiles` (:580):
its 4 side conditions are `0 < a`, `2 < p₁ + p₂*m`, `nominalSpeed < coneBound(P,J)`, and
`2 < nominalSpeed` on B. Take a=3, m=0, p₁=10, p₂=0: nominalSpeed = a(1+m²) = 3
(`TrueConeLoop.lean:196`), P = 10, J = 0, `coneBound 10 0 = 10` (`ConeAlgebra.lean:17`).
Then 0<3, 2<10, 3<10, 2<3 all hold, and `FamilyChoices.boundary_inactive` needs
`2 + delta/4 < 3` (`TrueConeLoop.lean:23,:457`), satisfiable with delta ≤ 1.
=> hypothesis set is JOINTLY SATISFIABLE; the theorem is not vacuous.

NOTEs (none is a defect; recorded for the pattern ledger):
- NOTE :110 `CompactCutoff` does NOT certify `0 ≤ value ≤ 1`, nor compact support, nor that
  `value` is bounded. Only `smooth`, `one_on` (on an open nbhd of K) and `zero_near` are
  carried. That is exactly what the three consumers use (`mul_contDiff` :166,
  `extendedPrimitive_hasDerivAt` :271 via `one_on`, `extendedPrimitive_periodic` :228 via
  `zero_near`), so nothing downstream silently assumes a bound it does not have. Shape-3
  adjacent but benign.
- NOTE :271 `extendedPrimitive_hasDerivAt` gives the clean derivative `c p * (f (p,θ) - m p)`
  ONLY for `p ∈ K` (it rewrites with `χ.one_on`). Off K the cutoff factor multiplies the
  derivative; no theorem in the file claims otherwise. Consistent, but every downstream
  θ-derivative fact inherits the `p ∈ K` gate (see :398, :527 `hp : (X,η) ∈ K`).
- NOTE :542 `realized_shears_exact` assumes `hE0 : E (X,η) ≠ 0`, `hn : n ≠ 0`, `hX : X ≠ 0`
  plus the two NOMINAL identities `haNom`/`hbNom` that PIN `a` and `m` to `2X∂ₓE/E` and
  `2X∂ₓU/E`. Those are hypotheses here, not constructed here; they are actually supplied at
  `NavierStokes/ModulatedCone.lean:123`, so the theorem is not dead. `E ≠ 0` is a shape-3
  non-degeneracy ruled out one layer up, as elsewhere in this artifact.
- NOTE :580 `exists_modulated_trueCone_profiles`, advertised as "End-to-end existence", is
  referenced by NOTHING else in the repo (grep over NavierStokes/): it is a showcase
  aggregation of :428/:466/:480/:505. Notably its conclusion carries the cone membership,
  smoothness, O(1/n) jets and boundary match, but NOT the shear identities of :542 -- the
  one conclusion that needs `haNom`/`hbNom`. Reading only this capstone would overstate
  what has been packaged.
- NOTE :416 `boundary_vanishing` / :505 `realized_profiles_boundary_match` make the modulation
  EXACTLY trivial on an open nbhd of B, for every n. This is intended (matching nominal data
  at the boundary), and it is where a shape-2 reader should look: on that neighbourhood the
  realized profiles carry no information beyond `E`, `U`. It is guarded, though: the region is
  `{0 < a} ∩ {highSpeed delta < nominalSpeed}` (`TrueConeLoop.lean:699`), NOT all of K, and
  `loop_trueCone` (:428) still constrains the loop on all of K.

## 2. NavierStokes/PeriodicPhaseAssembly.lean (884 lines, 95 decls, 1 structure)

Verdict: OK (the file's one load-bearing hypothesis IS discharged concretely downstream).
90 OK / 5 NOTE / 0 UNCLEAR / 0 ESCALATE / 0 KERNEL-RISK.

Content: `intervalCutoff` (:24) is an EXPLICIT product of two `Real.smoothTransition` factors with
a 2*padding plateau; `ClockWindow` (:55) is a bare 4-field record (`lower`, `upper`, `padding`,
`padding_pos`) so it is trivially inhabited -- no unsupplied-structure risk. `periodizeScalar`
(:127) is a literal `tsum` over `Frequency` of the deck copies; local finiteness comes from
`g.finite_copy_cutoffs` under `HasCompactSupport` (:130).

THE key hypothesis of this file, repeated verbatim in 12 theorems (:208, :229, :242, :287, :295,
:304, :340, :348, :432, :447, :535, :567, :734, :842), is
`hinj : InjOn quotientPoint ((fun z => g.center + g.basis z) '' w.outer)`.
Everything with real content (clock recovery `periodicClock_path` :242 -> `= t`, all germ/jet
identities) rests on it. Defect-shape-1 test = PASS, and it took cross-file work:
- `transportGeometry_injective` (:705) only TRANSPORTS such an InjOn, it does not create one;
- the generic producer is `TorusAverages.quotientPoint_injOn_small_chart`
  (`NavierStokes/TorusAverages.lean:171`), for a ball of radius r with `‖L‖ * r < 1/2`;
- and it IS discharged for a CONCRETE ClockWindow's `outer` BOX:
  `ActualGaussianCoverage.actual_outer_injective` (`NavierStokes/ActualGaussianCoverage.lean:974`)
  = `ActualSignedGeometry.clockWindow_injective` (`NavierStokes/ActualSignedGeometry.lean:424`),
  for `referenceWindow sys.radius (ChartScales.slotLength ...)` (`ActualGaussianCoverage.lean:153`),
  and consumed at `ActualCarrierTransportBase.lean:253,:263` and `ActualCycleAssembly.lean:652,:663`.
  ClockWindow itself is instantiated at `CorrectionInitialization.lean:4045` and
  `ActualGaussianCoverage.lean:153`. So this file is NOT a dead hypothesis-only layer.

Cross-checked by hand, both non-trivial coordinate claims:
- `profilePhase_eq_literal` (:423): expanded both sides. LHS = (pz/ε)s.2.2 + x0 s.1 - clock*(p F s
  + pz G s) + p*θ; RHS with `PhaseCalculus.phase` (`PhaseCalculus.lean:44`) and `slowSwap` (:411)
  gives p*θ + (pz/ε)q.1.2.1 + x0 q.1.1 - clock*(p F' q.1 + pz G' q.1) with q.1 = (s.1,(s.2.2,s.2.1)).
  The two swaps (`slowSwap` and the `fun s => F (s.1,(s.2.2,s.2.1))` re-swap) cancel exactly. CORRECT.
- `carrier_angularLift_eq_character` (:380): `carrier κ Φ = exp(κ i Φ)`
  (`HarmonicCalculus.lean:68,:77`), so carrier (jK) (angularLift Φ (m/K)) = exp(i j (K Φ + m θ))
  = character j (KΦ + mθ). CORRECT, and `hK : K ≠ 0` is genuinely needed (`m/K`).

NOTEs:
- NOTE (shape 4, junk value) :481 `transportPhase` carries the factor `Kr / K`. At K = 0 Lean gives
  `Kr/0 = 0`, so `transportPhase ≡ 0` and the theorems stated WITHOUT `K ≠ 0` (:492, :499, :508,
  :520, :535 `transportPhase_native_germ`, :567, :722, :734 `transportPhase_path`) degenerate to
  `0 = 0` -- including the "exact values on the entire sampling interval" claim :734, whose RHS
  `(Kr/K)*(A - t*B)` also collapses to 0. Not false, and the K = 0 case is excluded by the users
  (`hK : ∀ n, b.frequency n ≠ 0` at :625, :678, :865). But a reader taking :734 alone as
  "the phase equals the native affine phase" gets nothing at K = 0.
- NOTE (shape 6, stronger-than-needed hypothesis next to a weaker used twin) :621
  `physicalBlock_weighted` assumes `hK : ∀ n, b.frequency n ≠ 0` and uses exactly two instances
  (`hK reference`, `hK n`); the same `∀ n` form is repeated at :678 and :865, while the adjacent
  `physicalBlock_reference` (:612) correctly assumes only the single `b.frequency reference ≠ 0`.
  This is a THIRD occurrence of the artifact's stronger/weaker-twin pattern (2 previously
  confirmed) -- cosmetic here, since downstream discharges the `∀ n` form anyway, but it does
  make the pattern a named one.
- NOTE :151/:159/:164 `periodizeScalar_periodic` / `_refine` / `_transport` are stated for an
  ARBITRARY `f` with no summability or compact support; for non-summable copies both sides are
  the junk `tsum = 0`. True as stated (they are reindexing identities), just empty in that case.
- NOTE :602 `physicalBlock` OVERWRITES `b.angularFrequency` with the constant `fun _ => angular`
  while keeping `b`'s amplitudes and pressure coefficients (`{ b with ... }`). Any downstream
  fact about the original `b.angularFrequency n` does not survive this substitution; the file's
  own naturality theorem (:861) is consistent with the overwrite.
- NOTE :55 `ClockWindow` does not require `lower ≤ upper`. With `upper < lower` the `core`,
  `plateau` and the `Icc` hypotheses of :242/:734 are EMPTY, so those theorems say nothing;
  non-degeneracy is supplied one layer up (`referenceWindow` :153 uses `lower = (-r,0)`,
  `upper = (r,L)` with `0 < r`, `0 < L`). Shape 3, benign but uncertified by the type.

## 3. NavierStokes/BasePrefixIdentity.lean (396 lines, 29 decls, 2 Prop-structures)

Verdict: OK (both Prop-structures are CONSTRUCTED downstream; the pressure hypothesis is
discharged too). 25 OK / 4 NOTE / 0 UNCLEAR / 0 ESCALATE / 0 KERNEL-RISK.

Content: real FTC/curl computations, not repackaging. `average_radial_identity` (:23)
`U_avg + X ∂_X U_avg = U` is proved from `primitive_eq_mul_average` + `partialX_primitive`;
`radialFlux_eq_neg_X_Z_average` (:41) rewrites the flux with it; :85/:111/:132 then discharge
the three component identities and :157 `prefixVelocity_eq_profiles` assembles the curl
componentwise (`fin_cases i`, `velocity_zero/one/two`). Comment at :40 "No divergence equation
is assumed" is accurate: the flux is DEFINED from the axial history at :79/:83.

Structure census (defect shape 1 test):
- `VelocityMatches h d f` (:218, Prop: phi/axial/flux `EqOn` on `profileWindow`). CONSTRUCTED
  in-file by `velocityMatches_of_beta` (:271) from the single scalar premise
  `X * beta n w = radialFlux ...`, and downstream by
  `ConstructedSlowBase.repaired_coefficientMatches` (`ConstructedSlowBase.lean:67`).
- `CoefficientMatches h C d f` (:281, `Prop extends VelocityMatches`, adds pressure +
  thetaStress + zStress `EqOn`). No constructor in this file -- checked cross-file: CONSTRUCTED at
  `ConstructedSlowBase.lean:67` (`refine ⟨⟨_,_,_⟩,_,_,_⟩`) and reused at
  `ConstructedSlowBase.lean:219,:346`, `EntranceAlignedBase.lean:364`. NOT an unsupplied hypothesis.
- The capstone `finiteIdentities_of_coefficients` (:375) produces `BaseResidual.FiniteIdentities`,
  which is consumed as a hypothesis in ~8 places (`BaseResidual.lean:1530,:1623,:2480,:2518,:2612`,
  `ConstructedSlowBase.lean:148,:169`, `FinalSlowBase.lean:108`) -- and its own extra hypothesis
  `hp : ∀ n, ∀ w ∈ profileWindow, pressureCoefficient h C f n w = 0` (:379) IS discharged:
  `ConstructedSlowBase.lean:95` relays it and `ConstructedSlowBase.lean:227` supplies it from
  `GlobalSlowProfiles.lean:1781` (`nominal_pressureCoefficient`). So the whole chain closes.

Non-vacuity: `profileWindow` (:203) `= Ioi 0 ×ˢ Ioo (-1) 1` is a NONEMPTY open half-strip, and
`inner_mem_profileWindow` (:207) proves the physical similarity point actually lands in it under
`0 < h < 1/2`, `t < 1`, `0 < s`. So the `EqOn ... profileWindow` obligations are not empty
conditions. Also note `X > 0` on the window is what makes `X * beta = radialFlux` (:272) an
informative determination of `beta` rather than the degenerate `0 = flux` on the axis.

NOTEs:
- NOTE (shape 3/4) every theorem here takes an UNRESTRICTED `C : ℝ`, and the swirl branch runs
  through `C⁻¹` (:118-121 `partialX_swirl_primitive` gives `-C⁻¹ * d.phi n w`, and :256 rewrites
  `slowSwirl` as `C⁻¹ * (...)`). At C = 0 Lean's `0⁻¹ = 0` makes the whole swirl channel
  identically zero and :111/:236/:261 collapse to `0 = 0` for that component. Nothing in this file
  excludes C = 0; it is excluded one layer up (`W.axis.normalization_pos`, used e.g.
  `AssembledSlowBase.lean:1004`, `AlignedProfileSpectralCone.lean:48`). Same shape as the artifact's
  other "non-degeneracy ruled out one layer up" cases.
- NOTE (shape 6, mild) :23 `average_radial_identity` assumes global `ContDiff ℝ ∞ U` for a
  pointwise FTC identity at a single `w`; only differentiability of the average at `w` is used
  (through `average_smooth` / `partialX_primitive`, which themselves want the ∞ form). Same
  over-strength appears at :59/:68 where `hf : ∀ n ≤ J, DifferentiableAt ...` is the WEAKER twin
  actually used, while callers (:85, :111, :132) feed it from the global
  `SmoothCoefficients`. Cosmetic only.
- NOTE :375 has three separate side inputs (`hTheta`, `hZ` smoothness of the stress densities on
  `Ioo (-1) 1`, and `hp`); none is proved here. All three are supplied at
  `ConstructedSlowBase.lean:100-107`, so the theorem is live, but read alone it is a pure bridge.
- NOTE :314 `radialDivergence_congr_germ` and :287 `coefficient_germ` are germ-transport helpers;
  they hold for arbitrary `k` and arbitrary functions and carry no analytic content (fine).

## 4. NavierStokes/ModulatedExterior.lean (536 lines, 37 decls, 1 structure, 1 Prop-def)

Verdict: OK (both new predicates are constructed IN-FILE; exterior field is genuinely nonzero).
33 OK / 4 NOTE / 0 UNCLEAR / 0 ESCALATE / 0 KERNEL-RISK.

Structure / Prop-def census (defect shape 1 test):
- `RestoredSquaredSwirl W Q` (:93, Prop-def: the primitive of `f^2` at `nominalOuterX` agrees with
  the nominal one for every eta in S). CONSTRUCTED IN-FILE by `actual_squared_swirl_restored` (:326)
  from `v.restored` + `squared_swirl_anchor_of_rows` (:49). Not an unsupplied hypothesis.
- `RealizesScheme s hI d` (:144, Prop structure, three `d.field = extendedCoefficient` equations for
  indices 0, 1, 3). CONSTRUCTED twice by `rfl`: `realizes_coefficients` (:150) and
  `actual_realizes` (:334). Consumed downstream at `SlowBaseEndpoint.lean:360` and
  `FinalSlowBase.lean:609`. Live.
- Note the interface pins only indices 0/1/3 (phi, axial, pressure), never index 2 (the flux/beta
  row) nor 4; the flux row is instead constrained through `BasePrefixIdentity.VelocityMatches`
  (file 3) -- the two interfaces are complementary, not redundant.

The real content chain is honest: `integral_equal_after` (:28) is a plain
`integral_add_adjacent_intervals` splice; `squared_swirl_anchor_of_rows` (:49) cancels the shared
`pressure0` out of row 4 of `profileRows`; :105/:115/:126 propagate mass and pressure past the
outer radius; :226 `realized_exterior_coefficients` then yields `ExteriorCoefficients` and
:276/:289 conclude the exterior fields EQUAL the heat fields and the NS residual is exactly 0.

Non-vacuity check (shape 2) on the exterior target: `heatVelocity C h` is
`AxisymmetricResidual.velocity (fun _ => 0) (heatCoefficient C h) (fun _ => 0)`
(`BaseExterior.lean:37`) -- a PURE SWIRL field (zero radial and axial components). So the exterior
claims are only non-trivial because the swirl amplitude is nonzero:
`nominalHeatNormalization = PhysicalHeatCoordinates.normalization F.data (nominalHeatSwitch W)`
(`BaseExterior.lean:466`) is provably POSITIVE via `normalization_pos`
(`PhysicalHeatCoordinates.lean:42`) plus `nominalHeatSwitch_pos` (`BaseExterior.lean:469`).
If that constant were 0 the exterior fields would be identically 0 and :289/:363 would be
`residual of the zero field = 0`. It is not 0. GOOD.

NOTEs:
- NOTE (the one thing to know about this file) :460 `completed_fields_smooth_near_terminal`,
  :490 `realized_terminal_extension` and :514 `actual_terminal_extension` all require
  `hx : x 2 = 0` -- the terminal-time smooth extension is proved ONLY at terminal points on the
  central plane (third coordinate zero), plus `0 < radialEnergy x` (off the axis). The reason is
  structural, not cosmetic: the neighbourhood in `exists_terminal_exterior_neighborhood` (:402)
  needs `0 < forwardScalar (2h) (x 2) b = b - (x 2)^2 * b^(2h)`
  (`SimilarityCoordinates.lean:22`) at `t = 1`, which is exactly `0 < b` when `x 2 = 0` and can
  FAIL for `x 2 ≠ 0` since `b = radialEnergy x / (2*(R+1))` is not free. Checked the complement:
  `SlowBaseEndpoint.lean:365-380` splits on `x 2 = 0` and covers the other branch with
  `velocityNonzeroAxial` / `pressureNonzeroAxial`, assembling `AwayExtensions` for ALL `x ≠ 0`.
  So the restriction is COMPLETED downstream and is not a gap -- but the theorems in this file
  must not be quoted as terminal-plane statements on their own.
- NOTE :445/:448 `completedVelocity` / `completedPressure` are `if z.1 < 1 then u z else heat...`
  patches. Consequently every conclusion at or after `t = 1` is TRUE BY DEFINITION of the patch
  (`ite_eq_right`), and on the produced neighbourhood U the completed field is EqOn the heat field
  (:472-483), i.e. it carries no information beyond the heat solution there. The non-trivial input
  is the exterior equality :276, which is genuinely proved.
- NOTE (shape 3) the `C` argument of `completedVelocity`/`completedPressure` (:445, :448) and of
  the heat fields is unconstrained in this file; positivity comes one layer up
  (`nominalHeatNormalization`, see above). Same "non-degeneracy ruled out one layer up" pattern as
  files 1 and 3.
- NOTE :188 `realized_positive_exterior` and :199/:207 depend on `houter : s.B = nominalOuterRadius W`
  as an EQUATION on the scheme's outer radius, and the header comment (:11-13) claims the interface
  "allows any seed cutoff with the same order-zero profile and outer radius". That is accurate:
  `hbase` and `houter` are equations, not inequalities, so a scheme with a different outer radius
  gets nothing from this file even if it is larger. Deliberate, but a narrow interface.

## Closing summary (all 4 files)

All four files are CLEAN in direction. Every `structure`, `class`-free Prop record and Prop-def
introduced in them (`CompactCutoff`, `TrueConeRealization`, `ClockWindow`, `VelocityMatches`,
`CoefficientMatches`, `RealizesScheme`, `RestoredSquaredSwirl`) is CONSTRUCTED, either in-file or
at a located downstream site, so shape 1 (unsupplied hypothesis) does not appear here. Zero kernel
risk: no `inductive`, no recursion, no `decide`, no metaprogramming, no numeral bigger than one
digit in all 2428 lines. The systematic residue is the artifact's known shape-3/4 pattern -- junk
`0⁻¹ = 0` divisors (`C⁻¹` in BasePrefixIdentity, `Kr / K` in PeriodicPhaseAssembly,
`E (X,η) ≠ 0` in ParametricModulation) whose non-degeneracy is certified only one layer up -- plus
a THIRD instance of the stronger-hypothesis/weaker-used-twin pattern at
`PeriodicPhaseAssembly.lean:621,:678,:865` (`∀ n, b.frequency n ≠ 0` where two instances are used,
next to the correctly-weak `:612`).
