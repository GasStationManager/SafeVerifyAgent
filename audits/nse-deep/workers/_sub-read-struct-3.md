
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
