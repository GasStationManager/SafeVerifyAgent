
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
