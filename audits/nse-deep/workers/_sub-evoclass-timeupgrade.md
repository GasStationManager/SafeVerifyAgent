# NSE deep audit — worker slice: TIME-REGULARITY upgrade
Repo: /home/gsm/.openclaw/workspace/repos/NSE @ f9e8bc5 (openai/NavierStokesAndEuler). READ-ONLY.
Instrument: line-by-line source reading (python/grep). NO `lake build` (no Mathlib on disk) ->
**every verdict below is about the WRITTEN STATEMENTS and PROOF SCRIPTS, not about elaboration success.**
Nothing was modified in the repo.

## 0. Bottom line

The time-regularity upgrade in my slice is **genuinely derived from the challenge hypothesis
`h : EulerExistenceAndSmoothnessR3 u0 v p`**. I found **no extra hypothesis on the competitor**,
**no Prop-valued obligation left undischarged**, **no wrong-direction lemma on the used path**,
and **no junk-value / vacuity trick** in this slice. Kernel risk: one trivial `decide` on `(3:ℕ) ≠ 0`.

Chain actually used (all forward, challenge -> Evolution):

```
h  --(ClassicalBridge)-->            velocity_contDiff / velocity_memLp / pointwise_euler (HasDerivAt at t>0)
h  --(WeakTimeContinuity)-->         velocityLp_weakly_continuous          (uses globally_bounded_energy + integrable)
h  --(ProjectedEulerPairing)-->      velocity_solenoidal_test_pairing_hasDerivAt   (pressure killed by IBP vs div-free test)
h  --(other slice: elliptic)-->      recoveredVelocity (SmoothL2Field, all-order MemLp) + uniform jet bounds
   ==> isSmoothScalarEuler_of_weak_projectedEquation ==> IsSmoothProjectedEuler ==> Evolution
```

---

## 1. `Euler.ComparatorBridge.comparator_weak_pairings_continuous`
`Euler/CompactVorticityTimeUpgrade.lean:29-42`

Statement (my words): for a family `A : Icc 0 T -> SmoothL2Field Space` whose `field` is pointwise the
competitor velocity `v(.,t)`, the scalar map `t |-> <phi, (A t).toLp>` is continuous for **every** `phi : L2`.

Mechanism: shows `(A t).toLp = h.velocityLp (iota t)` by `Lp.ext` + a.e. filter_upwards on the two
`coeFn_toLp`s, then composes `h.velocityLp_weakly_continuous phi` with the continuous inclusion
`Icc 0 T -> Ici 0`. `velocityLp_weakly_continuous` (`Euler/WeakTimeContinuity.lean:81-124`) is itself
proved from `h` only: 3-epsilon argument using (i) `velocityLp_norm_bounded`
(`:66`, from `h.globally_bounded_energy`), (ii) continuity of pairings against continuous compactly
supported tests (`:44`, from `h.velocity_smooth` = joint `ContDiffOn` on `univ x Ici 0`), (iii)
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le` density in L^2. Includes t = 0.
**Verdict: OK.** No time regularity of A is assumed; `hA` is only a pointwise identification (and in the
caller it is literally `rfl`).

## 2. `comparator_velocity_mem_solenoidal`
`Euler/CompactVorticityTimeUpgrade.lean:46-55`

`(A t).toLp ∈ solenoidalSpace` from `smooth_mem_solenoidal` (`Euler/MeanSolenoidalSpace.lean:187`)
applied to `(A t).smooth`, `(A t).memLp` and the classical `h.div_free x t (t.property.1)`.
`solenoidalSpace := gradientSpace.orthogonal` (`MeanSolenoidalSpace.lean:58`), `gradientSpace` = closed span
of L^2 classes of gradients of compactly supported smooth scalars (`:50`). So the Hilbert constraint is
the honest one and is obtained from the challenge-class `div_free`. **Verdict: OK.**

## 3. `tensorNorm_fieldSub_le` / `jetLp_norm_le_tensorNorm` / `tensorNorm_uniform_of_jetLp_uniform`
`CompactVorticityTimeUpgrade.lean:59-79`

`tensorNorm q A = sum_{n<=q} ‖A.jetLp n‖` (`Euler/OrdinaryH3Norms.lean:12`); `jetLp n = (A.integrable n).toLp
(iteratedFDeriv ℝ n A.field)` (`Euler/LpSmoothField.lean:46`) where `SmoothL2Field.integrable : ∀ n, MemLp
(iteratedFDeriv ℝ n field) 2 volume` is a **structure field** (`LpSmoothField.lean:31-34`).
So the jets are real `MemLp.toLp` classes with genuine proofs — **not** the junk `toL2` fallback of
`Euler/SolutionDefinitions.lean:87-90` (that `toL2` never appears anywhere in my slice; grep = 0 hits).
`tensorNorm_uniform_of_jetLp_uniform` is bookkeeping: per-order uniform bounds -> finite-sum bound
(uses `Exists.choose`, harmless, `classical`). **Verdict: OK.**

## 4. `jetLp_continuous_of_toLp_continuous`  (the real content of the "all-order jet time-continuity")
`CompactVorticityTimeUpgrade.lean:83-108`

Statement: strong `L^2` continuity of `t |-> (A t).toLp` **plus** uniform-in-t bounds of every
`tensorNorm q (A t)` imply continuity of every jet `t |-> (A t).jetLp q`.

Mechanism, genuine and checkable: at each `s`, uses the interpolation inequality
`tensorNorm_interpolate_zero` (`Euler/OrdinaryCauchyInterpolation.lean:24-38`)
`tensorNorm q C <= wordCount q * sqrt(‖C.toLp‖ * N)` when `WordBound (2q) N C`, with
`C = fieldSub (A t) (A s)`; then squeeze_zero. The interpolation is a real log-convexity argument:
`wordMaximum_logconvex` (`Euler/OrdinaryWordInterpolation.lean:31-50`) proves
`wordMax_{n+1}^2 <= wordMax_n * wordMax_{n+2}` by **integration by parts in L^2**
(`field_directional_inner`, `Euler/OrdinaryL2Integration.lean:46`, itself from
`integral_bilinear_fderiv_right_eq_neg_left_of_integrable` with all three pairings integrable because
all orders are `MemLp`), plus Cauchy-Schwarz. `wordCount m = sum_{n<=m} 3^n > 0`.
So the "no continuity of higher derivatives is used" claim is honest: only `h0` (order 0 continuity)
and the *uniform bounds* enter. **Verdict: OK** (conditional on elaboration, which I cannot test).

## 5. `projectedRhs_norm_le_of_tensorNorm_le` / `projectedRhs_uniform_bound`
`CompactVorticityTimeUpgrade.lean:112-138`

`‖(projectedRhs A).toLp‖ <= 39 * smoothEmbeddingConstant * M^2` from `tensorNorm 2 A <= M`, via
`solenoidalProjection_apply_norm_le`, `advection_norm_velocity` (`Euler/OrdinaryAdvectionLimit.lean:39`,
honest pointwise `le_opNorm` + `Lp.norm_le_mul_norm_of_ae_le_mul`) and `wordBound_pointwise` /
`wordBound_derivative` (H^2 -> L^infty embedding). Only used to produce *some* Lipschitz constant, so the
numeric value of `39` / `smoothEmbeddingConstant` (`Euler/EulerProof.lean:8227`) is soundness-irrelevant:
no vacuity leverage here (a degenerate constant could only make the lemma unprovable, not the final
theorem weaker). Numerals are tiny; `norm_num` only. **Verdict: OK.**

## 6. `isSmoothScalarEuler_of_weak_projectedEquation`  (the hinge of my slice)
`CompactVorticityTimeUpgrade.lean:144-198`

Hypotheses: `hT : 0 < T`; `A`; `hs` (each slice solenoidal); `hb` (**uniform in t** bound of every
`tensorNorm q`); `D`, `hD : Dense D` (D a set in the subtype `solenoidalSpace`); `hc` (continuity of
pairings on D); `hd` (for phi in D and t in **Ioo 0 T**: `HasDerivAt` of the pairing with value
`<phi, (projectedRhs (A t)).toLp>`). Conclusion `IsSmoothScalarEuler A`.

Mechanism: define `u r = (A (projIcc r)).toLp` and `b r = (projectedRhs (A (projIcc r))).toLp` inside the
Hilbert space `solenoidalSpace` (b lands there by `projectedRhs_toLp` + `solenoidalProjection_mem`, line
156-159 — **proved, not assumed**). Then
* `WeakHilbertODE.lipschitzOnWith_of_dense_weak_equation` (`Euler/WeakHilbertODE.lean:90`) gives
  `LipschitzOnWith C u (Icc 0 T)`, hence **strong** L^2 continuity `h0` (line 177-183);
* `jetLp_continuous_of_toLp_continuous` then gives all-order jet continuity `hA`;
* `WeakHilbertODE.hasDerivAt_of_dense_weak_equation` (`:196`) gives the **strong** L^2 time law,
  pushed through `solenoidalSpace.subtypeL` (line 192-198).
`IsSmoothScalarEuler` is *defined* (`Euler/OrdinaryEulerClassicalClass.lean:194-206`) as jet continuity +
existence of B, p with the L^2 time law, div-free, `Differentiable (p t)` and the classical scalar Euler
identity; the `.mpr` of `scalarEuler_iff_projected` (`:245-269`) constructs B, p from the Helmholtz
`pressureField`, so no pressure data is demanded of the competitor. **Verdict: OK.**

### 6a. Weak -> strong: is it legitimate? YES
The Hilbert lemmas in `Euler/WeakHilbertODE.lean` are elementary and correct as written:
`norm_le_of_dense_inner_bound` (`:27`, `Dense.induction` on a closed predicate),
`eq_of_dense_inner_eq` (`:40`), `lipschitzOnWith_of_dense_scalar_derivative` (`:49`, MVT on `Ioo` +
`LipschitzOnWith.closure` to reach the endpoints using only *scalar* continuity),
`sub_eq_integral_of_dense_weak_equation` (`:161`, FTC per test vector then `innerSL` commutes with the
interval integral), `hasDerivWithinAt_of_dense_integral_equation` (`:138`). Density is used exactly twice
and only in the sound direction: (i) to turn a norm bound tested on D into a norm bound; (ii) to identify
two vectors with equal pairings. The strong derivative needs `Continuous b` — supplied by
`projectedRhs_continuous A hA 0` (line 185-188) **after** `hA` has been proved. No circularity.

## 7. Caller: does `Euler/ComparatorLocalEvolution.lean:72-82` discharge every hypothesis from `h`?
Per hypothesis of `isSmoothScalarEuler_of_weak_projectedEquation`:

| hypothesis | discharged by | source |
|---|---|---|
| `hT : 0 < T` | `hT` from `local_compact_vorticity_of_truncationFamily` (`:93-95`) | from `h` + compact-curl hyp `hc` |
| `A` | `recoveredVelocity h T K hK hsupport` (`:31-39`) | built from `h.velocity_contDiff`, `h.velocity_memLp`, `h.div_free` + compact curl support |
| `hs` | `comparator_velocity_mem_solenoidal h A hA` (`:74`) | `h.div_free` |
| `hb` | `tensorNorm_uniform_of_jetLp_uniform A (recoveredVelocity_jetLp_uniform ...)` (`:75-76`) | `h.component_word_energy_uniform_of_commonCompactCurl` (**other slice**: elliptic/uniform-jets) |
| `D`, `hD` | `compactSolenoidalTests`, `compactSolenoidalTests_dense` (`:77`) | closed-form theorem, no competitor input |
| `hc` | `comparator_weak_pairings_continuous h A hA φ` (`:78-79`), for **all** φ (D-membership ignored) | `h.globally_bounded_energy`, `h.velocity_smooth`, `h.integrable` |
| `hd` | `comparator_projected_pairing_hasDerivAt h hT A hA φ hφ t ht` (`:80-81`) | `h.euler` / `h.pointwise_euler` |

`hA` in the caller is `rfl` (line 71 + `recoveredVelocity_field :41`). **Nothing extra is assumed of the
competitor.** `compactCurlLocalUpgrade` (`:91-97`) is a plain theorem inhabiting the Prop-valued def
`CompactCurlLocalUpgrade`, i.e. discharged, not postulated. **Verdict: OK.**

## 8. `comparator_compact_rep_pairing_hasDerivAt` and `comparator_projected_pairing_hasDerivAt`
`Euler/CompactProjectedEulerLaw.lean:32-51` and `:55-66`

The weak projected derivative is obtained from `comparator_clamped_compact_pairing_hasDerivAt`
(`Euler/ProjectedEulerPairing.lean:140-158`), and the RHS is rewritten into
`<g, (projectedRhs (A t)).toLp>` by `EulerCompactProjectedPairing.inner_projectedRhs _ g.property`
(uses `g ∈ solenoidalSpace`, so the Leray projection is invisible to a solenoidal test) plus
`inner_smoothField_eq_integral`. `:55` only unpacks a `compactSolenoidalTests` member into a genuine
smooth compactly supported divergence-free representative. Upstream:
* `velocity_test_pairing_hasDerivAt` (`ProjectedEulerPairing.lean:32-98`): differentiation under the
  integral by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the *compact* `tsupport φ`, dominated
  by a bound from `IsCompact.exists_bound_of_continuousOn`; the pointwise time derivative value is
  identified with the classical Euler RHS by `HasDerivAt.unique` against `h.pointwise_euler` (line 95).
* `h.pointwise_euler` (`Euler/ClassicalBridge.lean:33-47`): converts the challenge class's
  `derivWithin ... (Ici 0) t` into `HasDerivAt` **only at t > 0**, via
  `derivWithin_of_mem_nhds (Ici_mem_nhds ht)` plus differentiability from joint `ContDiffOn`.
  This is the correct, non-vacuous handling: no `derivWithin`-junk-value exploit.
* pressure elimination: `EulerComparatorPressure.compact_solenoidal_pressure_pairing_zero`
  (`Euler/CompactPressurePairing.lean:64`) — `∫ <φ, ∇p> = 0` for compactly supported smooth div-free φ.
  No decay assumption on p is needed because φ has compact support.
**Verdict: OK.** No time regularity of A is used here (only `hA`, an a.e./pointwise identification).

## 9. `Euler/CompactSolenoidalDensity.lean` — is the test class really dense, and how is density used?

* `Test` (`Euler/MeanGradientTestSpace.lean:14-23`) = submodule of genuinely `ContDiff ℝ ∞` and
  `HasCompactSupport` vector fields. `curlTest f` stays in `Test` (`MeanVectorIdentities.lean:75`).
* `compactCurlGenerators := range (fun f : Test => testValue (curlTest f))` (`:75`), i.e. L^2 classes of
  curls of compactly supported smooth fields; each is solenoidal (`:87`).
* `weakHarmonicOn_univ_eq_zero` (`:21-49`): an L^2 field that is distributionally harmonic on all of R^3
  is 0. Proof: quantitative interior bound `weakHarmonic_pointwise_scaled`
  (`Euler/MeanWeakHarmonicScaling.lean:33`) gives `‖u x‖^2 <= (C/R^3)‖u‖^2` a.e. on the R/4-ball; let
  R -> ∞. `WeakHarmonicOn` (`Euler/MeanHarmonicDecomposition.lean:18`) is the honest distributional
  definition `∫ <u x, Δφ x> = 0` for all compactly supported smooth φ supported in U. This is a real
  L^2-Liouville argument, not a definitional trick.
* `weakHarmonicOn_univ_of_compactCurl_pairing_zero` (`:103-112`): if `u` is solenoidal and kills every
  compact smooth curl, then `<u, curl curl f> = 0`, and `solenoidal_curlcurl_pairing`
  (`Euler/MeanHarmonicDecomposition.lean:52`, using `curl curl = grad div - Δ` and orthogonality to
  gradients) turns this into `<u, Δf> = 0` for every test f, i.e. weak harmonicity.
* `compactCurlSpace_eq_solenoidal` (`:115-126`): `compactCurlSpace.orthogonal ⊓ solenoidalSpace = ⊥`
  plus `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection` (legitimate: `compactCurlSpace` is a
  topological closure, hence closed/complete — instance at `:85`).
* `closure_compactCurlGenerators` (`:129-138`) upgrades submodule-closure to set-closure using
  `span (range compactCurlMap) = range compactCurlMap` (linearity, `compactCurlMap` at `:52`).
* `compactSolenoidalTests_dense` (`:164-180`): `Subtype.dense_iff` + image computation +
  `closure_compactCurlGenerators`. So `D` is dense **in the subtype topology of `solenoidalSpace`**, which
  is exactly the space `H` in which `WeakHilbertODE` is applied. Types match; the density is the right one.

How density gets an EQUATION from PAIRINGS: **only** through `WeakHilbertODE.norm_le_of_dense_inner_bound`
and `eq_of_dense_inner_eq` (section 6a) — i.e. "pairings with a dense set determine a vector". That is
valid in any inner-product space and does **not** require the tests to be smooth or the equation to hold
strongly beforehand. The genuinely non-trivial upgrade (weak -> pointwise-in-x) is *not* done by density:
it is done later by `pointwise_derivative_of_l2` (`Euler/OrdinaryStrongTime.lean:48-64`) using bounded
Sobolev evaluation at order 3, whose hypotheses are exactly `hA`, `hB`, `hd` — all already proved.
**Verdict: OK.** (Note `solenoidal_eq_zero_of_compact_test_pairing_zero` (`:183`) is a separate exported
tool, unused on this path.)

## 10. Where the Evolution fields actually come from (cross-check of the task's central question)

`Evolution` (`Euler/OrdinaryEulerDifference.lean:21-32`) has 7 fields. Via
`exists_evolution_iff_scalar` -> `exists_evolution_iff_projected` ->
`evolutionOfProjectedEquation` (`Euler/OrdinaryEulerSobolevClass.lean:24-35`):
* `velocity := A`, `pressureForce := pressureField (A t)` — **constructed** (Helmholtz), not taken from p;
* `velocity_continuous := hA.1` — proved in section 4/6;
* `pressure_continuous := pressureField_continuous A hA.1` (`OrdinaryHelmholtzField.lean:83`) — proved;
* `solenoidal := hA.2.1` — from `h.div_free` (section 2);
* `gradient := pressureField_mem_gradient` (`:74`) — definitional Helmholtz identity, proved;
* `time_law` — `pointwise_derivative_of_l2` from the L^2 law `hA.2.2` + jet continuity, then
  `HasDerivWithinAt -> HasDerivAt` on the interior. **Proved, not assumed.**
So `IsSmoothProjectedEuler` = (all-order jet continuity) ∧ (solenoidal) ∧ (L^2 projected time law), and my
slice proves all three from `h`. **No field of `Evolution` is an added hypothesis on the competitor.**

---

## Explicit answers

**(a) Any unproved assumption / extra hypothesis on the competitor in my slice? NO.**
Every hypothesis of `isSmoothScalarEuler_of_weak_projectedEquation`
(`CompactVorticityTimeUpgrade.lean:144-152`) is discharged at
`ComparatorLocalEvolution.lean:73-81` from `h` (table in section 7), except `D`/`hD`, which are
competitor-independent theorems. The only hypothesis whose provenance is **outside my slice** is `hb`
(uniform-in-time bounds of every `tensorNorm q (A t)`), which comes from
`recoveredVelocity_jetLp_uniform` (`ComparatorLocalEvolution.lean:49-60`) -> 
`h.component_word_energy_uniform_of_commonCompactCurl` — that is the elliptic/uniform-jet slice and I did
NOT verify it. **If any hidden assumption exists, that is where to look, not here.** Same for
`smoothL2Field_of_curl_compact` supplying the `∀ n, MemLp (iteratedFDeriv n)` field of `SmoothL2Field`.
Also outside my slice: `h.local_compact_vorticity_of_truncationFamily` and the passage from the *local*
`CompactCurlLocalUpgrade` to the *global* headline (compact-curl hypothesis `hc` in `:92`) — the headline
contradiction must not silently need compactly supported initial vorticity.

**(b) Any lemma going in the WRONG direction? NO on the used path.**
All arrows are challenge -> Evolution. The only reverse-direction lemma I saw,
`Evolution.isSmoothProjectedEuler` (`OrdinaryEulerSobolevClass.lean:37-42`), is used solely for the
`mp` half of the `iff`; the breakdown proof uses `.mpr` (`ComparatorLocalEvolution.lean:82`).

**(c) Junk-value / vacuity tricks? NONE FOUND in my slice.**
* `SmoothL2Field.jetLp`/`toLp` use `MemLp.toLp` with real proofs (structure field `integrable`,
  `LpSmoothField.lean:31-47`). The junk-fallback `toL2` of `SolutionDefinitions.lean:87-90`
  (`if MemLp then toLp else 0`) has **zero** occurrences in my four slice files. Flag for other workers:
  that fallback lives in `SobolevSmoothOn`/`EulerSobolevExistenceAndSmoothnessR3On`, so anyone auditing
  those classes must check it is never load-bearing.
* No `fderiv = 0`-off-differentiability exploit: differentiability always comes from
  `SmoothL2Field.smooth` or `h.velocity_smooth`; `pointwise_euler` establishes real differentiability
  before using `derivWithin = deriv` (`ClassicalBridge.lean:39-42`).
* Hypotheses are non-trivial to satisfy but are all *discharged*, so no "hypothesis makes claim
  vacuous" pattern; in particular `hd` is required only on `Ioo 0 T` (interior), which matches both
  `Evolution.time_law` and the challenge class — no endpoint sleight of hand.
* The one place a degenerate constant could hide (`39 * smoothEmbeddingConstant`) is soundness-neutral:
  only the *existence* of a Lipschitz constant is used.

**(d) Kernel risk in my slice: essentially none.**
Scan of `CompactVorticityTimeUpgrade.lean`, `CompactProjectedEulerLaw.lean`, `CompactSolenoidalDensity.lean`,
`ComparatorLocalEvolution.lean`, `WeakHilbertODE.lean`, `ProjectedEulerPairing.lean`, `ClassicalBridge.lean`,
`WeakTimeContinuity.lean`, `OrdinaryCauchyInterpolation.lean`, `OrdinaryWordInterpolation.lean`,
`OrdinaryL2Integration.lean`, `OrdinaryH3Norms.lean`, `OrdinarySmoothWords.lean`,
`OrdinaryEulerSobolevClass.lean`, `OrdinaryEulerClassicalClass.lean`, `OrdinaryHelmholtzField.lean`,
`CompactPressurePairing.lean` for
`decide|native_decide|axiom|sorry|admit|macro|elab|set_option|partial|unsafe|Acc.rec|termination_by|decreasing_by|WellFounded|notation`:
* **`CompactSolenoidalDensity.lean:39`: `(by decide : (3 : ℕ) ≠ 0)`** — single `decide`, on a
  `Nat` inequality with literal 3. Trivial kernel cost; not a soundness concern, reported because the
  task asks for every hit.
* `local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` at `ProjectedEulerPairing.lean:23`,
  `ClassicalBridge.lean:14`, `WeakTimeContinuity.lean:27` — plain local notation, benign.
* Two `private local instance : Fact (0 < (1:ℝ))` (`OrdinaryCauchyInterpolation.lean:17`,
  `OrdinaryStrongTime.lean:18`) — benign, but note they silently select `AddCircle 1` machinery.
* Recursion: `wordField` (`OrdinarySmoothWords.lean:31-33`) is structural on `ℕ`; no `termination_by`,
  no `WellFounded`/`Acc.rec` anywhere in the slice. Numerals are all small (3, 13, 39, 40); only
  `norm_num`/`positivity`/`nlinarith`/`omega`, no big-numeral `decide`.
* Repo-wide: `grep -rnE '\bsorry\b|^axiom |native_decide|^unsafe |^partial |set_option' Euler` = **0 hits**
  (confirms the parent's scan).

## Caveat I want on the record
No build was possible (`lake build` forbidden, Mathlib absent), so I verified *what the source says*, not
that it compiles. All verdicts above are "statement + proof script are honest and go the right way",
conditional on elaboration. Two consequences: (i) a name I resolved by grep could in principle resolve to
a different declaration than I assumed; (ii) implicit-argument or instance mismatches would show up only
in a build. I saw no evidence of either.
