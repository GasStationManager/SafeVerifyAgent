# _sub-read-struct-9 — structural read: LoopMoments, TransversePacketNormalBudget, MeanPacketBudget, StressAlgebra
Repo /home/gsm/.openclaw/workspace/repos/NSE @ f9e8bc5. READ-ONLY, no build (no .olean). Every claim file:line.

## 1. NavierStokes/LoopMoments.lean (315 lines, 41 decls)

VERDICT: essentially CLEAN, and a useful POSITIVE CONTROL for both the junk-value and
witness sweeps. 1 structure (`TwoPoint`, LoopMoments.lean:200-204), 1 Prop-def
(`TwoPoint.IsProbability`, :212).

### Witness / supplier check (structure is CONSTRUCTED, twice, non-degenerately)
- `TwoPoint` is built by `symmetricPair` (:216-217, fields `1/2, 1/2, m-√V, m+√V`) and by
  `oneSidedPair` (:235-237). Both are *parametric* families, not one frozen witness, so the
  "one degenerate witness" shape does NOT apply here.
- `IsProbability` is CONCLUDED without being assumed: `symmetricPair_probability` (:219) and
  `oneSidedPair_probability` (:244). Genuine suppliers exist. This is what the closure-without-
  a-base-case files are missing.
- I re-derived both witnesses by hand and they are CORRECT, not junk-value artefacts. With
  W=V·p², D=d²: mean = m + (−W·d/p + D·V·p/d)/(D+W) = m (matches :252), and
  centeredSecond = (V·d² + V²p²)/(d²+Vp²) = V (matches :259). So `oneSidedPair_variance` has real
  content; it is not true "because everything is 0".

### Junk-value sweep (in-signature guards) — mostly GUARDED, one unguarded-but-harmless
- `phaseDensity a v t = a*(1+t^2)/v` (:100) divides by `v`. Every theorem using it carries
  `hv : v ≠ 0` IN ITS OWN SIGNATURE: :114, :126, :131, :137-138, :155-156, :168-169. In
  `rephased_moments` (:181-196) `v ≠ 0` is *derived* in-proof from `0 < a`, `0 ≤ ρ` and
  `hspeed` (:189-192) — i.e. the nonzeroness is certified by the type, shape-3 clean.
- `loopA v t = v/(1+t^2)` (:103), `loopC` (:106): denominator `1+t^2 > 0` proved
  unconditionally at :108. No junk-value channel at all.
- `energy_moment` (:73) has `ha : a ≠ 0` and `hvar : … = ρ/a` in the same signature (:74,:76);
  `required_variance_nonneg` (:90) strengthens to `0 < a` (:91). Both guarded.
- ONE unguarded division: `oneSidedPair_upper_projection` (:272-275) states
  `p * (rightValue − m) = V*p^2/d` with NO hypothesis on `d` or `p`. It is an EXACT identity, so
  this is the shape flagged in the brief — but here it is a FALSE POSITIVE: the identity
  `p*(V*p*d⁻¹) = V*p²*d⁻¹` is valid in a `DivisionRing` for every `d`, including `d = 0`, so the
  theorem is true with content, not by conspiracy. Its only caller supplies `0 < d`
  (:290 `hd : 0 < d`, used at :297). Contrast the twin `oneSidedPair_lower_projection` (:267)
  which DOES need `hp : p ≠ 0` and states it. Classification: NOTE, not ESCALATE.
- NOTE (shape-6 near-miss, benign direction): `oneSidedPair_mean` (:252) and
  `_variance` (:259) both take `hp : p ≠ 0`, `hd : 0 < d`, `hV : 0 ≤ V`; `hV` is genuinely needed
  (denominator positivity) so this is not an unused-strong-hypothesis instance.

### Vacuity / joint satisfiability — EXHIBITED WITNESS
`exists_projected_twoPoint` (:281-300) is the capstone. Hypotheses `2 < p₁ + p₂*m`, `0 ≤ V`.
WITNESS: p₁ = 3, p₂ = 1, m = 0, V = 1 ⟹ p₁+p₂m = 3 > 2 ✓, V ≥ 0 ✓. Then d = (3+0−2)/2 = 1/2 > 0,
`oneSidedPair 0 1 (1/2) 1` = ⟨1/(1/4+1)=4/5, (1/4)/(5/4)=1/5, 0−1/2 = −1/2, 0+1/(1/2)=2⟩;
weights 4/5+1/5 = 1 ✓, mean = 4/5·(−1/2)+1/5·2 = −2/5+2/5 = 0 ✓,
centeredSecond = 4/5·1/4 + 1/5·4 = 1/5+4/5 = 1 = V ✓, projections 3+(−1/2) = 5/2 > 2 ✓ and
3+2 = 5 > 2 ✓. All five conclusions hold simultaneously with V ≠ 0. NOT vacuous.
Also non-vacuous in the p₂ = 0 branch (:285-288) via `symmetricPair`.
`corrected_speed_bounds` (:304) is satisfiable at ζ = 1/2, v₀ = 0, vstar = 1. OK.

### Reachability NOTE (dead-weight, not a defect)
Cross-file grep: `TwoPoint`, `symmetricPair`, `oneSidedPair`, `exists_projected_twoPoint`,
`rephased_moments`, `corrected_speed_bounds`, and the whole `avg` family (:30-97) appear NOWHERE
outside this file. (The `avg` hits elsewhere are an unrelated homonym,
`LiftedMeanResidual.avg`, LiftedMeanResidual.lean:119.) Only `phaseDensity`/`loopA`/`loopC`/
`one_add_sq_pos`/`phaseDensity_pos` are consumed downstream (SmoothLoop.lean:198-204, :484-486,
:521-528; TrueConeLoop.lean:359-368, :585-599). LoopVariance.lean:882 explicitly calls itself
"the actual periodic analogue of `LoopMoments.exists_projected_twoPoint`", i.e. the finite
two-point block here is SUPERSEDED scaffolding. Direction is safe: it proves *more* than needed.
The file's own docstring is honest about scope (:10-17: "no existence, smoothness, or
invertibility of a circle reparametrization is asserted here").

### Kernel risk
NONE. No `inductive`, no `.rec`/`Nat.rec`/`Acc.rec`, no `termination_by`, no `deriving`, no
`decide`, no `Fin.cases`, no Type-valued `if`, no metaprogramming (grep over the file is empty).
Only `structure TwoPoint` (:200), non-recursive, 4 real fields — benign by inspection.
LARGEST NUMERAL IN FILE: `2` (:213 `= 1`, :282 `2 < p₁ + p₂*m`, :217 `1/2`, exponents `^2`).
No big-numeral arithmetic.

TALLY file 1: OK 38 / NOTE 3 (`oneSidedPair_upper_projection` :272 unguarded exact identity;
dead-weight TwoPoint block; superseded-by-LoopVariance:882) / UNCLEAR 0 / ESCALATE 0 /
KERNEL-RISK 0.
