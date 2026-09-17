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

## 2. Euler/TransversePacketNormalBudget.lean (109 lines, 15 decls)

VERDICT: CLEAN, and it settles the supplier question for `NormalBudget` POSITIVELY.
1 structure: `NormalBudget D q R` (:18-29, fields `Rc, C, Ri` + 2 nonneg + `inverse_radius`
+ `inverse_bound` + `strain_bound` + `radius`). No Prop-def.

### SUPPLIER (this is the point of the file) — BASE CASE EXISTS
`NormalBudget` is used in HYPOTHESIS position in ~25 files (e.g. PacketJoinedGradeBounds.lean:56,
PacketScalarPressureGrade.lean:84, TransversePacketPrimaryFullBounds.lean:119,
PacketAngularPressureStepBound.lean:22, TransversePacketForwardGradeBounds.lean:20, …), and the two
"defs that produce one" are the NON-supplying `P.foo`-from-`P` shape:
 - `initializedNormalBudget` (PacketInitializedCanonicalRadius.lean:55-57) = `NB.enlargeRadius …`,
   consuming an `NB : NormalBudget D 6 L.R` from its own variable block (:20).
 - `forwardInitializedNormalBudget` (PacketForwardCanonicalRadius.lean:33) — same shape.
 - `NormalBudget.enlargeRadius` itself (PacketCommonRadius.lean:66) — `NormalBudget → NormalBudget`.
BUT there IS a real base case: `EulerPacketParentNormalBudget.sourceNormalBudget`
(PacketParentNormalBudget.lean:56-76, `… where Rc := R; C := amplitude C C₁; Ri := inverseRadius …`),
whose only inputs are a `Data U`, `0 ≤ R/C/C₁`, `hdet : det = 1`, and the two jet bounds
`hF`/`hF₁` (PacketParentNormalBudget.lean:36-40). No `NormalBudget` is assumed. So this is NOT an
unsupplied-hypothesis structure (contrast the seven closure-without-a-base-case predicates).
`Data U` itself has a concrete witness (`firstPacketData`, BasePacketLowBounds.lean:17), so the
chain bottoms out.

### NON-DEGENERACY IS CERTIFIED, NOT ASSUMED (answers shape 3 for this structure)
Could the witness be degenerate (`C = 0`, which would make `inverse_bound`/`strain_bound`
"≤ 0" and hence force the jets to vanish)? NO, and the exclusion is in the supplier's own
signature: `hF 0 t x` gives `‖D.F.field t x‖ ≤ C` (spelled out at PacketParentNormalBudget.lean:45-48),
while `hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1` (:38) forbids `D.F.field t x = 0`
(a zero endomorphism has det 0 ≠ 1). Hence `C > 0` is forced, and the budget amplitude
`amplitude C C₁ = 9*C^2+27*C^2*C₁` (:15) is > 0. Independently, `Data` carries `inverse_left`
/`inverse_right` (MeanPacketData.lean:52-53 for the mean twin), so the frame is invertible and
cannot be 0. This is a *positive control* for shape 3.
Radii are also non-degenerate structurally: `correctorCoefficientRadius R Ri = R+4*Ri+1`
(TransversePacketCoefficientBounds.lean:15) is ≥ 1 whenever `Rc, Ri ≥ 0`, so
`coefficientRadius` (:38) can never be 0.

### Junk-value sweep — GUARDED (a clean positive control)
The only inverse reachable from this file's statements is `c⁻¹` inside
`gramCost c C D = 1 + c⁻¹*(3*C^2+D+1)` (TimeLpGramGevrey.lean:23), instantiated at `c = D.normalLower`
in the `inverse_radius` field (:24) and re-used in `Ri_nonneg` (:35-36). `D.normalLower_pos` is a
FIELD OF `Data`, so positivity travels with `D` in every signature that mentions `D` — it cannot be
dodged (`Ri_nonneg` passes `D.normalLower_pos` explicitly at :36). No `/` appears in any statement
of this file. No unguarded division at all.

### Content check on the two non-trivial theorems
- `pressure_radius` (:64-69): `sobolevCoefficientRadius (Fin 4) (4*N.Ri) ≤ R`. Real content, a
  monotone weakening of the `radius` field: `sobolevCoefficientRadius ι Rc = 4*(max 1 (card ι)*Rc)`
  (ParameterSobolevCoefficient.lean:38) is monotone in `Rc`, and `4*Ri ≤ Rc+4*Ri+1` by
  `N.Rc_nonneg`. Not vacuous, not an identity.
- `coefficient_bounds` (:42-54) is pure delegation to `D.corrector_coefficient_bounds`; the
  `Budget` block (:79-106) proves only nonnegativity of `velocityCost`/`derivativeCost` and the
  two `≤ commonCost` halves (:104-106). Direction safe (all are lower bounds of the form 0 ≤ x).

### Kernel risk
NONE. No `inductive`/`.rec`/`termination_by`/`deriving`/`decide`/`Fin.cases`/Type-valued `if`/
metaprogramming (grep empty). Only `structure NormalBudget` (:18), non-recursive.
LARGEST NUMERAL IN FILE: `18` (:95, inside `sobolevCoefficientAmplitude … (18*L.Ri*L.C₀*L.C₁)`),
then `4` (:64,:67,:91-97) and `3` (:97). All handled by `positivity`, benign by inspection.

TALLY file 2: OK 15 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 3. Euler/MeanPacketBudget.lean (183 lines, 18 decls)

VERDICT: CLEAN with 2 NOTEs. 1 structure: `Budget (D : Data) (q : ℕ) (R : ℝ) extends
SobolevData D (Fin 4) q R` adding only `forcing_one : 1 ≤ Cf` and `forcing_time : sqrt D.T ≤ Cf`
(:26-28).

### SUPPLIER — BASE CASE EXISTS
`EulerMeanPacketProvider.Budget` is supplied by `sourceMeanBudget`
(PacketParentMeanBudget.lean:99), whose variable block (PacketParentMeanBudget.lean:91-97) is a
bare `Data`, `hT : D.T ≤ 1`, `hTi : D.T⁻¹ ≤ Ti`, `hR : 1024 ≤ R`, three nonnegs, `hdet`, and
`hF`/`hF₁`/`hF₂` — no `Budget` input. The other two producers ARE the non-supplying shape
(`initializedMeanBudget` = `LM.enlargeRadius …`, PacketInitializedCanonicalRadius.lean:60-62;
`forwardInitializedMeanBudget`, PacketForwardCanonicalRadius.lean:38). Not an unsupplied structure.

### Non-degeneracy: certified by the parent record, and by a hard numeral floor
- `SobolevData.radius_lower : 1024 ≤ Rc` (MeanPacketSobolevData.lean:33) is a FIELD, so
  `coefficient_radius_nonneg` (:80-81) and `radius_bounds` (:83-87) are not empty statements:
  I re-checked `radius_bounds`, which derives `1 ≤ R` from `inverse_cost_lower : 1 ≤ M` +
  `radius_budget : 2*M*(sobolevCoefficientRadius (Fin 4) Rc+1) ≤ R`; with `M ≥ 1` and the radius
  ≥ 0 this gives `R ≥ 2`. Sound and non-vacuous.
- `pressureGradientCost = 3*sobolevCoefficientAmplitude (Fin 4) q B.Rc B.CF*B.pressureForceCost`
  (:78) would collapse to 0 if `CF = 0`. That is EXCLUDED by the type: `frame_bound`
  (MeanPacketSobolevData.lean:55) at `n = 0` forces `‖D.F.field t x‖ ≤ CF`, and `Data.inverse_left`
  /`inverse_right` (MeanPacketData.lean:52-53) make `D.F.field t x` invertible, hence nonzero.
  So `CF > 0`; the gradient bound is not a disguised `≤ 0`. Positive control for shape 3.
- `D.T_pos : 0 < T` is a field (MeanPacketData.lean:26), used at :95. So `forcing_time`
  (`sqrt D.T ≤ Cf`) is not vacuous, and `forcing_one` gives `Cf ≥ 1` anyway.

### Junk-value sweep — GUARDED via `[Fact (0 < P)]`
Every statement touching an inverse goes through `P⁻¹*sqrt P`: `restore_cylinder_word_bound` (:57-67)
and `physical_word_bounds` (:114-124). In BOTH the period carries `(P : ℝ) [Fact (0 < P)]` in the
signature (:39 for the `Forcing` block, :114 and :132 for the `Budget` block), and the proof uses
`embedding_mean_norm_product` (`sqrt P*(P⁻¹*sqrt P) = 1`, :63-66) which needs it; the positivity is
also consumed at :120-122 (`have hp := (Fact.out : 0 < P); positivity`). If `P = 0` were allowed,
`P⁻¹*sqrt P = 0` and the amplitude `A*C` restoration at :63 would be false, not vacuous — so the
guard is load-bearing AND present. `D.T⁻¹` and `frameLower⁻¹` occur only in the supplier
(PacketParentMeanBudget.lean:102, :137), each guarded by `D.T_pos`/`D.frameLower_pos` fields.
No unguarded division or inverse in this file's statements.

### NOTE 1 — `grade_profile_bounds` (:172-180) is a renaming, plus ℕ-truncated subtraction
The exponent `H₀^(2*p-2)` is NATURAL subtraction, so at `p = 0` and `p = 1` it is `H₀^0 = 1`: the
"grade envelope" silently disappears for the two lowest grades. This is harmless because the SAME
factor appears in the hypothesis `hF` (:175) and in all three conclusions (:176-178); the proof is
literally `three_shift_bounds` with `A := A*H₀^(2*p-2)` and a `mul` re-association
(:179-180). So `p`, `H₀`, `hH₀` add no mathematical content beyond `three_shift_bounds` (:161).
Classification NOTE, not ESCALATE: no false statement, but do not count this as an independent
grade-uniformity result — it is one, reparenthesized.

### NOTE 2 — degenerate-witness inheritance (`Bc = 0, L = 0, r = 0`)
`Data` carries `Be, Bc, L, r, K` with `L_lower : boundaryLocalizationC1*Bc ≤ L`, `r_le_quarter`,
`core_lower`/`exterior_lower` (MeanPacketData.lean:39-51). The known base witness has
`Bc = 0, L = 0, r = 0` by `rfl` (BaseEulerState.lean:57-63, `initialLowBounds_values`), which makes
`core_lower` range over the EMPTY set `‖ℓ•x‖ < 0` and `exterior_lower` range over ALL `x`.
IMPORTANT SCOPING RESULT FOR THIS FILE: none of the 10 in-cone theorems here mentions
`Be/Bc/L/r/K`. `L` enters only through `scaledBoundaryOperatorAmplitude D.L` inside the inherited
`operator_budget`/`forcing_budget` fields (MeanPacketSobolevData.lean:38-46), where `L = 0` makes
the budget EASIER to satisfy but leaves the conclusions (word bounds on velocity, time derivative,
and pressure gradient) with full content, since those are governed by `Rc ≥ 1024`, `CF`, `CF₁`, `Cf`.
So the `Bc = L = r = 0` degeneracy does NOT propagate into this file's statements. Flagging it only
so the cross-file ledger stays consistent.

### Kernel risk
NONE. No `inductive`/`.rec`/`termination_by`/`deriving`/`decide`/`Fin.cases`/Type-valued `if`/
metaprogramming (grep empty). One `structure Budget … extends SobolevData` (:26) — flat extension,
non-recursive. LARGEST NUMERAL IN FILE: `1024` (:81, `(by norm_num : (0:ℝ) ≤ 1024)`), then `6` and
`3`. `norm_num` on `0 ≤ 1024` over ℝ is benign; no `decide`, no big-numeral integer arithmetic.

TALLY file 3: OK 16 / NOTE 2 (`grade_profile_bounds` :172 is a renaming of :161;
`Bc=L=r=0` witness inheritance, non-propagating) / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.
