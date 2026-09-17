# Worker _sub-read-struct-10 -- READ-ONLY structural audit (NSE @ f9e8bc5)
Files: Euler/PacketSourcePropagator, PacketJoinedGradeBounds, PacketChildLowBounds, CoefficientJetPressureBounds.
No `lake build` attempted (no .olean, pinned toolchain). All claims are source-read + grep.

## 1. Euler/PacketSourcePropagator.lean -- 23 decls, verdict: CLEAN (OK), 1 NOTE
Prop-def `PhysicalGrowth` (PacketSourcePropagator.lean:119-123) is the only new Prop-valued object.

**SUPPLIED, twice, independently (not a P.foo self-loop):**
- `EulerPacketShortTimePhysicalGrowth.physicalGrowth_one_of_short` (Euler/PacketShortTimePhysicalGrowth.lean:40-53)
  concludes `PhysicalGrowth D S (fun _ => 1) 2` from only `hC : 0 <= C`, `hM` (strain op-norm bound on S),
  `hshort : C*D.T <= 1/2`. No `PhysicalGrowth` in its own hypotheses.
- `EulerPacketGeometrySourceGrowth.physicalGrowth_of_geometry` (Euler/PacketGeometrySourceGrowth.lean:47-54)
  concludes `PhysicalGrowth D Omega (growthProfile D G H) (growthConstant G)` from interval/horizon/strain/normal
  transfer identities only. Its constant `growthConstant G = 560*G.Theta^10/G.eps` is proved POSITIVE
  (PacketGeometrySourceGrowth.lean:41-45, `positivity` with `G.epsilon_pos`), so the supplier is non-degenerate.
Consumers `propagator_bound_of_physical` (:127) and `propagator_bound_of_deformation` (:165) are therefore live.

**JUNK-VALUE SWEEP -- this file is a POSITIVE CONTROL (all guards in-signature or structural):**
- `physicalRhs` (:48-50) divides by `||D.normal.field t x||^2`. Not guarded in the def, but guarded
  STRUCTURALLY by the bundled `D : Data U`: `Data.normalLower_pos` (Euler/TransversePacketData.lean:65-66,
  `0 < frameBound^-1^2`) + `Data.normal_lower` (:85-88) give `0 < ||normal||^2`, and the file actually
  discharges it in-proof at PacketSourcePropagator.lean:95-99 (`hnormal : D.normal.field t x != 0`).
  `Data` cannot be degenerate here: fields `inverse_left`/`inverse_right` (TransversePacketData.lean:31-32)
  force `F` invertible and `m0_unit : ||m0|| = 1` (:25) forbids the zero normal direction. So the reflection
  in `physicalRhs` is NOT a `x/0 = 0` collapse.
- Both propagator bounds divide by `g s`: constrained IN THEIR OWN SIGNATURE by `hg : forall t, 0 < g t`
  (:128, :166). NOTE (harmless direction): inside `PhysicalGrowth` itself (:123) `g` is unconstrained, so an
  instantiation with `g s = 0` makes the conclusion `||w t|| <= 0`, i.e. STRONGER, i.e. harder to supply --
  safe direction, and every consumer re-adds `0 < g`.
- `Data.normalLower/frameLower` use `.inv` (TransversePacketData.lean:51-52) but on `1 + ||.||` which is
  provably positive (:54-60). No junk inverse.
**VACUITY:** not vacuous -- `propagator_self` (:60) gives `propagator D s s x v = v`, so the propagator is not
identically 0; the bound at t=s reads `1 <= I*C*F` for nonzero U, real content.
**KERNEL RISK: none.** No `inductive`/`structure`/`decide`/`termination_by`/`deriving`/`.rec`/`Fin.cases`/
metaprogramming. Largest numeral in file: `3` (`3*F^3*C`, :172) besides exponents `2,3` and the `2` at :50/:102.
Benign by inspection.

## 2. Euler/PacketJoinedGradeBounds.lean -- 14 decls, verdict: OK (strong positive result), 0 ESCALATE
New object: `structure GradeGuards : Prop` (PacketJoinedGradeBounds.lean:84-88), fields
`common : L.commonCost <= L.R`, `corrector`, `correctorTime`, `pressureGradient : 3*L.pressureAmplitude <= L.R`.

**SUPPLIED FROM SCRATCH -- and this matters, because `GradeGuards` (the Join/Forward/Primary/Mean twins
together) is one of the most consumed hypotheses in the artifact (>100 hypothesis-position sites, grep).**
- `EulerPacketCommonRadius.commonRadius_guards` (Euler/PacketCommonRadius.lean:172-181) concludes
  `EulerTransversePacketJoin.Budget.GradeGuards (L.enlargeRadius R' hL) (N.enlargeRadius R' hL)` by the
  ANONYMOUS CONSTRUCTOR at :181 (`<hlv.trans h, hlc.trans h, hlct.trans h, hlp.trans h>`), with NO
  `GradeGuards` among its hypotheses. Its inputs are the four nonnegativity/threshold facts from
  `commonRadius_bounds` (:144-168), each proved from `Budget.radius_bounds` / `*_nonneg`.
- `exists_common_radius` (PacketCommonRadius.lean:185-191) closes the existential with the explicit witness
  `R' := commonRadius M L N CB` (:138-142, a finite SUM of the costs), i.e. an EXPLICIT WITNESS, not an
  appeal to satisfiability. Same for the Mean twin (PacketCommonRadius.lean:90-92 is only enlarge, but
  :180 constructs it). Forward/Primary twins get the same treatment in PacketForwardCommonRadius.lean:39-47
  and PacketPrimaryCommonRadius.lean:42-53.
- Distinguish from the NON-supplier `GradeGuards.enlargeRadius` (PacketCommonRadius.lean:106-108): that is
  exactly the `P.foo`-from-`P` shape and supplies nothing; the real supplier is :172/:185.
So `grade_bounds` (:105) and its five projections (:150,:155,:160,:165,:170) are LIVE, not dead.
**Amplitudes are division-free**, so no junk-value channel: `commonCost = velocityCost+derivativeCost`
(TransversePacketNormalBudget.lean:102), `pressureAmplitude = P*pressureCost ...`
(TransversePacketJoinedFullBounds.lean:34), `correctorAmplitude = 27*blockAmplitude^2*(P*commonCost)` (:37),
`correctorTimeAmplitude = 108*...` (:38).
**JUNK-VALUE SWEEP:** the only inverse is `c^-1` in `WordBound.scale_profile` (:35-39); `hc : 0 < c` is in
that theorem's OWN signature (:25 + used in the statement via `smul_profile_pos ... c hc`), and the
cancellation `c^-1*(A*c) = A` (:39) is discharged by `field_simp` under `hc.ne'`. In-signature guard: clean.
Profiles: `hg : forall t, 0 < g t` (:24) is likewise in-signature, so `c . g` is a positive profile
(`smul_profile_pos`, :17-19) -- the "positive scalar factor cancels exactly" claim of the header is real.
**NOTE (not a defect):** `grade_bounds` carries BOTH `F : Field P D.T raw` and `G : Forcing P D raw` over the
same `raw`; `hforce` is stated for `F` and moved to `G.forcingField` by `.transfer` at :121. Redundant but
sound, since `raw` is shared.
**Non-degeneracy of the conclusion:** the output amplitude is the literal `1` (:107-115), not a free
constant that could be 0, so the five grade bounds are not trivially satisfiable by an amplitude collapse.
**KERNEL RISK: none.** `structure GradeGuards : Prop` is non-recursive, no `deriving`, no `decide`, no
`termination_by`, no `.rec`, no metaprogramming. Largest numeral: `6` (`Fin 4`/grade 6); also `3`,`4`. Benign.

## 3. Euler/PacketChildLowBounds.lean -- 10 decls, verdict: OK + 1 NOTE (erw), 0 ESCALATE
New object: Prop-def `SourceErrors` (PacketChildLowBounds.lean:101-111) -- the two source-(20) error bounds
(velocity shear term `ev`, pressure term `ep`) for the normalized packet.

**(1) SUPPLIED, with a CONCRETE non-junk error size, and the chain does not self-loop:**
- In-file `sourceErrors_of_global` (:115-130) concludes `SourceErrors` from the STRICT (`< ev`,`< ep`)
  global bounds, using this file's own rewrite `pressureTerm_eq_coefficient` (:22-29) -- so it is a genuine
  weakening step, not `P.foo` from `P`.
- The strict bounds are actually produced: `EulerParentPacketFrames.exists_geometryJoinedChoice`
  (Euler/ParentGeometryJoinedChoice.lean:46-72) builds the `errors` field of `GeometryJoinedChoice`
  (:38-42) by `intro t x; constructor; ... exact (herror t x).1 / erw [pressureTerm_eq_coefficient]; exact
  (herror t x).2` (:65-72), where `herror` comes from `I.label.joined_uniform_child` (:60). No `SourceErrors`
  hypothesis anywhere in it.
- The supplied error sizes are EXPLICIT and nonzero: `ev = ep = k^(-(1/4 : ℝ))` (ParentGeometryJoinedChoice.lean:42).
  So `SourceErrors` is not instantiated at the degenerate `ev = ep = 0`.
**(2) NON-DEGENERATE WITNESS for the `Guards` record that gates all four main theorems** (variable `G :
Guards hτ hτT F H`, `hball : 1/2 <= G.radius`, PacketChildLowBounds.lean:95): constructed at
`EulerPacketInduction.Stage.joinedGuards` (Euler/PacketStageGuards.lean:48-69) via `geometryGuardsOfStage`.
Its numeric fields are pinned BY `rfl` and are NOT zero: `radius = 1` (PacketStageGuards.lean:71 -- so
`hball : 1/2 <= radius` holds), `delta = spike S.J S.X n` (:73, `S.spike_pos n` at :65), `hchild =
shear S.J S.X n` (:74, with `1 <= shear` via `S.shear_one n` at :66), `CM = gradientConstant`,
`CH = hessianConstant` (:75-76, both `= 8*(1+...)`, PacketLowConstants.lean:14-15). This is the opposite of
the `MeanPacketData` degenerate-witness case: the only witness here has hchild >= 1 and delta > 0, so
`CM+G.hchild*goodRatio+ev` (:141) is a genuinely larger-than-CM bound, not a collapse.
**JUNK-VALUE SWEEP -- guards are STRUCTURAL and reachable from the same signature:**
- `A.ell^-1` (:46,:49,:62,:146,:181): guarded by the `Parent` field `ell_pos`, and the file DISCHARGES it,
  `mul_inv_cancel0 A.ell_pos.ne'` (:51,:64). Clean.
- `hk : k*kappa = 1` (:73) is itself the nondegeneracy certificate: with `hkappa : |kappa| <= 1` (:69)
  allowing `kappa = 0`, `hk` is UNSATISFIABLE at `kappa = 0`, so every theorem carrying `include hk`
  (:75,:132,:167,:201) automatically has `kappa != 0` IN ITS OWN SIGNATURE. Good design, not a defect.
- The good/bad time split `scaledTime tau F.a F.epsilon t` (:136,:171,:222) expands to `(a/eps)*(t-t0)`
  (Euler/PacketPropagationTime.lean:12) -- a DIVISION BY `F.epsilon`. Guarded in-signature through the
  bundled `G : Guards`: `Guards.shear_pos` (Euler/PacketSourceGeometryData.lean:97) gives
  `Guards.epsilon_pos : 0 < P.epsilon` (:130) via `P.epsilon = sqrt (P.a/P.shear)` (:56) and
  `a_pos` from `coupling_lower : 1/2 <= P.a` (:96,:126). So no `x/0 = 0` collapse of the good-time branch.
  Had `epsilon` been unconstrained, `scaledTime = 0` would make `ht : 1 <= scaledTime` false and the
  good-time theorem (:133) vacuous -- so this guard is load-bearing and it IS present.
- `goodRatio = cutoffBound*(64*exp 6)` is proved POSITIVE (PacketGeometryLowBounds.lean:27-29); `badRatio =
  earlyRatio+historyRatio` (:207) only nonneg -- if `badRatio = 0` the whole-horizon bound (:213) merely
  becomes the good-time bound, i.e. sharper, not vacuous.
**NOTE (hygiene, not soundness):** `erw [pressureTerm_eq_coefficient]` at :129 and again at
ParentGeometryJoinedChoice.lean:70 -- `erw` unifies up to reducible defeq, so the two `rankOne` arguments
match only definitionally. Fragile under refactor; no unsoundness.
**KERNEL RISK: none.** No `inductive`/`structure`/`decide`/`deriving`/`termination_by`/`.rec`/`Fin.cases`/
metaprogramming. `by_cases` at :222 is on a real inequality (classical, no `decide`). `nlinarith only [...]`
at :226-236 is proof-side. Largest numeral in the file: `2` (in `2*CM*...`). Benign.

## 4. Euler/CoefficientJetPressureBounds.lean -- 11 decls, verdict: OK + 1 KERNEL-RISK (benign, precise below)
New object: Prop-def `TreeBound` (CoefficientJetPressureBounds.lean:39-42), a RECURSIVE predicate over the
jet tree: `.zero A => A.bound <= B`, `.succ _ lower _ => A.bound <= B /\ forall i, TreeBound (lower i) B`.

**SUPPLIED, and the whole chain is live down to a CONCRETE jet -- this is a base case, not closure-only:**
- In-file supplier `treeBound_of_levels` (:52-66) builds `TreeBound K B` from `hb : forall n <= s,
  boundLevel P K n <= B`. It is a genuine base+step construction (`refine <?_,?_>` at :57), NOT a
  `TreeBound -> TreeBound` algebra. (The `.truncate` (:69) / `.restrict` (:80) / `.root` (:45) lemmas ARE
  the closure-only shape, but the base case exists, so the seven-predicate "closure without a base case"
  pattern does NOT recur here.)
- The single external consumer `EulerCoefficientPath.coefficientJet_restrictedPressure_bound`
  (Euler/CoefficientPathPressureBounds.lean:48-56) discharges it by `apply treeBound_of_levels` (:53) for the
  EXPLICIT jet `coefficientJet P A hA s t`, with concrete `B = sobolevCoefficientAmplitude (Fin 4) b Rc C`.
- That jet is really built at positive order: `EulerCoefficientPath.coefficientJet`
  (Euler/CoefficientPathSmooth.lean:99-110) recurses `| 0 => .zero _ | n+1 => .succ ...` with real
  derivative data (`cylinder_fieldDerivative ...` for `derivative_eq`). A second independent construction at
  order 6 is Euler/CorrectionEnergyData.lean:122. So `CoefficientJet` is NOT populated only by `.zero`, and
  the `s >= 1` branches of every theorem in this file are reachable.
**JUNK-VALUE SWEEP -- clean, but with a NEAR-MISS worth recording:** `pressureCost c B 0 = c^-1` (:20) and
`CoefficientJet.pressureConstant .zero = c^-1` (Euler/EulerProof.lean:3286) are both UNCONSTRAINED in their
definitions. At `c = 0` both sides are junk `0`, so the base case of `TreeBound.pressureConstant_le` (:115),
which is closed by `rw` ALONE (an exact identity `c^-1 <= c^-1`), would survive `c = 0` with both sides junk.
It is not a defect: `hc : 0 < c` is in the OWN signature of every statement -- `pressureCost_nonneg` (:28),
`TreeBound.pressureConstant_le` (:113), and the consumer (CoefficientPathPressureBounds.lean:49). This is the
guarded/positive-control version of the `Kr / K` collapse. `productCost` (:15-17) is division-free.
**KERNEL RISK -- precise, and it is the THIRD flag of the structural block (benign by inspection):**
1. `inductive CoefficientJet` (Euler/EulerProof.lean:3073-3079) -- TYPE-valued (not Prop) inductive FAMILY
   over `N` and `SmoothCoefficient period`; the recursive field is `lower : forall i : Fin 4,
   CoefficientJet directions n (derivatives i)` -- strictly positive, non-nested, index strictly smaller.
   Standard structural recursor, no `deriving`, no reflection. Kernel-safe.
2. `TreeBound` itself (:39-42) is a recursive Prop-def with NO `termination_by`, i.e. structural recursion
   compiled through `CoefficientJet.rec`/`brecOn`; `induction K with` (:54) and `cases K with` (:47,:75,:88,
   :101,:117) use that recursor directly. Benign.
3. `termination_by` (WELL-FOUNDED, not structural) appears in the three imported defs this file rewrites
   with: `CoefficientJet.productConstant` (EulerProof.lean:3196-3202, `termination_by n`),
   `CoefficientJet.pressureConstant` (:3283-3291, `termination_by n`), and `boundLevel` (:4706-4712,
   `termination_by s`). Consequence: those defs do NOT reduce by `rfl`/`decide`, so every use here must go
   through equation lemmas -- and it does (`rw [CoefficientJet.productConstant,productCost]` :103,
   `rw [CoefficientJet.pressureConstant,pressureCost]` :119, `simp only [...]` :99). Correct usage; the
   measure (the N index; `.truncate` lowers `n` by 1 and each `lower i` sits at `n`) is decreasing by
   inspection. Benign, but this is the first `termination_by` seen in the structural block, so it is a new
   flag shape, not a repeat of `Nat.rec` / Type-valued `if`.
4. No `decide`, no `Fin.cases`, no metaprogramming. `productCost`/`pressureCost` (:15-21) are plain `Nat.rec`
   structural recursions.
Largest numeral IN THIS FILE: `8` (:17, `B+8*productCost B q`); also `4` (:21 and `Fin 4`). No big-numeral
arithmetic. (ADJACENT, not in my file: the same jet chain reaches `(9*L)^729` at
Euler/GevreyUniformConstants.lean:83 and `(9*L)^(3^q)` at Euler/H6PressureConstants.lean:187 -- a real
big-exponent site for whoever audits those files; it is symbolic `^`, not a `decide`.)

## Overall
All four files are LIVE and structurally guarded. Every new hypothesis-position object in this block --
`PhysicalGrowth` (PacketSourcePropagator.lean:119), `GradeGuards` (PacketJoinedGradeBounds.lean:84),
`SourceErrors` (PacketChildLowBounds.lean:101), `TreeBound` (CoefficientJetPressureBounds.lean:39) -- has an
identified supplier that does NOT assume it, and in three of the four cases the supplier comes with an
EXPLICIT non-degenerate witness (`commonRadius` sum; `ev = ep = k^(-1/4)` and `Guards.radius = 1`,
`hchild = shear >= 1` by `rfl`; the concrete `coefficientJet`). No vacuity, no unsupplied hypothesis, no junk
denominator that is not constrained in its own signature. 0 ESCALATE.

