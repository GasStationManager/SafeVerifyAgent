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

