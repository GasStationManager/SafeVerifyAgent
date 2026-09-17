# Worker: structural tail 4 (NSE @ f9e8bc5) -- READ-ONLY

## 1. Euler/PacketKnownPieceBounds.lean (72 lines, 3 decls, 1 structure) -- CLEAN

- Declares `structure PrefixBound (F : PrefixFields P T p a) (hT) (S : Scales ...) (R) : Prop`
  (`:15-22`): three fields `high` (`:17`, needs `1 <= i`), `mean` (`:19`, needs `2 <= i`),
  `corrector` (`:21`, needs `1 <= i`), each a `WordBound 6 R 1 <shift>` on the normalized field.
- CONSTRUCTED (not an unsupplied hypothesis): `ProfileBudget.prefixBound`
  `Euler/PacketProfileBudget.lean:42` (`... : PrefixBound (ProfileRegularity.prefixFields G) hT S R where`)
  and `prefixThrough_bound` `Euler/PacketProfileTailGrade.lean:19`. Also built inline as an
  anonymous witness on live paths: `Euler/PacketAngularPressureStepBound.lean:44`,
  `Euler/PacketJoinedStepBudget.lean:46`, `Euler/PacketForwardStepBudget.lean:45`,
  `Euler/PacketMeanPressureStepBound.lean:35`, `Euler/PacketForwardPressureBudgets.lean:44`.
  Consumed by ~9 files (PacketKnownTermBounds/PacketForcingBounds/PacketTail*).
- Both theorems here (`piece :31`, `pieceJet :67`) do conclude a NEW fact from `B`
  (a per-`KnownPiece` bound, incl. the inactive branch), so they are not `P.foo : P -> P`.
- Index bookkeeping re-derived and it is sound: `KnownPiece.active` is
  `high: 1<=i /\ i<p`, `mean: 2<=i /\ i<p`, `corrector: 2<=i /\ i<=p`
  (`Euler/PacketKnownPieces.lean:26-31`); `piece` feeds `hi.2/hi.1` into the matching field, and the
  corrector branch's `i-1 < p`, `1 <= i-1` (`:52-53`) follow from `2<=i /\ i<=p`.
  The `mean` field's `2 <= i` (vs `1 <= i` for the other two) is NOT a stronger-than-needed twin: the
  mean piece is genuinely inactive at `i<2` because `(a 1).mean = 0` on the live path
  (`Euler/PacketProfileTailGrade.lean:29`, `Euler/PacketKnownPieces.lean:64`).
- INACTIVE branch (`:61-65`) proves the bound from `raw = 0` via
  `Field.wordBound_normalized_of_zero`. This is a genuine zero-field case, but it is the honest
  content of the statement (the piece really is 0 off its index window), not a vacuity defect.
- JUNK-VALUE SWEEP: the only inverses are `(S.high i _)⁻¹` / `(S.mean i _)⁻¹` (`:40,48,58`), and they
  sit inside a `normalized hT (S.high i) (S.high_pos i)` call whose positivity proof is a FIELD of the
  `Scales` structure passed in the SAME signature (`Euler/PacketKnownPieceScales.lean:32-37`).
  In-signature guard => POSITIVE CONTROL, no degeneration. No `/` in any statement.
- KERNEL RISK: none in this file. Largest numeral = `6` (`:18`). No `decide`, no `termination_by`,
  no `Acc.rec`, no metaprogramming. (Imported `inductive KnownPiece ... deriving DecidableEq`,
  3 nullary constructors, `Euler/PacketKnownPieces.lean:14-18`, plus a `VectorField`-valued
  `if k.active p i` at `:40`; both benign by inspection and both outside my files.)
- Verdict: 3/3 OK.

## 2. Euler/MeanOperatorReflection.lean (60 lines, 11 decls, 1 Prop-def) -- CLEAN

- Prop-def `ReflectionInvariant (A : L2 ->L[R] L2) : Prop := forall u, A (reflection u) = reflection (A u)`
  (`:30-31`). Two theorems: `timeMultiplier_reflection :33`, `frameMultiplier_reflection :44`.
- NOT an unsupplied hypothesis. It is CONCLUDED without assuming itself at
  `Euler/MeanPacketReflection.lean:33-35` `multiplier_reflection_of_even (A : Field) (hA : forall x, A (-x) = A x) : ReflectionInvariant (multiplier A)`.
  The supplier's `hA` is discharged from a constructed structure: `EvenData` fields
  (`Euler/MeanPacketReflection.lean:26-31`) instantiated at `Euler/ParentPacketParity.lean:89`
  (`meanEvenData (H : LowBounds A) : EvenData (A.meanData H) where`), used at
  `Euler/ParentPacketCorrectionParity.lean:32,43`. So the chain reaches a real witness.
- Both theorems are consumed: `Euler/MeanFixedReflection.lean:76` (timeMultiplier) and
  `:43,:45` (frameMultiplier). Not dead.
- The other 9 decls are `private local instance : ... := inferInstance` re-exports (`:21-28`);
  no new axioms, no `Classical` junk, nothing Type-valued conditional.
- JUNK-VALUE SWEEP: no `/`, no `⁻¹` anywhere in the file. The statements are EXACT identities, but
  they are equalities of `Lp` elements under an assumed operator hypothesis, not quotients; there is
  no denominator that could silently be 0. `T` is only assumed `0 <= T` (`:33,:44`), and at `T = 0`
  the identity is still a genuine (if degenerate) claim on the one-point interval -- but a positive `T`
  is supplied by callers (`MeanFixedReflection`, ultimately `D.T_pos`), so not a vacuity.
- KERNEL RISK: none. No numerals at all except `0`/`1` indices. No `inductive`, `.rec`, `decide`,
  `deriving`, `termination_by`, metaprogramming.
- Verdict: 11/11 OK.

## 3. Euler/TransversePacketPrimaryBudget.lean (89 lines, 5 decls, 1 structure) -- CLEAN (one NOTE)

- Declares `structure Budget` (`:27-43`) in `EulerTransversePacketPrimary`: FOUR guard fields, each of
  shape `<explicit cost polynomial> <= L.R`: `history_weak :28`, `history_strong :31`,
  `history_uniform :35`, `forward_radius :40`. Auto-bound section variables (`:22-25`) put
  `D`, `tau`, `htau : 0 < tau`, `htauT : tau < D.T`, `B`, `iota`, `q`, and `L : EulerTransversePacketJoin.Budget ...`
  into the signature.
- CONSTRUCTED: `Euler/TransversePacketPrimaryRadius.lean:55-60` (built by taking a `max` of the four
  costs, so the witness is real, not vacuous) and re-derived at `:69-72` (`enlargeRadius`, monotone in
  `R`); reached on the live initialized path at `Euler/PacketInitializedCanonicalRadius.lean:50`
  (`initializedPrimaryBudget : EulerTransversePacketPrimary.Budget ...`).
- ALL FOUR fields are consumed: `history_weak/strong/uniform` inside this file at `:73-75`
  (feeding `EndpointBudget.weak_radius/strong_radius/uniform_radius`), and `forward_radius` externally at
  `Euler/TransversePacketPrimaryUnitBounds.lean:73` and `:97`. No dead field, no
  stronger-hypothesis-next-to-weaker-twin.
- NOTE (checked, benign -- a `*0` inside a guard). `forward_radius :40-43` passes
  `(forcingCost iota q L.Ri L.C0*0)` -- literally `0` -- into the `D` (forcing-data) slot of
  `forwardSobolevCost iota q T C A D CB Rc` (`Euler/LinearDuhamelSobolevGevrey.lean:27-29`, where `D`
  occurs only in the `+C*T*D` summand). So the guard is the ZERO-FORCING specialization and the
  `L.Ri, L.C0` written in that slot are inert. Likewise `derivativeCost :79` uses
  `physicalCost iota q L.Ri L.C0 L.C1 0 1` (`Df := 0`, `Da := 1`;
  `Euler/SourceCylinderTimeBounds.lean:66-68`). This is NOT a silent junk default: the consumer really
  does run a ZERO forcing and discharges the matching hypothesis explicitly --
  `Euler/TransversePacketPrimaryUnitBounds.lean:57-61` and `:83-87` prove
  `hf : block ... (forcingPath (zeroForcing ...)) j 0 <= 0*majorant L.R (d+2) j` from
  `zeroForcing`, then apply `source_velocity_normalized_bound`/`source_derivative_normalized_bound` with
  the `Df := 0` argument (`:70`, `:96`). The docstring `:5-9` states this intent ("use only the unit
  terminal-data cost, never the terminal amplitude"). So the `*0` is a shape-matched instantiation and
  the guard is honestly weaker exactly where the forcing is honestly absent.
- JUNK-VALUE SWEEP: the only inverse is `tau^-1` (`:41`, and inside `traceCost tau = tau^-1*sqrt tau+2*sqrt tau`,
  `Euler/FixedEvolutionSobolev.lean:27`). `htau : 0 < tau` is auto-bound into the SAME signature
  (used by `D.initial tau htau hTT.le` at `:29`), so this is an in-signature guard => POSITIVE CONTROL.
  No `/` anywhere. `L.C`, `L.Rc`, `L.C0`, `L.C1`, `L.CH` are never inverted, only multiplied, and each
  carries a `_nonneg` field of `L` (used at `:55-58`).
- Note the structure is not `: Prop`-annotated (`:27`), i.e. it is a `Type`-valued record of four
  inequality proofs. Harmless (all fields are Props, so it is a subsingleton in practice), but it does
  mean `Budget` lives in `Type`; no `Type`-valued `if` and no proof-irrelevance is relied on.
- KERNEL RISK: none. Largest numeral = `18` (`:43`); others `1,2,3,4`. No `inductive`, `.rec`,
  `decide`, `deriving`, `termination_by`, `Fin.cases`, metaprogramming. `positivity` at `:86` is the
  only automation and it closes a nonnegativity goal from context hypotheses (`:82-83`).
- Verdict: 5/5 OK (1 NOTE).

## 4. Euler/ParentPacketJoinedInput.lean (91 lines, 6 decls, 1 structure) -- CLEAN

- Declares `structure JoinedInputs (M) (D) (tau) (htau) (htauT) (H)` (`:19-23`): three fields
  `linear : EulerTransversePacketJoin.Budget D tau htau htauT H (Fin 4) 6`,
  `normal : NormalBudget D 6 linear.R`, `mean : EulerMeanPacketProvider.Budget M 6 linear.R`.
  The dependence of fields 2 and 3 on `linear.R` is exactly the "one common radius" claim of the
  header, and it is enforced by the TYPE, not by a side hypothesis -- good non-degeneracy-by-type.
- CONSTRUCTED here at `:74-88` (`joinedInputs`): builds `A` (`joinedRaw :62`), `N` (`normalBudget`),
  `M` (`meanBudget`), sets `Rc := max A.R (max Rn Rm)` (`:84`) and enlarges all three to `Rc`
  (`:86-88`). The three `enlargeRadius` proofs are the correct ones
  (`A.R <= Rc`, `Rn <= max Rn Rm <= Rc`, `Rm <= max Rn Rm <= Rc`). Consumed on the live path:
  `Euler/ParentPacketGeometryInput.lean:29`, `Euler/ParentPacketChildChoice.lean:30,71`,
  `Euler/ParentUniformJoinedChild.lean:22,72`, `Euler/ParentInitializedRadiusPolynomial.lean:135`.
  So: not an unsupplied hypothesis, and the witness is not the trivial one.
- JUNK-VALUE SWEEP: `tau^-1 <= Ti` (`:54`) is guarded by `htau : 0 < tau` in the SAME variable block
  (`:53`); `G.T^-1 <= TiTotal` (`:74`) is guarded because `htauT : tau < G.T` with `0 < tau` forces
  `0 < G.T` in the same signature (and `G.T_pos` is a field of `Parent`, used at `:43`).
  `hOmegaball : forall x in Omega, ||x|| <= 1/2` (`:58`) is a literal, no denominator.
  In-signature guards throughout => POSITIVE CONTROL.
- One thing I checked and it is fine: `Omega` is an ARBITRARY set here (`:57-58`), so `Omega = {}`
  would make `hOmegaball` trivial -- but then `hsub : S <= Omega` forces `S = {}`. This cannot silently
  degenerate the artifact because the live caller passes a real neighbourhood:
  `Euler/ParentPacketGeometryInput.lean:24-32` threads `Omega` through, and the fixed choice used by the
  physical-growth machinery is `halfBall = {x | ||x|| <= 1/2}` (`Euler/PacketParentPhysicalBudgets.lean:22`,
  discharged by `norm_num` at `Euler/PacketStageInputs.lean:56,124` and `subset_halfBall` at `:60`),
  which is nonempty. So a NON-degenerate witness exists.
- `omit [CompleteSpace U] in` before `secondInitial :35` and `secondInitial_derivative :39`: legitimate
  hypothesis hygiene, not a weakening.
- KERNEL RISK: none. Largest numeral = `6` (`:21-23`, the fixed base order); `4` appears only as `Fin 4`
  (n = 4, far below the 22 threshold). No `inductive`, `.rec`, `decide`, `deriving`, `termination_by`,
  metaprogramming.
- Verdict: 6/6 OK.

## 5. Euler/ParentHomogeneousPacketLowBounds.lean (109 lines, 3 decls, 1 Prop-def) -- CLEAN, one NOTE (dead helper)

- Prop-def `HomogeneousSourceErrors (ev ep : ℝ) : Prop` (`:35-45`): a pointwise pair of bounds
  (`||fderiv normalizedPacketVelocity - shearTerm ...|| <= ev` and the pressure analogue `<= ep`).
- IS IT CONSTRUCTED? YES, on the live path -- but NOT through this file's own helper.
  * The helper `homogeneousSourceErrors_of_global :49-64` does conclude it WITHOUT assuming it
    (it assumes the strict-inequality version `herr` and takes `.le`, plus one rewrite
    `forwardPressureTerm_eq_coefficient :63`). So the predicate is not an unsupplied hypothesis.
  * NOTE / dead code: `homogeneousSourceErrors_of_global` has ZERO call sites artifact-wide
    (grep: only its own definition line). The live construction is an INLINE duplicate of the same
    argument at `Euler/BaseFirstPacketChoice.lean:70-84` (`refine <<hn,Q,...,?_>>; intro t x; constructor`,
    discharging both halves from `herror` obtained from `forward_uniform_child :65-68`, and using the
    same `forwardPressureTerm_eq_coefficient` rewrite at `:80-83`). Same again in
    `Euler/BaseFirstPacketChoiceNoOptions.lean:81`. So the predicate is supplied; only this file's
    convenience lemma is orphaned. Harmless, but it is a real "written and never used" decl.
  * Consumers of the predicate: field `errors` of `FirstPacketChoice` (`Euler/BaseFirstPacketChoice.lean:45`,
    `Euler/BaseFirstPacketChoiceNoOptions.lean:81`), hypothesis at `Euler/ParentFirstPacketLowGuards.lean:40`,
    `Euler/BaseFirstPacket.lean:56`, and `herr` of `exactHomogeneousPacket_low_bounds :69`.
  * The live witness is NON-degenerate in the interesting sense: `ev = ep = k^(-(1/4 : R))`
    (`Euler/BaseFirstPacketChoice.lean:48,53` and `:96-102`), i.e. a small but strictly POSITIVE error,
    not 0.
- Main theorem `exactHomogeneousPacket_low_bounds :67-107` is LIVE: used at
  `Euler/ParentFirstPacketLowGuards.lean:74`, `Euler/BaseFirstPacketEvolution.lean:85`,
  `Euler/BaseFirstPacketEvolutionNoOptions.lean:118`.
- VACUITY CHECK on the constant that carries the whole content: the bounds are
  `CM+hchild*firstRatio+ev`, `CH+2*CM*(hchild*firstRatio)+ep`,
  `(Kupper+2*CM*delta*(hchild*firstRatio)+ep)*||z||^2` (`:82-86`), and the hypothesis `hsize :82` is
  `||normal.field|| * ||canonicalVelocity|| <= firstRatio` (`:70-72`). If `firstRatio` were 0 this would
  force the product to vanish and the theorem would be near-vacuous. It is NOT:
  `firstRatio = 4*cutoffBound` with `firstRatio_pos : 0 < firstRatio`
  (`Euler/PacketFirstLowBounds.lean:17-19`), and `hsize` is discharged by a real unconditional lemma
  `Euler/PacketFirstLowBounds.lean:68-77` (`||D.normal.field t x||*||canonicalVelocity D xi t x|| <= firstRatio`).
  So the hypothesis set is genuinely satisfiable and the content is a real bound.
- NON-DEGENERACY CERTIFIED BY A HYPOTHESIS (nice case, opposite of shape 3): the section carries
  `{kappa : R} {hkappa : |kappa| <= 1}` and `(k : R) (hk : k*kappa = 1)` (`:24,:28`). `hk` RULES OUT
  `kappa = 0` (and forces `1 <= |k|`), and `hk` is explicitly `include`d in the main theorem (`:66`).
  So the reciprocal pair cannot collapse.
- `hhchild : 0 <= hchild` (`:30`) does admit `hchild = 0`, which would drop the shear contribution
  (`shearTerm (delta*0)`). Direction-safe (the bound stays a true bound), and the live caller supplies
  `0 < hchild` (`Euler/BaseFirstPacketChoice.lean:53`, `Euler/ParentFirstPacketLowGuards.lean`), so a
  non-degenerate instantiation exists. NOT an escalation.
- JUNK-VALUE SWEEP: the only inverse-like term is `A.ell^-1 . x` at `:87-88`, and it occurs ONLY inside
  the proof, never in a statement; `A.ell` is positive by the `ell_pos` field of `Parent`
  (used e.g. at `Euler/ParentPacketJoinedInput.lean:67` as `G.ell_pos.le`), which travels inside
  `A : Parent` in the SAME signature. `E.inverse` is a named record field, not a Mathlib `Inv`, so it is
  not a junk-value channel. No `/` in any statement. POSITIVE CONTROL.
- KERNEL RISK: none. Largest numeral = `2` (`:84,:86`); `^2` on `||z||`. No `inductive`, `.rec`,
  `decide`, `deriving`, `termination_by`, `Fin.cases`, metaprogramming. `erw` at `:63` is the only
  fragile tactic and it is proof-side.
- Verdict: 3/3 OK (1 NOTE: `homogeneousSourceErrors_of_global` is never called).

## 6. Euler/MeanPacketSobolevData.lean (116 lines, 5 decls, 1 structure) -- CLEAN (guards all in-signature)

- Declares `structure SobolevData (D : Data) (iota) [Fintype iota] (q : N) (R : R)` (`:24-62`):
  7 real fields (`Rc, M, CF, CF1, CH, CM, Cf`), `radius_lower : 1024 <= Rc`, `inverse_cost_lower : 1 <= M`,
  five `_nonneg`s, five explicit budget inequalities (`:39-54`) and four coefficient-derivative bounds
  (`:55-62`). One theorem, `normalized_bounds :81`, which just feeds all fields into
  `EulerMeanSourceTimeSobolev.source_strong_time_block_bounds` and
  `EulerMeanSourcePressureSobolev.source_pressure_block_bounds`.
- CONSTRUCTED. `EulerMeanPacketProvider.Budget D q R extends SobolevData D (Fin 4) q R`
  (`Euler/MeanPacketBudget.lean:26`), and that is built for real by
  `EulerPacketParentLabelBudgets.meanBudget` (`Euler/PacketParentLabelBudgets.lean:80-102`) via
  `EulerPacketParentMeanBudget.sourceMeanBudget`, plus the radius-enlargement rebuild at
  `Euler/PacketCommonRadius.lean:17` (`toSobolevData := { M.toSobolevData with ... }`) and the live use in
  my file 4 (`Euler/ParentPacketJoinedInput.lean:79,88`). NOT an unsupplied hypothesis.
- DEGENERATE-WITNESS CHECK (the one that matters here). The live witness's numeric fields are
  `Rc := coefficientRadius K = max 1024 (4*K)`, `CF := frameAmplitude K = 1+embeddingCost*K^2`,
  `CF1 = CH := gradientAmplitude K = embeddingCost*K^2` (`Euler/PacketParentLabelCoefficients.lean:17-19`).
  So `Rc >= 1024 > 0` and `CF >= 1 > 0` ALWAYS -- the witness is never the all-zero record.
  Only `CF1 = CH = 0` at `K = 0`, which would force `D.F1`/`D.H` derivatives to vanish; the live label
  constant is `K = k^80` (`Euler/BaseFirstPacketChoice.lean:41`, `label_constant : labels.K = k^80`) with
  `k` large, so a NON-degenerate witness exists. NOTE only, not an escalation.
- JUNK-VALUE SWEEP -- this file is the sharpest positive control in my block. `operator_budget :39-42`
  and `forcing_budget :43-46` both INVERT a coercivity: `(sourceFixedCoercivity D.T D.F D.F1 D.opInv)^-1`.
  That inverse is NOT guarded by a hypothesis in the signature -- it is guarded by a THEOREM:
  `sourceFixedCoercivity_pos : 0 < sourceFixedCoercivity T F F1 FInv`
  (`Euler/MeanSourceFixedInverse.lean:57`), whose only side condition `0 <= T` comes from
  `D.T_pos` (a field of `D : Data`, used in this file at `:94,:101`). So the quantity is provably
  positive for EVERY `D` and the `x^-1 = 0` junk branch is unreachable -- strictly better than a
  hypothesis guard. Confirmed used that way at `Euler/PacketParentMeanBudget.lean:112-113`
  (`inv_nonneg.mpr (sourceFixedCoercivity_pos ...).le`). No `/` in any statement of this file.
- KERNEL RISK: largest numeral = `1024` (`:32`), and it appears only inside the real inequality
  `1024 <= Rc` -- no `decide`, no `Nat` literal arithmetic, nothing evaluated. Other numerals `1,2,3,6`.
  No `inductive`, `.rec`, `deriving`, `termination_by`, `Fin.cases`, metaprogramming. `Fin 4` is the
  only `Fin` (n = 4).
- Verdict: 5/5 OK.

## 7. Euler/EulerCorrectionLocal.lean (78 lines, 8 decls, 2 structures) -- 1 NOTE (kappa/direction not certified by the type)

- Declares `structure CoefficientPath (q) (T) [TopologicalSpace T]` (`:22-25`) and
  `structure CorrectionData (q) (T)` (`:33-45`), plus `CoefficientPath.operatorPath :28`,
  `CorrectionData.coefficients :48`, `CorrectionData.source_gradient_zero :57`, and
  `exists_local_euler_correction :66`.
- BOTH STRUCTURES ARE CONSTRUCTED. `CorrectionData` is produced by
  `EulerAllOrderCorrectionData.Data.atOrder` (`Euler/AllOrderCorrectionData.lean:75-88`), and `Data` has
  two independent witnesses:
  (a) `EulerConstantCorrection.data` (`Euler/ConstantCorrectionData.lean:104-121`): `kappa := 1`,
      `direction := 0`, `coercivity := 1`, identity metric, `linear = quadratic = 0`;
  (b) `EulerPacketCorrectionCoefficients.correctionData` (`Euler/PacketCorrectionSourceData.lean:17-31`):
      `kappa := kappa` (any `|kappa| <= 1`), `direction := D.m0` with
      `direction_bound := D.m0_unit.le`, i.e. a UNIT direction, `coercivity := D.normalLower` positive.
  `CoefficientPath` is constructed inside both (e.g. `metricTower`/`tower`,
  `Euler/ConstantCorrectionData.lean:99-102`). So no unsupplied hypothesis.
- NOTE, and it is the closest thing in my eight files to the "exact identity that collapses" pattern.
  `CorrectionData` constrains the two frequency parameters only by
  `scale_bound : |kappa| <= 1` (`:36`) and `direction_bound : ||direction|| <= 1` (`:37`).
  Both therefore ADMIT `kappa = 0` and `direction = 0` simultaneously. I re-derived what happens then:
  `liftedGradient kappa m phi x = toLp (fun i => kappa * d_{y_i} phi + m i * d_theta phi)`
  (`Euler/EulerProof.lean:1127-1131`), so at `kappa = 0 AND m = 0` every generator is 0, hence
  `gradientSpace = (span {0}).topologicalClosure = bot` (`Euler/EulerProof.lean:1265-1267`),
  hence `gradientProjection = bot.starProjection = 0` (`:1277-1278`) and
  `divergenceFreeSpace = bot.orthogonal = top` (`:1340-1341`). Consequences at that degenerate point:
  * `CorrectionData.source_gradient_zero :57-59` -- an EXACT identity `gradientProjection ... = 0` --
    becomes `0 = 0`;
  * the third conjunct of `exists_local_euler_correction :71`
    (`value (e t) in divergenceFreeSpace period D.kappa D.direction`) becomes trivially true.
  NEITHER theorem's own signature rules this out. WHY THIS IS ONLY A NOTE: the guard exists one layer
  up, at BOTH constructors, and neither is degenerate -- witness (a) has `kappa = 1 =/= 0` (so the
  `kappa * grad_y` generators survive), witness (b) has `||direction|| = 1 =/= 0` (so the `d_theta`
  generators survive). And on the packet path `kappa` additionally satisfies `k*kappa = 1`
  (`Euler/ParentHomogeneousPacketLowBounds.lean:28`, `Euler/CommonPressureRepresentative.lean:80`
  `hk : k * A.kappa = 1`), which is an explicit in-signature `kappa =/= 0` certificate.
  So: a real shape-3 instance, direction-safe, non-degenerate alternative present at both witnesses.
  The remaining content of `exists_local_euler_correction` (a Duhamel fixed point with `e 0 = 0`,
  `||e|| <= 1`, `T > 0`) is NOT vacuous even at the degenerate parameters.
- Good non-degeneracy that IS certified by the type: `coercivity_pos : 0 < coercivity` (`:40`), which is
  what the metric coercivity `metric_pos :41` needs.
- JUNK-VALUE SWEEP: no `/` and no `^-1` anywhere in this file's statements. `hnu : 0 < nu` and
  `hS : 0 < S` are in-signature (`:66-67`), `hT : 0 < T` is produced by the theorem (`:68`).
- KERNEL RISK: none. Largest numeral = `6` (`:49,:58,:66`, the `6 <= q` order threshold); `Fin 3`
  (`:43`, n = 3) and `Vector3`. No `inductive`, `.rec`, `decide`, `deriving`, `termination_by`,
  `Fin.cases`, metaprogramming; the two `local instance ... := inferInstance` (`:18-19`) add nothing.
- Verdict: 8 decls, 7 OK / 1 NOTE (`CorrectionData` `:33-37`, with `source_gradient_zero :57`).

## 8. Euler/AllOrderCorrectionBudget.lean (81 lines, 2 decls, 1 structure) -- ESCALATE (direction-safe): the structure is NEVER CONSTRUCTED, and it has a live twin

- Declares `structure Budget {T} (hT : 0 < T) (A : Data period T)` (`:18-50`) with 15 fields
  (`metric, radius, constant, delta, initialRadius, spatial, constant_bound, delta_pos, delta_le_one,
  radius_pos, decay, scale, small, radius_eq, divergence`) and one theorem `finite_exists :53-79`.
- FINDING (shape 1 UNSUPPLIED HYPOTHESIS + shape 6 SUPERSEDED TWIN).
  `EulerAllOrderCorrectionBudget.Budget` is NEVER CONSTRUCTED anywhere in the artifact. Evidence:
  * its two distinguishing fields have exactly ZERO assignment sites -- artifact-wide grep for
    `constant_bound` returns only `Euler/AllOrderCorrectionBudget.lean:33` (the declaration) and `:70`
    (its own use inside `finite_exists`); no `constant_bound :=` and no `constant :=` for this record
    exists in any file;
  * nothing `extends Budget` and no `toBudget` projection exists (grep `extends Budget|toBudget`:
    no hit for this namespace);
  * every other occurrence of the name in the six files that open `EulerAllOrderCorrectionBudget` is in
    HYPOTHESIS position: `Euler/AllOrderCorrectionStability.lean:17` (`stabilityBudget ... (B : Budget ...)`),
    `Euler/AllOrderCorrectionFamily.lean:18,23` (`solution`/`solution_initial ... (B : Budget ...)`),
    `Euler/AllOrderLiftedCorrection.lean`, `Euler/AllOrderPressureCoherence.lean`,
    `Euler/AllOrderSmoothPressure.lean`, `Euler/CommonPressureRepresentative.lean:19,25,33,41,48,67,72,79`.
  * a decl `B.foo` that consumes `B` supplies nothing, so `finite_exists :53` never fires.
  THE LIVE TWIN. `EulerAllOrderDriftCorrection.Budget` (`Euler/AllOrderDriftBudget.lean:19`) is a
  near-identical record over the same `Data period T` -- same `metric`/`radius`/`delta`/`initialRadius`/
  `spatial`/`decay`/`scale`/`small`/`radius_eq`/`divergence`, with `constant`+`constant_bound` replaced by
  `growthCoefficient`+`growth_bound` ("only the actual transport drift enters the shrinking-radius
  slope", `:18`). THAT one IS constructed on the live path:
  `Euler/PacketInitializedAllOrderBudget.lean:102-118` (`refine { metric := ...; growthCoefficient := cg;
  ... growth_bound := ?_ ... }`) and `Euler/PacketForwardInitializedAllOrderBudget.lean:99`, and it is
  consumed by the twin theorem `EulerAllOrderDriftCorrection.finite_exists`
  (`Euler/AllOrderDriftFinite.lean:19`), which then builds the `FiniteFamily`
  (`Euler/AllOrderDriftFinite.lean:66-68`) that the live pressure reconstruction actually uses
  (`Euler/CorrectionAssemblyReconstruction.lean:21-67`, its OWN `pointPressure`/`graphPressure`).
  SCOPE OF THE DEAD BRANCH: the whole chain
  `AllOrderCorrectionBudget -> AllOrderCorrectionStability -> AllOrderCorrectionFamily ->
  AllOrderLiftedCorrection -> AllOrderPressureCoherence -> AllOrderSmoothPressure ->
  CommonPressureRepresentative` (7 files, ~540 lines) is parameterized on this unconstructible record,
  so all of it is unreachable -- EXCEPT the one Budget-free declaration
  `EulerCommonPressureRepresentative.cylinderGraph_continuous`
  (`Euler/CommonPressureRepresentative.lean:60`), which IS used live at
  `Euler/CorrectionAssemblyReconstruction.lean:61`. That single decl is why the chain still sits in the
  import cone. DIRECTION: SAFE -- nothing here is false, and no live theorem depends on it; the risk is
  purely that a reader credits this branch (and its `finite_exists`) as part of the proof.
- Everything else in the file is internally coherent: `delta_pos :36`, `radius_pos :40` give the
  needed strict positivity in-type; `q-4` (`:31`) is safe truncated subtraction under `hq : 6 <= q`;
  `radius_eq :48` pins the radius path affinely, and `finite_exists :63-72` feeds exactly those fields
  into `exists_global_inviscid_gevrey_PDE`.
- JUNK-VALUE SWEEP: the only divisions are by the literal `2` (`initialRadius/2 :42`, `delta/2 :46,:59`).
  No unguarded inverse. Note `divergence :50` runs through the same
  `divergenceFreeSpace period A.kappa A.direction` channel flagged in file 7 (would be `top` at
  `kappa = 0 and direction = 0`), but here it is moot -- the record is never built.
- KERNEL RISK: none. Largest numeral = `6` (`:30,:54`); `by omega` inside the type at `:30` is a benign
  `Nat` side condition. No `inductive`, `.rec`, `decide`, `deriving`, `termination_by`, `Fin.cases`,
  `native_decide`, metaprogramming.
- Verdict: 2 decls, 0 OK / 1 NOTE (`divergence :50`) / 1 ESCALATE (`Budget :18` unconstructed, taking
  `finite_exists :53` with it).

## Block summary (structural tail 4)

- NO `Acc.rec`, NO `native_decide`, NO `decide` at all, NO `Fin n` with n > 4, NO `termination_by`, NO
  `deriving`, NO `inductive` and NO metaprogramming in any of the eight files. Largest numeral in the
  whole block: `1024` (`Euler/MeanPacketSobolevData.lean:32`), inside a real-number inequality, never
  evaluated. So the structural block's "exactly two benign flags" count does NOT grow here.
- Junk-value sweep: 4 files invert something (`tau^-1`, `A.ell^-1`, `G.T^-1`, `sourceFixedCoercivity^-1`)
  and ALL FOUR are guarded in-signature or by an unconditional positivity theorem
  (`MeanSourceFixedInverse.lean:57`). No unguarded division anywhere. These are positive controls.
- One VARIABLE-SHADOWING check done (the `PacketKnownTermSums.lean:16` vs `:18` pattern):
  `Euler/PacketKnownPieceBounds.lean:13` has `[Fact (0 < P)]` and no theorem in the file re-binds `P`;
  `Euler/EulerCorrectionLocal.lean:16` and `Euler/AllOrderCorrectionBudget.lean:15` likewise bind
  `period` once, at section level, and never shadow it. No escape found.

