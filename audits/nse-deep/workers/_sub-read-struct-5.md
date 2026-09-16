# Worker _sub-read-struct-5 -- READ-ONLY structural audit (NSE @ f9e8bc5)
Files: Euler/ParentPacketParity.lean, Euler/PacketCylinderFieldBounds.lean,
Euler/MeanPacketForcing.lean, Euler/TransversePacketData.lean
No build attempted (0 .olean, pinned lean4:v4.34.0-rc2). Source-read + cross-file grep only.

## 1. Euler/ParentPacketParity.lean -- 18 decls: OK 18 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0

VERDICT: CLEAN. Pure parity plumbing; no reopening of the Euler thread from this file.

Structural decl: `structure OddData (A : Parent) : Prop` (ParentPacketParity.lean:32), single field
`displacement : forall t, Function.Odd (A.displacement.field t)`.

Shape-1 (unsupplied hypothesis) -- REFUTED, OddData is really constructed, not only assumed:
  * base construction Euler/BaseStaticEuler.lean:151 `theorem baseOddData (hodd : forall x, u.field (-x) = -u.field x) : OddData (baseParent ...)`
  * instantiated on a genuine datum at Euler/BaseEulerInput.lean:52-55 `solutionOddData ... = baseOddData 1 (field (linear beta)) uniformL2Amplitude 1024 ... (velocity_odd (linear beta))`
    -- the underlying field is `field (linear beta)` with only `hbeta : |beta| <= 1` (Euler/BaseEulerInput.lean:25), i.e. beta may be nonzero, so this is not the zero-field witness.
  * consumed as a FIELD of the state record: Euler/ParentState.lean:22 `odd : OddData A`, supplied at Euler/BaseSmoothState.lean:20 and Euler/BaseEulerState.lean:50.
  * ParentPacketParity.lean:96 (`restrictTime`) and :99 (`child`) both `include O`, so they are propagation steps, not independent constructions -- correct, and the induction is closed by the base above.

Shape-6 (stronger-than-needed twin): NOT present, the opposite -- OddData assumes oddness only of
`displacement`; oddness of velocity (:41) and acceleration (:44) is DERIVED via
`A.displacement_time.odd` / `A.velocity_time.odd`. Minimal hypothesis. Good.

Junk-value / inverse sweep: the only inverse in the file is inside the invoked definition, via
`ell^{-1} . x` (ParentPacketParity.lean:22, def at Euler/SmoothPhysicalGraphFlow.lean:59-63
`physicalCoefficient ... field t x = ell . (A.field t (graphLinear k m (ell^{-1} . x))).1`).
NOTE (not a defect): `theorem physicalCoefficient_odd` (ParentPacketParity.lean:16) leaves `ell`
unconstrained, and at ell = 0 the coefficient field is identically 0 so the conclusion degenerates to
`Odd 0`. This is benign because (a) the proof is uniform in ell -- the ell != 0 content is also proved,
and (b) every caller passes `A.ell` which is certified positive by the type: Euler/ParentPacketFrames.lean:26
`ell_pos : 0 < ell`. Contrast the sibling `physicalCoefficient_trace_zero` (Euler/SmoothPhysicalGraphFlow.lean:109)
which DOES carry `hell : ell != 0` -- there the hypothesis is load-bearing.

Kernel risk: none. One Prop-valued single-field `structure` (:32); no `inductive`, no `.rec`/`Acc.rec`,
no `termination_by`, no `deriving`, no `decide`, no numerals at all in this file.

## 2. Euler/PacketCylinderFieldBounds.lean -- 17 decls: OK 17 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0

VERDICT: CLEAN. Nothing here reopens the Euler thread.

Prop-def: `def WordBound (G : Field P T raw) (q : N) (R A : R) (d : N) : Prop :=
  forall n, block standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) n 0 <= A*majorant R d n`
(PacketCylinderFieldBounds.lean:21-23).

Shape-1 (dead hypothesis): REFUTED, massively. `WordBound` is both concluded on genuine objects and
consumed as a structure field:
  * concluded for the actual static cylinder field: Euler/StaticCylinderField.lean:81 `(field P T u).WordBound q (sobolevCoefficientRadius (Fin 4) R) ...`
  * a FIELD of the packet budget records: Euler/PacketProfileBudget.lean:17-24 (7 fields, all WordBound),
    Euler/PacketInitializedPressureBudgets.lean:19-20.
  * ~300 further call sites across Euler/Packet*.lean. Fully load-bearing.

Shape-2 (vacuity) -- the only zero witness is explicitly labelled as such: PacketCylinderFieldBounds.lean:44
`wordBound_zero : (Field.zero P T).WordBound q R 0 d`, i.e. the trivial case is A = 0 for the zero field,
and it is a separate lemma, not the general content.

Junk-value sweep: NEGATIVE for this file. It contains no `/` and no inverse in any statement (checked
mechanically over all 142 lines). The two quantities that appear in the emitted amplitudes are
division-free by construction:
  * `majorant R d n = R^(n+d)*((n+d)!)^2` (Euler/EulerProof.lean:196-197) -- no inverse; at R = 0 the bound
    becomes `block <= 0`, i.e. STRONGER, so R is safe to leave unconstrained.
  * `sobolevCoefficientAmplitude i q Rc C = 2^q*C*sum_{k<=q} sobolevCoefficientRadius i Rc^k*(k!)^2`
    (Euler/ParameterSobolevCoefficient.lean:43-44) and `sobolevCoefficientRadius i Rc = 4*(max 1 (card i)*Rc)`
    (:38-39); `productBlockConstant P = card (SobolevWord 6)*sobolevProductConstant P 6`
    (Euler/CylinderPathProductBounds.lean:48-49). All polynomial, no denominators.
Where a positivity side condition IS needed it is present in the same signature, e.g. `hR : 0 <= R`
at :36, `hR : 1 <= R` at :40 (needed for `majorant_mono_shift`, Euler/PacketMajorantShift.lean:14),
`hR, hA, hB` at :116, :121, :126.

`WordBound.transfer` (:27-30) deserved a check because it moves a bound between two arbitrary witnesses
of the SAME raw field. It is honest: it rewrites by `G.path_eq_of_same_raw H`, and that is a real
uniqueness theorem proved a.e. through `Lp.ext` from the `raw_eq` field of the record
(Euler/PacketCylinderFieldUnique.lean:14-22; record at Euler/PacketCylinderField.lean:21-25). Not an axiom.

All 15 non-def declarations are either term-mode applications of already-proved majorant lemmas
(:37, :41, :92, :117, :122, :127, :136) or short `intro n` calculations, so no hypothesis can be silently
dropped. Kernel risk: none -- no inductive, no `.rec`, no `termination_by`, no `deriving`, no `decide`.
Largest numeral in the file: 9 (:122); the only other literals are 3, 4 (`Fin 4`), 6 (the fixed Sobolev order).

## 3. Euler/MeanPacketForcing.lean -- 21 decls: OK 21 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0

VERDICT: CLEAN. Regularity plumbing for the mean provider; nothing here reopens the Euler thread.

Structural decl: `structure Forcing (D : Data) (raw : VectorField)` (MeanPacketForcing.lean:24-29) with
fields `slices : R -> SmoothL2Field Space`, `jets_continuous`, `path : C(Icc 0 D.T, L2)`,
`path_eq : forall t, path t = (slices t).toLp`, `raw_eq : forall t x th, raw (t,(x,th)) = (slices t).field x`.

Shape-1: REFUTED. `Forcing` is constructed, not merely assumed:
  * `Forcing.ofSlices` Euler/MeanPacketForcingAlgebra.lean:28 and `Forcing.zero D` :35;
    `add` :38, `map` :45, `smul` :50, `neg` :53, `spatialDerivative` :56 -- a full algebra.
  * the angular-mean forcing of ANY raw field: Euler/MeanPacketAngularForcing.lean:37 and :46.
  * the packet recursion consumes it as `Nonempty (Forcing D raw)` admissibility
    (Euler/MeanPacketProvider.lean:117-127, Euler/MeanPacketOrbitForcing.lean:61-62).

STRUCTURAL OBSERVATION worth recording (not a defect): `raw_eq` (:29) forces the right-hand side to be
INDEPENDENT of the angle theta. So `Forcing D raw` is inhabited only for angle-independent raw fields.
That is exactly the intent of the mean provider (the companion transverse provider carries the
theta-dependence), and it matches the actual instantiation, which feeds the angular mean
`P^{-1} . integral_0^P raw dtheta` (Euler/MeanPacketAngularForcing.lean:46). Consistent, not vacuous.

Junk-value sweep: the file contains no `/` and no inverse. The nondegeneracy the whole file leans on is
`D.frameLower` / `D.frameLower_pos` / `D.frame_lower` (used at :82, :90-92, :101, :105, :109, :114) and this
is CERTIFIED, not assumed: `abbrev frameLower := meanFrameCoercivity D.T D.opInv` with
`theorem frameLower_pos` (Euler/MeanPacketData.lean:130-132), and the underlying definition is
`meanFrameCoercivity = ((‖FInv‖+1)^2)^{-1}` (Euler/MeanFrameCoefficients.lean:21). The `+1` is a
deliberate junk-value guard: the denominator is >= 1 unconditionally, so `positivity` closes
`frameLower_pos` (:23-25) with no side hypothesis. This is the CORRECT version of the defect shape that
was found elsewhere in the artifact (unconstrained denominator), so it is a negative result here.

NOTE: `slices : R -> ...` is indexed by ALL of R while `jets_continuous` (:26) and `path_eq` (:28)
constrain it only on `Icc 0 D.T`. Values of `slices` outside the horizon are therefore unconstrained
junk, but no declaration reads them (every consumer is indexed by `t : Icc (0:R) D.T`), so this is
cosmetic.

All 18 proofs are term-mode applications of already-established translation-regularity lemmas, so no
hypothesis can be silently dropped. Kernel risk: none -- no inductive, `.rec`, `termination_by`,
`deriving`, or `decide` (checked mechanically); no numeral other than 0. The `Classical.choice` in the
solve chain sits one layer up (Euler/MeanPacketData.lean:120, discharged by `sourceMeanSolver_strong`),
not in this file.

## 4. Euler/TransversePacketData.lean -- 21 decls: OK 21 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0

VERDICT: CLEAN, and the best-designed file of my four. The two inverses in it are the SAFE pattern.

Structural decl: `structure Data (U) [NormedAddCommGroup U] [InnerProductSpace R U]`
(TransversePacketData.lean:19-36): T with `T_pos`, compact `support`, `m0` with `m0_unit : ‖m0‖ = 1`,
an isometry `R : U =~li[R] referencePlane m0`, coefficient paths F, F1, FInv, M, and only three
identities: `inverse_left`, `inverse_right` (:31-32), `frame_time` (:33-35), `strain_equation` (:36).

This file is where I expected the junk-value defect, because it is the only one of my four with an
inverse in a DEFINITION: `def frameLower : R := D.inverseBound^{-1}^2` (:51) and
`def normalLower : R := D.frameBound^{-1}^2` (:52). It is NOT a defect. The denominators are
`def inverseBound := 1+‖D.FInv.field‖` (:49) and `def frameBound := 1+‖D.F.field‖` (:50), i.e. shifted by
1 so that `inverseBound_pos` / `frameBound_pos` are closed by bare `positivity` (:54-60) with no
hypothesis, and `frameLower_pos` / `normalLower_pos` follow by `pow_pos (inv_pos.mpr ...)` (:62-66).
So the two coercivity constants are POSITIVE BY CONSTRUCTION and the type certifies the non-degeneracy
(rubric shape 3 is answered in the good direction). The coercivity statements that use them,
`frame_lower : D.frameLower*‖v‖^2 <= ‖D.frame.field t x v‖^2` (:79-82) and
`normal_lower : D.normalLower <= ‖D.normal.field t x‖^2` (:85-88), therefore cannot degenerate to
`0 <= ...`; and each is derived from the record's own `inverse_left` + the matching norm bound
(`inverse_norm` :68-71, `frame_norm` :73-76), not assumed.

Shape-1: REFUTED. `Data U` is inhabited by a genuine object:
`def transverseData : EulerTransversePacketProvider.Data U` (Euler/ParentPacketSourceData.lean:95),
instantiated on the base solution as
`def firstPacketData : ... Data FirstPlane := (packetBaseParent ...).transverseData firstNormal firstNormal_unit firstFrame support compact`
(Euler/BasePacketLowBounds.lean:17-19), and `historyData` on top of it (ParentPacketSourceData.lean:129).
Note the `R : U =~li referencePlane m0` field makes the record uninhabited for U of the wrong dimension;
`FirstPlane` supplies the isometry, so the whole transverse tower is live rather than dead.

Shape-6 (stronger hypothesis beside a weaker used twin): NOT present. The record assumes both
`inverse_left` and `inverse_right`, and both are genuinely consumed separately -- `inverse_left` by
`frame_lower` (:81), `normal_lower` (:87), `frame_tangent` (:92); `inverse_right` only by
`frame_range` (:96), which needs surjectivity. Neither is redundant.

Kernel risk: none. `structure` only, no `inductive`/`.rec`/`termination_by`/`deriving`/`decide`
(checked mechanically). Largest numeral: 2 (the squares at :51-52, :63, :66, :80, :86).

## OVERALL

4 files, 77 declarations, 59 in-cone theorems: 0 ESCALATE, 0 UNCLEAR, 0 KERNEL-RISK, 2 cosmetic NOTEs.
The Euler thread stays CLOSED on this evidence. The strongest positive finding is that this block's
three inverse-valued definitions (`physicalCoefficient`'s `ell^{-1}`, `frameLower = (1+‖FInv‖)^{-2}`,
`meanFrameCoercivity = ((‖FInv‖+1)^2)^{-1}`) are all guarded -- either by a `+1` shift inside the
denominator or by `ell_pos` in the caller's type (Euler/ParentPacketFrames.lean:26) -- which is the
opposite of the `Kr / K` and `C^{-1}` junk-value defects reported elsewhere in the artifact.
