# sub-read-struct-tail3 -- structural tail (8 files), NSE @ f9e8bc5, READ-ONLY

## 1. Euler/PacketCorrectionPrimitiveBounds.lean (153 lines) -- CLEAN
Declares `structure CorrectionBounds (Kc : CorrectionCoefficientBudget D P) (X : ℝ) : Prop` with 9
`≤ X` fields (:79-88).
* CONSTRUCTED (not an unsupplied hypothesis): `correctionBudget_bounds` (:102-130) concludes
  `CorrectionBounds D P (correctionCoefficientBudget ...) (primitiveEnvelope P X)` from no
  `CorrectionBounds` hypothesis. Consumed downstream at PacketSourcePrimitiveBounds.lean:23,:35,:53,:65,
  PacketForwardUniformCosts.lean:28, PacketInitializedParameterBounds.lean:41. `CorrectionBounds.mono`
  (:90) is the P.foo-from-P shape and supplies nothing, correctly noted as such.
* JUNK-VALUE SWEEP: POSITIVE CONTROL. Two inversions appear in statements and both are guarded in the
  SAME signature: `c⁻¹ ≤ (1+X)^2` (:20) sits next to `hc : 0 < c` (:18); `((1+X)^2)⁻¹` (:64,:67) has
  `0 ≤ X` derived in-proof from `hR`/`hRX` (:26). No unguarded `/` or `⁻¹`.
* VACUITY: `correction_envelopes` (:17) is satisfiable by a concrete witness -- take
  `c = 1, R = C0 = C1 = CI = 0, X = 0`: hc 0<1 ok, all `0 ≤ 0` ok, all `_ ≤ 0` ok,
  `hci : 1⁻¹ = 1 ≤ (1+0)^2 = 1` ok. Non-degenerate witness also exists: `c = 1, X = 1, R=C0=C1=CI=1`
  (`1 ≤ 4`). Not vacuous.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`.
  `Fin 4` (:42, well under 22). Largest numeral: `64` (:42). Benign by inspection.
VERDICT: 5 decls read -- OK 5 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

## 2. Euler/LpSmoothFamily.lean (97 lines) -- CLEAN, base case exists
Declares `structure SmoothFamily (μ) (P) (V)` (Type-valued data: `field`,`smooth`,`jet`,`jet_ae`,
`bound`,`bounded`) at :21-28, plus `value` (:34), `derivative` (:45), and 4 theorems.
* CLOSURE-WITHOUT-BASE-CASE CHECK -- NEGATIVE (this one HAS a base). `derivative` (:45-60) is the
  closure operation (SmoothFamily -> SmoothFamily of the derivative type), but a genuine BASE witness
  is constructed from raw analytic data at `EulerMeanForcing.forcingFamily`,
  Euler/MeanForcingTranslation.lean:26-39 (`SmoothFamily (timeMeasure T) Space (L2Space V)` built out
  of a `ℝ → SmoothL2Field V` plus `MemLp` hypotheses -- no SmoothFamily input). It is used
  non-trivially at MeanForcingTranslation.lean:52-77 and downstream in Euler/LpSmoothFamilyJets.lean.
  Not degenerate: the field is `translation a (A t).toLp` for an arbitrary supplied `A`.
* NAME-TWIN WARNING (informational, not a defect): there are three unrelated `SmoothFamily`s in the
  artifact -- this one, `NavierStokes.MeanRankUpdate.SmoothFamily` (MeanRankUpdate.lean:1177, its own
  witness `SmoothFamily.ofReserved` at :1437), and `NavierStokes.CompactSmoothFamily`
  (CompactSmoothFamily.lean:14). Cross-file grep must be namespace-qualified here.
* `derivativeMap` vs `derivativeBundling` (:66 vs :92) is not an inconsistency:
  Euler/LpDerivativeBundling.lean:35-36 gives `derivativeBundling μ D = derivativeMap μ D` by `rfl`.
* JUNK-VALUE SWEEP: zero `/` and zero `⁻¹` in the file. Nothing to degenerate.
* KERNEL RISK: none. No `inductive`/`decide`/`termination_by`/`deriving`/`Acc.rec`/`native_decide`/
  `Fin.cases`. `Fin 0`-style currying equivs only (`continuousMultilinearCurryFin0`, :35). Largest
  numeral: `2` (the Lp exponent). Benign.
VERDICT: 7 decls read -- OK 7 / NOTE 0 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

