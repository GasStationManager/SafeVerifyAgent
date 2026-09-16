# sub-nosupplier-10 (READ-ONLY audit, NSE f9e8bc5)

## 1. NavierStokes.WaveStateRegularity.CoefficientSupport (WaveStateRegularity.lean:197)
VERDICT: UNSUPPLIED
- Decl is `noncomputable def CoefficientSupport ... : Prop := forall n l, ...` (Prop-valued def, not a structure).
- grep last component `CoefficientSupport` (whole artifact, --include=*.lean): 10 hits total.
  * LabelSupportPreservation.lean:322,450 = `section CoefficientSupport` / `end` -> section name only,
    NOT a namespace, NOT a twin predicate (route 5: no same-named predicate anywhere else).
  * WaveStateRegularity.lean:197 = the definition itself.
  * WaveStateRegularity.lean:211,250,261,272,282,293,294 = ALL BINDERS
    (`(hs : CoefficientSupport U a b labels blocks)`, `(hs0 : ...)`, `(hs1 : ...)`) in theorem signatures.
- Route 1: no decl anywhere has CoefficientSupport as its CONCLUSION (final top-level `:`); so the
  "concludes P from a P binder" trap does not even arise.
- Route 2: no `<...>`/`.mk`/`{ field := }`/`let H : CoefficientSupport ... :=` occurrence; a Prop-def of
  forall-shape would be proved by a theorem concluding it, and none exists.
- Route 3: no `instance` of it.
- Route 4 BOTH directions: (a) P-as-field-of-S: none of the 10 occurrences is a structure field
  declaration, so P is not a field of any structure -> no parent supplier. (b) S-as-field-of-P: P is a
  `def : Prop`, it has no fields, so nothing else can be supplied via it either. Came out NEGATIVE both ways.
- Occurrences examined: 10 (1 defn, 7 binders, 2 section markers). All uses are binders.
