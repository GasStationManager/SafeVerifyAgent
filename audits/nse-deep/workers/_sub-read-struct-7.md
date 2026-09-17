# _sub-read-struct-7 -- structural read (READ-ONLY, NSE @ f9e8bc5)

Scope: 4 previously-unnamed structural files. Classification per rubric OK/NOTE/UNCLEAR/ESCALATE/KERNEL-RISK.

## 1. NavierStokes/LocalizedGaussianBounds.lean (565 lines, 23 decls)

VERDICT: essentially CLEAN. 1 structure, constructed 3 independent ways. No kernel risk. Junk-value
guards are all in-signature or safe-direction. This file is a useful POSITIVE CONTROL.

Detail:
- `structure UniformComplementJets` LocalizedGaussianBounds.lean:259-264 (Prop, fields `smooth`+`bounds`).
  NOT an unsupplied hypothesis: it is CONCLUDED without assuming itself at
  :276 `of_zero_germs` (from zero germs off the cells), :289 `of_germs` (from
  `LabelSumBounds.UniformClass` of a comparison family g), :464 `uniform_source_complement_of_zero`,
  :510 `uniform_source_complement_of_harmonicSupport`, :532 `uniform_source_complement_of_excluded_class`.
  It is also DESTRUCTED at :268 `.each` -> `ComplementJets` and consumed at :417/:431. Base case exists,
  so no closure-without-base-case. OK.
- Two routes are non-trivial, not just "source = 0": :510 goes through `InputSupportOn` +
  `sourceFamily_zero_germ_on` (support-based, source may be nonzero on the cells), and :532 transfers a
  genuinely nonzero excluded harmonic tail via `of_germs` (hypothesis `he : UniformClass ... angleLift
  (excludedSource ...)`, :547-548). So the complement supply is not only the zero-source shortcut at
  :130 / :464. OK.
- Junk-value sweep. Statements contain `/` only as numeral literals (`1/2`, `1/5`, `c*ell/25`,
  `c*ell/50`, :155/:160/:179/:219) -- no unconstrained denominator. The one inverse in the
  cone is `(s.delta x)`inv inside `StripData.growth` = `slow n * max 1 (s.delta x)inv`
  (WeightedClasses.lean:50-51). It is GUARDED TWICE: `max 1 _` and `delta_pos` on the domain
  (WeightedClasses.lean:40). At delta = 0 the junk value 0 gives growth = slow >= 1, which SHRINKS the
  majorant, i.e. strengthens every bound -- safe direction. Positive control, OK.
- `s.epsilon n ^ alpha` is rpow with `epsilon_pos` (WeightedClasses.lean:35) in-structure. OK.
- NOTE (shape 3, hypothesis side, non-fatal): the weight in the load-bearing theorems is
  `fun n x => Real.sqrt (s.zeta x) * W n x` (:82-83, :377-380) and `StripData` only requires
  `zeta_nonneg` (WeightedClasses.lean:43), never zeta > 0; `domain` may also be empty
  (:32-33 no nonemptiness). Degenerate `zeta = 0` / `domain = {}` makes the hypotheses
  `LocalJets ... amplitude` say "all jets <= 0" and makes the conclusions vacuous. Direction is safe
  (these are universally quantified over `s`), and real StripData witnesses with positive data exist in
  bulk (e.g. ActualPrimaryBounds.lean:29-31, ActualInitialMean.lean:27, BaseContextAssembly.lean:154),
  so this is a NOTE not an ESCALATE.
- `indexedCutoffError` :346-349 is defeq to `LinearWaveBounds.excludedSlotError`
  (LinearWaveBounds.lean:740-742) = `CopyData.localGaussian` (PeriodizedWaveBounds.lean:785-786); the
  L x I re-indexing at :398-400 therefore typechecks honestly, no silent substitution. OK.
- KERNEL RISK: none. No `inductive`, no `.rec`/`Acc.rec`, no `termination_by`, no `deriving`, no
  `decide`, no metaprogramming. Largest numeral in the file: 50 (:160, :219, :236).

Tally file 1: 23 decls read -- OK 22 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.

