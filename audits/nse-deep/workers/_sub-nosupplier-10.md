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

## 2. NavierStokes.PhysicalCopyBounds.CommonChart (PhysicalCopyBounds.lean:336)
VERDICT: UNSUPPLIED  (twin trap present and neutralised)
- Declared inside `namespace NavierStokes.PhysicalCopyBounds` (line 16, ends 713) as
  `structure CommonChart (f : CopyFamily H K) (hc : SupportCells f) (a b h sigma : ℝ) (source ...)`
  -> ARITY: NO `r0` argument; fields sourceIndex/map/domain/open_domain/smooth/positive_jets/
  amplitude_eq(`= fun x =>`)/contains(no tsupport clause).
- ROUTE 5 (twins, decisive here): three distinct same-named structures exist:
  (i) NavierStokes.PhysicalCopyBounds.CommonChart  (PhysicalCopyBounds.lean:336, arity ...a b h sigma source)
  (ii) NavierStokes.LocalPhysicalCopyBounds.CommonChart (LocalPhysicalCopyBounds.lean:581, arity
       ...a b h r0 sigma source, amplitude_eq via EqOn, extra `tsupport` clause)
  (iii) NavierStokes.PhysicalClassBounds.CommonChart (PhysicalClassBounds.lean:317, takes a
       PhysicalWaveSum.WaveFamily, arity F a b h r0 sigma f).
  EVERY construction in the artifact belongs to (ii) or (iii), NOT to our (i):
  `LocalPhysicalCopyBounds.CommonChart ... where` at ActualSignedPhysicalData.lean:1812,
  WaveDataReindex.lean:106, DependentSignedPhysicalFamily.lean:406 and :440,
  ActualParticularPhysicalData.lean:320 (`identityCommonChart`, reused at :897,:909,:1178,:1216),
  InitialPhysicalData.lean:1092 (reused :1113,:1120), PositiveTimeSignedData.lean:319 -- all
  FULLY QUALIFIED to LocalPhysicalCopyBounds; and PhysicalClassBounds.lean:727
  (`cylindricalCommonChart ... : CommonChart F a b h r0 sigma f where`) is twin (iii)'s own builder
  (arity 7 with r0 + WaveFamily). SharpPhysicalCopyBounds.lean:177 `(hchart : CommonChart f hc a b h r0
  sigma source)` carries `r0` -> it is twin (ii) (that file opens both namespaces, line 6). None of these
  supplies (i).
- Cross-check: `grep -rn 'PhysicalCopyBounds\.CommonChart'` minus Local/Sharp lines returns NOTHING, i.e.
  our structure is never referred to by qualified name outside its own namespace.
- ROUTE 1: the only decls named `CommonChart.*` in our namespace is
  PhysicalCopyBounds.lean:356 `theorem CommonChart.amplitude_bound` whose CONCLUSION is
  `∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ...` -- NOT CommonChart -- and which itself TAKES
  `(hchart : CommonChart f hc a b h sigma source)`. So it is the trap-(c) shape twice over: no supplier.
- Sites of (i) in own namespace: 336 (decl), 359, 440, 464, 685 -> 4 BINDERS
  (`(hchart : CommonChart f hc a b h sigma source)`, and at 685 `(hchart : ∀ i, CommonChart (f i) ...)`).
- ROUTE 2: no `<...>`/`.mk`/`{ sourceIndex := ... }`/`let H : CommonChart ... :=` for (i).
- ROUTE 3: no `instance`.
- ROUTE 4 BOTH directions: (a) P-as-field-of-S: the only structure FIELD of CommonChart type is
  PhysicalStageBounds.lean:71 `chart : ∀ i, LocalPhysicalCopyBounds.CommonChart (copies i) (cells i) ...`
  -- explicitly the twin (ii), so our (i) is a field of NOTHING -> NEGATIVE.
  (b) S-as-field-of-P: (i)'s own 8 fields are ordinary data/Prop fields (no other audited predicate),
  and since (i) is never constructed it supplies nothing downstream -> NEGATIVE.
- Occurrences examined: 5 of (i) (1 decl + 4 binders); all uses binders.

## 3. NavierStokes.PhysicalStageSupport.NativeOuterBounds (PhysicalStageSupport.lean:234)
VERDICT: UNSUPPLIED
- `structure NativeOuterBounds (R : ℝ) (WA ...) (MA ...) (MB ...) (WP ...) (MP ...) : Prop where`
  fields potentialWave/potentialMean/directMean/pressureWave/pressureMean (all `∀ j, ... ≤ ...`).
- grep last component over whole artifact: 7 hits, ALL in PhysicalStageSupport.lean, so 1 file only
  (matches the 5-site count = 5 binders):
  234 decl; 254 `(H : NativeOuterBounds R WA MA MB WP MP)` binder of `NativeOuterBounds.radius_pos`;
  263 binder (`all_increment_support`); 281 binder (`exists_common_support`); 296 binder
  (`candidate_support_inputs`); 434 binder (`... NativeOuterBounds ActualInitialization.geometry.patch.b ...`).
- ROUTE 1 + trap (c): the only `NativeOuterBounds.*`-named decl is :253 `NativeOuterBounds.radius_pos`,
  whose CONCLUSION is `0 < R` and which TAKES `(H : NativeOuterBounds R ...)`. Verbatim read of the
  conclusions of :263 (`(∀ j, SublevelShrinkingSupport ...) ∧ ... ∧ ...`), :281 (`∃ C : ℝ, 0 < C ∧ ...`)
  and :434 (a three-fold conjunction of SublevelShrinkingSupport) shows NO decl anywhere concludes
  `NativeOuterBounds ...`. Hence not even a trap-(c) candidate exists.
- ROUTE 2: the `refine <?_,?_,?_>` at :266 and the `<outerConstant R, ...>` at :286 build the CONJUNCTION
  / EXISTENTIAL goals of those theorems, NOT NativeOuterBounds (checked by reading the goals). No
  `{ potentialWave := ... }`, no `.mk`, no `let H : NativeOuterBounds ... :=` anywhere.
- ROUTE 3: no `instance`.
- ROUTE 4 BOTH directions: (a) P-as-field-of-S: none of the 7 occurrences is a field declaration inside
  another structure (all are `(H : ...)` binders in theorem signatures) -> NEGATIVE, no parent supplier.
  (b) S-as-field-of-P: its 5 fields are plain inequalities over WaveData/MeanData `.upperRadius`,
  no audited predicate; and it is never constructed -> NEGATIVE.
- ROUTE 5: no same-named twin in any other namespace (all 7 hits in one namespace).
- Occurrences examined: 7 (1 decl + 5 binders + 1 self-named theorem that consumes it); all uses binders.

## 4. NavierStokes.SmoothParameterIntegral.LocallyDominatedOn (SmoothParameterIntegral.lean:127)
VERDICT: UNSUPPLIED
- `def LocallyDominatedOn (F : H → α → E) (μ : Measure α) (s : Set H) : Prop := ∀ (k : ℕ) (x : H),
  x ∈ s → ∃ ε, 0 < ε ∧ ball x ε ⊆ s ∧ ∃ bound, Integrable bound μ ∧ ...` (Prop-valued def).
- grep last component: 6 hits, all in SmoothParameterIntegral.lean (1 file):
  127 decl; 134, 143, 185, 203, 210 = 5 BINDERS `(h_dom : LocallyDominatedOn F μ s)` in
  integrable_jetOn / hasFDerivAt_integral_jetOn / hasFTaylorSeriesUpToOn_integral /
  contDiffOn_integral / iteratedFDeriv_integralOn.
- ROUTE 1: no decl concludes `LocallyDominatedOn ...`; conclusions read verbatim are
  `Integrable (jet F k x) μ`, `HasFDerivAt ...`, `HasFTaylorSeriesUpToOn ∞ ...`, `ContDiffOn ℝ ∞ ...`,
  `iteratedFDeriv ... = ∫ ...`. No `.of_*` smart constructor exists. Trap (c) not applicable.
- ROUTE 2: every use is a CONSUMER: `obtain <ε, hε, _, bound, hb, hbound> := h_dom k x hx` (:136, :148).
  The `constructor` at :188 has GOAL `HasFTaylorSeriesUpToOn ...`, NOT LocallyDominatedOn -- checked by
  reading the theorem's conclusion at :185-187, so it is not a route-2 construction. No
  `let/have H : LocallyDominatedOn ... :=` anywhere.
- ROUTE 3: no `instance`.
- ROUTE 4 BOTH directions: (a) P-as-field-of-S: no occurrence is a structure field (all 5 are theorem
  binders) -> NEGATIVE. (b) S-as-field-of-P: P is a `def : Prop` with no fields -> NEGATIVE.
- ROUTE 5 / near-name trap: SIBLING predicates with DIFFERENT names ARE supplied in this file --
  `LocallyDominated` (:33) is proved at PhysicalMeanDomain.lean:685 (`have hd : SmoothParameterIntegral.
  LocallyDominated g μ := by`), MeanMomentBounds.lean:195, ParametricFlatFactor.lean:202, and by
  `LocallyDominatedDeriv.toLocallyDominated` (:272-273, concludes LocallyDominated from
  LocallyDominatedDeriv), and `LocallyDominatedDeriv` (:267) is supplied at ShapeTransition.lean:566/1057,
  RenormalizedHeatMoment.lean:63, EvenSmoothDescent.lean:67, FlatPrimitiveFactor.lean:236. NONE of these
  is our `LocallyDominatedOn` (different last name component, extra `s : Set H` argument, and there is NO
  `LocallyDominated -> LocallyDominatedOn` bridge lemma). Their suppliers do NOT count for P.
- Occurrences examined: 6 (1 defn + 5 binders); all uses binders.

## 5. NavierStokes.ActualWaveRegularity.NativeData (ActualWaveRegularity.lean:47)
VERDICT: UNSUPPLIED  (route 4 positive-then-refuted: parent chain exists but is never constructed)
- grep last component `NativeData` artifact-wide: hits split into two DISJOINT predicates.
  ROUTE 5 (twin): `NavierStokes.SignedMeanGain.NativeData` (SignedMeanGain.lean:1096, `structure
  NativeData (G : Geometry) where`, arity 1) is a DIFFERENT structure; it is used at
  BandReindexedSignedMeanGain.lean:72/98/134, CorrectionStep.lean:7717/8254/8456/8983,
  SignedMeanGain.lean:1144/1226/1285/1327 -- all binders -- and ActualSignedMeanBinding.lean:69 even
  proves `IsEmpty (SignedMeanGain.NativeData ActualInitialization.geometry)`. Nothing there can supply
  OUR `ActualWaveRegularity.NativeData a s d Ω hΩ` (arity 5).
- OUR occurrences (ActualWaveRegularity.lean only): 47 decl; 56/163 `namespace NativeData`/`end`;
  59 `variable ... (h : NativeData a s d Ω hΩ)` = BINDER for the whole NativeData namespace;
  393 `native : NativeData a s d (nativeDomain e U) (nativeDomain_open e U)` = a structure FIELD.
- ROUTE 1: no decl concludes `NativeData ...` (no `NativeData.of_*`, no builder def). The namespace
  56-163 only CONSUMES the variable-bound `h`.
- ROUTE 2: no `<...>` / `.mk` / `{ ... := }` / `let H : NativeData ... :=` for our structure.
- ROUTE 3: no `instance`.
- ROUTE 4 direction (a) P-as-field-of-S: POSITIVE FIND, then REFUTED (trap (b)). NativeData IS the field
  `native` of `structure ModeData` (ActualWaveRegularity.lean:390). But ModeData is NEVER constructed:
  its only 6 occurrences are 390 (decl), 408/461 (namespace), 412 (binder `(h : ModeData a s d e U r0 r1)`),
  610 (field `mode : ∀ l j, j ∈ modes v.residualBand → ModeData ...` of `structure ParticularData`:606),
  776 (field `mode : ∀ l, ModeData ...` of `structure SignedData`:773). Chasing one level further:
  ParticularData occurs only at 606 (decl), 620, 630, 811 -- ALL BINDERS; SignedData only at 773 (decl),
  783, 794, 811 -- ALL BINDERS. Neither grandparent is ever constructed (no `where`, no anonymous
  constructor, and ActualCyclePreservation.lean:655 `nativeParticularData` is a near-name red herring:
  it returns `... .copyData ...`, i.e. a CopyData, not a ParticularData). So the parent chain
  NativeData -> ModeData -> {ParticularData, SignedData} terminates in binders only -> supplies NOTHING.
  Direction (b) S-as-field-of-P: NativeData's own fields are consumed by its namespace lemmas; since
  NativeData is never built, it supplies nothing downstream -> NEGATIVE.
- Occurrences examined: 5 of our predicate (1 decl, 2 namespace markers, 1 variable binder, 1 field of an
  unconstructed parent); all uses binders/fields-of-binders.

## 6. NavierStokes.CorrectionStep.PhysicalFields (CorrectionStep.lean:912)
VERDICT: UNSUPPLIED  (trap (c): the ONLY construction is `PhysicalFields.add`, which takes TWO
PhysicalFields hypotheses; there is NO base case / zero / builder anywhere)
- `structure PhysicalFields (P : Type) where mean / pressure / oscillation / oscillatoryPressure /
  baseError / gaussianError / aliasError` (Type-valued data structure, arity 1).
- Occurrences of our structure: ALL inside CorrectionStep.lean (12 grep hits; `grep -rn
  'CorrectionStep.PhysicalFields'` artifact-wide returns NOTHING, so no external qualified use):
  912 decl; 921 `noncomputable def PhysicalFields.add (u v : PhysicalFields P) : PhysicalFields P where
  mean := u.mean + v.mean ...`; 941 structure PARAMETER `(v : PhysicalFields P)` of
  `structure RepresentsPhysical ... : Prop where`; 960 binder `{v w : PhysicalFields P}`;
  1003 binder `{v : PhysicalFields P}`; 968/973/979/985/989/993/997 are `simp only [... PhysicalFields.add
  ...]` REWRITES, not constructions.
- ROUTE 1 + trap (c) EXPLICIT CHECK: `PhysicalFields.add` DOES conclude `PhysicalFields P`, and it DOES
  construct with `where ... := u.x + v.x`, but every field value is built from its two `PhysicalFields`
  INPUTS. So it supplies nothing on its own, and no base case exists (no `PhysicalFields.zero`, no
  `Zero`/`Inhabited` instance, no `def ... : PhysicalFields P where` with concrete data).
- ROUTE 2: no anonymous `<...>`/`.mk`/`{ mean := ..., ... }` term of this type anywhere. Cross-check on
  the distinctive field names: every `aliasError :=` / `gaussianError :=` / `oscillatoryPressure :=`
  assignment in the artifact (PhysicalResidualTZ:201/207, CorrectionInitialization:1101/1111,
  ActualBaseResidual:838, HarmonicResidual:1350, PhysicalResidualNaturality:1176,
  AxisymmetricResidualGrouping:29/33/131, CorrectionState:155,
  CorrectionInitializationNoOptions:1112/1122) belongs to a DIFFERENT structure (ExcludedErrors /
  State / seed records) -- none of those files mentions PhysicalFields at all.
- ROUTE 3: no `instance` of it.
- ROUTE 4 BOTH directions: (a) P-as-field-of-S: NEGATIVE -- line 941 is a structure PARAMETER of
  RepresentsPhysical, not a field, and no structure has a field of type PhysicalFields. (b) S-as-field-of-P:
  its 7 fields are plain functions (`P -> Fin 3 -> ℝ` etc.), no audited predicate -> NEGATIVE.
- ROUTE 5 (twin, checked and excluded): `NavierStokes.ActualCycleResidualBounds.PhysicalFields`
  (ActualCycleResidualBounds.lean:1015, arity 6 `(B N : ℕ) (U : Set Cylinder) (s : State Point) ...`) is a
  different structure; its own occurrences are 1041/1042/1093 binders plus 1143
  `abbrev PhysicalData ... := PhysicalFields B N ActualPolarCoverage.nativeDomain s u P` -- a TYPE ALIAS,
  the exact trap-(b) shape, NOT a builder. Also `PositiveTimeCopyFamily.lean:103` and
  `OffplaneCorrectionExtensions.lean:728` are only `section PhysicalFields` names. No twin supplier, and
  no twin supplier would count anyway.
- Occurrences examined: 12 (1 decl, 1 self-recursive `add`, 3 binder/parameter sites, 7 simp rewrites).

## 7. NavierStokes.ParticularWaveBounds.CopyControl (ParticularWaveBounds.lean:563)
VERDICT: UNSUPPLIED
- `structure CopyControl (s : StripData (P x Plane)) (α : ℝ) (d : ℕ → LinearData P V H)
  (g : ℕ → Geometry) (copy : ℕ → Frequency) (L : ℕ → ℝ) (W : ℕ → ℝ → ℝ) where slowDomain / open_slow /
  domain / ... / energy / input_jets` (24 fields, data+Prop mix).
- grep last component `CopyControl` artifact-wide: 27 hits, but MOST are the DIFFERENT structure
  `ModalCopyControl` (see route 5 below). Hits of OUR `CopyControl` (whole-word, ParticularWaveBounds.lean
  only, 1 file): 563 decl; 593 `theorem CopyControl.waveClass`; 595 binder `(h : CopyControl s α d g copy
  L W)`; 1784 + 1785 binders `(hr/hi : CopyControl s α (fun n => (realData/imagData ...).linearData) g copy
  L W)`; 1940 + 1941 same pair; 2001 + 2002 same pair. -> 7 BINDER sites, 0 conclusions.
- ROUTE 1 + trap (c): the only self-named decl is :593 `CopyControl.waveClass`, whose CONCLUSION is
  `WaveClass s (fun n p => W n ((g n).coordinates (copy n) p.2).2) α (fun n => (d n).copySolve ...)`
  -- NOT CopyControl -- and it consumes `(h : CopyControl ...)` plus `h.errorRate`, `h.rate`,
  `h.open_slow`, ... So it is a pure CONSUMER; no `CopyControl.of_*` smart constructor exists.
  Read verbatim, the theorems at 1780-1795 and 1998-2010 take hr/hi as HYPOTHESES among many others
  (hb/hN/hNdot/hA/hf/...) and conclude wave-class/bound statements, never `CopyControl ...`.
- ROUTE 2: no `<...>`, `.mk`, `{ slowDomain := ... }`, `let/have H : CopyControl ... :=`, and no
  `constructor`/`refine <_,_>` with GOAL CopyControl anywhere.
- ROUTE 3: no `instance`.
- ROUTE 4 BOTH directions: (a) P-as-field-of-S: NEGATIVE. The only structure FIELDS of a *CopyControl type
  are ParticularWaveAssembly.lean:1431 `modal_real : ModalCopyControl s α frame ...` and :1434
  `modal_imag : ModalCopyControl s α frame ...` -- these are the OTHER structure, so even if that assembly
  structure is constructed it supplies ModalCopyControl, NOT our CopyControl (trap (a) applied in the
  correct direction: I checked CONTAINMENT, not mere distinctness -- see (b)).
  (b) S-as-field-of-P / containment check in the OTHER direction: I read ModalCopyControl's full field list
  (ParticularWaveBounds.lean:1290-1327): interval, open_interval, length_pos, contains_interval, bridge
  (`PrimaryCopyBridge.Inputs`), coefficient_smooth, forcing_smooth, columns_smooth, current_slot, rate,
  envelope_pos, envelope_deriv, errorRate, errorRate_nonneg, constant, constant_ge_one, coordinate_power,
  length_bound, exponential_bound, coordinate_bound, energy, input_jets -- there is NO field of type
  `CopyControl`. ModalCopyControl is a PARALLEL re-statement, not a wrapper, so constructing it would
  still not supply CopyControl. Our CopyControl is a field of NOTHING.
- ROUTE 5: no same-named twin in another namespace (all `CopyControl` hits are in
  NavierStokes.ParticularWaveBounds; `ModalCopyControl` is a different last name component).
- Occurrences examined: 8 of our structure (1 decl + 7 binders); all uses binders.

## 8. NavierStokes.PhysicalSignedWave.ReferencePhase (PhysicalSignedWave.lean:142)
VERDICT: UNSUPPLIED
- `structure ReferencePhase where geometry : CommonCoverSolve.Geometry; window :
  PeriodicPhaseAssembly.ClockWindow; epsilon : ℝ; axialFrequency : ℝ; radialFrequency : ℝ;
  angularMode : ℤ; F, G : PeriodicPhaseAssembly.Parameter → ℝ` (parameterless data structure).
- grep last component `ReferencePhase` artifact-wide: 9 hits, ALL in PhysicalSignedWave.lean (1 file):
  142 decl; 152/213 `namespace ReferencePhase` / `end`; 154 `variable (C : ReferencePhase)` = BINDER for
  the namespace; 463 `noncomputable def withReferencePhase (C : ReferencePhase) : PrimaryData U := ...`
  = BINDER (conclusion is `PrimaryData U`, NOT ReferencePhase; the name `withReferencePhase` is a
  consumer, not a builder -- it CONVERTS a given C); 794 `noncomputable def periodicAngular
  (C : ReferencePhase) ...` = BINDER, its conclusion at :801 is `(B.withReferencePhase C).Angular request
  reference where` -> the `where` builds an `Angular`, using C, NOT a ReferencePhase; 811
  `periodicStateAngular (C : ReferencePhase) ...` = BINDER, conclusion at :819 is again `... .Angular ...`.
- ROUTE 1: no decl anywhere concludes `ReferencePhase`. `grep ': ReferencePhase'` returns only the four
  binder occurrences above; no `ReferencePhase.mk`, no `.of_*`. Trap (c) not applicable.
- ROUTE 2: no `<...>` / `{ geometry := ..., window := ... }` term of this type. Cross-check on the
  distinctive field names `axialFrequency := / angularMode := / radialFrequency :=`: every hit
  (ActualReferenceRebase:42, PhysicalResidualTZ:178, MeanIncrementBounds:1119, CorrectionState:294,
  StateReindex:77, TorusMeanRequestRebase:44) sets a FUNCTION-valued `radialFrequency` (`fun _ => 0`,
  `o.radialFrequency`, `r.frequency`) in a different record, whereas ours is a bare `ℝ`; and none of those
  files mentions `ReferencePhase` at all. So none constructs ours.
- ROUTE 3: no `instance`.
- ROUTE 4 BOTH directions: (a) P-as-field-of-S: NEGATIVE -- no structure has a field of type
  ReferencePhase (all 4 typed occurrences are `variable`/`def` binders). (b) S-as-field-of-P: its 8 fields
  are Geometry/ClockWindow/reals/functions, consumed by the namespace lemmas; since it is never built it
  supplies nothing downstream -> NEGATIVE.
- ROUTE 5: no same-named twin in any other namespace (all 9 hits in one namespace/file).
- Occurrences examined: 9 (1 decl, 2 namespace markers, 4 binders incl. 1 `variable`, 2 `.Angular` builder
  conclusions that consume C); all uses binders.

## SUMMARY (all 8 items)
1 CoefficientSupport UNSUPPLIED | 2 PhysicalCopyBounds.CommonChart UNSUPPLIED (twin Local/Class excluded)
3 NativeOuterBounds UNSUPPLIED | 4 LocallyDominatedOn UNSUPPLIED (siblings LocallyDominated/Deriv supplied)
5 ActualWaveRegularity.NativeData UNSUPPLIED (field of ModeData -> ParticularData/SignedData, none built)
6 CorrectionStep.PhysicalFields UNSUPPLIED (only `add`, P from two P; no base case)
7 ParticularWaveBounds.CopyControl UNSUPPLIED (ModalCopyControl is parallel, contains no CopyControl field)
8 PhysicalSignedWave.ReferencePhase UNSUPPLIED

