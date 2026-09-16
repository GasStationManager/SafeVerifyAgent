# sub-nosupplier-4 (READ-ONLY audit, NSE f9e8bc5)

## 1. NavierStokes.ErrorHarmonics.GaussianData (ErrorHarmonics.lean:446)
VERDICT: UNSUPPLIED. 14 grep hits, 1 file (ErrorHarmonics.lean) only.
Census: :446 = `structure GaussianData (D : Type) [..] where` (a DATA structure, 6 fields:
directions/cutoff/amplitude/source/harmonic/phase). All other 13 hits are BINDERS or projections:
:454,:457,:461,:467 `(g : GaussianData D)` binders of defs/theorems about g;
:473,:477,:489,:501,:509 `(g : ℕ → GaussianData D)` binders; :581,:591,:604,:615
`(g : ℕ → GaussianData (Lift S))` binders. ZERO hits are a CONCLUSION.
Route 1: no decl concludes `GaussianData ...`. Route 2: no `⟨..⟩`/`.mk`/`{ .. := .. }` of it
(grep over ALL .lean shows the type name appears nowhere else, so no ascribed construction).
Route 3: no `instance`. Route 4: no `structure`/field of type GaussianData (no hit of the form
`field : GaussianData` outside binders). Route 5: single namespace, no twin (name unique, 1 file).
=> nothing in the artifact ever produces an inhabitant.

## 2. NavierStokes.PhysicalResidualNaturality.PositiveSupport (PhysicalResidualNaturality.lean:713)
VERDICT: UNSUPPLIED. 43 grep hits over 4 files (PhysicalResidualNaturality, GaussianErrorNaturality,
CorrectionStep, ActualParticularRealization); every one except the decl is a BINDER.
Census: :713 decl `structure PositiveSupport (b : CorrectionState.HarmonicBlock Associated)
(G A : HarmonicResidual.BlockCoefficients Associated) (n : ℕ) where` -- 7 fields, incl. the DATA
field `supportSet : Set Associated` (so it is not a Prop, and no `constructor`-style proof can appear).
:727 `theorem PositiveSupport.source_zero ... (H : PositiveSupport b G A n) ... : residualSource ... = 0`
-- CONSUMER (binder H, conclusion is an equation, NOT PositiveSupport). All remaining hits are the
paired binders `(hn : PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)` and
`(hr : ... D.reference.band)` at PhysicalResidualNaturality:744,745,764,765,774,775;
GaussianErrorNaturality:260,261,274,275,324,325,351,352,389,390,426,427,459,460;
CorrectionStep:7980,7981,7991,7992; ActualParticularRealization:105,106,317,318,409,410,510,511,
891,892,991,992,1056,1057. ZERO conclusions.
Route 1: none (the only `PositiveSupport.*` decl concludes an equation from a PositiveSupport binder --
the trap case, supplies nothing). Route 2: no `⟨..⟩`/`.mk`/`{ .. }`; case-insensitive grep
`positivesupport` finds ONLY :713 and :727, so there is no lowercase smart constructor/`of_` builder.
Route 3: no instance. Route 4: NOT a field of any structure -- every hit is a `(h.. :` binder, none is
`fieldname : PositiveSupport ...` inside a `structure ... where` block. Route 5: only ONE declaration of
this name in the whole tree (single namespace NavierStokes.PhysicalResidualNaturality); no twin.
=> the hypothesis is assumed everywhere and produced nowhere.

## 3. NavierStokes.ActualParticularDynamics.SourceClasses (ActualParticularDynamics.lean:1335)
VERDICT: SUPPLIED (route 2: unnamed construction of the abbrev's body), at
NavierStokes/ActualParticularCycleData.lean:648 and :679.
Decl: `abbrev SourceClasses (x : CycleState (Label B N0)) (N : ℕ) (α : ℝ) : Prop :=
  ∀ j ∈ modes N, LabelSumBounds.UniformWaveClass
    (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
    nativeEnvelope α (currentSource x j)` -- an ABBREV (reducible), so a term of the unfolded
∀-form supplies it without ever naming SourceClasses.
Name-hit census (13): :1335 decl; :1385,:1406,:1460,:1473,:1490,:1505,:1514,:1530,:1585 all
`(Hs : SourceClasses x N α)` BINDERS; CommonCoverClass.lean:846/902 and
ActualMeanPhysicalData.lean:1115/1195 are unrelated `section SourceClasses` markers (NOT the predicate).
SUPPLIER CHAIN (all verified verbatim):
 (a) ActualParticularStageControls.lean:560 `theorem current_source_class (x) {α} (H :
     UniformHarmonicInteraction.UniformVelocity ... ) (j : ℤ) (hj : j ≠ 0) : LabelSumBounds.
     UniformWaveClass (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip))
     nativeEnvelope α (currentSource x j)` -- conclusion is EXACTLY the SourceClasses body at one j,
     and its hypotheses are UniformVelocity + j≠0, i.e. NO SourceClasses/UniformWaveClass-of-
     currentSource binder. (Not the route-1 trap.)
 (b) ActualParticularCycleData.lean:639 `theorem native_source_class (H : Invariant σ x) (j) (hj : j ≠ 0)
     : ... UniformWaveClass (sourceStrip (angleStrip slowStrip)) nativeEnvelope (1/2+σ)
     (currentSource (particularState x) j) := ActualParticularStageControls.current_source_class _
     (native_residual H) j hj` -- same body, discharged from `Invariant`.
 (c) THE CONSTRUCTION: ActualParticularCycleData.lean:648 (inside `theorem solenoidal`) passes
     `(fun j hj => native_source_class H j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1)` as the
     `Hs : SourceClasses ...` argument of `ActualParticularDynamics.cycle_modeSolenoidal`; the identical
     lambda appears at :679 feeding `cycle_context_linear_cancellation`. That lambda IS an inhabitant of
     `∀ j ∈ modes N, UniformWaveClass ... (currentSource x j)` = `SourceClasses x N α`.
 Also ActualParticularStageControls.lean:1430 builds the body per-j from `current_source_class x H j`.
Route 5 note: `GluedStageEstimates.lean:555 theorem current_source_class` is a DIFFERENT same-named
twin; I did NOT count it -- the supplier used above is the fully qualified
`NavierStokes.ActualParticularStageControls.current_source_class`, reached via the explicit qualified
call at ActualParticularCycleData.lean:644.

## 4. NavierStokes.CorrectionStep.ParticularParameters.NativeControl (CorrectionStep.lean:5693)
VERDICT: UNSUPPLIED. All hits inside CorrectionStep.lean only (grep "NativeControl" over the whole
tree returns 23 lines, ALL in CorrectionStep.lean).
Namespace pinned: `namespace ParticularParameters` opens at :5679 (after `end PeriodizedSignedParameters`
at :5677), so :5693 `structure NativeControl (W : ℕ → (Q × ℝ) × Plane → ℝ) (α κ : ℝ) where`
(fields cells/phasePatch/background/frame/envelope/realControl/...) is the ParticularParameters one.
Its applications are recognisable by ARITY: `p.NativeControl s c u b G A j W α κ` (9 explicit args)
vs the PeriodizedSignedParameters twin's `p.NativeControl s P κ`.
BINDER census for THIS twin (9 sites, all BINDERS, all parenthesised, none a structure field):
:5776 `theorem NativeControl.raw_jets (h : p.NativeControl s c u b G A j W α κ) :` (consumer, concludes
LocalJets), :5791 `theorem NativeControl.global_bounds (h : ...) (hκ : κ ≤ 1/2) :` (consumer),
:5823 `(C : ∀ j ∈ ParticularWaveAssembly.modes N, p.NativeControl ...)`, :6122 `(h : ...)`,
:6477 `{h : ...}` (variable), :6571 `(C : ∀ j ∈ modes N, ...)`, :7107 `(h : ...)`,
:7178 `(C : ∀ j ∈ modes N, ...)`, :7375 `(C : ∀ j ∈ modes N, ...)`, :8153 and :8186
`(C : ∀ l j, j ∈ modes N → (p l).NativeControl s c u (b l) (G l) (A l) j (W l) α κ)`.
ZERO conclusions.
Route 1: no decl concludes `NativeControl ...`; the two `NativeControl.*` theorems are the trap shape
(NativeControl binder in, other Prop out) -- they supply nothing.
Route 2: no `⟨..⟩`/`.mk`/`{ .. := .. }` producing it; case-insensitive grep for a lowercase
builder (`nativecontrol`) returns NOTHING, so there is no `nativeControl`/`of_*` smart constructor.
The ONLY cross-file consumer of this namespace's uniform layer,
`ParticularParameters.uniform_assembled_bounds` (:8130, called from
ActualParticularStageControls.lean:1431), takes hW/ha/hp/hg UniformWaveClass hypotheses and NO
NativeControl -- so no external call site ever has to build a NativeControl either.
Route 3: no instance. Route 4: NOT a field of any structure -- every one of the 9 sites is a
`( .. : ..)`/`{ .. : ..}` binder in a `theorem`/`variable` line, never a bare `field : NativeControl ..`
inside a `structure ... where`. Downstream `NativeDynamics (C l j hj)` merely TAKES a NativeControl as a
parameter, so it cannot supply one. Route 5: the same-named twin is
NavierStokes.CorrectionStep.PeriodizedSignedParameters.NativeControl (:5543, item 5); it is a DISTINCT
structure and is itself unsupplied -- no credit transferred in either direction.

## 5. NavierStokes.CorrectionStep.PeriodizedSignedParameters.NativeControl (CorrectionStep.lean:5543)
VERDICT: UNSUPPLIED. Same single-file grep set as item 4.
Namespace pinned: `namespace PeriodizedSignedParameters` :5537 .. `end` :5677, so :5543
`structure NativeControl (P : ℕ → D → ℝ) (κ : ℝ) where` (fields cells, phasePatch, background,
covariance, mask, fundamental, normalMotion, action, cutoff, cutoff_support, phase_cover,
envelope_nonneg, lower, upper, lower_pos, normal_lower, normal_upper, inverse_frequency) is this twin.
Recognisable by arity `p.NativeControl s P κ`.
BINDER census for THIS twin (9 sites, all BINDERS): :5595 `theorem NativeControl.raw_jets
(h : p.NativeControl s P κ) ... :` (consumer -> LocalJets), :5616 `theorem NativeControl.global_bounds
(h : p.NativeControl s P κ) (hκ : κ ≤ 1 / 2)`, :5649 `theorem NativeControl.block_bounds (h : ...)`,
:5995 `(h : p.NativeControl s P κ)`, :6260 `{h : p.NativeControl s P κ}` (variable),
:7011 `(h : p.NativeControl s P κ)` + :7014 `theorem NativeControl.amplitude_cover` (consumer using
that variable), :7426 `{h : p.NativeControl s P κ}`, :8333 `(C : ∀ l, (p l).NativeControl s (P l) κ)`
(a `variable` line in the ι-indexed PeriodizedSignedParameters section). ZERO conclusions.
Route 1: none (all `NativeControl.*` decls conclude something else FROM a NativeControl binder -- the
trap; they supply nothing). Route 2: no anonymous-constructor/`.mk`/record-literal site; no lowercase
builder anywhere (case-insensitive grep clean). Route 3: no instance. Route 4: NOT a field of any
structure (every site is a parenthesised/braced binder, never `field : NativeControl` in a `structure`
body); `NativeDynamics (C l) request` only CONSUMES it as a parameter. Route 5: twin is
NavierStokes.CorrectionStep.ParticularParameters.NativeControl (:5693, item 4), a DISTINCT structure with
different arity, also unsupplied; no cross-credit.
