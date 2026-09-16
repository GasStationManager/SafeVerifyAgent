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

## 6. NavierStokes.CorrectionStep.SignedParameters.Dynamics (CorrectionStep.lean:3982)
VERDICT: UNSUPPLIED. Every hit is in CorrectionStep.lean; 19 lines mention it, all BINDERS.
Decl :3982 `structure SignedParameters.Dynamics (p : SignedParameters D) (s : StripData D)
(request : ℕ → D × ℝ → SignedWaveUpdate.Vec2) where` -- 17 fields, first one the DATA field
`slope : ℕ → ℝ`, then angular/angular_direction/angular_frequency/angular_nonzero/geometry/
matrix_frozen/target_frozen/request_frozen/mask_frozen/frequency_nonzero/ode/action_eq/cutoff_smooth...
(so not a Prop; no `constructor`/`refine ⟨..⟩` proof of it can exist).
Census of the 9 consumer decls, each with a `(h : p.Dynamics s request)` BINDER and a NON-Dynamics
conclusion: :4010 `Dynamics.phase_eq`, :4020 `Dynamics.good_represents`, :4042
`Dynamics.exact_represents`, :4053 `Dynamics.linear_identity` (also takes `(hc : p.Control ...)`),
:4105 `Dynamics.gaussian_represents`, :4115 `Dynamics.context_linear_identity`, :4159
`Dynamics.linearGood_bounds`, :4267 `Dynamics.full_divergence_zero`, :4308 `Dynamics.modeSolenoidal`
(binder lines :4011,:4021,:4043,:4056,:4106,:4119,:4163,:4271,:4312). ZERO conclusions are `Dynamics ..`.
Route 1: none -- all 9 are exactly the trap shape (Dynamics binder in, equation/bound out).
Route 2: no `⟨..⟩`/`.mk`/record literal / `let H : p.Dynamics := ..` anywhere; the whole tree grep for
`Dynamics` shows this name only at these 19 CorrectionStep lines (the other `*Dynamics` hits are the
unrelated identifiers ActualPrimaryDynamics / ActualParticularDynamics / ActualSignedCommonDynamics /
NativeDynamics).
Route 3: no instance. Route 4: NOT a field of any structure. I checked the natural containment candidate
explicitly: `structure NativeDynamics` at :6000 (PeriodizedSignedParameters) and `structure NativeDynamics
: Prop` at :6124 (ParticularParameters) do NOT have a `Dynamics` field -- :6000's fields are
slope/angular/open_patch/radius_nonzero/radial_radius/matrix_frozen/target_frozen/request_frozen/
mask_frozen/frequency_nonzero/ode/action_eq (a PARALLEL re-statement over `h.phasePatch`, not a wrapper),
and no `structure ... where` line anywhere contains `: p.Dynamics`/`: SignedParameters.Dynamics`.
Route 5: no twin -- `Dynamics` as a bare last component exists only at :3982; `NativeDynamics` is a
DIFFERENT name (and is itself never constructed either: :6029..:7429 are all `(d : NativeDynamics h ..)`
binders and :6572/:7179/:7376/:8154/:8187/:8334 are `(dyn : ∀ .., NativeDynamics (C ..))` binders).

## 7. NavierStokes.GlobalSlowProfiles.PatchSupport (GlobalSlowProfiles.lean:400)
VERDICT: SUPPLIED (route 2: unnamed construction by delta-unfolding), witness
NavierStokes/GlobalSlowProfiles.lean:639-643; ultimate producer
NavierStokes/PositiveOrderMoments.lean:916 (`exists_parameterized_exact_repair`).
Decl :400 `noncomputable def PatchSupport (a b : ℝ) (f : Field) : Prop :=
  ∀ eta, tsupport (fun R => f (R, eta)) ⊆ Ioo a b` -- a plain (non-irreducible) Prop def, so any term of
the unfolded ∀-statement inhabits it.
Name-hit census (9 sites, 1 file): :400 decl; :403 `theorem patch_zero .. (hs : PatchSupport a b f)`
BINDER (concludes `f (R, eta) = 0`); :416 `noncomputable def phiCorrection .. (hs : PatchSupport a b f)
(C : ℝ) : EvenProfile S` BINDER; :440,:447,:460,:470,:562,:571 all `(hs : PatchSupport a b f)` BINDERS
(:571 `theorem exterior_phiCorrection .. (hs : PatchSupport a b f) (C : ℝ) : Exterior B S (phiCorrection
hS ha hf hs C)`). ZERO hits have `PatchSupport` as the conclusion, so route 1 is empty -- BUT route 2
fires:
 THE SUPPLIER: PositiveOrderMoments.lean:916 `theorem exists_parameterized_exact_repair (lam a b : ℝ) ..
 : ∃ du de : JointProfile, ContDiffOn ℝ ∞ du (univ ×ˢ S) ∧ ContDiffOn ℝ ∞ de (univ ×ˢ S) ∧
 (∀ eta, tsupport (fun R => du (R, eta)) ⊆ Ioo a b) ∧
 (∀ eta, tsupport (fun R => de (R, eta)) ⊆ Ioo a b) ∧ ...` -- the 3rd and 4th conjuncts are LITERALLY the
 body of `PatchSupport a b du` / `PatchSupport a b de`, and this theorem takes NO PatchSupport hypothesis
 (its hypotheses are 0<lam, 0<a, a<b, IsOpen S, 0<n, ContDiffOn A, A≠0, two initial-row equations,
 jointRowDensity smoothness, 0≤B, exterior vanishing).
 THE CONSTRUCTION SITE: GlobalSlowProfiles.lean:639 `obtain ⟨du, de', hdu, hde, hduS, hdeS, hm⟩ :=
 PositiveOrderMoments.exists_parameterized_exact_repair lam a b hlam ha hab hS hn uraw eraw oraw A hA hAn
 hu0 he0 hd hB.le hs`, then :643 `let phin : EvenProfile S := phi n + phiCorrection hS ha hde hdeS C`
 -- `hdeS` is accepted in the `(hs : PatchSupport a b f)` slot of `phiCorrection` (:416), i.e. the
 PatchSupport hypothesis IS discharged here; the same `hdeS` is re-used at :650, :656, :682, :685, :686
 (e.g. `exterior_phiCorrection hS ha hab hbB hde hdeS C`), and the sibling `hduS` likewise feeds the
 evenCorrection lemmas.
Route 3: no instance (it is a Prop def, not a class). Route 4: not a field of any structure (all 9 sites
are `(hs : ..)` binders). Route 5: single declaration of the name in the tree; no twin, so no
mis-attribution risk.

## 8. NavierStokes.ParticularWaveBounds.CopyGeometryMatch (ParticularWaveBounds.lean:1764)
VERDICT: UNSUPPLIED (route 4 candidate found and REFUTED: the containing structure is itself never
constructed).
Decl :1764 `structure CopyGeometryMatch (s : StripData (P × Plane)) (dirs : GraphDirections (P × Plane))
(base : WaveCoefficients (P × Plane)) (t : ℕ → TangentData P ProblemStatement.Space) (g : ℕ → Geometry)
(copy : ℕ → Frequency) : Prop where` -- fields normal / damping / fast / action ...
Name-hit census (10 lines, 2 files): ParticularWaveBounds.lean :1857,:1882,:1910,:1952,:2013,:2059,
:2119,:2183 -- ALL `(hgeometry : CopyGeometryMatch s dirs base t g copy)` BINDERS (e.g. :1857 sits in a
theorem concluding `... .principal s dirs n x = -source n x`), and ParticularWaveAssembly.lean:1455.
ZERO conclusions => route 1 empty. No `⟨..⟩`/`.mk`/record literal / `constructor` site => route 2 empty.
No instance => route 3 empty. No twin: the name is declared exactly once in the tree => route 5 empty.
ROUTE 4 CHECKED EXPLICITLY (this is the interesting part):
 CopyGeometryMatch IS a field of another structure. ParticularWaveAssembly.lean:1455 reads
 `  geometry : CopyGeometryMatch s dirs (actualCarrier base b j) (tangentFamily r charts j)
      (bandGeometry r charts) copy`
 and the enclosing declaration is S = `NavierStokes.ParticularWaveAssembly.LocalControl`, declared at
 ParticularWaveAssembly.lean:1422 `structure LocalControl (r : Reference P) (charts : BandCharts P) ...`
 (the nearest preceding top-level `structure`; the next one after it is at :1477 `namespace LocalControl`).
 So constructing LocalControl WOULD supply CopyGeometryMatch. But LocalControl is ITSELF never
 constructed: grep "LocalControl" over the tree gives 16 lines and every single use is a BINDER or an
 alias --
   ParticularWaveAssembly.lean:1422 decl; :1477/:1718 `namespace`/`end`; :1484
   `(C : LocalControl r charts c u b G A j base copy s dirs α κ)` (a `variable` for the whole
   LocalControl namespace of consumer theorems); :1758 inside
   `noncomputable def controls (N : ℕ) (α κ : ℝ) : Type := ∀ j ∈ modes N, LocalControl D.reference
   D.charts D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j D.background D.copy D.strip
   D.directions α κ` -- a TYPE ALIAS, not an inhabitant;
   PhysicalParticularWave.lean:40,:627,:895,:1289 `(C : LocalControl D.reference ...)` binders;
   ActualParticularPhysicalData.lean:192, ActualParticularRealization.lean:727,:810,:899,:916 same
   binder shape; ActualPrimaryBounds.lean:914/:1079 are an unrelated `section LocalControl` marker pair.
 The alias `D.controls N α κ` is likewise only ever a BINDER type (`(C : D.controls N α κ)` at
 PhysicalParticularWave.lean:1137,:1235,:1341,:1351,:1359,:1369) -- never a value, no
 `⟨..⟩`/`fun j hj => ..` inhabitant anywhere. Hence route 4 does NOT fire: no `LocalControl.mk` /
 `{ geometry := .. }` / anonymous-constructor site exists, so the field is never filled and
 CopyGeometryMatch is never produced.

