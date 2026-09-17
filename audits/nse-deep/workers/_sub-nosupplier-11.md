# _sub-nosupplier-11 (READ-ONLY audit, NSE @ f9e8bc5)

## 1. NavierStokes.ActualSignedPhysicalData.PrimitiveLocalization (decl ActualSignedPhysicalData.lean:1322)
Grep `PrimitiveLocalization` -> 9 hits total, 4 in ActualSignedPhysicalData.lean, 5 in PositiveTimeSignedData.lean.
Own-namespace sites: 1322 decl; 1363 `variable ... (hloc : PrimitiveLocalization (h := h) f a b s)` BINDER;
1716 `variable ... (hloc : ...)` BINDER; 1837 `variable ... (hloc : ...)` BINDER (section WaveData). No
conclusion, no anonymous ctor, no `where`, no instance, no field-of-S occurrence, no abbrev alias.
TWIN (route 5): `NavierStokes.PositiveTimeSignedData.PrimitiveLocalization` decl PositiveTimeSignedData.lean:29
IS constructed: `theorem singletonLocalization ... : PrimitiveLocalization (h := ActualPrimary.h) ... where
normalized/domain/mask_pullback` at PositiveTimeSignedData.lean:542 (no PrimitiveLocalization hypothesis).
The twin is genuinely distinct (its `normalized` adds `y in nativePast`, drops `0 < y.2.1.1`); the file
`open ActualSignedPhysicalData`s but its own same-namespace decl shadows, and the ctor's field list matches
the twin. Twin supplier does NOT count.
VERDICT: UNSUPPLIED (4 occurrences examined: 1 decl + 3 variable binders).

## 2. NavierStokes.ActualStageEstimates.WaveInputs (decl ActualStageEstimates.lean:171)
Grep `WaveInputs` -> 6 hits. 171 decl (a non-Prop `structure ... where` record of WaveData fields);
197 `variable ... (W : WaveInputs DP IP KP DS IS KS)` BINDER (section CycleInputs);
276 same shape BINDER; ActualEndpointInputs.lean:223 `(W : ActualStageEstimates.WaveInputs ...)` BINDER of
`theorem endpointInputs_of_run` (it only PROJECTS W: `cycleInputs R M hN W`, `e.potential_smooth ... W ...`).
GermEndpointInputs.lean:167/190 are `section ExistingWaveInputs` / `end ExistingWaveInputs` -- trap (d),
not a namespace and not a twin (and not even the same identifier).
No conclusion `: WaveInputs ...`, no `WaveInputs.mk`/anonymous ctor, no `where` construction, no instance,
no occurrence as a FIELD of any other structure, no abbrev alias, no twin in any other namespace.
VERDICT: UNSUPPLIED (4 occurrences examined: 1 decl + 3 binders; 2 further hits are a section marker).

## 3. NavierStokes.ActualWaveRegularity.ParticularData (decl ActualWaveRegularity.lean:606)
Grep `ParticularData` -> 10 hits. Own sites: 606 decl (fields `mode : forall l j, ... ModeData ...`,
`radius_angular`, `radial_angular`, `frequency`); 618/620 `theorem ParticularData.block_regular ...
(h : ParticularData p v c u U r0 r1) (l : i) : AngularSmooth ... /\ ...` -- BINDER, conclusion is NOT
ParticularData; 628/630 `theorem ParticularData.regular ... (h : ParticularData ...) : AngularSmooth ...`
-- BINDER, conclusion not ParticularData; 811 `(hp : ParticularData p v c u U r0 r1)` BINDER.
PeriodizedWaveBounds.lean:1536/1680 = `section ActualParticularData` / `end` -- trap (d), not a namespace.
ActualCyclePreservation.lean:655 `noncomputable def nativeParticularData ... := (...).copyData ...` --
DIFFERENT identifier, no ascribed type, returns a `copyData` value, not a ParticularData; 670 projects it.
No conclusion, no ctor, no instance, no field-of-S, no abbrev, no twin namespace.
VERDICT: UNSUPPLIED (5 occurrences examined: 1 decl + 4 binders; no base case, only 2 consumer theorems).

## 4. NavierStokes.ActualWaveRegularity.SignedData (decl ActualWaveRegularity.lean:773)
Grep `SignedData` -> 24 hits; 20 are the unrelated MODULE/namespace `PositiveTimeSignedData` (import lines
and `PositiveTimeSignedData.<lemma>` calls in ActualSignedFamilySupport.lean / ActualSignedWaveData.lean --
that namespace contains no `SignedData` decl, only `PrimitiveLocalization` etc.). Real sites: 773 decl
(fields `mode : forall l, ModeData ...`, `angles : forall l, SignedAngles ...`);
783 `theorem SignedData.block_regular ... (h : SignedData p v c u U r0 r1) (l : i) : AngularSmooth ... ` BINDER;
794 `theorem SignedData.regular ... (h : SignedData ...) : ...` BINDER; 811 `(hs : SignedData p v c u U r0 r1)`
BINDER of `theorem next_regular` (conclusion is an AngularSmooth/Periodic/Support triple).
VERDICT: UNSUPPLIED (4 occurrences examined: 1 decl + 3 binders).

### Trap (b) chain, settled consistently (ActualWaveRegularity.lean)
`ModeData` (decl :390) occurs at :390 decl, :408 `namespace ModeData`, :412 `variable ... (h : ModeData a s d
e U r0 r1)` + `include h` (all lemmas in that namespace CONSUME it), :610 as the FIELD `mode` of
`ParticularData`, :776 as the FIELD `mode` of `SignedData`. So route 4 for ModeData needs ParticularData or
SignedData to be constructed -- and NEITHER IS (items 3 and 4 above: binder-only).
EXPLICIT: none of the three -- ActualWaveRegularity.ParticularData, .SignedData, .ModeData -- is ever
constructed anywhere in the artifact. All three are UNSUPPLIED.

## 5. NavierStokes.ErrorHarmonics.GaussianData.Compatible (decl ErrorHarmonics.lean:461)
It is a Prop-valued `def` (a 5-way conjunction over cutoff/amplitude/source/phase). Grep `Compatible`
repo-wide -> 83 hits; grep `GaussianData.Compatible` -> 1 (the decl). Dot-notation uses all live in
ErrorHarmonics.lean: 461 decl; 468 `theorem GaussianData.block_represents ... (hg : g.Compatible k Phi kp) :
(g.block ...).oscillation = g.error k` BINDER (conclusion is an equation); 479
`(hg : forall s < steps, (g s).Compatible k Phi kp)` BINDER; 594 same shape BINDER. No decl anywhere
CONCLUDES `.Compatible`, no `And.intro`/anonymous-ctor supplier, no instance, not a field of any structure.
TWINS (route 5), checked and NOT counted: `NavierStokes.ActualCycleExcluded.Compatible` (:54; IS concluded at
ActualCycleGeometry.lean:84 / ActualCycleParameters.lean:228,453) and `NavierStokes.AxisCoefficientSpace.
Compatible` (:92; IS concluded at :304), plus `ValidBandGluing/ValidDyadicBandCover.Compatible`,
`NaturalAxisBridge.CompatibleData`, `PositiveAxisExistence.RealCompatible`, `PrimaryTargetBounds.
CompatiblePair` -- all different, fully-qualified names; none supplies ErrorHarmonics.GaussianData.Compatible.
VERDICT: UNSUPPLIED (4 occurrences examined: 1 decl + 3 binders).

## 6. NavierStokes.GaugeMomentBalances.LocalFluxInputs (decl GaugeMomentBalances.lean:325)
Grep `LocalFluxInputs` -> 5 hits, all in GaugeMomentBalances.lean, no twin in any other namespace.
325 decl (Prop, 4 fields `velocity/radial/axial/stress : LocalField a b U _`);
363/364 `theorem LocalFluxInputs.localize ... (H : LocalFluxInputs a b U u R Z T) ... : FluxInputs a b
(localizeFamily ...) ...` -- BINDER; its CONCLUSION is the DIFFERENT structure `FluxInputs` (built with
`<...>` from H's projections), so it supplies FluxInputs, not LocalFluxInputs (trap (c) shape);
393 `(H : LocalFluxInputs a b U u R Z T)` BINDER in `theorem local_angular_moment` (conclusion = a
radialMoment equation); 408 same shape BINDER in `theorem local_axial_moment`.
No conclusion `: LocalFluxInputs ...`, no ctor/`.mk`/`where`, no instance, not a field of any structure.
VERDICT: UNSUPPLIED (4 occurrences examined: 1 decl + 3 binders).

## 7. NavierStokes.LocalPhysicalCopyBounds.PatchData (decl LocalPhysicalCopyBounds.lean:401)
Grep `PatchData` -> 4 hits, all in LocalPhysicalCopyBounds.lean, no twin anywhere.
401 decl (a data `structure ... where` with amplitudeDomain/Core/Open/... 17 fields);
425 `theorem PatchData.amplitude_contDiff (hp : PatchData f a h r0) ... : ContDiff R inf (f.amplitude k I)`
BINDER; 433 `theorem PatchData.smoothData (hp : PatchData f a h r0) (hr : SupportData ...) (ha : 0 < a) :
SmoothData f a h r0` BINDER -- conclusion is the DIFFERENT structure `SmoothData` (trap (c) shape);
460 `theorem PatchData.sum_smooth (hp : PatchData f a h r0) ...` BINDER.
No conclusion `: PatchData ...`, no `<...>`/`.mk`/`where` construction of it, no instance, not a field of any
structure, no abbrev alias.
VERDICT: UNSUPPLIED (4 occurrences examined: 1 decl + 3 binders).

## 8. NavierStokes.ParticularWaveAssembly.BackgroundControl (decl ParticularWaveAssembly.lean:1403)
Grep `BackgroundControl` -> 6 hits, no twin namespace. 1403 decl (Prop);
ActualParticularRealization.lean:254 `(B : BackgroundControl (CorrectionStep.ParticularParameters.nativeStrip
s) D.directions D.background D.carrierBlock j)` BINDER of `theorem corrected_amplitude_invariant`
(conclusion = `Invariant ...`); :279 and :322 `(B : forall j in modes N, BackgroundControl ...)` BINDERS.
ROUTE 4 checked (two levels, trap (b)): it IS the field `background` of TWO structures --
(i) `ParticularWaveAssembly.LocalControl` (decl :1422, field at :1439) and
(ii) `CorrectionStep.ParticularParameters.NativeDynamics` (decl CorrectionStep.lean:6124, field at :6125).
NEITHER parent is constructed:
 * `LocalControl` (16 hits): all uses are binders `(C : LocalControl D.reference ... )`
   (PhysicalParticularWave.lean:40,627,895,1289; ActualParticularPhysicalData.lean:192;
   ActualParticularRealization.lean:727,810,899,916; ParticularWaveAssembly.lean:1484 `variable`),
   plus `namespace LocalControl`/`end` (:1477/:1718) and `section LocalControl`/`end`
   (ActualPrimaryBounds.lean:914/1079, trap (d)). ParticularWaveAssembly.lean:1758 is
   `noncomputable def AssemblyData.controls N alpha kappa : Type := forall j in modes N, LocalControl ...`
   -- a TYPE abbreviation, and every use of `D.controls` is again a binder
   (PhysicalParticularWave.lean:1137,1235,1341,1351,1359,1369 `(C : D.controls N alpha kappa)`); nothing
   ever produces a term of it.
 * `NativeDynamics` (ParticularParameters one): all uses are binders `(d : NativeDynamics h)` /
   `(dyn : forall j hj, NativeDynamics (C j hj))` (CorrectionStep.lean:6142,6165,6175,6196,6479-6526,6572,
   7116,7136,7179,7376,8154,8187) with non-NativeDynamics conclusions; ActualPrimaryDynamics.lean:53/198 is
   `section NativeDynamics`/`end` (trap (d)). No decl concludes NativeDynamics, no ctor, no instance.
VERDICT: UNSUPPLIED (6 occurrences examined: 1 decl + 3 binders + 2 field-of-S sites whose parents
LocalControl and ParticularParameters.NativeDynamics are themselves binder-only).

## 9. NavierStokes.PhysicalResidualJetBounds.ResidualChartData (decl PhysicalResidualJetBounds.lean:774)
Grep `ResidualChartData` -> 6 hits, all in PhysicalResidualJetBounds.lean, no twin namespace.
774 decl (data structure: `active`, `changed_subset`, `gap`, `gap_le`, `realization : ChartIdentity ...`,
`annulus`, `in_domain`); 793/795 `theorem ResidualChartData.residual_jet_bound ... (d : ResidualChartData
a b h N D U F u u0 p p0) ... : exists C, ...` BINDER; 833/835 `theorem ResidualChartData.residual_jetRate ...
(d : ResidualChartData ...)` BINDER; 1052 `(d : forall J, ResidualChartData a b h N D (U J) (F J) (u J) u0
(p J) p0)` BINDER of `theorem finite_residual_rates` (conclusion = a `DiagonalResidual.JetRate` statement).
No conclusion `: ResidualChartData ...`, no anonymous ctor / `.mk` / `where` / `let`, no instance, not a
field of any other structure, no abbrev alias.
VERDICT: UNSUPPLIED (4 occurrences examined: 1 decl + 3 binders).

## 10. NavierStokes.ActivationContinuation.HoldSourceControl (decl ActivationContinuation.lean:1861)
Prop-valued `noncomputable def HoldSourceControl (h j sigma Lambda B : R) : Prop := forall {D} (P) (p),
p.2 in Icc (-1) 1 -> logSlope P p = 3/5 -> |Lambda*(P.U p - ...)| <= B -> ... -> 5/4 < sourceQ P h p`.
Grep `HoldSourceControl` (also -i) -> 3 hits: 1861 decl; 1876 `(hsource : HoldSourceControl h j sigma Lambda
(B + 2))` BINDER of `theorem comparable_final_first`; 1908 same BINDER of `theorem comparable_relaxed`.
ROUTE 2 HIT (construction without naming P): `theorem ordered_reference_preparation`
(ActivationContinuation.lean:977) has as the SECOND component of its proved existential conclusion
(:984-990) the VERBATIM body of HoldSourceControl with B := B + 2:
`(forall {D : RadialDomain} (P : Profiles D) (p : Point), p.2 in Icc (-1) 1 -> ReferenceBounds.logSlope P p
= 3/5 -> |Lambda*(P.U p - NaturalAxisData.U j p.2)| <= B + 2 -> ... -> (5/4 : R) < ReferenceBounds.sourceQ
P h p)`, discharged from `actual_hold_source_threshold` (:1001). It is then USED AS a HoldSourceControl:
`theorem exists_activation_continuation` does `obtain <hsource, C0, K, ...> := ordered_reference_preparation
...` (:1954) and passes that same `hsource` into both consumers -- `relaxed := fun p hn hX =>
comparable_relaxed E hs r c hc hsource hn hX` (:1968) and `final_first := ... comparable_final_first E hs r c
hc hsource hn hX` (:1969) -- so the Prop def is genuinely inhabited (the def unfolds; no HoldSourceControl
hypothesis is taken by :977, so trap (c) does not apply). No twin namespace (case-insensitive grep = 3 hits).
VERDICT: SUPPLIED <NavierStokes/ActivationContinuation.lean:977 (used at :1954/:1968/:1969), route 2>.

## SIDE NOTE A (requested): ActualStageEstimates.Representations vs GluedStageEstimates.Representations
Grep `Representations` -> 21 hits. TWO distinct structures with the same last component:
 * `NavierStokes.GluedStageEstimates.Representations` (decl GluedStageEstimates.lean:288) IS CONSTRUCTED,
   through its own `abbrev ActualRepresentations` (:675-677): `theorem representations_of_signed_eqOn`
   (ActualCandidateAssembly.lean:772) concludes `GluedStageEstimates.ActualRepresentations (runData ...) ...`
   and proves it with `refine <?_,?_,?_,?_,?_,?_>` (route 2); `theorem representations`
   (ActualCandidateAssembly.lean:869) concludes it again from that lemma. => SUPPLIED.
 * `NavierStokes.ActualStageEstimates.Representations` (decl ActualStageEstimates.lean:285) is binder-only:
   :304 `variable ... (e : Representations R M hN W qbig WA WP A Bdirect P)` + consumer theorems
   `Representations.potential_smooth/.direct_smooth/.pressure_smooth` (:309,:320,:330, all taking `e`),
   and ActualEndpointInputs.lean:227 `(e : ActualStageEstimates.Representations R M hN W qbig WA WP A V P)`
   BINDER. Nothing concludes it. => UNSUPPLIED. The Glued twin's suppliers do NOT count for it
   (different namespace, different argument list: particularA/particularP vs WA/WP).

## SIDE NOTE B (requested): is ActualCycleResidualBounds.PhysicalFields only an `abbrev` alias of
## CorrectionStep.PhysicalFields?  -> THE ALIAS CLAIM IS REFUTED, AND THE PREDICATE IS SUPPLIED.
Grep `PhysicalFields` -> ActualCycleResidualBounds.lean:1015 is a genuine `structure PhysicalFields (B N : N)
(U : Set Cylinder) (s : State Point) (u : VelocityField) (P : PressureField) : Prop where velocity_smooth /
pressure_differentiable / velocity_germ / pressure_germ / exterior` -- NOT an abbrev, and unrelated to
`CorrectionStep.PhysicalFields (P : Type)` (CorrectionStep.lean:912, a DATA record of 3 component fields with
a `.add` closure at :921). The abbrev runs the OTHER WAY: ActualCycleResidualBounds.lean:1142
`abbrev PhysicalData (B N) (s) (u) (P) := PhysicalFields B N ActualPolarCoverage.nativeDomain s u P`.
SUPPLIER FOUND through that abbrev (route 2/1): `theorem ActualPhysicalPrefixFields.physicalFields_all`
(ActualPhysicalPrefixFields.lean:475) concludes `forall J, ActualCycleResidualBounds.PhysicalData B Nr ...`
from StageRealizations + ExteriorStages + floor + smoothness + CycleRepresentation (NO PhysicalFields/
PhysicalData hypothesis -- trap (c) does not apply), proved via `physicalFields_of_stages`; and
`theorem ActualCandidateAssembly.physicalData` (ActualCandidateAssembly.lean:1079) concludes the same for the
actual run using it. Consumers of the binder form are ActualCycleResidualBounds.lean:1042,:1093,:1161,:1195,
GluedStageEstimates.lean:385,690,733, ActualStageEstimates.lean:350,408, WholeDomainStageBounds.lean:165.
So: `NavierStokes.ActualCycleResidualBounds.PhysicalFields` = SUPPLIED
<NavierStokes/ActualPhysicalPrefixFields.lean:475 (also ActualCandidateAssembly.lean:1079), route 1 via the
`PhysicalData` abbrev>.

