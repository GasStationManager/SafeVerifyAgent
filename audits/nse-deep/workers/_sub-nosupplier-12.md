# _sub-nosupplier-12 (NSE f9e8bc5, read-only)

## 1. NavierStokes.ActualCycleResidualBounds.PhysicalFields (ActualCycleResidualBounds.lean:1015)
VERDICT: **SUPPLIED** (route 1 + route 2)
Key: the structure is re-exported as `abbrev PhysicalData B N s u P := PhysicalFields B N ActualPolarCoverage.nativeDomain s u P` (ActualCycleResidualBounds.lean:1142), so grepping only "PhysicalFields" hides the supplier.
Supplier: `NavierStokes.ActualPhysicalPrefixFields.physicalFields_of_stages` (ActualPhysicalPrefixFields.lean:438-455):
  conclusion `ActualCycleResidualBounds.PhysicalData B Nr ... ` proved `by constructor` + 5 field proofs.
  Its hypotheses are StageRealizations / ActualExteriorPrefix.ExteriorStages / ContDiffOn / CycleRepresentation -- NO PhysicalFields or PhysicalData binder (trap (c) checked, clean).
Also `physicalFields_all` (:474) = `fun J => physicalFields_of_stages ...` (same, no P binder).
Consumers (all binders): ActualCycleResidualBounds.lean:1042,1093,1161,1195; GluedStageEstimates:385,690,733; WholeDomainStageBounds:165; ActualStageEstimates:350,408; ActualCandidateAssembly:1081.
Twin note: `NavierStokes.CorrectionStep.PhysicalFields` (CorrectionStep.lean:912) is a DIFFERENT, non-Prop structure (data, `PhysicalFields (P : Type)`); its `.add` did not count here. `section PhysicalFields` in PositiveTimeCopyFamily.lean:103 / OffplaneCorrectionExtensions.lean:728 are sections, not namespaces (trap (d)).

## 2. NavierStokes.ActualParticularRealization.CurrentInputs (ActualParticularRealization.lean:596)
VERDICT: **UNSUPPLIED** (6 occurrences repo-wide, all declaration or binder)
Occurrences (whole repo, word-boundary grep on `CurrentInputs`):
 - :596 `structure CurrentInputs ... : Prop where` (6 equality fields: context/state/carrier/gaussian/aliasError/parameters)
 - :607-610 `theorem CurrentInputs.particularBlock ... (J : CurrentInputs D p v c u l h gap) :` BINDER; conclusion is a `particularBlock = cycleBlock` equality, not `CurrentInputs`.
 - :987 `variable ... (J : CurrentInputs D p v c u label h gap)` inside `section CurrentCycle` -- BINDER.
 - :996 `theorem CurrentInputs.velocity_realization` and :1020 `theorem CurrentInputs.pressure_realization`, both `include J ...` of that variable -- BINDERS; conclusions are field/pressure-map equalities.
Routes checked: (1) no decl concludes `CurrentInputs`, no `.of_*` smart constructor; (2) no `⟨...⟩`/`.mk`/`{ ... }`/`constructor` with goal `CurrentInputs` anywhere (only 6 hits total, none is a term/tactic construction); (3) no `instance`; (4) not a field of any structure (no hit outside this file, so no other structure mentions it); (5) no twin -- `CurrentInputs` occurs in exactly one namespace, `NavierStokes.ActualParticularRealization`. `section CurrentCycle` is a section (trap (d)).
No alias abbrev exists (all textual hits enumerated; nothing of the form `abbrev X := CurrentInputs ...`).

## 3. NavierStokes.ActualStageEstimates.Representations (ActualStageEstimates.lean:285)
VERDICT: **UNSUPPLIED** (6 occurrences, all declaration/binder)
Occurrences of the ActualStageEstimates twin:
 - ActualStageEstimates.lean:285 `structure Representations : Prop where` (6 EqOn fields: potential_zero/direct_zero/pressure_zero/potential_succ/direct_succ/pressure_succ)
 - :304 `variable ... (e : Representations R M hN W qbig WA WP A Bdirect P)` + `include e hq` -- BINDER
 - :309 `.potential_smooth`, :320 `.direct_smooth`, :330 `.pressure_smooth` -- consume `e`, conclude `ContDiffOn ...`, NOT Representations.
 - ActualEndpointInputs.lean:227 `(e : ActualStageEstimates.Representations R M hN W qbig WA WP A V P)` in `endpointInputs_of_run`, whose conclusion is `EndpointInputs h qbig A V P` -- BINDER (it destructs e.potential_succ etc.).
Routes: (1) no decl concludes it, no `.of_*`; (2) no `⟨...⟩`/`{ ... }`/`constructor` targeting it (all textual hits enumerated); (3) no instance; (4) never a field of another structure (no other file mentions the name except ActualEndpointInputs as a binder); (5) TWIN checked: `NavierStokes.GluedStageEstimates.Representations` (GluedStageEstimates.lean:288) is a distinct structure with a different signature; GluedStageEstimates.lean:677 is only an `abbrev ActualRepresentations := Representations ...` (alias, no construction) for the GLUED twin and cannot supply the ActualStageEstimates one. No alias abbrev exists for the ActualStageEstimates version.

## 8. NavierStokes.GluedStageEstimates.Representations (GluedStageEstimates.lean:288)  [done out of order: same family as item 3]
VERDICT: **SUPPLIED** (route 1 + route 2)
Key: it is consumed through the alias `abbrev ActualRepresentations (qbig) (A Bdirect P) : Prop := Representations R M hN W (currentPotential ...) (currentPressure ...) (InitialPhysicalData.potentialWaveData ...) (InitialPhysicalData.pressureWaveData ...) A Bdirect P` (GluedStageEstimates.lean:675), so a grep on "Representations" alone hides the supplier.
Supplier: `NavierStokes.ActualCandidateAssembly.representations_of_signed_eqOn` (ActualCandidateAssembly.lean:772-782):
  conclusion `GluedStageEstimates.ActualRepresentations (runData ...) (meanCycleInput ...) ... (potentialStages ...) (directStages ...) (pressureStages ...)` proved `by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩` (all six EqOn fields discharged by rw/rfl).
  Hypotheses: `GluedStageEstimates.SignedInputs`, two `EqOn` families -- NO Representations/ActualRepresentations binder (trap (c) checked, clean).
Fully-closed instance: `ActualCandidateAssembly.representations` (:868) = `representations_of_signed_eqOn B N0 hN (ActualSignedWaveData.signedInputs B N0 hN) ...` -- no remaining P-hypothesis.
Binder-only sites: GluedStageEstimates.lean:307 (variable + include e), :689, :732; consumers :311/:323/:333 conclude ContDiffOn.
Twin note: `NavierStokes.ActualStageEstimates.Representations` (ActualStageEstimates.lean:285) is a DIFFERENT structure and this supplier does NOT count for it (see item 3).

## 4. NavierStokes.AxisResolvent.AxisVanishesBelow (AxisResolvent.lean:303, Prop-valued `def`)
VERDICT: **SUPPLIED** (route 2 -- an in-tactic base case, `k = 0`)
`def AxisVanishesBelow I ε A k : Prop := ∀ x : I.interval, JetVanishesBelow (fun n m => jet I (weight ε) A.1 n m x) k`.
All 4 occurrences:
 - :303 declaration.
 - :335 `axisLinearOperator_increases_order ... (hA : AxisVanishesBelow I ε A k) : AxisVanishesBelow I ε (Q A) (k+1)` -- this is exactly trap (c): P-from-P closure, supplies NOTHING on its own.
 - :350 `axisLinearOperator_bound_on_order ... (hA : AxisVanishesBelow ...)` -- BINDER, concludes a norm bound.
 - :382-386 `axisLinearOperator_pow_bound`: `apply pow_bound_of_filtration Q (fun k A => AxisVanishesBelow I ε A k) (by positivity)` then the FIRST bullet `· intro A x n hn` / `omega`.
BASE CASE FOUND: `pow_bound_of_filtration` (AxisResolvent.lean:222) has argument `hzero : ∀ x, P 0 x`, so that bullet's goal is `∀ A, AxisVanishesBelow I ε A 0`, i.e. `∀ A x, JetVanishesBelow ... 0`, closed by `intro A x n hn; omega` (vacuous `n < 0`). It takes NO AxisVanishesBelow hypothesis. So the closure algebra of :335 does have a base case, and the whole predicate family is inhabited (`AxisVanishesBelow I ε A 0` for every A, hence `... (Q^k A) k` by :335).
No twin: `AxisVanishesBelow` occurs only in NavierStokes/AxisResolvent.lean (single namespace). `section AxisOperators` is a section, not a namespace.

## 5. NavierStokes.CorrectionStep.RepresentsPhysical (CorrectionStep.lean:940)
VERDICT: **UNSUPPLIED** (5 occurrences repo-wide, all declaration or binder; only a closure lemma, no base case)
Occurrences (whole repo):
 - :940 `structure RepresentsPhysical (chart) (domain) (Q) (A) (u : State D) (v : PhysicalFields P) : Prop where` -- 7 scaling-identity fields.
 - :959-965 `RepresentsPhysical.addIncrement (hu : RepresentsPhysical ... u v) ... (hw : RepresentsPhysical ... ⟨m,p,osc,pr,e⟩ w) : RepresentsPhysical ... (u.addIncrement ...) (v.add w) := by constructor ...` -- this is EXACTLY trap (c): the `constructor` here is fed by TWO RepresentsPhysical hypotheses, so it supplies nothing. It is a pure closure (sum) rule.
 - :1002-1004 `RepresentsPhysical.mean_overlap (hu : RepresentsPhysical ...)` -- BINDER, concludes a `meanComponents ... / Q n ^ A = ...` identity.
Routes: (1) the only decl concluding it also takes it (twice) -- no `.of_*` smart constructor; (2) no other `⟨...⟩`/`.mk`/`{ ... }`/`constructor`/`refine` with goal `RepresentsPhysical` (all 5 textual hits enumerated); (3) no instance; (4) not a field of any structure (name appears nowhere outside CorrectionStep.lean); (5) no twin -- single namespace `NavierStokes.CorrectionStep`; `section PhysicalRepresentation` is a section (trap (d)).
DEPENDENCE ON ITS NEIGHBOUR (asked): yes -- its last explicit argument is `v : PhysicalFields P` (CorrectionStep.lean:912, the same-file data structure you already ruled UNSUPPLIED, whose only producer is the closure `PhysicalFields.add` at :921, itself needing two PhysicalFields). So RepresentsPhysical is doubly stranded: its closure `addIncrement` even produces `v.add w`, i.e. it can only reach PhysicalFields values that are themselves sums of assumed ones. No base case for either.

## 6. NavierStokes.VolterraParity.CoefficientParity (VolterraParity.lean:44, Prop-valued `def`)
VERDICT: **SUPPLIED** (route 1 + route 2)
`def CoefficientParity (A : Coeff) : Prop := ∀ r z i j, A (-r) z i j = -(paritySign i * paritySign j) * A r z i j` (the unrestricted, NO-`On` sibling of `CoefficientParityOn` at :37).
SUPPLIERS (both in NavierStokes/PositiveAxisSystem.lean, namespace `NavierStokes.PositiveAxisSystem`, which does `open VolterraAnalyticBounds VolterraParity` at line 727 -- and neither of those namespaces nor PositiveAxisSystem declares a rival `CoefficientParity`, so the name resolves to `VolterraParity.CoefficientParity`; grep shows :37 and :44 are the ONLY definitions of the name in the repo):
 - PositiveAxisSystem.lean:761-762 `theorem coefficient0_parity (h lam C : ℂ) (F : CoefficientData) : CoefficientParity (coefficient0 h lam C F) := by intro r z i j; simp only [...]; fin_cases i <;> fin_cases j <;> simp [A0, paritySign, axialValue]` -- closed proof, NO parity hypothesis (trap (c) clean).
 - PositiveAxisSystem.lean:767-768 `coefficient1_parity ... : CoefficientParity (coefficient1 h F)` -- same shape, closed.
Binder-only sites: PositiveAxisExistence.lean:273 (`hp₀ hp₁` binders); VolterraParity.lean:656-657 in `symmetricSolution_parity_of_global`.
BRIDGE (asked): yes, bare -> On, used INLINE, not as a named lemma. In `symmetricSolution_parity_of_global` (VolterraParity.lean:650-664) the bare hypotheses are weakened by `(fun r _ z _ => hpA₀ r z)` / `(fun r _ z _ => hpA₁ r z)` / `(fun r _ z _ => hpf r z)` to feed `symmetricSolution_parity`, which wants `CoefficientParityOn (Icc 0 R) U ...`. So `CoefficientParity A -> CoefficientParityOn S U A` is available for any S,U by that one-liner. There is NO bridge in the other direction (On -> bare). Caveat for your CoefficientParityOn verdict: the two supplied bare instances are for `coefficient0 h lam C F` / `coefficient1 h F`, whereas every On-consumer wants `symmetricRawCoefficient hR A`; I did not verify any identification of those two coefficient families, so this does not by itself overturn the UNSUPPLIED verdict for CoefficientParityOn at the argument shapes it is used with.

## 7. NavierStokes.ActualWaveRegularity.ModeData (ActualWaveRegularity.lean:390)
VERDICT: **UNSUPPLIED** (4 occurrences repo-wide; only field positions + one binder; both parent structures are themselves unconstructed -- trap (b))
Occurrences of the name `ModeData` (word-boundary grep, whole repo -- only this file):
 - :390 `structure ModeData (a : CopyData D I) (s : StripData D) (d : GraphDirections D) (e : Cylinder ≃ₗᵢ[ℝ] D) {coord} (U : SlowRegion coord) (r₀ r₁ : ℝ) where` (fields native/reindex/cutoff_deck/amplitude_deck/radius_deck/radial_deck/phase_deck/radial_zero).
 - :412 `variable ... (h : ModeData a s d e U r₀ r₁)` + `include h` inside `namespace ModeData` -- BINDER (its lemmas, e.g. `.regular`, consume h).
 - :610 field `mode` of `structure ParticularData` (:606).
 - :776 field `mode` of `structure SignedData` (:773).
ROUTE 4 CHECKED AND REFUTED (this is trap (b)): neither parent is ever constructed.
 - `ParticularData`: hits are :606 decl, :620 binder (`block_regular`), :630 binder (`regular`), :811 binder (`next_regular` hyp `hp`). No `⟨...⟩`/`{...}`/`.mk`/`of_*`/instance anywhere. (`ActualCyclePreservation.lean:655 nativeParticularData` is a DIFFERENT name -- a `def` returning `.copyData`, not a ParticularData; matched only as a substring.)
 - `SignedData`: hits are :773 decl, :783 binder, :794 binder, :811 binder (`hs`). Never constructed. (`PositiveTimeSignedData.*` / `ActualSignedFamilySupport` hits are a different name, substring only.)
Routes: (1) no decl concludes ModeData; (2) no term/tactic construction (all 4 hits enumerated); (3) no instance; (5) no twin -- the name exists in exactly one namespace; `namespace ModeData` at :410 opens the projection namespace only.

## 9. NavierStokes.PrimaryMaterialDefect.DirectionMatch (PrimaryMaterialDefect.lean:89)
VERDICT: **UNSUPPLIED** (2 occurrences repo-wide: the declaration and one binder)
 - :89 `structure DirectionMatch (s : StripData E) (d : GraphDirections E) (s' : StripData E') (d' : GraphDirections E') (ψ : ℕ → E' → E) : Prop where` -- 8 fields (maps/differentiable/radial/auxiliary/angular/axial/fast/slow), i.e. the whole chart-change differential is ASSUMED.
 - :104 `theorem NativeCoordinates.comp ... (hψ : DirectionMatch s d s' d' ψ) : NativeCoordinates s' d' (fun n => χ n ∘ ψ n)` -- BINDER; the `refine ⟨...⟩` there builds a NativeCoordinates, not a DirectionMatch, and every bullet consumes `hψ.*`.
Routes: (1) nothing concludes DirectionMatch (no `.of_*`); (2) no `⟨...⟩`/`.mk`/`{ ... }`/`constructor`/`refine` with goal DirectionMatch (only 2 textual hits exist, so no candidate site); (3) no instance; (4) never a field of another structure (the name appears in no other file, hence in no other structure body); (5) no twin -- single namespace `NavierStokes.PrimaryMaterialDefect`; `section CommonPullback` is a section (trap (d)). No alias abbrev.
So `NativeCoordinates.comp` (the transport of native coordinates along a chart change) can never be applied: its chart-change premise has no producer anywhere in the artifact.

---
## SUMMARY (this worker)
1. ActualCycleResidualBounds.PhysicalFields  : SUPPLIED  (ActualPhysicalPrefixFields.lean:438, route 1+2, via `abbrev PhysicalData`)
2. ActualParticularRealization.CurrentInputs : UNSUPPLIED (6 sites, all binders)
3. ActualStageEstimates.Representations      : UNSUPPLIED (6 sites, all binders)
4. AxisResolvent.AxisVanishesBelow           : SUPPLIED  (AxisResolvent.lean:384, route 2, k=0 base case of pow_bound_of_filtration)
5. CorrectionStep.RepresentsPhysical         : UNSUPPLIED (5 sites; only the `addIncrement` P-from-P closure)
6. VolterraParity.CoefficientParity          : SUPPLIED  (PositiveAxisSystem.lean:761 and :767, route 1+2)
7. ActualWaveRegularity.ModeData             : UNSUPPLIED (4 sites; parents ParticularData/SignedData also unconstructed)
8. GluedStageEstimates.Representations       : SUPPLIED  (ActualCandidateAssembly.lean:772, route 1+2, via `abbrev ActualRepresentations`)
9. PrimaryMaterialDefect.DirectionMatch      : UNSUPPLIED (2 sites)

