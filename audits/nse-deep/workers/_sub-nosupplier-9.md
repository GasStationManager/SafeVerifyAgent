# sub-nosupplier-9 verdicts (artifact NSE @ f9e8bc5, read-only)

## 1. NavierStokes.ParticularWaveAssembly.LocalControl (decl ParticularWaveAssembly.lean:1422)
Greps: `LocalControl` (16 hits incl. section names), `LocalControl.mk|LocalControl.of|: LocalControl`, `controls\b`.
Sites: PhysicalParticularWave 40/627/895/1289, ActualParticularPhysicalData 192, ParticularWaveAssembly 1484,
ActualParticularRealization 727/810/899/916 -- ALL of form `(C : LocalControl D.reference ...)` = BINDER.
ParticularWaveAssembly:1758 `noncomputable def AssemblyData.controls (N)(α κ) : Type := ∀ j ∈ modes N, LocalControl ...`
  -> TYPE ALIAS (trap b): its conclusion is `Type`, not a LocalControl value; it constructs nothing.
  All `D.controls N α κ` uses (PhysicalParticularWave 1137/1235/1341/1351/1359/1369) are also BINDERS `(C : D.controls ..)`.
ActualPrimaryBounds:914-1079 `section LocalControl` is only a SECTION NAME (contents: fullCopy/controlCell/... , no LocalControl term).
Route 1: no decl concludes `LocalControl ...`. Route 2: no `.mk`/anonymous-constructor site (searched `LocalControl.mk`).
Route 3: no `instance`. Route 4 BOTH WAYS: (a) P-as-field -> no hit of shape `name : LocalControl` inside a structure
  (every `: LocalControl` hit is a parenthesised/braced binder of a theorem or def); (b) P containing others -> irrelevant.
Route 5: only ONE `structure LocalControl` in the artifact (ParticularWaveAssembly.lean:1422); no same-named twin.
VERDICT: UNSUPPLIED (10 occurrence sites examined, all binders; plus 1 Type-alias def).

## 2. NavierStokes.ParticularWaveBounds.ModalCopyControl (decl ParticularWaveBounds.lean:1290)
Grep `ModalCopyControl` -> 19 lines total, one decl + 2 field lines + all others binders:
 ParticularWaveBounds 1336 (h : ...), 1347 (h : ...), and pairs (hr/hi : ...) at 1818/1819, 1880/1881,
 1908/1909, 2047/2048, 2107/2108, 2181/2182 -- ALL BINDERS.
Route 1: theorems `ModalCopyControl.contDiffOn` (1333) and `.waveClass` (1344) TAKE a ModalCopyControl binder and
  conclude ContDiffOn/waveClass -- they supply nothing (and are the P-hyp-to-P-conclusion trap's cousin).
Route 2: no `.mk`, no anonymous constructor site anywhere in the 19 hits. Route 3: no instance.
Route 4 DIRECTION (a) P as a FIELD: YES -- it is fields `modal_real`/`modal_imag` of
  `structure LocalControl` (ParticularWaveAssembly.lean:1431,1434). BUT (per item 1) LocalControl is itself
  NEVER constructed (all 10 of its sites are binders; `AssemblyData.controls` is only a Type alias).
  So route 4 comes out NEGATIVE: parent found, parent not constructed.
Route 4 DIRECTION (b) fields OF P: not a supply route.
Route 5: single `structure ModalCopyControl` in the artifact; no same-named twin in another namespace.
VERDICT: UNSUPPLIED (16 binder occurrences + 2 field decls in the never-constructed parent LocalControl).

## 3. NavierStokes.ParametricTerminalCompensation.FirstJetWithinBound (decl ParametricTerminalCompensation.lean:20, Prop-valued def)
Grep `FirstJetWithinBound` -> 13 lines. Binders: 27, 33, 368 (`(h : FirstJetWithinBound ...)`, `(hE : ...)`).
CONCLUSIONS (inside existential goals, no P-hypothesis): 133, 306, 359, 480.
ROUTE 1 SUPPLIER: `theorem exists_variable_compensation` ParametricTerminalCompensation.lean:124-135; binders are only
  (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) {S} (hS : IsCompact S) (huniq : UniqueDiffOn ℝ S) (a) (ha : ContDiffOn ..) (hpos)
  -- NO FirstJetWithinBound hypothesis -- and the goal contains
  `FirstJetWithinBound P a c S η (C * (‖v η‖ + ‖derivWithin v S η‖))` as a conjunct (line 133). Proof is `by ... obtain/refine`,
  no `sorry` in the file (grepped `sorry|admit` -> none). Line 306 (`... FirstJetWithinBound P a c S η (C / K) ∧`) is the
  conclusion of a second such theorem whose hypotheses are also P-free; it consumes exists_variable_compensation.
  (Trap 1 checked explicitly: 26-28 `.mono` and 32-33 `.toFirstJetBound` DO take a P binder and are NOT counted.)
Route 4 (a): it is also field `first_jet` of structures at HeatedOutgoing.lean:313 and ExtendedHeatedOutgoing.lean:73
  (not needed for the verdict). Route 5: single definition; fully-qualified name checked
  NavierStokes.ParametricTerminalCompensation.FirstJetWithinBound, no twin.
VERDICT: SUPPLIED <NavierStokes/ParametricTerminalCompensation.lean:124 (goal line 133), route 1>.

## 4. NavierStokes.VolterraParity.CoefficientParityOn (decl VolterraParity.lean:37, Prop def)
Grep `CoefficientParityOn` -> 13 lines, ALL in VolterraParity.lean. One decl (37) + 12 BINDERS:
 455 (hA), 510 (hA), 529/530 (hA₀,hA₁), 555/556, 576/577, 602/603, 629/630 -- every one a parenthesised hypothesis
 `(h.. : CoefficientParityOn (Icc 0 R) U (symmetricRawCoefficient hR A..))`.
Route 1: NO decl has `CoefficientParityOn ...` as its conclusion (no hit occurs on a goal line; searched all 13 hits).
Route 2: no `⟨...⟩`/constructor site -- it is a plain `∀ r ∈ S, ∀ z ∈ U, ∀ i j, A (-r) z i j = ...` Prop, and no
  `intro`-style proof of it exists (no decl targets it). Route 3: not a class, no instance.
Route 4 BOTH WAYS: (a) it is NOT a field of any structure -- every `: CoefficientParityOn` hit is a theorem binder,
  no `name : CoefficientParityOn` line inside a `structure`. (b) n/a.
Route 5: NEAR-twins in the SAME namespace: `CoefficientParity` (line 43) and `ForcingParity` (46) -- unrestricted
  (no `On`) versions. These are DIFFERENT predicates (no `S`/`U` sets); any supplier of them is NOT counted here,
  and no `CoefficientParity -> CoefficientParityOn` bridge lemma exists (would have shown as a conclusion hit).
  No same-named `CoefficientParityOn` in any other namespace (grep is repo-wide).
VERDICT: UNSUPPLIED (12 occurrences examined, all binders).

## 5. NavierStokes.VolterraParity.ForcingParityOn (decl VolterraParity.lean:41, Prop def)
Grep `ForcingParityOn` -> 8 lines, all in VolterraParity.lean. One decl (41) + 7 BINDERS:
 469 (hf), 519 (hf), 531 (hf), 557 (hf), 578 (hpf), 604 (hpf), 631 (hpf) -- all
 `(h.. : ForcingParityOn (Icc 0 R) U (symmetricRawField hR f))` style hypotheses.
Route 1: no decl concludes `ForcingParityOn ...` (no goal-line hit among the 8). Route 2: no constructor/intro proof
 of it anywhere (it is `∀ r ∈ S, ∀ z ∈ U, ∀ i, f (-r) z i = -(paritySign i) * f r z i`; nothing targets that goal).
Route 3: no instance. Route 4 BOTH WAYS: (a) NOT a field of any structure -- every `: ForcingParityOn` hit is a
 theorem binder, none inside a `structure` body; (b) n/a.
Route 5: near-twin `ForcingParity` (VolterraParity.lean:46, same namespace, unrestricted version) is a DIFFERENT
 predicate and is not allowed to supply this one; no bridge lemma `ForcingParity -> ForcingParityOn` exists.
 No same-named decl in another namespace (repo-wide grep).
VERDICT: UNSUPPLIED (7 occurrences examined, all binders).

## 6. NavierStokes.CorrectionInitialization.MovingInitialization.PrimaryMeanData (decl CorrectionInitialization.lean:3412, `structure ... : Prop`)
Grep `PrimaryMeanData` -> 21 lines in 3 files. Binders in CorrectionInitialization: 3456, 3568, 3709 `(d : PrimaryMeanData U g ...)`.
ROUTE 5 FIRST (twin): CorrectionInitializationNoOptions.lean:3423 declares a SECOND `structure PrimaryMeanData`
  inside `namespace NavierStokes.CorrectionInitializationNoOptions` (line 56) -- fully qualified
  NavierStokes.CorrectionInitializationNoOptions...PrimaryMeanData, DISTINCT from the target
  NavierStokes.CorrectionInitialization.MovingInitialization.PrimaryMeanData. Its 8 sites are excluded and not used below.
SUPPLIER (routes 1 + 2), and it is for the CORRECT twin: ActualInitialMean.lean imports
  `NavierStokes.CorrectionInitialization` and does `open ... CorrectionInitialization` (lines 2, 19) and does NOT import
  the NoOptions file, so its `MovingInitialization.PrimaryMeanData` is the TARGET.
 * ActualInitialMean.lean:411 `noncomputable def PrimaryData (B N0 : ℕ) : Prop := MovingInitialization.PrimaryMeanData (cL := ...) ...`
   -- a Prop ALIAS (supplies nothing by itself; trap b noted).
 * ActualInitialMean.lean:434 `theorem primaryData_of_covariance (B N0) (hc : ∀ i j, MeanClass ...) (hr : ... Regular ...)
   (hp : ... PeriodicOn ...) : PrimaryData B N0 := by ... refine { ... }` -- CONCLUSION is the alias for PrimaryMeanData,
   hypotheses contain NO PrimaryMeanData/PrimaryData binder, and the proof builds the structure with `refine {` (route 2).
 * ActualInitialMean.lean:561 `theorem primary_mean_data (B N0 : ℕ) : PrimaryData B N0 := primaryData_of_covariance B N0
   (covariance_bounds B N0).1 (seed_covariance_regular B N0) (seed_covariance_periodic B N0)` -- HYPOTHESIS-FREE.
 * `grep -c sorry NavierStokes/ActualInitialMean.lean` -> 0.
Route 4 both ways: (a) not needed (already supplied); no `field : PrimaryMeanData` line seen. (b) n/a.
VERDICT: SUPPLIED <NavierStokes/ActualInitialMean.lean:561 (via :434), routes 1+2>.

## 7. NavierStokes.DefectIncrementBounds.RankGeometry (decl DefectIncrementBounds.lean:726, `structure`)
Grep `RankGeometry` -> 90 lines repo-wide. ROUTE 5 (the dominant trap here): there are TWO structures of this name:
  * TARGET: NavierStokes.DefectIncrementBounds.RankGeometry, DefectIncrementBounds.lean:726
    (args `(p : CorrectionState.ReconstructionData) (r : CorrectionState.RankData P) ...`).
  * TWIN: NavierStokes.LocalRankDefect.RankGeometry, LocalRankDefect.lean:503 (args `(g : VariableGaugeMean.GaugeData P) (r ...) (U ...)`).
    The twin IS supplied (e.g. CorrectionInitialization.lean:4394 `... : LocalRankDefect.RankGeometry commonGauge rankData
    U.carrier (commonContext B) u := by`, and ActualCycleCoherence.lean:470 conclusion). Those suppliers are NOT counted for the target.
  Disambiguation is airtight: I grepped for bare `RankGeometry` outside the two declaring files -- only 2 hits, both inside
  DOC COMMENTS (MovingMomentBounds.lean:296, MeanLocalDefectBounds.lean:230); every other cross-file use is explicitly qualified.
TARGET's 6 sites, ALL BINDERS: DefectIncrementBounds.lean:756 `(hg : RankGeometry p r c u)`, 835 `(hg : RankGeometry p r c u)`;
  CorrectionInitialization.lean:1214, CorrectionInitializationNoOptions.lean:1225, CorrectionStep.lean:1068, 2220 --
  each `(hg : DefectIncrementBounds.RankGeometry p r c ...)`.
Route 1: no decl anywhere concludes `DefectIncrementBounds.RankGeometry ...` (qualified grep returns exactly the 4 binder
  lines above; the file-local grep returns only decl + namespace + 2 binders). Route 2: no `.mk`/`⟨⟩`/`refine {` targeting it.
Route 3: no instance. Route 4 BOTH WAYS: (a) target is NOT a field of any structure (no `name : ... RankGeometry` line inside a
  structure body among the 90 hits); (b) whatever fields the target itself has is not a supply route.
VERDICT: UNSUPPLIED (6 occurrences examined, all binders; the same-named LocalRankDefect.RankGeometry twin is supplied but excluded).

## 8. NavierStokes.JetBounds.AllJetBound (decl JetBounds.lean:35, Prop def)
Grep `AllJetBound` -> EXACTLY 20 lines, ALL in NavierStokes/JetBounds.lean (`grep -rln` -> that one file only), so the
full census is here. Sites: 35 decl; 62-64 `.fderiv`; 197-198 (aux lemma binders); 210-213 `.add`; 224-228 `.bilinear`;
234-237 `.mul`; 267-274 `.mul_rpow` (274 is a `have h := AllJetBound.mul ...` inside a proof).
Route 1 -- TRAP 1 CHECKED EXPLICITLY: every decl whose CONCLUSION is `AllJetBound ...` (64, 213, 228, 237, 272) ALSO takes
  one or two `AllJetBound` hypotheses (`(hf : AllJetBound f s C)`, `(hA : ...) (hB : ...)`). These are closure/calculus
  lemmas (fderiv, add, bilinear, mul, mul_rpow) and supply NOTHING. There is NO base case: no decl proves AllJetBound for
  a concrete function (no `of_contDiff`, no const/zero lemma, no `AllJetBound.of_...` at all).
Route 2: no `⟨⟩`/`.mk`/`refine {`/`constructor` proof of an `AllJetBound` goal that is hypothesis-free (it is a plain
  `∀`-Prop; the only proofs of it are the 5 closure lemmas above). Route 3: no instance.
Route 4 BOTH WAYS: (a) NOT a field of any structure -- all 20 hits are in binders/goals of theorems in JetBounds.lean,
  none inside a `structure` body; (b) n/a as a supply route.
Route 5: single decl named AllJetBound in the whole artifact; fully-qualified NavierStokes.JetBounds.AllJetBound; no twin.
VERDICT: UNSUPPLIED (19 occurrences examined: 14 binders + 5 conclusions that each also consume an AllJetBound hypothesis).

