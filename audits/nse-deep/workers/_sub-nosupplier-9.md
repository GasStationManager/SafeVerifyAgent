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

