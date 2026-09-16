# NSE read-only no-supplier audit (commit f9e8bc5)

I did not modify `NSE` and did not run `lake build`. I searched all `NavierStokes/**/*.lean` source with fixed-string `grep` and read the declaration/use contexts. A “supplier” below means a conclusion/constructor/field that supplies the named fully-qualified predicate without assuming that same predicate.

## 1. `NavierStokes.CorrectionStep.PeriodizedSignedParameters.NativeDynamics`

**Verdict: UNSUPPLIED.** The candidate structure is declared at `NavierStokes/CorrectionStep.lean:6000`; its fields run through `:6027`. The candidate-specific occurrences in its namespace are the declaration and hypothesis binders/receiver arguments at `:6029`, `:6039`, `:6050`, `:6072`, `:6262`, `:6265`, `:6276`, `:6296`, `:6310`, `:6344`, `:6387`, `:7024`, `:7051`, `:7079`, `:7429`, and `:8334`. The methods at `:6029-6072`, `:6265-6387`, `:7024-7079`, and `:7429` all take `d : NativeDynamics ...`; they do not conclude `NativeDynamics`. The uniform theorem at `:8334` takes `dyn : ∀ l, NativeDynamics ...`.

I found no `NativeDynamics.mk`, no anonymous constructor whose goal is this candidate, and no conclusion `... : PeriodizedSignedParameters.NativeDynamics ...` without the predicate as an input in the full Lean grep. No other structure field of this type appears in the scanned source (`:6000-8446` and all other files). The same-named twin checked is `NavierStokes.CorrectionStep.ParticularParameters.NativeDynamics`, declared separately at `:6124`; its methods at `:6142-6196` and its uses are not suppliers for the candidate.

There is 1 distinct using file (`CorrectionStep.lean:6000-8334`). The hypotheses look load-bearing: `exact_represents`, `good_represents`, `gaussian_represents`, and `context_linear_identity` use `d` at `:6276-6344`; `rawCurlData`/`full_divergence_zero`/`modeSolenoidal` use it at `:7024-7079`; and `residual_gain_local` takes it at `:7429`. Thus this is a main signed-dynamics/estimate branch, not a dead theorem branch (`:6265-6387`, `:7024-7079`, `:7429-7480`).

## 2. `NavierStokes.PhysicalParticularWave.ReferenceODE`

**Verdict: UNSUPPLIED.** The only declaration is the four-field structure at `NavierStokes/PhysicalParticularWave.lean:810-817`. Every occurrence examined after the declaration is a binder: `PhysicalParticularWave.lean:822,835,869,897,1060,1068,1094,1139,1175,1237,1254`; `GaussianErrorNaturality.lean:192,205,276,326,353,391,428,461`; and `ActualParticularRealization.lean:418,450,517,812,850,901,918,937,959,1004,1022,1063`. The `∀ j ... ReferenceODE` forms at `PhysicalParticularWave.lean:1139,1175,1237,1254` and the corresponding forms at `ActualParticularRealization.lean:418,450,517,937,959,1004,1022,1063` are also hypothesis binders.

No theorem/def/instance conclusion, anonymous constructor, `.mk`, or parent-structure field supplying this `ReferenceODE` appeared in the all-file grep. There is no same-named twin declaration: the sole declaration is `PhysicalParticularWave.lean:810`. In particular, the references at `GaussianErrorNaturality.lean:192,205` are fully qualified to this same predicate, not suppliers.

There are 3 distinct using files (`PhysicalParticularWave.lean`, `GaussianErrorNaturality.lean`, `ActualParticularRealization.lean`; citations above). The hypothesis is strongly load-bearing: `label_physical_velocity` and `label_physical_pressure` pass it to each band theorem at `PhysicalParticularWave.lean:1139-1175`; `native_amplitude_transport` takes it at `GaussianErrorNaturality.lean:272-276`; and actual block/cycle realization theorems take it at `ActualParticularRealization.lean:418-450`, `:812-918`, and `:989-1063`.

## 3. `NavierStokes.HarmonicResidual.ExtractionRegular`

**Verdict: UNSUPPLIED.** The candidate structure is declared at `NavierStokes/HarmonicResidual.lean:1461-1474`. All candidate occurrences examined are hypothesis binders: `HarmonicResidual.lean:1479,1492,1512,1545,1600`; `HarmonicWaveInteraction.lean:1123-1124`; `AxisymmetricResidualGrouping.lean:140,142,167,196,218,238,266`; `PhysicalResidualJetBounds.lean:129,694`; `CorrectionStep.lean:1410,1424,1520,1533,3122,9250,9258`; and `HarmonicMeanInteraction.lean:619-620`. (The `:142` occurrence is the result expression of a theorem whose input at `:140` is the candidate; it is not an independently supplied candidate.)

No candidate conclusion without an `ExtractionRegular` input, no constructor goal/`.mk`, and no other-structure field of candidate type was found by all-file grep. The same-named twin explicitly checked is `NavierStokes.LocalResidualGrouping.ExtractionRegular`, declared at `NavierStokes/LocalResidualGrouping.lean:210`; it is a different type. Its actual constructor is at `NavierStokes/ActualInitialization.lean:848-849` and begins `constructor` at `:850`, so it cannot supply the HarmonicResidual candidate.

There are 6 distinct files using the candidate (`HarmonicResidual.lean`, `HarmonicWaveInteraction.lean`, `AxisymmetricResidualGrouping.lean`, `PhysicalResidualJetBounds.lean`, `CorrectionStep.lean`, `HarmonicMeanInteraction.lean`; citations above). These hypotheses look load-bearing, not dead: `HarmonicResidual.stateGoodWaveResidual_grouped` consumes `h` at `:1479-1488`; `CorrectionStep.fullGoodWaveResidual_grouped` and `fullResidual_harmonic_decomposition` consume it at `CorrectionStep.lean:1410-1424`; and cycle residual reconstruction consumes it at `:9250-9258`. The theorem documentation explicitly says finite sums alone are not used as uniform estimates and cross-label support separation comes from this predicate (`HarmonicWaveInteraction.lean:1115-1124`).

## 4. `NavierStokes.ValidBandGluing.Compatible`

**Verdict: UNSUPPLIED.** The candidate is a `def`, not a structure, at `NavierStokes/ValidBandGluing.lean:22-23`. The 16 candidate hypotheses occur at `:40,48,52,66,78,94,99,105,112,120,125,134,141,148,168,173`; each is named `hf`/`hA` and is an input to a representative theorem. The only external candidate expression is the RHS of the distinct wrapper definition at `NavierStokes/ValidDyadicBandCover.lean:73`.

No theorem/def/instance concludes this candidate, and no anonymous constructor or parent field can construct a reducible `Compatible` predicate; all scanned `ValidBandGluing.lean:22-173` uses are hypotheses. The same-named twin checked is `NavierStokes.ValidDyadicBandCover.Compatible`, declared at `ValidDyadicBandCover.lean:72`; line `:73` defines it as `ValidBandGluing.Compatible ...`, but does not prove or supply a value. Other namespaces also contain unrelated `Compatible` names (for example `NavierStokes.AxisCoefficientSpace.Compatible` at `AxisCoefficientSpace.lean:92`), none are this candidate.

There are 2 distinct files with candidate references (`ValidBandGluing.lean:22-173` and `ValidDyadicBandCover.lean:73`). The candidate is load-bearing only inside the gluing infrastructure: `representative_eq_of_mem`, `representative_continuousOn`, and derivative/jet transfer theorems all require it (`ValidBandGluing.lean:40-148`). I found no concrete downstream hypothesis or supplier; the external wrapper at `ValidDyadicBandCover.lean:72-93` remains a dead/uninstantiated branch in this artifact.

## 5. `NavierStokes.DefectIncrementBounds.ShellTriple`

**Verdict: UNSUPPLIED.** The candidate structure is declared at `NavierStokes/DefectIncrementBounds.lean:109-112`. The candidate references examined there are all binders except the declaration: `:115,119,171,349,353,357,362,367,448,532,637,652,791,799,800,808,809,816,817,837,838`. The constructor in `ShellTriple.updated` at `:115` uses two pre-existing hypotheses `(hm : ShellTriple ...)` and `(hh : ShellTriple ...)`; under the task rule this does not supply anything. `ShellTriple.smooth` similarly only takes a candidate hypothesis (`:119`).

No candidate conclusion without a candidate input, `.mk`, anonymous constructor against a candidate goal, or other parent field was found. No same-named twin declaration was found: the only `structure ShellTriple` is `DefectIncrementBounds.lean:109`. The two external references at `CorrectionInitialization.lean:1215-1217` and `CorrectionInitializationNoOptions.lean:1226-1228` are named hypotheses.

There are 3 distinct using files (`DefectIncrementBounds.lean`, `CorrectionInitialization.lean`, `CorrectionInitializationNoOptions.lean`; citations above). The hypotheses are load-bearing in the rank/defect estimate branch: `fiveRows_preserve_masses` requires two shells at `DefectIncrementBounds.lean:799-805`, `zeroMasses` requires them at `:808-814`, `debt_eq_remainders` requires them at `:816-826`, and `ConstructedBounds` takes both at `:837-848`. Earlier pressure/defect calculations also consume them at `:448-460` and `:532-545`.

## 6. `NavierStokes.PhysicalResidualNaturality.BandCoherence`

**Verdict: UNSUPPLIED.** The candidate structure is declared at `NavierStokes/PhysicalResidualNaturality.lean:678-691`. Its methods only take candidate hypotheses: `BandCoherence.source_on` at `:694-697`, `source_eq` at `:740-743`, `residualBandAmplitude_eq` at `:760-763`, and `residualBandPressure_eq` at `:770-773`. External hypothesis occurrences are `GaussianErrorNaturality.lean:258,272,322,349,387,424,457`, `ActualParticularRealization.lean:103,315,407,508,889,989,1054`, and `CorrectionStep.lean:7978,7989`; all are `(H : PhysicalResidualNaturality.BandCoherence ...)` binders. (Thus 4 distinct files occur in this commit, despite the assignment’s “3 files” annotation.)

No theorem/def/instance conclusion, `.mk`, anonymous constructor against this candidate, or parent field of candidate type appeared in the all-file grep. No same-named twin declaration was found; `PhysicalResidualNaturality.lean:678` is the only `structure BandCoherence` declaration.

There are 4 distinct files with candidate references (citations above). The hypothesis is clearly load-bearing: `GaussianErrorNaturality.native_source_transport` and `native_amplitude_transport` use `H.source_eq` at `:258-276`; `CorrectionStep.fromReference_coherent_amplitude` and `_pressure` use `H.residualBandAmplitude_eq`/`H.residualBandPressure_eq` at `:7978-7994`; and actual/cycle realization variables carry `H` through the main realization chain at `ActualParticularRealization.lean:103-107`, `:407-450`, and `:989-1063`.

## Calibration: `NavierStokes.LocalResidualGrouping.ExtractionRegular`

**Verdict: SUPPLIED — `NavierStokes/ActualInitialization.lean:848-850`, route 2 (anonymous structure constructor).** The theorem conclusion is the fully qualified local twin at `:848-849`, and its proof opens with `constructor` at `:850`, then supplies every field through the remaining proof (`:851-875`). This is not the HarmonicResidual candidate declared at `HarmonicResidual.lean:1461`; the two declarations are separate (`LocalResidualGrouping.lean:210`, `HarmonicResidual.lean:1461`).

The calibration is used in 4 distinct files: the supplier is `ActualInitialization.lean:848-875`; hypotheses/consumers occur at `ActualCycleResidualBounds.lean:269,311,702` and `CorrectionStep.lean:9268,9276`; and the declaration is `LocalResidualGrouping.lean:210`. The actual supplier demonstrates that the local twin is reachable, unlike the candidate.
