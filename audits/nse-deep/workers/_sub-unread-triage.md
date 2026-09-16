# Unread-triage hostile audit (NSE f9e8bc5)

I used the rows in `UNREAD_TRIAGE.csv` (the class rows are visible at e.g. ESTIMATE lines 2, 29, 268, 336, 385, 446, 545, 648, 753, 854, 911, 929; PLUMBING lines 91, 137, 286, 488, 551, 794, 959; STRUCTURAL top rows 3--27). I read the declarations and proof statements, not just the 600-character signal.

## 1. ESTIMATE sample (12 files)

The measured false-positive rate in this deliberately size-spread sample is **4/12 = 33%** if “estimate” excludes pure smoothness/contract/construction spine items:

* `Euler/PacketPhysicalCoefficients.lean` — **ESTIMATE yes**: coefficient-error inequalities and velocity-entry error bounds are the theorem conclusion (30--58).
* `Euler/MeanHarmonicSmallBall.lean` — **yes**: explicit r³ local energy bound (4,25--30).
* `Euler/ParameterSobolevProductAt.lean` — **yes**: fixed-radius product majorant bound (16--24).
* `Euler/ParentParticleRegularity.lean` — **NO / false positive**: only inverse derivative and `ContDiff` construction, no estimate (5--6,17--34).
* `Euler/ContinuousAccelerationSobolev.lean` — **yes**: forcing and acceleration block norm bounds (26--40,52--70).
* `Euler/MeanPacketContract.lean` — **NO / false positive**: contract of the concrete mean solver (angle independence, divergence, support, continuity, jets), not a bound (4,16--47).
* `Euler/PacketPhysicalCorrectionPotential.lean` — **NO / false positive**: defines the physical correction potential and proves its exact gradient/jet/hessian interface, a construction contract rather than a quantitative estimate (4--6,20--22,48--75).
* `Euler/CorrectionStabilityConstants.lean` — **yes**: explicit L² Lipschitz/growth/defect constants and difference remainder estimate (13--26,43--65).
* `Euler/PacketInitializedOutputCosts.lean` — **yes**: polynomial envelope and actual output-cost inequalities (4--5,16--44,65--81).
* `Euler/SmoothFlowJacobian.lean` — **NO / false positive**: constructs the actual Jacobian evolution/equivalence and proves derivatives of the constructed forward/backward flow (5--10,25--27,37--38,69--118).
* `Euler/ParentPacketScaledBounds.lean` — **yes**: physical-label derivative bounds for frame/gradient/inverse/strain/curvature (4--6,43--110).
* `NavierStokes/SquaredPartition.lean` — **yes, estimate-support**: constructed normalized masks are then used for jet and rescaling bounds (10--15,96--118,293--329,598--599).

Thus the crude signal has real false positives: contracts and construction/smoothness files can look estimate-like. The four named false positives contain 15 in-cone theorems in aggregate (CSV lines 268, 446, 545, 753).

## 2. PLUMBING sample (8 files)

This sample shows why low signal is not a safe “trivial plumbing” label. **Five of eight are proof-spine/construction items; three are genuine support/algebra plumbing.**

* `Euler/TransversePacketInitialRepresentative.lean` — **spine**: identifies the raw forward field with the actual continuous representative of initial data (4--5,19--41).
* `NavierStokes/RadialSchedule.lean` — **support/algebra**: ideal schedule identities, moment reset, and energy arithmetic; the file explicitly says it does not construct the smooth schedule or prove stress-cone bounds (10--19,56--92,147--165).
* `Euler/MeanStrongCoordinates.lean` — **spine**: terminal-primitive uniqueness identifies the actual strong velocity with the canonical fixed-coordinate solution (5--10,25--47,55--69).
* `Euler/TransverseInitialCoordinates.lean` — **spine**: defines candidate coordinates/derivative and proves reconstruction and physical velocity identity (5--10,31--39,70--107).
* `NavierStokes/TangentProjection.lean` — **support/algebra**: projection, pressure cancellation, damping, and uniqueness identities; explicitly no pulse existence/size estimates (9--15,26--35,67--79,102--128).
* `Euler/AngleMeanZeroPrimitive.lean` — **spine**: explicit normalized angular primitive, periodicity, zero mean, and uniqueness (5--10,21--30,50--78).
* `Euler/CylinderDirichletTranslation.lean` — **support/plumbing**: shifted coefficients and translation covariance of frame, velocity, acceleration, and physical derivatives (4--5,43--60,89--136).
* `Euler/TransversePacketPrimaryPressure.lean` — **spine**: defines pressure as the actual mean-zero primitive, proves its derivative/normalization and the full field equation (7--8,118--151,172--200).

## 3. Twelve largest STRUCTURAL files

The structural flag is often triggered by a useful Prop record, but most of these are support. The top 12 are (CSV lines 3--27):

1. `NavierStokes/IntegratedMeanBalances.lean` (53): `SmoothShell`/moment infrastructure and actual integrated angular/axial balances, pressure-moment reconstruction (360--390,616--645,673--740). **Spine-adjacent and likely load-bearing** because it states the reduced balance equations.
2. `NavierStokes/MeanStateRegularity.lean` (53): `OperatorData`, `BaseData`, `PeriodicTriple`, `MovingTriple`, `PrimitiveData`, and regularity closure (62--106,212--253,337--435). **Estimate-support/regularity plumbing**, not headline construction.
3. `NavierStokes/PulseCovariance.lean` (44): `PulseBounds`, `CutoffBounds`, `TangentPulse`, Gaussian/covariance factorization and cone/positivity bounds (128--153,184--236,568--635,637--715). **Estimate-support**, though pulse data is a candidate component.
4. `NavierStokes/CopyAngularInvariance.lean` (37): invariance records and angular-zero/invariance propagation through copy, pressure, curl, and corrected coefficients (201--229,304--357,467--509). **Symmetry plumbing**.
5. `NavierStokes/ActualPhysicalPrefixFields.lean` (34): `StageRealizations` and conversion to `PhysicalData`; `physicalFields_all` is the consumer interface (340--343,438--475). **Genuinely load-bearing NS construction/spine.**
6. `NavierStokes/ClosedNativeWaveIdentities.lean` (34): closed-cell differential identities, geometry/exact/raw-jet records, curl/divergence cancellation and realization (359--373,472--573,630--657). **Estimate/PDE support**, not the candidate existence spine.
7. `NavierStokes/ParametricModulation.lean` (29): existence of `TrueConeRealization`, integral primitives, and end-to-end modulated true-cone profiles (298--316,322--340,577--608). **Genuinely load-bearing construction/spine.**
8. `NavierStokes/VolterraRegularity.lean` (28): regular Volterra primitives, disk curves, Cauchy jets and smoothness bootstrap (40--58,201--238,453--531,657--700). **Smoothness plumbing/support**.
9. `NavierStokes/PeriodicPhaseAssembly.lean` (25): clock/phase periodicization and assignment into `periodicAssembly`; actual carrier germ/periodicity interface (53--120,667--680,805--831). **Load-bearing wave/phase construction.**
10. `NavierStokes/BasePrefixIdentity.lean` (24): `VelocityMatches`/`CoefficientMatches`, finite prefix and pressure germs, and finite identities needed by residual estimates (215--224,278--311,372--380). **Load-bearing prefix interface**, although downstream quantitative.
11. `NavierStokes/ModulatedExterior.lean` (24): actual modulation realizes coefficients, exact heat exterior and zero residual, terminal extension (324--368,398--406,489--520). **Genuinely load-bearing NS exterior/terminal construction.**
12. `NavierStokes/AxisCoefficientSpace.lean` (22): compatible jet Banach/subspace, actual derivatives, constructors and completeness (47--52,90--130,163--188,327--450). **Coefficient-space plumbing**, not headline.

## 4. Headline answer and priority

Summing the CSV rows (`UNREAD_TRIAGE.csv:2-965`) gives 843 STRUCTURAL + 738 PLUMBING = **1,581/5,067 (31.2%)** files/theorems outside the estimate class. The hostile sample also found four estimate-class false positives (15 theorems), so a defensible rounded answer is **about 1,600 non-estimate in-cone theorems (roughly 31--32%)**, not “almost all estimates.” The exact figure cannot be inferred from 20 manual files; this is a measured lower baseline plus sampled correction.

Read first, in this order:

1. `NavierStokes/ActualPhysicalPrefixFields.lean` — stage realizations become the actual physical residual data (`physicalFields_of_stages`, `physicalFields_all`, 340--343,438--475).
2. `NavierStokes/ModulatedExterior.lean` — actual modulated base has exact heat exterior and zero NS residual, then terminal extension (333--368,489--520).
3. `NavierStokes/ParametricModulation.lean` — explicit existence/construction of the true-cone loops, primitives, and profiles (304--316,577--608).
4. `NavierStokes/BasePrefixIdentity.lean` — coefficient agreements become prefix/pressure germs and finite identities (217--224,278--311,372--380).
5. `NavierStokes/PeriodicPhaseAssembly.lean` — constructs the actual periodic phase assembly and carrier interface (667--680,805--831).
6. `NavierStokes/IntegratedMeanBalances.lean` — reduced angular/axial balances and pressure reconstruction (638--645,674--740).
7. `Euler/TransversePacketPrimaryPressure.lean` — actual pressure primitive and full packet field equation (118--151,172--200).
8. `Euler/SmoothFlowJacobian.lean` — actual invertible Jacobian of the constructed flow, a sampled ESTIMATE false positive (25--27,37--38,82--118).

Bottom line: the remainder is estimate-heavy by count (3,486), but not basically all estimate material. The non-estimate minority is large enough to contain several construction and equation interfaces that should be audited before spending time on more norm bounds.
