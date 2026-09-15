# Coverage ledger — NSE deep audit

Two denominators, because only one of them is honest:

* **52,516** declarations / **38,503** theorems in the artifact.
* **38,369** declarations / **27,725** theorems in the *cone* of the four headline theorems
  (`audits/cone.py`, mark 4; `CONE.csv`). A defect outside the cone cannot make a headline
  theorem false, so the cone is the denominator that matters. It is an over-approximation with
  one known blind spot (instance synthesis and the ambient `@[simp]` set — 611 out-of-cone
  declarations carry an implicit-use attribute).

Restricting to files that contain at least one in-cone theorem: **2,306 files, 27,753 in-cone
theorems/lemmas**.

## What the audit has touched

A file is "cited" below if some worker report names it. That is a deliberately **generous** upper
bound on coverage: several reports cite a file to say they read three lines of it. The reports
themselves state their own read counts honestly (e.g. `jet-inductives`: 119 of 1,227 declarations
in `EulerProof.lean` read line-by-line; `expr-inductives`: 103 of 103; `ns-uniqueness`: 67 files
surveyed).

| | count |
|---|---|
| worker reports | 40 |
| distinct files cited by a report | 432 |
| files with in-cone theorems, cited | **395 of 2,306** |
| in-cone theorems living in cited files | **6,808 of 27,753 (24.5%)** |

So: the *spine* of both claims has been walked end to end, every one of the 14 inductives, all 12
`termination_by`, all 5 explicit recursors, all 210 `decide` and all 121 large numerals have been
classified — but the **estimate mass** of the Navier-Stokes half is largely unread, and that is
where the remaining work is.

## Work queue — largest in-cone theorem counts not yet cited by any report


| file | in-cone theorems | lines |
|---|---|---|
| `NavierStokes/CorrectionStep.lean` | 264 | 9,849 |
| `NavierStokes/InitialPhysicalData.lean` | 167 | 2,854 |
| `NavierStokes/TerminalEdgeFactor.lean` | 151 | 1,675 |
| `NavierStokes/VariableGaugeMean.lean` | 138 | 3,004 |
| `NavierStokes/TransitionRamp.lean` | 127 | 2,253 |
| `NavierStokes/OutgoingHistories.lean` | 114 | 1,278 |
| `NavierStokes/HarmonicResidual.lean` | 112 | 1,620 |
| `NavierStokes/AssembledSlowBase.lean` | 108 | 1,760 |
| `NavierStokes/ActualInitialization.lean` | 105 | 1,517 |
| `NavierStokes/TailCone.lean` | 104 | 1,714 |
| `NavierStokes/ParticularWaveAssembly.lean` | 103 | 2,015 |
| `NavierStokes/ActualPrimaryBounds.lean` | 96 | 1,753 |
| `NavierStokes/NominalConeAssembly.lean` | 93 | 1,523 |
| `NavierStokes/OutgoingTail.lean` | 89 | 1,000 |
| `NavierStokes/ActualWaveRegularityData.lean` | 87 | 1,951 |
| `NavierStokes/LocalRankDefect.lean` | 87 | 1,044 |
| `NavierStokes/PhysicalMeanDomain.lean` | 87 | 1,761 |
| `NavierStokes/LiftedMeanResidual.lean` | 87 | 1,257 |
| `NavierStokes/PhysicalGraphBounds.lean` | 85 | 1,502 |
| `NavierStokes/ActualMeanPhysicalData.lean` | 85 | 1,312 |
| `NavierStokes/RepairConeBounds.lean` | 85 | 1,294 |
| `NavierStokes/MeanIncrementBounds.lean` | 84 | 1,262 |
| `NavierStokes/OutgoingSchedule.lean` | 83 | 1,013 |
| `NavierStokes/OutgoingPulseBounds.lean` | 81 | 1,342 |
| `NavierStokes/SlowBorelBase.lean` | 80 | 1,689 |
| `NavierStokes/PeriodizedWaveBounds.lean` | 80 | 1,682 |
| `NavierStokes/ExtendedHeatDebts.lean` | 79 | 1,208 |
| `NavierStokes/UniformAngularReset.lean` | 79 | 1,364 |
| `NavierStokes/TerminalPressure.lean` | 78 | 1,508 |
| `NavierStokes/ActualSignedStageControls.lean` | 77 | 1,352 |

These are estimate/assembly files: long `nlinarith`/`calc` chains over constructed constants.
For the *kernel-trust* question they are the lowest-risk mass in the artifact (no inductives, no
recursors, no `decide`, numerals of a few digits — see `SITES_*.md`), which is why the audit
attacked the spine and the recursion/numeral surface first. For the *mathematical* question they
are exactly where an off-by-one in a constant would hide, and they are not covered.