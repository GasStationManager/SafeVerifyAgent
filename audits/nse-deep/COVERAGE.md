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
bound on coverage, and here is a measured example of how generous: `NavierStokes/VariableGaugeMean.lean`
(138 in-cone theorems) counts as cited because three `rfl`-census reports name **one line** of it.
The reports themselves state their own read counts honestly (e.g. `jet-inductives`: 119 of 1,227
declarations in `EulerProof.lean` read line-by-line; `expr-inductives`: 103 of 103;
`ns-index-nonempty`: ~46 of 1,246 in 11 files, the rest by targeted grep).

| | count |
|---|---|
| worker reports | 65 |
| distinct files cited by a report | 610 |
| files with in-cone theorems, cited | **560 of 2,306** |
| in-cone theorems living in cited files | **11,511 of 27,753 (41.5%)** |

So: the *spine* of both claims has been walked end to end, every one of the 14 inductives, all 12
`termination_by`, all 5 explicit recursors, all 210 `decide`, all 121 large numerals and all 541
in-cone bare-`rfl` proofs have been classified — but a majority of the **estimate mass** of the
Navier-Stokes half is still unread, and that is where the remaining work is.

## Work queue — largest in-cone theorem counts not yet cited by any report

| `NavierStokes/TransitionRamp.lean` | 127 |
| `NavierStokes/OutgoingHistories.lean` | 114 |
| `NavierStokes/AssembledSlowBase.lean` | 108 |
| `NavierStokes/TailCone.lean` | 104 |
| `NavierStokes/ParticularWaveAssembly.lean` | 103 |
| `NavierStokes/NominalConeAssembly.lean` | 93 |
| `NavierStokes/OutgoingTail.lean` | 89 |
| `NavierStokes/ActualWaveRegularityData.lean` | 87 |
| `NavierStokes/LiftedMeanResidual.lean` | 87 |
| `NavierStokes/LocalRankDefect.lean` | 87 |
| `NavierStokes/RepairConeBounds.lean` | 85 |
| `NavierStokes/OutgoingSchedule.lean` | 83 |
| `NavierStokes/OutgoingPulseBounds.lean` | 81 |
| `NavierStokes/SlowBorelBase.lean` | 80 |
| `NavierStokes/UniformAngularReset.lean` | 79 |
| `NavierStokes/TerminalPressure.lean` | 78 |
| `NavierStokes/ActivationHolomorphic.lean` | 77 |
| `NavierStokes/ActualParticularDynamics.lean` | 76 |
| `NavierStokes/DefectIncrementBounds.lean` | 76 |
| `NavierStokes/ExtendedHeatedOutgoing.lean` | 74 |
| `NavierStokes/HeatedOutgoing.lean` | 73 |
| `NavierStokes/LocalizedWaveBounds.lean` | 73 |
| `NavierStokes/SlowResidualMatching.lean` | 70 |
| `NavierStokes/HeatSwitchCone.lean` | 69 |

These are estimate/assembly files: long `nlinarith`/`calc` chains over constructed constants.
For the *kernel-trust* question they are the lowest-risk mass in the artifact (no inductives, no
recursors, no `decide`, numerals of a few digits — see `SITES_*.md`), which is why the audit
attacked the spine and the recursion/numeral surface first. For the *mathematical* question they
are exactly where an off-by-one in a constant would hide, and they are not covered.

**In flight** (this cycle): `ns-transition-ramp` (queue ranks 1 and 2),
`ns-variable-gauge-mean` (cited-in-passing only, see above), plus two kernel-numeral threads
(`cert-numerals`, `kernel-choose-pow`) re-testing the published report's own headline numbers for
vector (2).

## Update (W32/W33 cycle) — recomputed, with the denominator stated

The 41.5% above was measured over **65** worker reports. Recomputed at **78** reports with the *same*
definition ("a file is cited if some worker report names it", boundary-matched so `Solution.lean` does
not match inside `ComparatorSolution.lean`):

| | count |
|---|---|
| worker reports | 78 |
| files with in-cone theorems, cited by a report | **710 of 2,306** |
| in-cone theorems living in cited files | **15,310 of 27,753 (55.2%)** |
| the same, also counting the synthesis documents (FINDINGS/kernel-trust) | 22,686 (81.7%) — too generous to quote |
| files NO audit document has ever named | **964**, holding **5,067** in-cone theorems (18.3%) |

Those 964 files are classified in `UNREAD_TRIAGE.csv`. The classification was hostile-tested by a
worker (see `workers/_sub-unread-triage.md`) and corrected:

* **STRUCTURAL** — 73 files, 843 in-cone theorems. Declares a `structure`/`class`/`inductive` or a
  Prop-valued `def`. Highest priority: new predicates are declared here, and this is what
  `audits/nosupplier.py` feeds on.
* **ESTIMATE** — 761 files, 3,486 in-cone theorems. Sampled error 4 of 12 files, but those 4 hold only
  **15** in-cone theorems, so by theorem mass this bucket is ~99.6% right. Lowest priority.
* **CONSTRUCTION** (was called PLUMBING — the rename is the finding) — 130 files, 738 in-cone theorems.
  A worker found **5 of 8** sampled files are proof-spine/construction, not trivial algebra:
  they define objects and prove things about them. "Plumbing" invited the wrong triage.

So **~1,581 of the 5,067 unread in-cone theorems (~31%) are not estimate material**, and the answer to
"is the remainder all estimates?" is **no**. Ranked read-first list is in `FINDINGS.md` §W33.
