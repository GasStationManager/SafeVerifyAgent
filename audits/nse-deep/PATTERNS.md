# Defect patterns in openai/NavierStokesAndEuler @ f9e8bc5

A synthesis of the deep audit's recurring shapes, with instance counts and file:line witnesses.
Written because the audit's individual findings are scattered across 39 worker sections of `FINDINGS.md`,
and the *patterns* are more useful than any single finding: they say where to look next, and they say what
kind of artifact this is.

**One direction holds across every pattern below: nothing here makes a theorem FALSE.** Every shape is
"the statement says less than it appears to" or "this theorem cannot be reached". That is worth stating
first, because the list is long and could otherwise read as an indictment. The Navier-Stokes and Euler
headline claims are not touched by any of it.

---

## P1 — UNSUPPLIED HYPOTHESIS: a predicate nobody ever constructs
**45 confirmed, carrying 444 in-cone hypothesis sites** (one earlier verdict, `ValidBandGluing.Compatible`, was REVERSED -- supplied through a definitional wrapper). Found mechanically by
`audits/nosupplier.py`, each one confirmed by reading. Effect: the theorems taking it are **unreachable**,
so a dependency cone that counts them as live is wrong. Never a falsity — an unsatisfiable hypothesis makes
a vacuously fine theorem.

**It clusters, which is the actionable part.** 46 predicates across **29 files**, but:
- `CorrectionStep.lean` — **7**
- `ActualWaveRegularity.lean` — **4**
- `ParticularWaveBounds.lean` — **3**
- then 6 files with 2 each, and 20 files with exactly 1.
The top 5 predicates alone carry **150 of the 463** sites. So this is not diffuse rot; it is a handful of
abandoned neighbourhoods. Biggest single: `PhysicalStageBounds.MeanData` (`:154`, 49 sites),
`GaussianTailFlat.FlatEdges` (`:446`, 28), `PhysicalParticularWave.ReferenceODE` (`:810`, 27),
`HarmonicResidual.ExtractionRegular` (`:1461`, 22 — the original W30 finding).

## P2 — CLOSURE WITHOUT A BASE CASE
**7 instances.** A predicate with a complete algebra of closure lemmas (`.add`, `.mul`, `.partial`,
`.updated`, `.mono`) and **no way to make the first one**. This is *why* P1 keeps being mis-verified: a
reader sees five declarations concluding `P` and stops, without noticing every one also *assumes* a `P`.
- `JetBounds.AllJetBound` (`:35`) — **5** conclusions (`:64,213,228,237,272`), every one takes an `AllJetBound`.
- `CorrectionStep.PhysicalFields` (`:912`) — sole build is `add (u v : PF) : PF` (`:921`).
- `DefectIncrementBounds.ShellTriple` (`:109`) — `.updated` (`:115`) takes **two**.
- `CorrectionStep.RepresentsPhysical` (`:940`) — `.addIncrement` (`:959`) takes two, and its argument is
  itself the stranded `PhysicalFields`. **A coupled pair, stranded together.**
- `MeanResidual.AngularPeriodic` (`:56`), `HarmonicResidual.ExtractionRegular` (`:1461`),
  `IntegratedMeanBalances.SmoothShell` (`:582`).

## P3 — MULTI-LEVEL UNSUPPLIED FAMILY
**1 instance, 3 levels deep.** `ActualWaveRegularity.ModeData` (`:390`) is a field of `.ParticularData`
(`:606`) and `.SignedData` (`:773`), and **none of the three is ever constructed** — both parents are
binder-only, so the route-4 rescue fails at every level. Independently confirmed by two workers. Its twin
`SignedMeanGain.NativeData` is *proved `IsEmpty`*. Also `ParticularWaveAssembly.BackgroundControl` (`:1403`)
is a field of **two** parents, both binder-only.

## P4 — STRONG HYPOTHESIS BESIDE A WEAKER TWIN THAT CARRIES THE LIVE TRAFFIC
**6 instances, and W30 predicted 3 would make it a pattern.** Always safe in direction (a stronger
hypothesis is a weaker theorem) and always misleading about reachability.
1. `HarmonicResidual.ExtractionRegular` (no constructor) vs `LocalResidualGrouping.ExtractionRegular`
   (constructed, `ActualInitialization.lean:849`).
2. `IntegratedMeanBalances`' balance branch vs the `StateMomentBalances`/`GaugeMomentBalances` same-named
   twins on a *different* operator.
3. `MeanStateRegularity.Periodic` (`:26`) vs the sufficient `PositivePeriodic` (`:30`).
4. `ActualPhysicalPrefixFields` `:362` demands `ContDiffOn ℝ ∞` where `DifferentiableOn` is used (`:214,370`).
5. `PeriodicPhaseAssembly` `:621` assumes `∀ n, b.frequency n ≠ 0` using two instances, beside the correctly
   weak `:612`.
6. `WaveStateRegularity.CoefficientSupport` (`:197`, unconstructed) beside `fieldSum_support` (`:226`, built
   at `ActualWaveRegularity.lean:445,483`), which carries all live traffic.
**And one with REVERSED polarity:** `NaturalAxisRange` re-derives its sibling under a *weaker* hypothesis,
but its `Parameters` (`:13`) is only ever inhabited from the far stronger `SmallParameters` via `ofSmall`
(`:20`) — so here the *general* result is the decoration.

## P5 — LEAN JUNK VALUES: `x / 0 = 0` and `0⁻¹ = 0` silently empty a channel
Mechanised in `audits/junkvalue.py`; **581 in-cone hits**, triaged by sampling. **Distinct from P1-P4
because it is a property of the ambient library, not of this artifact** — it belongs on the checklist for
auditing *any* Lean development.
- **Defect-shaped:** `PeriodicPhaseAssembly.transportPhase` (`:481`) carries `Kr / K`; **8** theorems
  (`:492,499,508,520,535,567,722,734`) degenerate at `K = 0`, including `:734` advertising "exact values on
  the entire sampling interval". And `BasePrefixIdentity`'s swirl runs through `C⁻¹` (`:119,255`) with `C`
  unconstrained in **every** signature.
- **The sharpest specimen, and it is caller-guarded:** `PulseCovariance:74 integral_gaussian_scaled` claims
  `∫ gaussian b m r = r * sqrt(π/b)` with `r` guarded and `b` not. At `b = 0` the LHS integrand is a
  non-integrable constant → Lean's integral junk value `0`; and `sqrt(π/0) = 0`. **An exact identity that
  survives only because two independent junk values conspire.** Same for all `b < 0`.
- **Measured false-positive kinds** (from a 38-hit triage: A=13 B=12 C=10 D=3): already-guarded signatures
  (`1 ≤ k`), positivity certified by a structure field (`StripData.epsilon_pos`, `WeightedClasses.lean:35`),
  `1 + ‖·‖` denominators, shared evaluation points, and deliberate zero-extensions whose junk value is
  *proved* right. **Rule that works: flag only if the denominator reaches a subterm on ONE side.**

## P5b — THE MIRROR IMAGE: nonvanishing guards that are NOT needed
**Candidate pattern, 1 file / 5 sites.** `NavierStokes/StressAlgebra.lean` `:317` (`hφ`), `:331` and `:339`
(`hR`, `hL`) carry nonvanishing hypotheses the identities do not require — parent-re-derived: under
`x/0 = 0` each identity still holds at the excluded value (at `L = 0` both sides of `:340-341` equal
`(2x·Ex − E)/R`; at `φ = 0` and `R = 0` both sides are `0`). Only `hE` is genuinely needed.
**Cause:** both proofs are `field_simp; ring`, and `field_simp` demands the side conditions to clear
denominators, so they migrate into the statement. **Direction: safe** — a theorem with extra hypotheses is
weaker than provable. **Cost:** callers must discharge a non-degeneracy the mathematics does not need.
Where P5 makes a statement say *less* than it appears to, P5b makes it *demand* more than it needs. Both are
the same total-division convention seen from opposite sides.

## P8 — FILTER VACUITY: `∀ᶠ x in ⊥, P x` is true for every `P`
**2 instances, both BENIGN and arguably correct design.** The filter analogue of P5, and the sharpest vacuity
question this audit managed to aim at the blow-up argument itself.
`Flatness.lean:24 PowerFlat` has **no `[NeBot l]`**, so at `l = ⊥` it holds for any `f` with `C = 0`.
`BaseResidual.lean:350 PhysicalApproach` has **every field** `∀ᶠ` or `Tendsto` and **no `NeBot` field**, so with
`carrier := ∅` it is inhabited at `l = ⊥`.
**But the guard sits exactly where the contradiction is derived:** `BlowupImplication.lean:78
no_eventual_bound_of_profile` and `:95 no_continuous_extension_of_profile` are both `[NeBot l]`.
One does not need `NeBot` to *state* flatness; one needs it to *conclude* from flatness — and that is where it
is. **Residual cost: a reading hazard.** A `PowerFlat`/`PhysicalApproach` hypothesis read in isolation carries
no content, and the reader must go two layers up to find the instance that makes it bite.

## P7b — NON-DEGENERACY PROVED ONCE AT A BASE CASE, THEN ONLY PROPAGATED
**The mechanism behind the degenerate-witness family**, parent-verified in the Euler tower.
`ParentEulerLowBounds.lean:61-70 lowBoundsFromPhysical` admits `r = 0` (it asks only `0 ≤ r`, `r ≤ 1/4`).
`firstChildLowBounds` (`ParentFirstPacketLowGuards.lean:77-79`) is the **only** place that supplies a positive
one, `r := A.ell` with `A.ell_pos`, applied on the live path at `BaseFirstPacket.lean:67`. Every later step —
`updateLowBounds` (`:84-92`) and both generic child steps (`ParentPacketChildLowGuards.lean:41,76`) — passes
`H.r` **unchanged**. So non-degeneracy is established once and thereafter merely carried, and is invisible to
every lemma downstream: a tower skipping the first child keeps `r = 0` forever, making `core_lower` vacuous
and the `C2·Bc·r³·T` budget term identically zero in every generation.
**Benign for the headline** (the live tower does go through `firstChildLowBounds`), but it is why
"which witness?" is the right question to ask of any Data-level estimate. Same shape as
`cartesianPotential = 0`.
**Four consequences of that single base witness, all traced and all confined to the base generation:**
`ParentPacketSourceData:30-35` makes `C2·Bc·r³·T` identically 0; `MeanPacketData:50 core_lower` is vacuous
while `exterior_lower` covers all `x`; `MeanStrongEquation:39 initial_velocity` collapses to `velocity 0 = 0`;
and `PacketPrimaryGradeBounds:89` discharges 2 of 7 `ProfileBudget` fields against the zero field.
`BaseEulerState.initialLowBounds_values:56-62` states `.Bc = 0 ∧ .L = 0 ∧ .r = 0` **each by `rfl`**, and
`firstChildLowBounds` (`ParentFirstPacketLowGuards.lean:77`) is the sole escape, setting `r := A.ell > 0` and
`L := C1·Cnew + 1 ≥ 1`. Three independent workers reached this chain from different files.

## P6 — SUPPLIED PREDICATE USED AT ARGUMENTS NOBODY ESTABLISHES
**3 instances.** The half of P1 that no syntactic instrument catches, because the predicate *is*
constructed — just never for the objects that matter.
- W8's `hres : ∀ J m, JetRate l q (fs J) m (rho J − Lres m)` (`GenericSupportedPolynomial.lean:130`).
- `IntegratedMeanBalances.SmoothShell` — 3 producers (`:899,904,912`), **none for a velocity or flux field**.
- `VolterraRegularity.SmoothCoefficientData` — constructed (`PositiveAxisExistence.lean:348`), but its
  `symmetricRaw*` wrapper uses (`:830,848`) have no supplier.

## P7 — NEAR-TAUTOLOGICAL / ZERO-WITNESSED STATEMENTS
- All **177** theorems of `InitialPhysicalData.lean` survive `cartesianPotential = 0`.
- `TerminalEdgeFactor.lean:1467,1562,1659` hold because `Tz` is flat-zero.
- The `PrimitiveData` spine is bootstrapped at `⟨MovingField.zero, ×3⟩` (`ActualInitialCoherence.lean:649`)
  and the wave stage provably never moves the mean — **but this one resolved NEGATIVE**: the temporal and
  rank stages do move it (`initializedBands_mean`, `ActualMeanPotentialRealization.lean:589-604`). Recorded
  because the *reading hazard* is real even though the defect is not.

---

## What the instruments cost, and what that says
Five instrument bugs were found in this audit, **four of them by a worker's number disagreeing with the
script's**, and one by a reader finding a case the tool passed. Two failed in the dangerous direction
(hiding findings): bare-suffix twin masking, and multi-line `variable` blocks. One was blindness to Greek
identifiers — in an analysis library. **The working rule: treat every parent/worker numeric disagreement as
a defect report against the instrument, not as noise to average away.**

A sixth limitation was then found by a reader rather than by a count: `nosupplier.py` does not chase
suppliers through **definitional wrappers**, so it called `ValidBandGluing.Compatible` unsupplied when a
theorem concluding `ValidDyadicBandCover.Compatible` -- a `def` whose body IS that predicate -- supplies it.
Same shape as `junkvalue.py`'s two-level-indirection gap. Both need definition unfolding, which is precisely
what a syntactic pass cannot do, so both are recorded rather than fixed.

**And one methodological result worth more than any single finding: a rule that measured 41/41 was still
wrong.** A triage worker recommended "flag only if the denominator reaches one side of the equality"; a
second worker produced a counterexample showing it would delete the audit's sharpest junk-value finding
(`PulseCovariance:74`, where the divisor is on both sides and both sides collapse independently). Perfect
agreement on a sample is not validation when a single counterexample can be decisive.
