# Junk-value triage tranche 4 — NSE @ f9e8bc5 (READ-ONLY)

Instrument: source read only (no `lake build`; 0 .olean, pinned lean4:v4.34.0-rc2).
Classes: A guarded-in-signature, B certified-by-type/construction, C guarded-by-callers-only,
D genuinely unguarded. Appended file-by-file in the order given.

## 1. NavierStokes/BasePrefixIdentity.lean:111 `prefixSwirl_radial` — denom `C` — **C (caller-guarded)**

CLAIM: exact identity `-partialS (prefixSwirl J h C d) p = slowSwirl J h C (profiles h d) p`
(the finite Borel swirl prefix's radial derivative EQUALS the slow swirl field). Signature
(BasePrefixIdentity.lean:111-113) has `(C : ℝ)` with no hypothesis at all.

COLLAPSE AT C = 0. The swirl channel is `C⁻¹` on both sides:
* `SlowBorelBase.coefficientBundle`:1137 slot 1 = `-C⁻¹ * primitive (d.phi j)`, exported as
  `bundleComponent C d 1` (SlowBorelBase.lean:1153).
* LHS: `BaseResidual.prefixSwirl`:614-615 = `physicalUncutPrefix h (1/2 - A h) (bundleComponent C d 1) J`;
  `physicalUncutPrefix` (SlowBorelBase.lean:885-886) is `q^b • uncutPrefix` of that family, so with the
  family identically 0 (because `(0:ℝ)⁻¹ = 0`) the prefix is the zero function and `partialS 0 = 0`.
* RHS: `SlowExpansionResidual.slowSwirl`:553-554 = `C⁻¹ * finiteProfile ...` = 0.
So at C = 0 the theorem reads `-0 = 0`, i.e. `0 = 0`. This is the PulseCovariance:74 shape: an EXACT
identity surviving by two conspiring junk values (`0⁻¹ = 0` on each side independently), not a bound.

WHY C, NOT D. Nothing in this file constrains C — the internal caller `prefixVelocity_eq_profiles`:157-158
and `prefixVelocity_eq_slowVelocity`:235-237 and `prefixVelocity_germ`:260-262 all keep `(C : ℝ)` free.
Positivity only appears at the instantiation layer, where C is always `…axis.normalization`:
* NavierStokes/ConstructedSlowBase.lean:219 and :346, NavierStokes/EntranceAlignedBase.lean:364
  (`BasePrefixIdentity.CoefficientMatches F.data.h W.axis.normalization …`);
* NavierStokes/BaseWitnessClosure.lean:92 (`BaseResidual.FiniteIdentities ActualPrimary.h
  ActualPrimary.nominal.axis.normalization`), with :54-60 exhibiting `0 < …axis.normalization` via
  `NominalProfile.AxisStage.normalization_pos` (NominalProfile.lean:79-81, derived from the
  `normalization_large` field at NominalProfile.lean:69-70).
So the degenerate branch is unreachable in the assembled proof, but the theorem AS STATED says nothing at
C = 0, and no type records that. Benign-but-weakened; matters because it is an exact identity, and because
the whole swirl channel (:86, :112, :133, :158, :237, :262) inherits the same free `C`.

## 2. NavierStokes/ClosedNativeWaveIdentities.lean:279 `curlRemainder_contDiffAt` — denom `K` — **D (unguarded, but LOW severity)**

CLAIM: a REGULARITY statement — `ContDiffAt ℝ ∞ (curlRemainder K R Vr Vθ Vz B) x` from smoothness of
R, Vr, Vθ, Vz, B and `R x ≠ 0`. `(K : ℝ)` is explicit and unconstrained (:279).

COLLAPSE AT K = 0. `CurlClassBounds.curlRemainder`:269-271 is `(1 / K) • (Complex.I • cylindricalCurl …)`,
so at K = 0 the function is identically `0` and the conclusion becomes `ContDiffAt ℝ ∞ (fun _ => 0) x`,
provable without any hypothesis. Nothing guards it: `WaveCoefficients.frequency : ℕ → ℝ` is a bare field
(LinearWaveBounds.lean:185, no positivity/nonzero field), and the only caller
`RawJetsAt.curlCorrection` (ClosedNativeWaveIdentities.lean:564-565) passes `a.frequency n` while
`RawJetsAt` (:545-552) carries only `cutoff`, `radius_ne`, `normal_ne` — no `frequency ≠ 0`.
The sibling record `LocalizedCurlRealization.RawData`:55 DOES carry `frequency : ∀ n, a.background.frequency n ≠ 0`,
which is the guard that this chain omits.

SEVERITY: low. This is the "bound collapsing to 0 ≤ 0" kind — a smoothness claim, and smoothness of
`c • f` is insensitive to c anyway. Report it only as a missing-hypothesis hygiene item, not as a
content-free EXACT identity. (Class-A/B it is not: nothing at all excludes K = 0.)

