# Worker audit: compactness / nonlinear-limit machinery (SmoothLimitData + advection limit)

Repo: `/home/gsm/.openclaw/workspace/repos/NSE` (clone of `openai/NavierStokesAndEuler` @ `f9e8bc5`).
Mode: READ-ONLY, source-level only (no Mathlib in `.lake`, no `lake build`). All claims carry `file:line`.

## Scope

Read IN FULL (2 files, 26 declarations):

* `Euler/OrdinarySmoothLimit.lean` (119 lines, 13 decls): `jetPath` :22, `structure SmoothLimitData` :27,
  `nonempty_smoothLimitData` :34, `smoothLimitData` :62, `field` :74, `field_continuous` :76,
  `fieldPath_eq` :79, `fieldPath_convergence` :83, `jetPath_convergence` :88, `jet_convergence` :101,
  `toLp_convergence` :105, `tensorNorm_convergence` :109, `tensorNorm_bound` :113.
* `Euler/OrdinaryAdvectionLimit.lean` (150 lines, 13 decls): `jetLp_fieldSub` :17, `advection_difference` :28,
  `advection_norm_velocity` :39, `advection_sub_norm` :48, `advectionPath` :61, `projectedRhsPath` :65,
  `pressurePath` :69, `projectedRhsPath_eq` :73, `pressurePath_eq` :81, `advectionPath_sub_norm` :89,
  `advectionPath_convergence` :108, `projectedRhsPath_convergence` :135, `pressurePath_convergence` :142.

SKIMMED (only the cited declarations, to check that every appealed-to lemma is real and not vacuous):
`Euler/OrdinarySobolevTower.lean` :23-101, `Euler/OrdinaryCauchyInterpolation.lean` :49-98,
`Euler/SobolevCauchyInterpolation.lean` :21-94, `Euler/SobolevPathInterpolation.lean` :14-40,103,
`Euler/CylinderSobolevSpace.lean` :44-63, `Euler/OrdinaryHelmholtzField.lean` :18-92,
`Euler/OrdinaryFieldAlgebra.lean` :67,118-124, `Euler/OrdinaryEulerL2Stability.lean` :18-25,
`Euler/OrdinaryH3Norms.lean` :12-24, `Euler/OrdinarySmoothWords.lean` :97, `Euler/OrdinaryWordBounds.lean` :76-84,
`Euler/EulerProof.lean` :8375-8383, `Euler/LpSmoothField.lean` :31-98, `Euler/MeanSolenoidalSpace.lean` :22,104,
`Euler/MeanOrbitSmoothL2Field.lean` :41-52, `Euler/OrdinaryPressureCancellation.lean` :20-27,
consumer `Euler/OrdinaryEulerLimit.lean` :23-110.

## Per-declaration findings

### A. `Euler/OrdinarySmoothLimit.lean`

**`structure SmoothLimitData` (:27-32) — verbatim fields**

```
structure SmoothLimitData (A : ℕ → Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ k n, Continuous (fun t => (A k t).jetLp n)) where
  tower : SobolevTower T                                                        -- :29  DATA
  value_convergence : Tendsto (fun k => fieldPath (A k) (hA k)) atTop (𝓝 tower.field)   -- :30  PROOF field
  sobolev_convergence : ∀ q,
    Tendsto (fun k => sobolevPath (A k) (hA k) q) atTop (𝓝 (tower.realization q))       -- :31-32 PROOF field
```

So the two convergence properties ARE structure fields (hypotheses), i.e. downstream theorems in the
`SmoothLimitData` namespace are conditional on them. That is normal bundling, NOT an axiom — provided
some constructor discharges them. It is discharged:

* `nonempty_smoothLimitData` (:34-60) — verdict **OK**. Statement: from `hT : 0 ≤ T`, uniform Sobolev bounds
  at EVERY order (`hb : ∀ q, ∃ M, ∀ k t, tensorNorm q (A k t) ≤ M`, :37) and L² path Cauchyness
  (`h0 : CauchySeq (fun k => fieldPath (A k) (hA k))`, :38), `Nonempty (SmoothLimitData A hA)`.
  Proof mechanism, field by field:
  - `tower.field := u` where `u` is the L² path limit from `cauchySeq_tendsto_of_complete h0` (:39) —
    completeness of `C(Icc 0 T, L²)`.
  - `tower.realization := v` from `choose v hv using exists_sobolevPath_limit hT A hA hb h0` (:40).
    `exists_sobolevPath_limit` (`Euler/OrdinaryCauchyInterpolation.lean:91-98`) is a REAL compactness/
    interpolation step: `sobolevPath_cauchy_of_l2` (:60-89) takes the uniform bound at order `q+1`
    (`hb (q+1)`, :66) plus L² Cauchyness and produces Cauchyness at order `q` via
    `cauchy_restrict_of_value` (`Euler/SobolevCauchyInterpolation.lean:78-85`), which reduces to per-word
    `wordPath_cauchy_of_value` (:21-37, induction on derivative order) and ultimately the
    log-convexity/square-bound interpolation `cauchySeq_of_square_bound`
    (`Euler/SobolevPathInterpolation.lean:14-30`) and `wordPath_cauchy_step` (:103). Completeness of
    `SobolevSpace 1 q` is real: it is a closed submodule of a finite product of `Lp` spaces
    (`Euler/CylinderSobolevSpace.lean:44-60`), NOT a trivial/junk type.
  - `tower.value_eq` (:41-59): proved, not assumed — `he q` shows the two continuous-linear images of the
    two limits agree by `tendsto_nhds_unique hleft hright` (:55) after the per-`k` identity
    `ordinarySobolev_value` (:52). This is the coherence between the L² limit and the Sobolev-order limits.
  - `value_convergence := hu`, `sobolev_convergence := hv` (:60) — exactly the two limits just produced.
* `smoothLimitData` (:62-67) — verdict **OK**. `Classical.choice (nonempty_smoothLimitData hT A hA hb h0)`.
  This is choice applied to a PROVED `Nonempty`; it adds no axiom beyond Mathlib's `Classical.choice` and
  is only a noncomputability. It is NOT a "supply the field by fiat" route. Real consumer confirms this:
  `eulerLimitData` (`Euler/OrdinaryEulerLimit.lean:79-83`) builds the datum only via `smoothLimitData`,
  and `limitEvolution` (:85-88) feeds `Classical.choose (hb 3)` as `M`.
* `field` (:74, abbrev) / `field_continuous` (:76) — **OK**. The limit field is `L.tower.smoothField t`,
  the genuine smooth spatial representative from `SobolevTower.smoothField`
  (`Euler/OrdinarySobolevTower.lean:37`), whose `toLp` is proved equal to the prescribed L² path
  (`smoothField_toLp` :39-56) and whose jets are continuous in time (`smoothField_jet_continuous` :58-59).
  So `L.field` is not a fresh unrelated object.
* `fieldPath_eq` (:79-81), `fieldPath_convergence` (:83-86) — **OK**. Rewriting the structure field's
  target `tower.field` into `fieldPath L.field …` by `smoothField_toLp`; then `value_convergence`.
* `jetPath_convergence` (:88-99) — **OK** and this is the load-bearing one for the nonlinear limit.
  Mechanism: `ordinaryTensorOperator n` is a CONTINUOUS LINEAR map `SobolevSpace 1 n →L[ℝ] Lp (jets)`
  (`OrdinarySobolevTower.lean:73-76`); it is pushed to paths by `compLeftContinuous` (:90); continuity
  transports `sobolev_convergence n` (:91); the two identifications
  `ordinaryTensorOperator_apply` (:95, proved at `OrdinarySobolevTower.lean:78-95`) and
  `tensorOperator_realization` (:98, :97-101) turn both sequence and limit into `jetPath`s. Conclusion:
  **strong L²-in-space, uniform-in-time convergence of the full `n`-th jet**, in particular `n = 1`
  (the gradient). No junk-value trick.
* `jet_convergence` (:101-103), `toLp_convergence` (:105-107) — **OK**. Evaluation `evalCLM ℝ t` is
  continuous linear; pointwise-in-time corollaries.
* `tensorNorm_convergence` (:109-111) — **OK**. `tensorNorm q A = ∑_{n≤q} ‖A.jetLp n‖`
  (`Euler/OrdinaryH3Norms.lean:12`), so a finite sum of norms of convergent sequences.
* `tensorNorm_bound` (:113-116) — **OK**. `le_of_tendsto` + `Eventually.of_forall`: the uniform bound
  passes to the limit. This is the standard "bound survives the limit" step and it is honest.

### B. `Euler/OrdinaryAdvectionLimit.lean`

**`projectedRhsPath_convergence` (:135-140) — verbatim**

```
theorem projectedRhsPath_convergence (hT : 0 ≤ T) (M : ℝ)
    (hb : ∀ k t, tensorNorm 3 (A k t) ≤ M) :
    Tendsto (fun k => projectedRhsPath (A k) (hA k)) atTop (𝓝 (projectedRhsPath L.field L.field_continuous)) := by
  simp only [projectedRhsPath_eq]
  exact ((-solenoidalProjection).compLeftContinuous ℝ (Icc (0 : ℝ) T)).continuous.tendsto _
    |>.comp (L.advectionPath_convergence hT M hb)
```

Verdict **OK**, with the content located one step down (not circular, not self-conversion):

1. `projectedRhsPath` (:65-67) is `fieldPath (fun t => projectedRhs (A t)) …`, and `projectedRhs A`
   is the GENUINE Euler right-hand side: `projectedRhs A = fieldNeg (solenoidalField (advectionField A A))`
   (`Euler/OrdinaryHelmholtzField.lean:63-64`), i.e. `-P(u·∇u)` with `P = solenoidalProjection`
   (`Euler/MeanSolenoidalSpace.lean:104`, the `starProjection` onto the solenoidal subspace — a real
   orthogonal projection, hence a bounded linear map on `L²`). Pointwise it is exactly `-u·∇u - ∇p`:
   `projectedRhs_field` (`OrdinaryHelmholtzField.lean:78-81`). And `advectionField A B` really is
   `x ↦ fderiv ℝ B.field x (A.field x)` (`Euler/OrdinaryFieldAlgebra.lean:118-124`), i.e. `A·∇B`.
   So the name does not overclaim; the object IS the advection/Euler nonlinearity.
2. `projectedRhsPath_eq` (:73-79) rewrites the path as the bounded linear `-P` applied to `advectionPath`
   (proof: `projectedRhs_toLp`, `OrdinaryHelmholtzField.lean:66-68`). `simp only [projectedRhsPath_eq]`
   rewrites BOTH the sequence and the limit, so the composition really lands on the intended limit point.
3. The real work is `advectionPath_convergence` (:108-133) — verdict **OK**. It proves
   `advectionPath (A k) → advectionPath L.field` in the sup-in-time / `L²`-in-space norm of
   `C(Icc 0 T, L²)`, i.e. `u_k·∇u_k → u·∇u` strongly. Mechanism:
   - uniform H³ bound `hb : ∀ k t, tensorNorm 3 (A k t) ≤ M` gives a UNIFORM GRADIENT SUP BOUND
     `‖fderiv ℝ (A k t).field x‖ ≤ G := 9·smoothEmbeddingConstant·M` (:116-121) via the genuine Sobolev
     embedding `real_smooth_fderiv_le_H3` (`Euler/EulerProof.lean:8375-8383`) plus `tensorNorm_eq`
     (`OrdinaryH3Norms.lean:14`);
   - the LIMIT gets a uniform velocity sup bound `‖(L.field t).field x‖ ≤ K := 13·smoothEmbeddingConstant·M`
     (:122-125) through `wordBound_pointwise` (`Euler/OrdinaryWordBounds.lean:76-84`),
     `wordBound_tensorNorm` (`OrdinaryH3Norms.lean:21`) and `L.tensorNorm_bound 3 M hb`
     (i.e. the bound passed to the limit — not assumed for the limit);
   - the bilinear difference estimate `advectionPath_sub_norm` (:89-101), from `advection_sub_norm` (:48-57):
     `‖A·∇A − B·∇B‖ ≤ G‖A−B‖ + K‖∇A−∇B‖` with `G ≥ sup‖∇A‖`, `K ≥ sup‖B‖`. Its algebra is honest:
     `advection_difference` (:28-37) is the exact Leibniz split
     `A·∇A − B·∇B = (A−B)·∇A + B·∇(A−B)` (uses `fderiv_sub` with genuine differentiability from
     `A.smooth`, :35), and the two factors are bounded by `advection_norm_gradient`
     (`Euler/OrdinaryEulerL2Stability.lean:18-25`) and `advection_norm_velocity` (:39-46), both via
     `Lp.norm_le_mul_norm_of_ae_le_mul` and `le_opNorm`. `jetLp_fieldSub` (:17-26) and
     `norm_derivative_jetLp` (`LpSmoothField.lean:94-98`) convert `‖∇(A−B)‖` into `‖A.jetLp 1 − B.jetLp 1‖`.
   - `squeeze_zero` (:131-133) against `G·‖fieldPath diff‖ + K·‖jetPath 1 diff‖ → 0`, whose two inputs are
     `L.fieldPath_convergence` and **`L.jetPath_convergence 1`** (:127-130).
   So the passage to the limit is legitimate: it needs, and uses, STRONG L² CONVERGENCE OF THE GRADIENT
   (`jetPath … 1`), which comes from `sobolev_convergence`, which the constructor obtained from the
   uniform bound at one higher order plus L² Cauchyness (interpolation). No weak-convergence gap, no
   "convergence converted into itself".
4. Composition with `-P` is valid precisely because `P` is a bounded linear operator on `L²`; the pressure
   analogue `pressurePath_convergence` (:142-147) is the same move with `P − id`
   (`pressurePath_eq` :81-87, from `pressureField_toLp`, `OrdinaryHelmholtzField.lean:70-72`).
   Verdict **OK**; the docstring claim "pressure convergence is a consequence" (:6) is accurate.

Consumer check (context given in the task): `field_integral_equation`
(`Euler/OrdinaryEulerLimit.lean:27-41`) uses `L.projectedRhsPath_convergence hT M hb` (:31), pushes it
through the continuous Volterra `integral` and `evalCLM` (:32-34), and closes with `tendsto_nhds_unique`
against the per-`k` integral equations (:36-41). `toEvolution` (:55-73) then differentiates the integral
identity (`field_hasDerivWithinAt` :43-53) to get `time_law`. The chain is coherent with what
`projectedRhsPath_convergence` actually proves.

Remaining decls in the file, verdict **OK**: `advectionPath` (:61), `pressurePath` (:69),
`jetLp_fieldSub` (:17), `advection_norm_velocity` (:39), `advection_sub_norm` (:48),
`advectionPath_sub_norm` (:89).

## Kernel-risk

Scan of both files for `decide`, `native_decide`, `Nat.pow`, numerals ≥ 4 digits, `.rec`/`recOn`/`Acc.rec`,
`termination_by`, `WellFounded.fix`, `rfl`, `sorry`/`admit`/`axiom`/`trivial`,
`macro`/`elab`/`syntax`/`set_option`/`unsafe`/`partial`:

* `Euler/OrdinarySmoothLimit.lean`: ZERO hits except `Classical.choice` at :67 (discussed above; legitimate).
  No `rfl`, no `decide`, no recursion, no `termination_by`, no numerals beyond `0`/`1`.
* `Euler/OrdinaryAdvectionLimit.lean`: ZERO hits except `le_rfl` inside `⟨0,le_rfl,hT⟩` at :111 (a
  `0 ≤ 0` proof term, not `rfl` on recursive data). Numerals: `1`, `3`, `9` (:112), `13` (:113), `2` (:51,
  inside `jetLp 1` arithmetic) — all tiny; no bignum/kernel-arithmetic exposure.
* No `macro`/`elab`/`syntax`/`set_option`/`unsafe`/`partial`/`native_decide` in either file (consistent
  with the repo-wide zero). No `erw` in either file (`erw` does appear elsewhere, e.g.
  `OrdinarySobolevTower.lean:64`, outside my scope).
* Only structural/type-level notes: `private local instance : Fact (0 < (1 : ℝ))` (`OrdinarySmoothLimit.lean:18`)
  — a benign positivity instance for the `period = 1` cylinder; `abbrev field` (:74) is reducible by design.

No KERNEL-RISK findings in scope.

## Escalations

None of soundness type. Two items an aggregator may want to price:

1. **INFO (not a defect): all convergence in scope is at fixed finite Sobolev order via interpolation, not
   via Rellich compactness.** The mathematical engine behind `SmoothLimitData` is
   `uniform bound at order q+1` + `L² Cauchy` ⇒ `Cauchy at order q`
   (`Euler/OrdinaryCauchyInterpolation.lean:60-98`, `Euler/SobolevCauchyInterpolation.lean:78-85`,
   `Euler/SobolevPathInterpolation.lean:14-30,103`). The `hb` hypothesis is at EVERY order `q`
   (`OrdinarySmoothLimit.lean:37`), which is a strong (but explicitly stated) input; `L² Cauchyness`
   (`h0`, :38) is also assumed, not derived. So this file family does not by itself produce a limit from
   bounds alone — it needs an L² Cauchy sequence handed to it. Whoever audits the PRODUCERS of `h0`
   (`Euler/OrdinaryEulerCauchy.lean`, `Euler/OrdinaryEulerLocalExistence.lean`) owns that risk.
2. **INFO: `T < 0` degeneracy.** For `T < 0` the domain `Icc (0:ℝ) T` is empty and every path norm is `0`,
   so path statements are trivially true. All the interesting theorems carry `hT : 0 ≤ T`
   (`:34`, `:108`, `:135`) or `hpos : 0 < T` downstream, so this is not exploited; the norm-level lemmas
   `advectionPath_sub_norm` (:89) hold for all `T` only because they are vacuous when the interval is empty.
   Harmless, but it means those lemmas alone say nothing for `T < 0`.

## Residue

* Not verified here (no Mathlib source in `.lake`, and by scope): the Mathlib lemma names used
  (`cauchySeq_tendsto_of_complete`, `Lp.norm_le_mul_norm_of_ae_le_mul`, `iteratedFDeriv_sub_apply`,
  `ContinuousMap.norm_le`, `squeeze_zero`, `le_of_tendsto`, `tendsto_finsetSum`, `compLeftContinuous`).
  They are used with plausible signatures; a build would settle it.
* Depth-limited (statements read, proofs not audited line by line): `wordPath_cauchy_step`
  (`Euler/SobolevPathInterpolation.lean:103`) and `SobolevInterpolation` below it — the actual
  interpolation inequality. `SobolevTower.smoothField_toLp` (`OrdinarySobolevTower.lean:39-56`, uses
  `exists_smooth_of_lift` and `pointField_unique`). `solenoidal_orbit`
  (`Euler/OrdinaryPressureCancellation.lean:20-27`) and `smoothL2Field`
  (`Euler/MeanOrbitSmoothL2Field.lean:41-44`) — both read and both look genuine.
* `smoothEmbeddingConstant` (`Euler/EulerProof.lean:8227`) definition and its `_nonneg` lemma were not
  opened; only nonnegativity is used in scope, so a bad value could not create unsoundness here, only a
  weaker/uninformative constant.
