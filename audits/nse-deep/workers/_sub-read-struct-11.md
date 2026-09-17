# Worker _sub-read-struct-11 — structural files, NSE @ f9e8bc5 (READ-ONLY, no build)

## 1. NavierStokes/ValidBandGluing.lean (179 lines, 24 decls, 1 Prop-def) — CLEAN

Generic chart-gluing library over `{ι D E : Type*}`; nothing Navier-Stokes-specific except the last
two curl corollaries.

- Prop-def `Compatible U f := ∀ i j, EqOn (f i) (f j) (U i ∩ U j)` (ValidBandGluing.lean:22-23).
  **SUPPLIED, not orphaned.** Concluded (not assumed) by `ActualValidBandWaves.compatible`
  (NavierStokes/ActualValidBandWaves.lean:259-267), which proves it from `local_fields_eq`
  (ActualValidBandWaves.lean:238) with no `Compatible` in its own hypotheses; consumed one layer up
  as `ValidDyadicBandCover.Compatible` (NavierStokes/ValidDyadicBandCover.lean:72-73) and used at
  GluedStageEstimates.lean:562-570. Also trivially satisfiable (constant family), so no vacuity risk.
  VERDICT OK.
- Junk-value sweep: **no `/`, no `⁻¹`, no `decide`, no `inductive`, no `termination_by`, no
  `deriving`, no metaprogramming, no `.rec`** anywhere in the file. Largest numeral: `2`
  (`nhds`-free, in `𝓝` names only) / `0` for the default value — benign by inspection.
  KERNEL-RISK: none.
- Silent default (shape 4) considered and OK: `representative` returns `0` off the valid union
  (`representative` ValidBandGluing.lean:27-29). That default is not hidden — it is *stated* as the
  content of `representative_zero` (:34) and `representative_zero_germ` (:72-75) — and every transfer
  theorem (`representative_eq_of_mem` :39, `_germ` :65, `_contDiffAt` :93, `_fderiv_eq` :105,
  `_iteratedFDeriv_eq` :120, `_jet_bound` :125, `_jet_bound_on_union` :134, `_finite_jets_bound` :141,
  `_jet_apply_eq` :148, `_spatialCurl_eq` :167) carries an in-signature `hx : x ∈ U i` or
  `x ∈ domain U`. No statement is true merely by the default.
- NOTE (minor, harmless direction — a *redundant* hypothesis, shape-6-adjacent):
  `representative_unique_on_domain` (ValidBandGluing.lean:51-56) assumes BOTH `hf : Compatible U f`
  and `hg : ∀ i, EqOn g (f i) (U i)`. `hf` is derivable from `hg`: for `x ∈ U i ∩ U j`,
  `f i x = g x = f j x`. So the theorem is stated with a strictly stronger hypothesis set than needed.
  Weakening only, no soundness impact.
- `representative_jet_bound_on_union` (:134-139) doc-comment claims "no multiplicity factor" — correct,
  because `representative` picks ONE chart pointwise, not a sum; the proof is a rewrite (:139).
  Docstring matches statement.

Tally: 24 decls read — OK 23 / NOTE 1 / UNCLEAR 0 / ESCALATE 0 / KERNEL-RISK 0.
