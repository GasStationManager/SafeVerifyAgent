# Audit: openai/NavierStokesAndEuler — coverage of in-cone proofs, and paper ↔ Lean statement alignment

**Artifact:** `openai/NavierStokesAndEuler` @ `f9e8bc5` (read-only throughout; never modified).
**Paper:** the published manuscript, https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf
(166 pages; text extracted with PyMuPDF, 78 numbered statements indexed in
`nse-deep/alignment/paper-statements.json`).
**Method:** four independent reading agents, each given one slice of the paper and the
whole artifact, asked to locate every numbered statement's Lean counterpart and classify it
EXACT / LEAN STRONGER / LEAN WEAKER / NO COUNTERPART / UNRESOLVED. Every `file:line` cited
in the four reports was re-read by the agent that cited it; the coordinator re-verified the
headline items at the source (listed in §4). Nothing was compiled: the artifact has
already passed Comparator, and a compile re-run answers a different question from the one
this audit asks (whether the kernel could have been fooled, and whether what it checked is
what the paper claims).
**Auditor family:** all readers are from one model family. Independence is between slices, not
between models.

Two questions were asked. Both are answered below, the short answer first.

---

## 1. Are all in-cone proofs read by an agent?

**No.** The ledger in `nse-deep/COVERAGE.md` and the 9/18 final report, restated in tiers:

| tier | files | in-cone theorems |
|---|---|---|
| in the cone (denominator) | 2,306 | 27,753 |
| living in some file a worker report names (generous upper bound on "touched") | 710 | 15,310 (55.2%) |
| structural bucket, read line-by-line | 73/73 | 843 |
| never-named files, read line-by-line | 41 | 737 |
| screened and adjudicated by a human | 47 | ~398 |
| screened clean by two mechanised passes only, never read | 876 | 3,932 |

"Named by a report" is a deliberately loose bound (one cited line makes a 138-theorem file
count as touched), so the honest reading is: the *spine* of both headline theorems has been
walked end to end, every kernel-exposure site has been classified (14 inductives, 12
`termination_by`, 5 explicit recursors, 210 `decide`, 121 large numerals, 541 bare-`rfl`
proofs), roughly 1,580 in-cone theorems outside the spine were read line by line, and the
bulk of the estimate mass of the Navier–Stokes half was screened for two defect classes and
not read. A wrong constant in that mass is invisible to both screens.

One kernel-exposure surface remains **unbounded**: the 1,176 in-cone theorems whose tactic
block is *closed* by `rfl`. Their defeq goal is not in the source, so no statement-level
screen prices it; bounding it needs the elaborated goals (a compile with tracing), which
this audit did not run by the user's instruction. It is the one item in this section that
is a kernel-trust question rather than a coverage question, and it is recorded in the
9/16 kernel-trust report at the same number.

---

## 2. Are intermediate Lean theorems weaker than what the paper claims?

**No load-bearing weakening was found in any of the four slices, and no paper statement is
without a Lean counterpart.** The headline (Theorem 1.1) matches the paper clause by
clause. Where Lean and the paper differ, Lean is more often the stronger: explicit
constants, larger domains, a closed-form blow-up rate at the fixed origin that the paper
never states. The genuine weakenings are all of the kind "the paper's stronger form is
true and is not used", and each is listed so a reader can check that claim rather than
take it.

### 2.1 The headline, clause by clause (slice D)

`NavierStokesR3.theorem_1_1 : ProblemStatement.breakdownStatement` is EXACT against the
paper's Theorem 1.1 (p1). Two clauses that the 9/15 report described as specialisations
are the paper's own: `u(·,0) = 0` is in the paper's display and the abstract ("starting
from rest"), and the force being compactly supported in space *and* time is the paper's
`f ∈ C_c^∞(R³ × (0,∞))`. Neither is a divergence. The one structural asymmetry is that
the PDE is imposed on the open time interval only (`R3/ProblemStatement.lean:104`,
`Ioo 0 1`; the competitor class at `:135`, `Ioi 0`), for the stated reason that the
operators are ordinary `fderiv`s. That makes the positive half marginally weaker (the
equation at `t = 0` is not asserted; moot for the candidate, which is zero for `|t| ≤ 3/8`)
and the negative half marginally stronger (more competitors are ruled out). The stronger
direction is the one that carries the theorem.

### 2.2 Genuine weakenings, ranked by how much an expert should care

None is a defect. Each is "Lean proves less than the paper's sentence, and the difference
is not consumed".

1. **Lemma 9.8, residual exponent.** Lean's (9.18) uses the one common gain
   `gain h j = h·j/10` (`NavierStokes/ActualIterationLedger.lean:29`,
   `MixedCandidateAssembly.lean:62–65`) where the paper has `h(1/5 + j/10)`. Weaker by
   `h/5` in the exponent. Only `gain → ∞` is used downstream
   (`DiagonalScale.exists_diagonal_scales:156`). If anyone wants the paper's `σ_j` decay
   from the formalization, it is not there. (D-F4)
2. **Lemma 8.6, uniqueness and derivative loss.** `TorusInverse` proves existence of a
   smooth zero-mean solution and a finite-loss bound; no uniqueness statement for the
   directional torus inverse exists in the artifact, and the composite bound is
   `C^{m+5}`, not the paper's `C^{m+4}` (Lean sums against `weight⁻⁴`,
   `SmoothFourierData.lean:343`). The artifact avoids needing uniqueness by rewriting both
   sides to one constructed series (`TemporalMeanUpdate.lean:245`); the paper's own uses
   (p64, p92) need only finite, order-independent loss. Both stronger forms are true and
   elementary. (C-F1)
3. **Lemma 4.11 / Lemma C.1, hypothesis strengthened.** `TrueConeLoop.lean:765` takes
   `ContDiff ℝ ∞` on all of the ambient space where the paper assumes smoothness on
   `I × [−1,1]` with one-sided derivatives. The artifact's data is built from globally
   smooth pieces, so it is discharged in practice, but neither the statement nor its
   callers record the extension step. The two halves of Lemma 4.7 use different
   conventions for the same issue (open neighbourhood vs `Icc`), which is worth one
   question to the authors. (A-3)
4. **Proposition 5.3, exponent one slow order short** (`2Nh − 2 − m` vs
   `2h(N+1) − K_m`). Benign: the paper's form is recovered by shifting `N`. (B-3)
5. **`f₀ > 1/4` where the paper has `f₀ ≥ .265`** (`AxisSeries.lean:302`). Lean's
   hypothesis is weaker, so its theorem is stronger; listed because a reader matching
   constants will see a discrepancy. (B-4)
6. **Lemma 10.2, "uniformly on R³" is locally uniform in Lean**
   (`JointResidualLimits.lean:148,156`). Harmless because the force has fixed compact
   support and the Whitney route consumes boundary jets, not a global modulus. (D-F5)
7. **Definitions 6.4 / 6.5 formalized as size bounds only.** `WeightedClasses.MemClass`
   (`:107`, three fields) omits angular invariance, common-torus descent and the support
   conditions that the paper puts into *membership*. Lean carries those as separate
   predicates at the use sites; verified at the cross-label product
   (`PartitionedCovariance.cross_product_zero`) and the curl lemma
   (`CurlClassBounds.curlRemainder_waveClass`), **not verified at the residual and
   correction-cycle sites**. This is the one item in the list that is still an open check
   rather than a closed observation. (C-F2)

### 2.3 Where Lean is stronger, worth knowing so nobody double-counts

* Blow-up: `FinalSlowBase.origin` (`NavierStokes/FinalSlowBase.lean:361`) gives the closed
  form `u(t,0) = ((1−t)^{−(1/2+h)} · j) • e₂`, `j > 0`, at the fixed spatial origin. The
  paper's proof uses a moving path converging to the origin and never asserts
  `‖u(t,0)‖ → ∞`. An expert should confirm the axial closed form is the intended leading
  behaviour rather than an artifact of the chosen base profile. (D-F3)
* Theorem 3.1 / Lemma 9.9 on a larger domain; Lemma 5.1 with one radius and one complex
  η-neighbourhood serving every order, and its placement chain
  `X_keep < X_cut < a² < inf I_pos` *proved* about the real witness
  (`AssembledSlowBase.lean:1083–1117`), not assumed. (A-2.6, B addendum)
* Lemma A.8 / Proposition B.8: the five moment conditions are five *equations*, pointwise
  in η (`NominalProfile.FiveMomentCertificate:2079`, proved for the assembled profile at
  `:2536`); "stress vanishes for `X ≥ X_b`" is an identity
  (`TerminalEdgeFactor.lean:1627,1631`), not a derived bound. The smallness objects
  (`MatchingBounds`, `SmallDebt`) are the repair solver's input, exactly the paper's
  logic on p155–156. (B addendum)
* Theorem 4.6(vi): the reserved windows, the `U = 0` / `E = c(1+η²)^{−1}X^{−1/2−λ}` shape
  and preservation under corrections are all conclusions in
  `NavierStokes/ReservedPatches.lean` (`heated_fields:333`, `xAmplitude_shape:282`), and
  both consumers discharge against it (`.mean` in `MeanRankUpdate.lean:1391–1430`,
  `.positive` in `AssembledSlowBase.lean:848–960`). No single declaration composes the
  pieces for the finished profile; that is packaging. (A-2.9, closes D-F11)
* Lemma 6.1, 6.2, 8.7 stronger on the count or the constant. (C)

### 2.4 Still open after this pass

Small, and each is a grep or a ten-minute read for someone who knows the artifact:

* MemClass consequences at the residual and correction-cycle sites (item 7 above).
* The zeroth-order forward↔backward stress identification behind Lemma A.8: the order-1
  analogue is proved (`FirstOrderBaseEdge.first_angular_eq_backward:248`) and the
  terminal-cone results consume `profileStress` directly, so the headline route may not
  need order 0; not located. Same shape as Lemma 4.9's angular backward primitive (the
  axial twin is `TerminalPressure.axialBackwardStress:1049`). (B-1, A-2)
* Lemma 5.2's weighted stress bound (5.13), left unresolved by slice B.
* Lemma 6.3 (label counting) is formalized faithfully but only in `LabelCounting.lean`,
  which is out of the cone. Either the headline chain avoids the label sum or bounds it
  another way. (C-F3)

### 2.5 A navigation finding that affects every future reader

The Lean docstrings cite a **draft** of the manuscript, not the published PDF. There is no
§11 in the published paper; Lemmas 3.5–3.7 do not exist there; the renumbering is
non-uniform (draft §3 → published §4; draft §6 → Appendix C; draft §8 → §6 and §7; draft
§N ≈ published §(N−1) for N ≥ 8), and the `R3/` files use the *published* numbering.
Anyone using the docstrings as a map will be wrong about half the time. The
correspondences established by content are tabulated at the end of each slice report.
The method lesson for the next auditor: in this artifact "not located" is cheap to get
wrong, because the paper's symbols are not the Lean names. Grep for structures and
consumers, not for paper notation. Slice A's rank-1 gap and slice B's two rank-1 items all
closed that way on a second pass.

### 2.6 Dead code and unreliable landmarks

`LeadingStressWeights.exists_weighted_profile:1154` has zero references in the artifact;
the headline reaches its conclusions individually. `Covariance.lean` and
`SmoothCovariance.lean` carry disclaimers that make Proposition 7.5 look unformalized;
`PrimaryCovarianceBounds.compact_chart_pair_bounds:385` plus `FlatCovariance.lean` prove
it. Neither is a defect; both mislead a sampling reader.

---

## 3. What this audit did not do

* Did not compile anything. Comparator has passed; the compile-backed checks are in the
  9/18 report.
* Did not bound the 1,176 closing-`rfl` defeq goals (§1).
* Did not read the 3,932 screened-only in-cone theorems (§1).
* Did not check the paper's *proofs*, only its *statements* against Lean's. A paper
  argument that is wrong but whose conclusion Lean proves anyway is out of scope, by
  design: the Lean proof is the proof.
* Did not use a second model family.

---

## 4. Coordinator's source re-verification

Every headline claim above was re-read at the cited line by the coordinator, independent of
the reporting agent: paper p1 Theorem 1.1 text (`u(·,0) = 0`, `f ∈ C_c^∞(R³ × (0,∞))`);
`R3/ProblemStatement.lean:102–106`; `ActualIterationLedger.lean:29`;
`FinalSlowBase.lean:361`; `ReservedPatches.lean:22–40, 282, 333`; `TrueConeLoop.lean:765`;
`WeightedClasses.lean:107`; `AxisSeries.lean:302`; `NominalProfile.lean:2079, 2536, 2543`;
`TerminalEdgeFactor.lean:1627, 1631`; `AssembledSlowBase.lean:1083–1104`;
`exists_weighted_profile` reference count. All confirmed.

## 5. Files

`nse-deep/alignment/align-{A,B,C,D}.md` are the four slice reports (A: §3, §4, App. C;
B: §5, App. A, App. B; C: §6–§8; D: §9, §10, Theorem 1.1), each with a summary table over
every numbered statement in its slice, per-statement notes, ranked findings, a
"what I did not check" section and the draft→published numbering it established.
`lean-paper-layer.md` is the index of the artifact's own paper citations that the slices
started from; `paper-statements.json` / `paper-index.json` are the 78 paper statements with
page numbers.
