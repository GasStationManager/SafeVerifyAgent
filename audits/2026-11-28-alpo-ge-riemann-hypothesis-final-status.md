# alpo.ge `lean.tar.gz` — final status of the audit (RH and GRH for Dirichlet L-functions)

Status: **no defect found; the claim is not confirmed by this audit, 2026-11-28.**
What this audit did not run is stated first. It did not build the headline, did not run
`#print axioms` on it, and ran no independent kernel. An external page reports all three for
the archive with our SHA-256; this audit did not re-verify that page's logs or export. The
mathematical argument was reconstructed by reading and tested by experiment, not checked:
every proof body not listed as read below was taken at its statement, and no mathematician
has reviewed the reconstruction.

Artifact: `https://alpo.ge/lean.tar.gz.part01 … part14`, SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; 175,187 `.lean` files,
17,374,215 lines; Lean `v4.33.1`, Mathlib `0df444a3…` (upstream tag `v4.33.1`). BARE claim.
This file closes three earlier reports and indexes them:

- [first audit](2026-11-20-alpo-ge-riemann-hypothesis.md): statement, trust surface, supply
  chain, cone, compile sample;
- [kernel surface](2026-11-20-alpo-ge-riemann-hypothesis-kernel-surface.md):
  metaprogramming, big integers, kernel computation;
- [argument reconstruction](rh-intake/argument/MAIN-ARGUMENT.md), with its running record
  [`SUMMARY.md`](rh-intake/argument/SUMMARY.md).

## 1. Verdict by rung

| rung | result | who ran it |
|---|---|---|
| statement | BARE, EXACT: `riemannHypothesis : RiemannHypothesis` with Mathlib's own definition; the four Dirichlet statements are typed over Mathlib only; nothing weakened or vacuous; scope is Dirichlet L-functions | this audit |
| trust surface | no `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by` in 17.4 M lines; three custom elaborators read, none can add an unchecked declaration | this audit |
| supply chain | Mathlib pin is an upstream tag; manifest unchanged | this audit |
| kernel computation | every located kernel-evaluated numeric fact recomputed independently (modular powers, primes to 186 digits, loops, ladders, a prime table); eleven negative controls fire | this audit |
| compile | 174 of 174 sampled modules built here; full build of all 175,187 modules | sample: this audit; full: external report |
| axioms | `[propext, Classical.choice, Quot.sound]` on the five headline theorems | external report (its `audit.log` read, not reproduced) |
| independent kernels | nanoda, default kernel, con-leche and con-ron (master builds) accept the export; Comparator v4.33.0 passes | external report |
| argument | reconstructed top-down from the live path; no defect found; not verified | this audit |

External report: `math.mit.edu/~drew/grh/` (A. Sutherland, last read at its 2026-11-23
update), which names the archive by the hash above, and a joint statement by the Lean FRO
and the Mathlib Initiative dated 2026-11-21. Caveats the first states about itself: the
original build invoked `lean` directly; the Comparator run used a stub for its build step;
bundled v4.36.0 con-leche/con-ron declined (one reflexive inductive type unsupported); one
`.olean` is byte-nondeterministic; two checks were still running. Neither addresses the
mathematics.

The first report's escalations: E1 (build, axioms, kernels) is discharged by others on that
evidence; E2 (nobody can say why the theorem is true) is what the reconstruction addresses
and does not close; E3 (deep published theorems re-proved in-tree) stands as a reading list;
E4 was closed by trace in the second report.

## 2. The argument, as reconstructed

Fourteen steps, given in full in `MAIN-ARGUMENT.md` §0. In brief, for a character ψ:

1. A windowed one-sided Landau lemma: a bound G_m(y) ≤ C·y^θ on windows [Y, Y^{1+δ}] for a
   positive combination G_m of smoothed Chebyshev error terms of ζ and ⟨ψ⟩ gives
   zero-freeness for Re s > θ. Target: G_m(x) ≤ x^{1/2+9ε}.
2. For each window a host CM field E ⊃ ℚ(√−d) in which ψ(p) is a Frobenius coordinate, with
   (q, d) chosen by an elementary averaging argument so that the quadratic twists are small
   at the point x. Only primes inert in ℚ(√−d) are then counted.
3. Bridge: the target becomes ASK ≤ Main + Err, ASK = Σ Λ(n)(1 − χ_{−d}(n))(a/n − w)₊.
4. Loss bound: ASK − Ga ≤ C·|TT|·m·b for an explicit piecewise-linear gain formula Ga.
5. Engine: at an inert prime, in height-2 Lubin–Tate coordinates, every jet
   (top form)^a × (minors) of the CM theta kernel has valuation
   ≥ Σ_{e odd}(a/p^e − cap)₊ − loss, on the whole integral lattice; gains add over m ≈ √x
   chained lifts.
6. The source lattice is scaled by exactly the exponent defining Ga; the engine says the
   chain map still lands in the target lattice.
7. Bost's slope inequality (by Harder–Narasimhan pieces, robust rank from a near-tight
   frame of Poincaré series, layer cake) bounds Ga by height plus covolume terms.
8. An exact identity turns height minus the Chowla–Selberg term into the explicit-formula
   main term. A level prime T, shared by all lifts and pinned by a dimension match, is what
   brings the cap into the archimedean main term.

Error families per unit U: one-off terms x/m, per-lift terms m, the congruence allowance
k/n²; balanced at m ≈ √x. The Galois-theoretic machinery (congruence modules, Selmer
killing, a Ш bound from a U(3) deformation ring, in-tree Galois representations) enters
through one error term only.

## 3. Denominators

| | count |
|---|---|
| project files / in the cone of the headline | 175,187 / 175,187 |
| declarations / in cone | 1,066,087 / 905,410 |
| explainer nodes written | 108, each citing only `file:line` that was read |
| reviews | 4 (two of single nodes, two cold reviews of the exposition, the second adversarial) |
| numerical experiments | 6 exact-arithmetic or high-precision, plus 4 hand/numeric checks, each with controls |
| rounds | 17 |
| corrections of one node by a later one | about 50, recorded in `SUMMARY.md` |
| escalations raised and closed by trace | 2 (TWIST → ORDER; zero-chain alarm → ADM11) |
| escalations open | 0 |

Coverage in tiers. Read to the bottom on the live path: the Landau step; host selection
(top levels); the ledger of the final inequality and its assembly; both divisibility routes
down to the orthonormal theta integrality, which was itself read to the bottom; the
Young-diagram inequality; Chowla–Selberg (statement and constant, checked by hand and
numerically); the gain–lattice tie; the type prime; the covolume transport; the orbit
decomposition under near-orthogonality. Read to a mechanism with content bodies unopened:
near-orthogonality and the counting theorem; the covolume's volume side; the index budget;
the integral p-adic comparison for widely spaced weights; the Galois side. Taken at their
statements: in-tree proofs of classical theorems (Siegel–Weil, comparison theorems, mass
formulas, the Galois-representation theorem's geometric inputs).

## 4. What the experiments tested

| experiment | object | result |
|---|---|---|
| NUMTEST, ℘ addendum | Taylor coefficients of σ and ℘ at inert primes | σ gains a/(p²−1), ℘ gains γ_p·a; explained later by the self-Gaussian |
| NUMTEST2–4 | Kronecker theta and the Lean's kernel at small orbit lengths | capped law holds |
| NUMTEST5 | capped law at a signal place across the kink cap = a/p | holds over ≈ 250,000 jets, loss O(1); controls break it |
| NORMS | period constant; archimedean size at a ≈ 6000 | constant matches to 8 decimals; residual O(log a) |
| NUMTEST6 | composition of up to 8 lifts in an archimedean model | loss ≤ 11 against a·log 2 up to 1065 |
| INTINERT, THMS models | rank-2 unitary frames; SL₂ Poincaré blocks | agree with the statements read |

None runs the Lean; none reaches the real sizes (rank ≈ x^{399}, m ≈ √x).

## 5. What remains open

- **The reconstruction is unreviewed.** It was made by one model family across passes; the
  second cold reviewer, reading only the exposition, judged the argument as described very
  unlikely to be correct and named five candidate failure points. Each was then read; none
  produced a defect; three were answered with a mechanism, two remain predictions
  (`MAIN-ARGUMENT.md` §9.7–§9.10).
- **What carries the √x barrier in truth is not established.** The chain as built pays a
  cost at the type prime by definition, so it cannot prove too much; whether any term is
  forced to that size is unknown.
- **Unread beneath the main inequality:** the geometric inputs under the volume side and
  the open/compact link; the evaluation of the Hodge metric at CM points; about a dozen
  content bodies under near-orthogonality and the count.
- **Not started:** a dimension-three test of the integral comparison; congruences with
  weight varying over two places. Both feed only the Galois-side error term.
- **One conceptual question:** why the share weights are 4:3; any positive weights would
  serve the Landau step.

## 6. Instrument notes

- `cone.py` misses imports of module names ending in `'` (two false orphans); not fixed.
- Auditor: one Claude-family agent with subagents of the same family; independence is
  between passes, not between models.
- The extracted source lived in session scratch space; node citations are `file:line`
  against the archive with the hash above.

## 7. Plain-language summary

Is the headline sound? The statement is exactly Mathlib's Riemann Hypothesis, the source
contains no escape hatch we could find, and an independent party reports that this exact
archive compiles with only the three standard axioms and is accepted by several independent
kernels. This audit did not reproduce that. What it did was read: it reconstructed a
coherent mathematical argument from the Lean, tried repeatedly to break it by adversarial
review, hand computation and numerical experiment, and found no defect. That is evidence
the proof expresses a real argument, not a kernel exploit; it is not a verification of the
argument, most of whose proof bodies were not read.

Can an intermediate theorem be reused? Several in-tree results go beyond the published
literature (the divisibility law for CM theta jets, the integral comparison outside the
Fontaine–Laffaille range, the determinantal local model for patching, uniform counting on
unitary groups). Each is on the route and non-vacuous as far as read, but none has been
checked by a specialist; treat them as leads, with the node files as maps.
