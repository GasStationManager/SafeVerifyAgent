# What we checked in openai/math result 107 (ω ≤ 9/4), and what we concluded

A plain-language summary of the read-through of the Lean formalization of "An Upper Bound of
9/4 for the Matrix Multiplication Exponent" (OpenAI, 2 October 2026) in `github.com/openai/math`
(commit `adc7f1241`, Lean 4.34.1 with Mathlib). The detailed report is
`2026-10-08-openai-math-MatrixMultiplication-9-4.md`; evidence is under `mm94-intake/`. The
artifact was never modified.

## The claim

The exponent of matrix multiplication over the complex numbers is at most 9/4: for every ε > 0
there is a constant C such that two n × n complex matrices can be multiplied by a straight-line
arithmetic program (additions, subtractions, multiplications, free complex constants, no
division) of at most C · n^{9/4+ε} operations, for every n. The best previously known bound was
about 2.3712. The proof is a new method: Strassen's spectral theory of tensors ("characters")
plus two inequalities for ordinary polynomial multiplication obtained by degenerating tensors
whose pieces share one of their three variable groups.

## What was checked

- **The statement.** A reference statement was written from the paper and compared clause by
  clause with the Lean statement. They agree exactly: the computational model is the standard
  one, correctness is required on all inputs, and the exponent is defined as the paper defines
  it. The one way such a statement could be vacuous in Lean (the infimum of an empty or
  unbounded set is 0 by convention) is excluded: the set is proved nonempty and bounded below,
  and the explicit "for every ε there is a C" form is proved as a separate theorem.
- **The proof, read in full.** Six independent readers each took one section of the paper and
  reconstructed the Lean argument against it: the conversion from tensor rank to programs; the
  tensor and character definitions and Strassen's dot-product exponents; the existence of
  "detecting characters" (Appendix A, including a proof of the Schauder–Tychonoff fixed-point
  theorem from Brouwer's); the central separation construction (a finite Fourier projection and
  a weight whose surviving part is the square of a label mismatch); the two polynomial
  multiplication inequalities (a determinant filtration and a three-sector partition); and the
  discrete growth lemma that forces the final 3/4. In every section the Lean carries out the
  paper's construction explicitly rather than assuming it, with the same hypotheses and the same
  conclusions. Nine small independent computations reproduced the constructions numerically,
  including negative controls that fail as they should.
- **Trust surface.** Across the 509 solution files there is no `sorry`, no axiom, no
  `native_decide`, no unsafe code and no metaprogramming; on the 129 modules the 9/4 proof
  actually uses there is not even an `attribute` line. The proof uses one external package for
  Brouwer's fixed-point theorem, with a compatibility patch shipped in the repository; it was
  scanned and is clean.
- **Build and checkers.** The route was compiled here in 16 minutes. The headline theorem and the
  explicit-constant theorem depend on exactly the three standard axioms. The export of the proof
  (49,693 declarations) is accepted by Lean's own leanchecker, by con-leche in its proof-covered
  mode, by con-ron and by nanoda.

## Conclusions

- **No defect found.** The Lean theorem is the paper's theorem; the Lean proof is the paper's
  proof; four independent checkers accept it. ω ≤ 9/4 over ℂ is a theorem of Lean + Mathlib +
  the three standard axioms.
- **The bound is tight for the method.** The growth lemma's hypotheses force exactly the
  a^{4/3} the paper extracts, so 9/4 is the most this argument gives.
- **What the audit does not say.** The algorithm is not explicit: its coefficients come from a
  rank decomposition chosen non-constructively, and no competitive finite matrix size is given,
  exactly as in the paper. All readers were one model family. The two companion theorems in the
  same Lean directory (the dual exponent and a rectangular bound, proved by Coppersmith–Winograd
  machinery) were not read.
