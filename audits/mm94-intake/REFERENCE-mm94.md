# Reference statement — openai/math result 107, "An Upper Bound of 9/4 for the Matrix Multiplication Exponent"

Written from the paper (Theorem 1.1 and §1's definition of ω) and the standard
definition of the arithmetic exponent. HONESTY NOTE: `Model.lean` (114 lines) and the
challenge file were read BEFORE this was written, because locating the result required
opening them; the reference below is nevertheless written from the paper and the standard
textbook definition (Bürgisser–Clausen–Shokrollahi §15), and the diff is recorded in
`STATEMENT.md`.

## The claim (paper, Theorem 1.1)

For every ε > 0, two n × n complex matrices can be multiplied using O_ε(n^{9/4+ε})
arithmetic operations. In particular ω ≤ 9/4.

Paper's definition of ω (§1): the infimum of the real τ such that, for every ε > 0, two
n × n matrices can be multiplied in O_ε(n^{τ+ε}) scalar arithmetic operations; the
algorithm and its constants may depend on ε.

## What a faithful formal statement must contain

1. A MODEL of computation: division-free straight-line programs over ℂ whose steps are
   +, −, × of earlier values, inputs are the 2n² matrix entries, constants from ℂ are
   allowed. Cost = number of +, −, × steps. Loading an input or a constant may be free
   (standard: constants are free in the algebraic model; this does not change ω). No
   division (standard; Strassen showed division does not help for ω), no branching, no
   indirect addressing — the model must NOT allow anything that reads the matrix size into
   control flow, and must not let one "gate" compute more than one scalar operation.
2. CORRECTNESS: the program's designated outputs equal the entries of A·B for ALL
   A, B ∈ ℂ^{n×n} (not generic, not up to approximation — exact).
3. THE EXPONENT: ω = inf { τ : ∀ ε>0 ∃ C ∀ n ≥ 1 ∃ correct program of cost ≤ C n^{τ+ε} }.
   The constant C may depend on ε, the program on n and ε.
4. THE CONCLUSION: ω ≤ 9/4, AND (to exclude the real-`sInf` convention trap, where the
   infimum of an empty or unbounded-below set is 0) the explicit form:
   ∀ ε>0 ∃ C>0 ∀ n≥1 ∃ correct program P with cost(P) ≤ C · n^{9/4+ε}.

## Things that would weaken the statement (to look for)

- cost counting only multiplications (then the bound is a statement about bilinear
  complexity; still implies ω ≤ 9/4 for the full count since additions add O(n²) per
  recursion level — but the paper claims the full count, so check).
- "Correct" quantified over some matrices, or over a subring, or up to a scalar.
- A program type that can depend on the inputs (non-uniform in a way that cheats), or
  gates with unbounded fan-in at unit cost.
- ω defined as inf over a set that could be empty or unbounded below, with no explicit
  ε-C-n-P form proved.
- Matrices over a type other than ℂ, or "matrix multiplication" meaning something other
  than Mathlib's `Matrix.mul`.
