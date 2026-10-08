# Statement rung — challenge `ComparatorChallenges/MatrixMultiplication.lean` vs the reference

PAIRED: the challenge file exists (132 lines), `definition_names: []` (no holes), three
theorem names; the comparator therefore compares the whole statement including every
definition it reaches. The challenge's `Arithmetic` namespace is byte-identical in content
to `OAI/LinearAlgebra/MatrixMultiplication/Model.lean` (checked by diff below).

Clause-by-clause against `REFERENCE-mm94.md`:

| reference clause | challenge | verdict |
|---|---|---|
| model: straight-line, +,−,× of earlier registers, ℂ constants, inputs | `Gate`: constant / input / add / sub / mul of two earlier `Fin r` registers; `Program` is an inductive list, each new gate sees exactly the earlier registers (`Fin r`); `Fin.cases` puts the newest gate at index 0 | EXACT. No division, no branching, no fan-in > 2, no size-dependent control |
| cost: number of +,−,× | `Gate.cost`: constant 0, input 0, add/sub/mul 1; `Program.cost` sums | EXACT (constants and input loads free — standard) |
| correctness: all A, B, exact `A * B` | `Correct P := ∀ A B, P.eval A B = A * B` with Mathlib `Matrix` product over `Fin n` | EXACT |
| exponent set and ω | `AdmissibleExponent F τ := ∀ ε>0 ∃ C>0 ∀ n≥1 ∃ P, P.Correct ∧ cost ≤ C n^(τ+ε)`; `omega F := sInf {τ | Admissible}` | EXACT in form. `sInf` trap: see below |
| conclusion ω ≤ 9/4 | `complex_omega_le_nine_quarters : Arithmetic.omega ℂ ≤ 9/4` | EXACT |
| explicit ε-C-n-P form | NOT in the challenge. In the solution: `AuxiliarySeparation.matrix_multiplication_cost_le (ε) (hε) : ∃ C>0, ∀ n≥1, ∃ P, P.Correct ∧ cost ≤ C n^(9/4+ε)` (`AuxiliarySeparation/Main.lean:21`), and `Arithmetic.admissibleExponent_iff_omega_le : AdmissibleExponent ℂ τ ↔ omega ℂ ≤ τ` (`Arithmetic/Exponent.lean:49`; the alias `arithmeticBound_iff_omega_le` is `AuxiliarySeparation/Arithmetic/Exponent.lean:39`) | the challenge's `sInf` statement is non-vacuous ONLY because the solution also proves the iff; `#print axioms` of `matrix_multiplication_cost_le` is the audit's headline check, not only the three comparator names |

Observations:
- `innerSize n k := ⌈n^k⌉₊` and `rectangularOmega`, `complexAlpha := sSup {k ∈ [0,1] | rectangularOmega ℂ k = 2}` concern the two secondary theorems (α > 0.465, ω(1,0.709,1) < 2.092); not this audit's headline.
- `Real.sInf` of a set unbounded below is 0: `omega ℂ ≤ 9/4` would hold vacuously if the admissible set were unbounded below. It is bounded below by 2 (`Arithmetic/LowerBound.lean`, read by reader A) and `admissibleExponent_iff_omega_le` makes the ≤ statement mean what it says.
- Comparator config permits only `propext`, `Quot.sound`, `Classical.choice`; `enable_nanoda: false` as in 402/405 configs.
