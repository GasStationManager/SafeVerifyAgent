# openai/math result 107 — "An Upper Bound of 9/4 for the Matrix Multiplication Exponent": read-through

- **Artifact:** `github.com/openai/math`, commit `adc7f1241` (the single "Initial commit"), `lean/`
  project, Lean `v4.34.1` + Mathlib. Solution `OAI/LinearAlgebra/MatrixMultiplication/`
  (509 files, 83,302 lines); the 9/4 headline's route is the `AuxiliarySeparation` subtree plus
  the shared `Model`/`Arithmetic`/`ComplexArithmetic`/`Tensor` modules — 129 modules, 20,694
  lines (`mm94-intake/route-closure.txt`). The two companion theorems (α > 0.465,
  ω(1,0.709,1) < 2.092) ride the Coppersmith–Winograd machinery (163 and 115 modules) and are
  NOT audited here.
- **Claim:** PAIRED. Challenge `ComparatorChallenges/MatrixMultiplication.lean` (132 lines),
  config `MatrixMultiplication.json`: three theorem names, `definition_names: []`, standard
  axioms, `enable_nanoda: false`. Headline `OAI.MatrixMultiplication.complex_omega_le_nine_quarters :
  Arithmetic.omega ℂ ≤ 9/4`.
- **Paper:** `preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf` — ABSENT from
  the checkout and from the git tree (only `README.md`); fetched from the public repository
  (371 KB, 12 pages). Two "secondary writeups" (Sep 24) carry the other two theorems.
- **Auditor:** one Claude Fable 5.1 coordinator (statement rung, mechanical rung, build,
  checkers) and six Claude Opus readers A–F (one per paper section), reports in
  `mm94-intake/READ-*.md`. ONE model family: independence is between passes, not models.
- **Artifact never modified.**

(sections filled in as the rungs complete)
