# What we checked in openai/ten-proofs (GapCVP), and what we concluded

A plain-language summary of the audit of the `GapCVP.lean` formalization in
`github.com/openai/ten-proofs` (commit `94bc0feb`, Lean 4.32.0 with Mathlib), the seventh
of OpenAI's "Ten advances": polynomial-factor hardness of approximating the closest vector
problem. The detailed report is `2026-10-04-openai-ten-proofs-GapCVP.md` and its evidence is
under `gapcvp-intake/`. The artifact was never modified.

The formalization is one file of 130,430 lines with no comments, written by OpenAI's model
"Astra" according to the repository's metadata. It was chosen because, of the AI-written
Lean projects we surveyed, it was the only remaining one with a tactic-macro layer. Unlike
the earlier audits, this one was carried through the build: the module was compiled here,
the authors' comparator configuration was re-run, and the proof was replayed by four
independent checkers.

## The headline

Four theorems in a `Comparator` namespace: for every language in NP there is a
deterministic polynomial-time reduction to the promise problem GapCVP with gap n^{1/400} in
the Euclidean norm, and likewise to binary nearest-codeword and syndrome decoding with gap
n^{1/200} and to ℓ_p closest vector with gap n^{1/(200p)}. NP, polynomial time and
reductions are all defined through Mathlib's two-stack Turing machines with polynomial time
bounds. We wrote the reference statement from the paper's Theorem 1 and Corollaries 15–16
before reading the Lean statement file, then paired them clause by clause. Every clause
matches. Three differences all make the formal statement stronger than the paper's:
targets are restricted to integer vectors, syndrome-decoding NO-instances must be
consistent systems, and the generator matrix is written transposed.

## What was checked

- **The statement, and what the comparator did not compare.** The statement file lists
  the four promise problems as comparator "definition holes", because its disjointness
  fields are `sorry` placeholders. For a hole the comparator checks only the name and type,
  never the body, so the authors' comparator pass certified the NP-hardness scaffolding and
  nothing about the YES and NO languages or the gap factors. We showed this concretely: a
  copy of the statement file with the gap exponent changed from 1/400 to 1/4 still passes
  the comparator. We then did the missing comparison ourselves at the level of elaborated
  terms: the four promises and the thirty definitions they reach are identical between the
  statement file and the proof, up to auxiliary proof names and variable names.
- **Is NP even nonempty?** Every theorem says "for every language in NP". The artifact
  never shows that any language is in NP under its own definition, so the theorems could in
  principle have been vacuous. We built a two-stack machine that accepts every input,
  against Mathlib's definitions, and proved inside the built artifact that the
  everything-language is in NP, using only the three standard axioms. The class is
  inhabited and the theorems are not vacuous.
- **The proof, read at three places.** The Cook–Levin step (an arbitrary polynomial-time
  verifier run, with guessed certificate bits, encoded as a 3-CNF through a tableau and a
  Tseitin translation) is the standard argument with nothing left over. The gap core matches
  the paper in exponent, dimension, radius and parameters, with only intermediate constants
  differing; one numeric fact the bridge rests on was recomputed. The coding and ℓ_p
  transfers match the paper's lemma and corollaries. Every object that looks like an
  assumption, including closure of polynomial time under composition, is constructed in the
  file.
- **Metaprogramming and trust surface.** Twenty-three tactic macros, each a `simp` over a
  concrete machine's step definitions followed by `congr`, case splits and `rfl`, used 439
  times. Classical decidability instances only package propositions as booleans. No
  axioms, `sorry`, `native_decide`, unsafe code, options or elaborators anywhere; the
  largest numeral in the file is 2000.
- **Build and checkers.** Compiled here in under twelve minutes. The four headline theorems
  depend on exactly the three standard axioms. The authors' comparator configuration passes.
  The export of the four theorems, 57,683 declarations, is accepted by Lean's own
  leanchecker, by con-leche in its proof-covered mode, by con-ron and by nanoda.

## Conclusions

- **No defect found.** The theorem stated is the paper's theorem, slightly strengthened; the
  proof matches the paper where it was read; the kernel and four independent checkers
  accept it.
- **The comparator pass should not be read as a statement check** for this artifact. Its
  configuration leaves the problem definitions unchecked, and a wrong gap factor would pass.
  Our elaborated-term comparison fills that gap, with the caveat that statement and proof
  share an author.
- **What this audit does not say.** Two large blocks were read only at their interfaces:
  the algebraic reconstruction behind the gap (about eight thousand lines) and the Turing
  machine constructions that make the reduction polynomial-time (about seventy thousand
  lines, which only the kernel can certify, and did). About five percent of the lines and
  three percent of the theorem statements were read by a person-equivalent. The comparator
  ran with its development sandbox shim rather than the real one, which does not affect the
  kernel verdicts.

## Reports

- `2026-10-04-openai-ten-proofs-GapCVP.md` — the report.
- `gapcvp-intake/STATEMENT.md`, `REFERENCE-gapcvp.md` — the statement rung.
- `gapcvp-intake/ROUTE-MAP.md`, `ROUTE-WALK.md` — the dependency map and the three reconstructions.
- `gapcvp-intake/TRUST.md` — the metaprogramming and trust surface.
- `gapcvp-intake/controls/` — the axiom listing, the NP-inhabitation control, the checker
  script, the comparator logs for the real and the mutated challenge, and the
  elaborated-term dumps.
