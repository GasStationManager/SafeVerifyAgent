# What we checked in RBarish-UTokyo/FourColorTheorem-Lean4, and what we concluded

A plain-language summary of the audit of the Lean 4 port of Gonthier's Coq proof of the
Four Color Theorem, published at `github.com/RBarish-UTokyo/FourColorTheorem-Lean4`
(commit `20fa3459`, Lean v4.35.0-rc2) and registered with Palomar at trust level "high".
The detailed report is `2026-09-30-RBarish-FourColorTheorem-Lean4-metaprogramming.md`
and its evidence is under `fct-intake/`. The artifact was never modified.

The artifact says of itself that an AI agent wrote essentially all of it and that no human
has reviewed the mathematics. We picked it from a survey of recent AI-written
formalizations because it is the only one with a real elaboration-time engine: Lean code
that runs during the build, computes hundreds of megabytes of certificate data, and injects
it into the proof as literal numbers. That is the kind of construction where a wrong step
could in principle smuggle an unchecked value into a kernel-checked proof. This audit asked
whether it does, and whether the theorem stated is Gonthier's theorem.

## The headline

`FourColor.RealPlane.four_color`: every simple map of the real plane, with possibly
infinitely many regions, has a colouring with at most four colours in which adjacent
regions get different colours. The statement file is a transcription of Gonthier's
`realplane.v`. We fetched the Coq files at the exact commit the port names and compared all
twenty definitions and the theorem one by one: every one matches. The single difference is
declared by the port: Coq proves the theorem for any model of its axiomatised real numbers,
and the Lean version fixes the model to Mathlib's `ℝ`. The statement uses the reals only
through "less than", which Coq defines as "not greater-or-equal", so on `ℝ` the two
definitions coincide. The statement that Palomar checks and the one the proof is about are
byte-identical in their definition block, by our own diff.

## What was checked

- **The engine, read end to end.** The two generator files and every macro in the tree.
  Every declaration the engine creates goes through Lean's ordinary `addDecl`, which hands it
  to the kernel; the only switch that skips the kernel is never set anywhere in the artifact.
  The compiled code produces data only (network masks, checkpoints, configuration programs).
  Every theorem about that data is either a kernel evaluation (`Eq.refl true`) or an
  application of theorems proved in ordinary Lean source. The engine adds nothing else: no
  axioms, no opaque constants, no inductive types, so the two 2026 kernel bugs that
  metaprograms could reach are out of shape as well as fixed before this Lean version.
- **Controls, run live.** We built the engine on this machine and generated two
  certificates ourselves, one at the smallest ring size and one at the largest (ring 14, the
  memory-heavy case). Then, calling the engine's own helpers, we re-added a genuine
  checkpoint theorem (accepted), flipped one bit of a checkpoint (rejected by the kernel), and
  dropped one layer of a network (all six position checks rejected). The docstring's claim
  "a wrong literal only makes a kernel check fail" is what happens.
- **Independent checkers.** Both certificates were exported and replayed by the four
  checkers that now ship with the Lean toolchain: Lean's `leanchecker`, con-leche in its
  proof-covered mode, con-ron, and nanoda. All four accepted both, with exactly the three
  standard axioms. On the question whether con-ron is "guaranteed consistent": it carries the
  same consistency theorem as con-leche through one more translation layer (a Rust-to-Lean
  model), with its own verified bignum; its authors do not call it high assurance, and
  running both means a bug would have to exist in both runtimes at once.
- **Why the engine exists.** Measured: a single 4-megabit number written as a decimal
  numeral takes eleven minutes to elaborate, and the ring-14 networks are forty times that.
  Generating at build time is a cost decision, not a soundness one. Its visible price is
  that the certificates live only in build outputs and in Palomar's export, not in the
  repository. Malformed number objects cannot reach the external checkers either: the
  export writes each number as a decimal string the checkers parse for themselves.

## Conclusions

- **No defect found.** The metaprogramming layer does what it says, the kernel refuses
  corrupted certificates, and two certificates spanning the engine's range pass four
  independent checkers.
- **The theorem is Gonthier's theorem**, specialised to Mathlib's reals.
- **What this audit does not say.** We did not read the mathematical route from the
  headline down to the 633 configurations (compactness, discretisation, unavoidability,
  the Birkhoff replay), and we ran the external checkers on two certificates, not 633;
  Palomar's own pipeline ran them on the whole proof. Whether the 633 configurations and the
  discharge rules are exactly Gonthier's was not checked here. The kernel's big-number
  arithmetic remains trusted, now by four implementations rather than one.

## Reports

- `2026-09-30-RBarish-FourColorTheorem-Lean4-metaprogramming.md` — the report.
- `fct-intake/METAPROGRAMMING.md` — the read-through, the controls, the checker runs,
  what the engine adds and why.
- `fct-intake/STATEMENT.md` — the definition-by-definition pairing with `realplane.v`.
- `fct-intake/CHECKERS.md` — what con-leche's and con-ron's proofs cover.
- `fct-intake/controls/` — the Lean files that ran the controls.
- `targets/2026-09-30-survey.md` — how this artifact was chosen.
