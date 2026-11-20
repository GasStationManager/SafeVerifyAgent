# Argument reconstruction protocol

Goal: recover the informal mathematical argument that the Lean source expresses, top
down from `riemannHypothesis`, one node (theorem) at a time. Nothing is compiled; all
claims are from reading source. Source root (read-only): the `src/` directory given in
the brief. Find declarations with ripgrep (`rg -n 'theorem NAME\b|def NAME\b'`); names
are often written fully qualified at root (`theorem UpperTheory.Top.plugAll`) or short
inside a `namespace`. The tree has 175,187 files: never list directories wholesale,
never read a file you did not locate by search, and cap any single read at ~300 lines.

## Explainer

Input: one node (theorem name + file). Output: `NODE-<id>.md` with these sections.

1. **Statement.** The theorem in ordinary mathematical language, after unfolding every
   project-defined predicate in it far enough that a number theorist would recognise
   it. Quote the Lean statement. For each project definition unfolded give `file:line`.
2. **Argument.** How the proof goes, as mathematics: what is applied to what, and why
   that yields the conclusion. Not a tactic paraphrase.
3. **Children.** A table of every project lemma the proof uses that is not routine
   glue: name, `file:line`, its statement in mathematical language, its role, and a
   weight: `core` (the argument fails without real content here), `standard` (a known
   theorem of the literature, name it), `glue`.
4. **Oddities.** Anything a mathematician would query: a hypothesis that looks
   unsatisfiable or trivially satisfiable, a definition weaker or stronger than its
   name, a `Prop` supplied as `True`/`trivial`, a quantifier over an empty type, a
   constant that looks arbitrary, a statement that is false as literally read, a step
   you could not follow. Say "none seen" only if you looked.
5. **Coverage.** Files and line ranges actually read; what you did not open.

Rules: every `file:line` you cite you read. Distinguish "the Lean says" from "I
infer". If a definition is too deep to unfold in budget, stop and list it under
Children as `definition to unfold`. Do not judge whether the mathematics is plausible
as a proof of RH; report what is there. Do not edit anything outside your output file.

## Reviewer

Input: one `NODE-<id>.md`, and read access to the source. You did not write it. Task:
decide whether, taking each child's *stated* statement as a black box, you could
write the node's proof yourself. Check by reading the Lean statement of the node and of
at least three children (all `core` ones) that the explainer's mathematical renderings
are faithful. Output `REVIEW-<id>.md`:

- **Verdict**: `SATISFIED` / `NEEDS-DETAIL` / `ESCALATE`.
- **Mismatches** between explanation and Lean, with `file:line`.
- **Gaps**: steps where the stated children do not suffice.
- **Expand next**: which children must be opened for the argument to be understood,
  ranked, with one line each on what question the child has to answer.
- **Escalations**: anything that does not make sense mathematically, stated so a
  human expert can check it in ten minutes.
