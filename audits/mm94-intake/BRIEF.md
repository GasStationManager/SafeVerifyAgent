# Reader brief — openai/math result 107, ω ≤ 9/4 (Lean read-through)

You are one of six independent readers of the Lean formalization of "An Upper Bound of 9/4
for the Matrix Multiplication Exponent" (OpenAI, 2 Oct 2026). The result, if sound, would be
the largest advance in algebraic complexity since 1990 (best known: ω < 2.3712). It is
therefore worth reading as an adversary would.

## Where things are (READ-ONLY — never modify the artifact)

- Lean project: `/home/user/openai-math/repo/lean` (Lean 4.34.1, Mathlib). Solution modules
  under `OAI/LinearAlgebra/MatrixMultiplication/`; the 9/4 headline is
  `OAI.MatrixMultiplication.complex_omega_le_nine_quarters` in `Main.lean`, proved by
  `AuxiliarySeparation/Main.lean`. The route's import closure is 129 modules, 20,694 lines,
  listed in `route-closure.txt` (lines TAB module). The challenge statement the authors'
  comparator checks is `ComparatorChallenges/MatrixMultiplication.lean`.
- Paper text: `<scratch>/mm94paper/paper.txt`
  (609 lines; pdftotext of the 12-page PDF). Sections: 2 characters (Def 2.1, Lemma 2.2
  detecting characters, §2.1 dot-product exponents (2.3)–(2.4), Lemma 2.3 interpolation);
  3 separation (Prop 3.1, Cor 3.2); 4 polynomial multiplication (C(a,b) (4.1), (4.2),
  profile (4.4)–(4.5), Lemma 4.1 discrete concavity, Lemma 4.2 shifted tripling);
  5 Lemma 5.1 diagonal growth and proof of Thm 1.1; Appendix A (Lemma A.1, proof of 2.2).
- Mechanical facts already established (do not re-derive): the solution subtree has no
  `sorry`, no `axiom`, no `native_decide`, no `unsafe`, no `run_cmd`/`macro`/`elab`/
  `set_option`; the only metaprogramming sites are 229 `attribute [...]` lines (163 `local
  instance`, 78 `local instance <prio>`, 9 `instance`, 5 `local irreducible`, 1 `local simp`).
  The challenge's `Arithmetic` namespace is textually identical to `Model.lean`. The build
  and `#print axioms` are being done by the coordinator.

## What reading is for (from the audit playbook)

Reading a Lean proof has one purpose: reconstruct the mathematical argument the proof
expresses, and escalate any discrepancy between that argument and the claim, the paper, or
your own mathematics. "It compiles and looks fine" is not a reading. "This lemma proves X by
Y; the paper claims X' by Y'; here is the difference" is.

Because the kernel will certify the LOGIC, your job is the SEMANTICS:
1. Do the definitions mean what their names and docstrings say? (A `Character` that is not
   Strassen's spectral point; a `convolution` tensor that is not polynomial multiplication; a
   `restrict` that is not a linear restriction; a `Tensor.matrixMultiplication` that is not
   T_n; an `AdmissibleExponent` that is weaker than O_ε(n^{τ+ε}).) Read every definition on
   your route in full and state what it is in your own words.
2. Are any hypotheses vacuous or secretly strong? (A structure field that no instance can
   satisfy; a lemma whose hypotheses are only met by trivial objects; a `0 < t` guard that
   hides the `t = 0` case; a theorem quantified over a type that is empty.)
3. Does each theorem's STATEMENT match the paper's statement it claims to formalize —
   quantifier order, which objects may depend on which, exact vs approximate, ℂ vs other?
4. Reconstruct the argument of your part for a reader with a complexity-theory background:
   what is proved, by what construction, and why it should be true. Note which steps are the
   paper's and which the formalization had to add.
5. For a computational step (a numeric inequality, a combinatorial identity), recompute it
   by other means where feasible (a short Python script run with `python3 -I`, written in
   your scratchpad, never in the artifact) and say what you checked.

Rules: every `file:line` you cite was read with `sed -n` or Read, never from a name. "Not
located" is a claim: say what you grepped. Follow consumers (`obtain … :=`, `exact`, `apply`)
not names. Do not trust a docstring over the statement under it. You may use `grep -rn` over
the subtree freely. Files are small (33–600 lines); read your assigned ones WHOLE, in import
order (leaves first). Do not spawn a Lean build; the coordinator owns it.

## Output

Write ONE markdown report to `/home/user/SafeVerifyAgent/audits/mm94-intake/READ-<your letter>.md`:
1. Files read, each with its line count, and files only skimmed or only grepped.
2. Argument reconstruction: a numbered chain of the key Lean theorems (name, file:line,
   one-line statement in words) mapped to paper statements.
3. Definitions checked: a table `Lean name | file:line | what it is | matches paper? | note`.
4. Escalations: anything a human expert should look at, with file:line and WHY. An
   escalation is not an accusation; include things you resolved and how.
5. Verdict for your part in one sentence, and an explicit list of what you did NOT read.
Keep it under ~400 lines. Then reply with a 10-line summary.
