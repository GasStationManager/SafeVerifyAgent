# Statement-check brief (one challenge per agent)

Repository: a sparse checkout of openai/math at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
directory `/home/user/openai-math/repo/lean` (only `lean/` is checked out). READ-ONLY: never
modify any file there. Do not run `lake build` (a build is already running and memory is tight).

Each challenge is a Lean file `ComparatorChallenges/<Name>.lean` whose final theorem ends in
`sorry`; the config `ComparatorChallenges/<Name>.json` names the theorem(s) and the solution
module; the scope note is the `docs/NNN.md` that links the challenge; the paper is a PDF under
`preprints/` in the FULL repo (not checked out). Fetch it with
  curl -sSL -o <dir>/paper.pdf "https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/<path-from-docs-link>"
into a fresh directory under the scratchpad (`<scratch>/oaimath/statements/<Name>/`),
URL-encode spaces if any, and extract text with `python3 -I -c 'import pypdf,sys; ...'` (pypdf works).

Method (SafeVerifyAgent audit discipline — follow it exactly):
1. Write the REFERENCE statement from the paper FIRST (the theorem as the paper states it, every
   hypothesis and quantifier, with its paper location) before reading the Lean theorem body.
   Record the docs scope note's own stated scope/gaps separately.
2. Then read the Lean challenge file top to bottom: every definition the statement depends on,
   not just the final theorem. Pair clause by clause: reference clause ↔ Lean clause, with the
   definitions unfolded as far as needed to see they mean the same thing. Classify each clause
   EXACT / STRONGER (Lean proves more) / WEAKER (Lean proves less) / NOT LOCATED (no Lean
   counterpart) / DIFFERENT.
3. Two denominators: (a) of the paper's main claims, which are formalised at all; (b) of the Lean
   theorem's clauses, which match the paper. The docs note usually states (a) itself — check it.
4. Look for statement-level traps: definitions that could be vacuous or trivially satisfiable
   (e.g. an `IsNP`/`Complete`/`Proper` predicate nothing inhabits, an existential over an empty
   type, a `Prop` that is `True` by construction, a numeric constant that makes the claim
   trivial, `0 < k` guards, Fin/ℕ vs ℤ/ℝ coercions, `=` vs `≤` sense, strict vs non-strict,
   a hypothesis stated in the paper but missing in Lean), and `opaque`, `axiom`,
   `implemented_by`, `native_decide`, `unsafe` anywhere in the challenge file.
5. Verdict: PAIRED (you compared against the paper statement) or BARE (paper unavailable);
   EXACT / STRONGER / WEAKER / MISMATCH, with the deviations listed. "Not located" is a claim
   you make; say what you searched.

Output: write `<scratch>/oaimath/statements/STATEMENT-<Name>.md`
(reference statement; clause table; both denominators; traps checked; verdict). Plain prose,
no model names or AI-vendor names anywhere in the file. Keep it under ~250 lines. Run any
Python with `python3 -I`. Finish within about 40 minutes; if the PDF cannot be fetched, report
BARE and say what you tried.
