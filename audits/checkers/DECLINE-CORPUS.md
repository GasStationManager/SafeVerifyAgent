# What the external checkers decline, reject and accept: a measured corpus

Run 2026-10-04. Sixteen one-theorem fixtures (`declines/Fix/*.lean`, Lean core only, no
Mathlib), compiled with Lean `v4.32.0`, each exported with `lean4export` (the build pinned by
`openai/ten-proofs`, format 3.1.0) as the single target `t`, and replayed with the four
checkers bundled in the `leanprover/lean4:v4.35.0-rc2` toolchain: `leanchecker
--from-export`, `con-leche --verified`, `con-ron` (default, verified), `nanoda_bin` (Palomar
config: permitted axioms `propext`/`Quot.sound`/`Classical.choice`,
`unpermitted_axiom_hard_error: false`). `declines/run.sh` reproduces the table; the checker
messages for the four non-accepted rows are under `declines/logs/`.

| fixture | what it exercises | `#print axioms t` | leanchecker | con-leche | con-ron | nanoda |
|---|---|---|---|---|---|---|
| Control | `3 + 4 = 7 := rfl` | none | accepts | accepted 23 | accepted 23 | rc 0 |
| NativeDecide | `by native_decide` | `t._native.native_decide.ax_1_1` | **accepts** | **declined**: "not implemented yet: non-standard axiom" | **declined**: non-standard axiom | **panic** (rc 101, in `TypeChecker::infer`) |
| Axiom | a user `axiom foo` used by `t` | `foo` | **accepts** | declined: non-standard axiom | declined: non-standard axiom | panic (rc 101) |
| Sorry | `:= sorry` | `sorryAx` | **accepts** | declined: "1 skipped for tolerated axioms … via sorryAx" | same | panic (rc 101) |
| OfReduceBool | `Lean.ofReduceBool b true (by rfl)` on a compiled `decide` | `Lean.ofReduceBool`, `Lean.trustCompiler` | **rejects**: application type mismatch (`Eq.refl (reduceBool b)` is not `reduceBool b = true` without native evaluation) | rejected | rejected | panic (rc 101) |
| BvDecide | `x &&& x = x` on `BitVec 8` by `bv_decide` | `propext`, `Quot.sound` (closed by the normaliser, SAT oracle not reached) | accepts | accepted 1639 | accepted 1639 | rc 0 |
| BigLit | `2 ^ 100000 % 3 = 1` by `decide +kernel` | none | accepts | accepted 177 | accepted 177 | rc 0 |
| Str | `"abc".length = 3` by `decide` (String literal) | the three standard | accepts | accepted 3222 | accepted 3222 | rc 0 |
| Nested | nested inductive `Tree` with `List Tree` | none | accepts | accepted 6 | accepted 6 | rc 0 |
| Mutual | mutual `Ev`/`Od` | none | accepts | accepted 22 | accepted 22 | rc 0 |
| Quot | `Quot.sound` | `Quot.sound` | accepts | accepted 10 | accepted 10 | rc 0 |
| ProofIrrel | `(p : True) : p = trivial := rfl` | none | accepts | accepted 5 | accepted 5 | rc 0 |
| StructEta | `p = ⟨p.a, p.b⟩ := rfl` | none | accepts | accepted 7 | accepted 7 | rc 0 |
| ImplBy | `@[implemented_by]` on a def used by `t` | none | accepts | accepted 24 | accepted 24 | rc 0 |
| Partial | an unrelated `partial def` in scope | none | accepts | accepted 3 | accepted 3 | rc 0 |
| Unsafe | an unrelated `unsafe def` in scope | none | accepts (the `unsafe` def is not in the export at all) | accepted 3 | accepted 3 | rc 0 |

## What this says

1. **Only con-leche and con-ron turn a non-standard axiom into a verdict.** `leanchecker
   --from-export` accepts an export whose theorem rests on `sorryAx`, a user axiom or the
   per-proof axiom `native_decide` adds in v4.32: it checks well-typedness and leaves the
   axiom policy to the caller (the comparator does that job in Palomar's pipeline). nanoda
   with `unpermitted_axiom_hard_error: false` does not report a verdict either; it panics in
   the type checker (exit 101), which an ensemble must classify as "no verdict", not as a
   reject. So "accepted by leanchecker" must always be read together with `#print axioms`
   or an axiom scan of the export.
2. **The `native_decide` family is a decline, not a reject, in both verified checkers**, and
   con-leche's wording ("not implemented yet") is the same category as con-ron's "declined".
   The deprecated `Lean.ofReduceBool` route is different: Lean's own kernel accepts it at
   build time (native reduction of a compiled `decide`), and every replay rejects it, since
   no replay evaluates native code. That is a reject that is the kernel's own trust
   extension, not an error in the artifact.
3. **Everything else in the corpus is accepted by all four**: nested and mutual inductives,
   quotients, proof irrelevance, structure eta, String literals, a 100,000-bit `Nat` literal
   under `decide +kernel`, and the compile-only attributes (`implemented_by`, `partial`,
   `unsafe`), which never reach the export. In particular an `implemented_by` that lies is
   invisible to every checker, because the kernel never sees compiled code; only
   `native_decide`/`ofReduceBool` route compiled code into a proof, and those are caught.
4. **Not exercised here**: a `bv_decide` that actually calls the SAT oracle (the fixture was
   closed by the normaliser), a toolchain without con-leche pins for the well-founded `Nat`
   operations, memory limits (the Four Color ring-14 certificate measured con-leche at 3 GB
   and 720 s where con-ron took 130 s), and the module system.

## Public formalizations with declines

In the public AI-written corpus we surveyed (Lean Pool, 213 projects; Palomar's 200 most
recent entries), a decline would come from `native_decide`, `bv_decide`'s oracle, a user
axiom or a used `sorry`. A comment-aware grep over all of Lean Pool finds 41 textual
mentions of `native_decide`/`bv_decide`/`axiom`, every one of them a docstring saying the
project does NOT use it (eight projects, seven AI-written: Sundogcert, Egrs75,
CriticalPortraits, TwoColoringOneRound, Erdos403, Schoenflies, DomainTheory, and the human
Erdos137). The AI-written projects advertise "axiom-clean, no native_decide" in their
module docstrings, which is the ecosystem adapting to reviewers' checks. Palomar's policy
forbids the non-standard axioms outright, so its 199 "high" entries cannot decline for that
reason; its one "qualified" entry is qualified for importing Tau Ceti in the statement, not
for a checker verdict. The realistic decline sources on public artifacts are therefore not
axioms but (a) a Lean version the checker has no `Nat` pins for, and (b) resources.
