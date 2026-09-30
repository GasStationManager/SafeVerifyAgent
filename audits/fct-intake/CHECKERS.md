# con-leche and con-ron: what each one's proof covers

Read 2026-09-30 from `leanprover/con-ron` (`README.md`, `OVERVIEW.md` §3, §3.1, §7.7, §8)
and con-leche's `ConLeche/MainTheorem.lean` as cited there. Both ship in the
`leanprover/lean4:v4.35.0-rc2` toolchain's `bin/` next to `nanoda_bin`, `leanchecker`,
`leanchecker-paranoid`, `lean4lean` and `leanexport`.

| | con-leche | con-ron |
|---|---|---|
| implementation | Lean 4 | Rust, "a port of con-leche ... very closely" |
| headline theorem | `model_exists`: an accepted stream has a model in every set theory `V`; corollary: no accepted theorem of type `False` | the same two statements, `ConRon.Capstone.model_exists` / `no_False_declaration`, about the AENEAS MODEL of the Rust functions the binary calls |
| proof shape | pure checker proved sound; the caching implementation proved to refine it | Theorem 1: a Lean "twin" (con-ron's data structures, in Lean) refines con-leche's pure checker; Theorem 2: the Aeneas translation of the Rust refines the twin; composed with con-leche's soundness |
| axioms | `propext`, `Classical.choice`, `Quot.sound` | the same three; `#guard_msgs` census |
| bignum | Lean runtime (GMP), OUTSIDE the proof | own `ron::Nat`, proved against its mathematical meaning in the leaf tier (§7.7) |
| not covered | driver (file reading, thread scheduling), Lean compiler and runtime | driver and `main` (call order is trusted, one comment per premise), the worker pool's contract (an argument, not a proof), the in-process modeller (a hypothesis `hmr`), `rustc`/std/allocator, and the Aeneas/Charon translation itself |
| partiality | | `Native` errors (resource limits) are outside the theorems: con-ron may DECLINE where con-leche accepts, "but it never accepts where con-leche rejects" |
| mode covered | `--verified` (default) | `--verified` (default); `--trusted`, `--pins FILE`, `--no-pins` are outside the theorems |

So the answer to "is con-ron also guaranteed consistent?" is: it carries the same
end-to-end consistency theorem as con-leche, but through one more translation layer.
con-leche's guarantee stops at Lean's compiler, runtime and GMP; con-ron's stops at
`rustc`, its standard library, and Aeneas, which the authors themselves call "not a high
assurance verification effort". The point of running both is that a bug would have to exist
in both runtimes at once. Neither proof covers the file parser/driver, and neither checks
the STATEMENT: both are the kernel half of an evidence ceiling, never the comparator half
(`DESIGN.md` §4.2).
