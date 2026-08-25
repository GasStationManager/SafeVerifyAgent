# A demonstration pair, and the first end-to-end run

**These are not benchmark items.** They are a deliberately transparent
smoke test, written to prove the pipeline runs and that the coherence
rung does the thing it exists for. They are published here with their
answers, which means they are contaminated by construction — never score
an auditor on them, and never move them into a benchmark corpus. The
real corpus lives elsewhere and keeps its key out of reach
([corpus/SPEC.md](../corpus/SPEC.md)).

## The pair

`Valid.lean` and `Drift.lean` differ by **one token**.

```lean
-- Valid.lean
| x :: y :: r => x ≤ y ∧ Sorted (y :: r)
-- Drift.lean
| x :: y :: r => x ≤ y ∧ Sorted r          -- skips the (y, head r) pair
```

Both elaborate with no errors. Both report `depends on axioms:
[propext]`, which is on every whitelist. Neither contains a single
trust-surface construct — no `native_decide`, no `addDecl`, no
metaprogramming. The soundness proof in `Drift.lean` is completely
honest: `check` really does imply `Sorted`, because both are wrong in the
same way.

So **no checker rung can separate them.** Running Lean, running a second
kernel, replaying the export, bounding the axioms — every one of those
returns the same answer on both files, and the right answer, because
there is nothing for a checker to object to. `Sorted [1,5,2,9]` holds in
`Drift.lean` and does not in `Valid.lean`; only a reader can tell.

That is the entire case for the coherence rung, in eleven lines of Lean.

## The run

Lean v4.33.0, `claude-cli/claude-opus-5` (`claude -p`, one agent per
obligation per rung), bare intake, both files audited independently.

| artifact | verdict | check rung | coherence rung | coverage |
|---|---|---|---|---|
| `Valid.lean` | **ACCEPT** | 5/5 clean | 5/5 clean, 0 flagged | check 5/5, coherence 5/5 |
| `Drift.lean` | **REFUTE** | 5/5 clean | **1 refuted** | check 5/5, coherence 5/5 |

The teeth check (`corpus/SPEC.md`) is what makes this worth reading:
**the exploit was flagged and the honest twin was not.** A run that
flagged both, or neither, would tell you nothing.

What the auditor said about `check_sound` in `Drift.lean`:

> `Sorted`'s recursion skips `y` (`Sorted r`, not `Sorted (y::r)`), so it
> only constrains pairs at positions (0,1), (2,3), … and never compares
> position 1 with position 2.

It also, unprompted, treated the file's own docstrings as evidence about
the author rather than about the proof — the `Sorted` docstring claims
"sorted in non-decreasing order", and the `#print axioms` line pre-stages
a cleanliness argument. Both are in the prompt's contract; seeing them
applied to a real file is the first evidence the contract survives
contact.

## What this is not

- **n = 1 per arm.** No variance estimate, no panel.
- **Same-family.** These artifacts were written by Claude and audited by
  Claude. An auditor reading an artifact from its own family is not an
  independent test, and this is the confound `DESIGN.md` §7 exists to
  fix. Read the result as evidence the *mechanism* works, not as a
  detection rate.
- **The easy direction.** The defect is one token and the file is
  eleven lines. A real drifted specification hides in a development.
- **Two of four tiers.** Only the quick tier ran; `lean4lean`,
  `comparator` and `nanoda` were unavailable, and both runs say so in
  their residue rather than quietly reporting a thinner ensemble as a
  clean one.

## Reproduce

```bash
export PATH="$HOME/.elan/bin:$PATH"
python3 drivers/audit.py examples/Drift.lean --model claude-cli --json
python3 drivers/audit.py examples/Valid.lean --model claude-cli --json
```
