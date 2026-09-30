# Audits

Reports from running this agent at real, published artifacts.

Plain-language overviews: [`SUMMARY-openai-NavierStokesAndEuler.md`](SUMMARY-openai-NavierStokesAndEuler.md)
and [`SUMMARY-qinz1yang-differential-geometry.md`](SUMMARY-qinz1yang-differential-geometry.md).

They are kept in the repo for one reason: **a verdict whose method is not
reproducible is an opinion.** Each report states the commit it audited, which
rungs actually ran, what it did not cover, and how to re-run the mechanical
half. Disagreeing with one should be a matter of re-running it, not of trusting
the auditor.

| date | artifact | verdict | escalations |
|---|---|---|---|
| 2026-09-15 | [openai/NavierStokesAndEuler](2026-09-15-openai-NavierStokesAndEuler.md) | no defect found | 3, for expert review |
| 2026-09-16 | [openai/NavierStokesAndEuler — kernel trust](2026-09-16-openai-NavierStokesAndEuler-kernel-trust.md) | no defect found | kernel-exposure surface classified; closing-`rfl` defeq goals unbounded |
| 2026-09-18 | [openai/NavierStokesAndEuler — final](2026-09-18-openai-NavierStokesAndEuler-FINAL.md) | no defect found | E-A4 closed clean by compile; coverage stated in tiers |
| 2026-09-28 | [qinz1yang/differential-geometry — Poincaré](2026-09-28-qinz1yang-differential-geometry.md) | no defect found; con-leche accepts 50 theorems incl. most of the README list; headline `#print axioms` not run (memory-bound closure) | route read to the analytic core; 4 unsupplied predicates, all off route |
| 2026-09-20 | [openai/NavierStokesAndEuler — paper alignment](2026-09-20-openai-NavierStokesAndEuler-paper-alignment.md) | no load-bearing weakening; headline EXACT | 4 open checks, none a defect; docstrings cite a draft numbering |
| 2026-09-30 | [RBarish-UTokyo/FourColorTheorem-Lean4 — metaprogramming](2026-09-30-RBarish-FourColorTheorem-Lean4-metaprogramming.md) | no defect; engine's "nothing here is trusted" holds by reading and by kernel controls; 2 of 633 certificates accepted by leanchecker, con-leche, con-ron, nanoda | statement rung and route walk not done |

## How to read one

Four rules the reports follow, each of which exists because the opposite is a
way to mislead with a true sentence:

1. **An escalation is not an accusation.** It marks a place a human expert
   should look. Several become non-findings once traced — E3 in the
   NavierStokes report did, and the trace is recorded rather than the flag
   quietly dropped.
2. **A clean mechanical rung is a beginning, not a verdict.** No hole and no
   trust surface says nothing about whether the theorem proved is the theorem
   intended. That is the coherence rung's question, and on a bare claim no
   checker can answer it at all.
3. **What did not run is stated as prominently as what did.** An audit that
   hides its own gaps is worth less than one that does not. If Comparator was
   not run, the report says so at the top, not in a footnote.
4. **The auditor's family is recorded.** An auditor reading an artifact from
   its own model family is not an independent test.

## Reproducing the mechanical rung

Every script is stdlib-only, reads source (no Lean toolchain), streams files,
prints progress to stderr, and states both of its error directions in its
docstring. In playbook order (§5):

```bash
R=/path/to/lean-project
SEED=Some.headline_theorem          # repeat --seed for several headlines

# 1. manifest, trust surface, and every metaprogramming site LISTED
#    (run_cmd, macro, elab, syntax, notation, set_option, attribute, #eval,
#    implicit-use attributes on defs) with file:line and three lines of text
python3 audits/scan_repo.py $R --md SCAN.md
python3 audits/scan_kernel_risk.py $R

# 2. the dependency cone from the headline (name-level; see its docstring)
python3 audits/cone.py $R --seed $SEED -o CONE.csv
#    ... and the route a reader walks: in-cone declarations by BFS depth
python3 audits/cone.py route --cone CONE.csv -o ROUTE.md

# 3. no-supplier over the route. Under a "missing results are named, not
#    sorry-ed" convention, add --convention named-hypothesis: it also lists
#    Prop-valued defs and classes, and predicates supplied only CONDITIONALLY
#    (by a theorem that assumes another unsupplied predicate), with the chain
python3 audits/nosupplier.py $R --cone CONE.csv --convention named-hypothesis \
    -o NOSUPPLIER.csv                  # also writes NOSUPPLIER.md

# 4. dead code: which declarations assume an unsupplied predicate (directly,
#    or because every consumer does). Takes NOSUPPLIER.csv's no_supplier and
#    conditional rows, so confirm those by reading first
python3 audits/cone.py $R --seed $SEED --unsupplied NOSUPPLIER.csv -o CONE.csv

# 5. classify citations (a paper-alignment table, a worker's file:line list):
#    route / dead / orphan / above_seed / wrapper / unknown, with consumer counts
python3 audits/cone.py join CONE.csv CITATIONS.csv -o JOINED.csv

# 6. the coverage ledger, in tiers, from the worker reports
python3 audits/ledger.py CONE.csv reports/ -o LEDGER.md
```

`CITATIONS.csv` needs `file` and `line` columns; every other column passes
through. A worker report declares what it read line by line with a line of its
own, `READ-LINE-BY-LINE: path/to/File.lean` (optionally `:START-END`); anything
else it cites only counts as "named" or "cited", never as read. `ledger.py`
lists declarations that do not resolve rather than dropping them.

`scan_repo.py` alone runs the manifest scan (`sorry`, `admit`, `axiom`
declarations) and trust-surface scan (`native_decide`, `addDecl`, raw `Expr`
work, `macro`/`elab`, hash-for-equality), both over comment-stripped source —
because the comments were written by whoever submitted the artifact, and are
evidence about the author rather than about the proof.

A CONE.csv written before 2026-09-28 has only the first six columns; `route`
and `join` refuse it and say to re-run `cone.py`. The instruments are tested
against a synthetic project with a known answer for every tool
(`tests/test_audit_tools.py`).

The coherence rung is not reproducible by a script: it is agents reading. Each
report quotes what the auditors actually said, so the reasoning can be judged
even where the run cannot be repeated byte for byte.

## The statement rung for a bare claim (`statement.py`)

For a BARE claim (no independently authored challenge, so no Comparator),
PLAYBOOK §1.1 makes the statement check the whole first job. `statement.py`
does not answer "is this the theorem that was claimed?" — nothing mechanical
can — it puts what the answer depends on in one file:

```bash
python3 audits/statement.py PROJECT MODULE THEOREM \
    [--mathlib DIR] [--toolchain-src DIR] \
    [--reference REF.md] [--no-lean] -o STATEMENT.md
```

- the theorem's source, each binder (hypothesis or instance argument) on its
  own row, the conclusion, and the `namespace`/`open`/`variable`/`universe`/
  `set_option`s in scope — including the lakefile's project-wide
  `leanOptions`, which no file shows;
- every constant and notation in the signature resolved **by source** (the
  project, `.lake/packages/*` or a Mathlib checkout given with `--mathlib`,
  then the toolchain's `Init`), with docstring, binders, `extends`, fields
  or body — one level down, each with a `root:path:line`;
- forgetful instances out of the assumed classes (`SimplyConnectedSpace ⟹
  PathConnectedSpace ⟹ ConnectedSpace`), by source grep, two steps;
- the Lean rung — `#check`, `#print`, `#print axioms`, and `#print` of each
  resolved constant — only when the module's `.olean` exists; otherwise the
  dossier says it did not run and why. The tool never builds the project.

`--reference REF.md` is a file the auditor writes **before** reading the
Lean: the claim in words, one clause per list item, conclusion under a
`## Conclusion` heading. The tool pairs each clause with the Lean clause it
overlaps most (camel-case splitting, notation expansion, a small synonym
table) and lists what matched nothing on either side. The pairs are
pointers; the unmatched lists are the output. Worked example:
[`dg-intake/`](dg-intake/) — `REFERENCE-poincare.md` and the dossier
`STATEMENT.md` for differential-geometry's `poincare_conjecture`.

## con-leche as a checker tier (`safeverifyagent.checkers.ConLeche`)

[con-leche](https://github.com/leanprover/con-leche) is an external checker
written in Lean with its own term representation, proven in Lean not to
accept a proof of `False` in `--verified` mode. It reads a `lean4export`
NDJSON stream, so it shares nothing with Lean's C++ kernel or with nanoda.

```python
from safeverifyagent.checkers import ConLeche
cl = ConLeche.discover()          # $CON_LECHE (binary or repo), PATH, ~/.local/bin
nd = cl.export(project_dir, "Mod", decls=["Mod.headline"])   # $LEAN4EXPORT
v = cl.check(nd, verified=True, jobs=8)
v.outcome, v.tier, v.mode, v.axioms
```

The verdict comes from the parsed verdict line (which names its mode),
cross-checked against the exit code: 0 accept, 1 reject, 2 `declined` (a
statement about the checker, not a vote), 3 error, and an out-of-memory
panic — also exit 1 — is an error, not a reject. `--trusted` runs are tier
`high-trusted`: outside the proven theorem, and `Finding` refuses to file
them `formal`. `axioms` lists the axiom records the stream declares; export
one theorem's cone (`decls=`) so that list means what `#print axioms` means.
Build `lean4export` at the project's toolchain (the commit whose
`lean-toolchain` matches). Scope of the theorem: `DESIGN.md` §3.
