# Audits

Reports from running this agent at real, published artifacts.

They are kept in the repo for one reason: **a verdict whose method is not
reproducible is an opinion.** Each report states the commit it audited, which
rungs actually ran, what it did not cover, and how to re-run the mechanical
half. Disagreeing with one should be a matter of re-running it, not of trusting
the auditor.

| date | artifact | verdict | escalations |
|---|---|---|---|
| 2026-09-15 | [openai/NavierStokesAndEuler](2026-09-15-openai-NavierStokesAndEuler.md) | no defect found | 3, for expert review |

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

```bash
python3 audits/scan_repo.py /path/to/lean-project
```

Manifest scan (`sorry`, `admit`, `axiom` declarations) and trust-surface scan
(`native_decide`, `addDecl`, raw `Expr` work, `macro`/`elab`, hash-for-equality),
both over comment-stripped source — because the comments were written by
whoever submitted the artifact, and are evidence about the author rather than
about the proof.

The coherence rung is not reproducible by a script: it is agents reading. Each
report quotes what the auditors actually said, so the reasoning can be judged
even where the run cannot be repeated byte for byte.
