# Corpus contract

The corpus is **not in this repo**, and may become a public benchmark in
its own right. What lives here is the contract an item must satisfy, so
that a corpus maintained elsewhere can be dropped in.

Two reasons for the split. Release sequencing is the boring one. The
other is that a benchmark living in the same repo as the agent it scores
is a benchmark the agent's authors are always one commit away from
contaminating.

## Layout

```
<corpus>/
  ANSWERS.json              the key — never reachable from a staged workspace
  items/
    <item-id>/
      item.json             metadata (below)
      claim.lean            bare intake: the claimed proof
      Challenge.lean        paired intake: the independently authored statement
      Solution.lean         paired intake: the claimed proof of it
      notes.md              what the defect is; NOT shipped to an auditor
```

### `item.json`

```json
{
  "id": "spec-drift-sorted",
  "artifact": "claim.lean",
  "intake": "bare",
  "summary": "a sortedness checker, proved sound against its own Sorted",
  "toolchain": "leanprover/lean4:v4.33.0",
  "axioms": ["propext"],
  "elaborates": true
}
```

### `ANSWERS.json`

```json
{"items": {"spec-drift-sorted": {
    "label": "exploit",
    "channel": "coherence",
    "defect": "Sorted compares alternating pairs only"}}}
```

`label` is `valid` | `exploit` | `wild`. `channel` is the cheapest rung
that *can* catch it — `check` | `coherence` | `hunt` — and it is the
column that makes a corpus worth having: an item every checker catches
measures your plumbing, not your auditor.

## Four rules an item must satisfy

**1. It must compile, and its axioms must match the key.** An "exploit"
that does not elaborate is not an exploit, it is a broken file, and a
corpus without this gate measures a detector's ability to notice syntax
errors. The loader refuses an index whose items do not verify.

**2. Every item pins a toolchain.** A kernel bug that gets fixed makes
its item uncatchable-by-checker, and the item then scores as "caught by
the cheap rung" — true, and telling you nothing about whether an auditor
can read. A corpus of live exploits structurally lags the newest Lean:
anything catchable today is either not yet public or not yet fixed.

**3. The corpus must keep coherence-only items.** The class this whole
design exists for is: *zero trust surface, clean axioms, honest proof,
wrong definition.* No checker rung can see it, because there is nothing
for a checker to object to. A corpus that loses that class silently
becomes a test of the ensemble.

**4. Blinding is the harness's job, not the item's.** Ids like
`exploit-spec-drift` give the answer away, and so do `notes.md` and
`ANSWERS.json` sitting next to the artifact. A staged workspace contains
the artifact and nothing else, under an opaque id.

## Teeth

`DESIGN.md` §4.6 makes controls mandatory: a run's verdicts count only
if known-status items were mixed into the queue and the auditor
separated them.

```
teeth(run) = flagged(exploits) > 0  AND  flagged(valids) == 0
```

**A run that flags everything and a run that flags nothing both fail.**
This is the only thing standing between the design and a confident random
number generator, and it is why a corpus without valid controls is not a
corpus — it is a collection of positives that any flag-everything auditor
scores 100% on.

## Reporting

A result is reported per rung, and always with the denominator that
produced it: whether early exit was on, which tiers were available,
which model family audited, and which family authored. Same-family
authorship is a confound no amount of *n* removes (`DESIGN.md` §7), so a
run that does not record both families has not measured a detector.
