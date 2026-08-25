# SafeVerifyAgent — design

An agent that is handed a Lean 4 proof somebody claims is finished and
decides whether to believe it.

Not a prover. The stance is the one a referee takes rather than an
author: **the verifier never proves, it refutes.** A claimed proof is a
conjunction — it is sound only if every step is sound — so it is unsound
if *some* step is unsound, and the job is to find one bad step or run out
of ways to look.

---

## 1. Why an agent, when a checker already exists

If the question were "does this file compile", there would be nothing to
build. Lean answers that, and [SafeVerify][sv] and [comparator][cmp]
answer the harder mechanical versions of it — sandboxing, axiom budgets,
kernel replay, and whether the solution proves the *statement that was
asked*.

The gap is narrow and it is the whole reason this repo exists:

> Every mechanical checker runs the artifact through an elaborator, so
> every mechanical checker shares the elaborator's blind spots. A proof
> that exploits a checker bug is *accepted* by the kernel and tells you
> nothing — being accepted is what makes it an exploit.

So the one signal that cannot be corrupted by the bug being exploited is
a reader who tries to reconstruct why a step is true and cannot. That
reader is an LLM, and everything below is the machinery for pointing one
at a proof without letting it fool itself.

The finding the agent is hunting is therefore not "a checker said no". It
is **two kinds of evidence disagreeing about the same claim**: the
ensemble says true and nobody can say why.

[sv]: https://github.com/GasStationManager/SafeVerify
[cmp]: https://github.com/leanprover/comparator

### 1.1 Two intake shapes, and they are not worth the same

| shape | input | what an ACCEPT can mean |
|---|---|---|
| **paired** | a challenge (statement authored by someone else) + a claimed solution | *this proves the thing that was asked.* comparator can compare the declarations the statement mentions across both environments, so specification drift is a mechanical finding, caught in seconds |
| **bare** | a claimed proof, alone | *something was proved, with these axioms, and the statement was taken on the author's word.* With no independently authored statement there is nothing for the specification to have drifted **from** |

Most Lean proofs in the world arrive bare, so the agent accepts both. The
consequence is enforced rather than advised: **on a bare claim, no tier
may certify the claim as a whole.** A lemma may be certified — the kernel
really did accept that lemma — but certifying "this proves the intended
theorem" asserts something the input does not contain. That is how an
audit launders a gap into a guarantee, and the aggregator refuses it.

The shape is recorded in every report, because the same word means
different things in the two cases.

---

## 2. Architecture: flat decomposition

```
    claimed proof (bare)  ──┐
    challenge + solution ───┴──►  ┌──────────────┐
                                  │  0. INTAKE   │  elaborate; manifest check;
                                  │              │  axiom scan; record shape
                                  └──────┬───────┘
                                         │  malformed ──► REJECT (not a refutation)
                                         ▼
                                  ┌──────────────┐
                                  │  1. PLANNER  │  one obligation per lemma
                                  │    (agent)   │  + dependency order
                                  └──────┬───────┘
                    ┌────────────────────┼────────────────────┐
                    ▼                    ▼                    ▼
             ┌────────────┐       ┌────────────┐       ┌────────────┐
             │ 2. WORKER  │       │ 2. WORKER  │  ...  │ 2. WORKER  │
             │  lemma h1  │       │  lemma h2  │       │  claim     │
             │            │       │            │       │            │
             │ check rung │       │ check rung │       │ check rung │
             │     ↓      │       │     ↓      │       │     ↓      │
             │ coherence  │       │ coherence  │       │ coherence  │
             └──────┬─────┘       └──────┬─────┘       └──────┬─────┘
                    └────────────────────┼────────────────────┘
                                         ▼
                                  ┌──────────────┐
                                  │ 3. AGGREGATE │  conjunction + residue
                                  └──────┬───────┘
                                         ▼
                        ACCEPT · REFUTE · REJECT · ESCALATE
```

### Stage 0 — intake

Deterministic, no model. Elaborate the artifact, read the axioms it
prints for itself, and check the **manifest**: does the file contain
`sorry`, or admitted holes it did not declare? A claimed proof with an
undeclared hole is *malformed*, and the verdict for that is `REJECT` —
which is not a refutation. "You did not submit a proof" and "you
submitted a proof and it is wrong" are different findings and must not
share a bucket.

Intake also records the intake shape, the toolchain, and what checkers
this environment could actually run. A verdict whose ensemble is unstated
cannot be read later.

### Stage 1 — the planner

One agent reads the artifact and emits the obligation list: each
`have`/`lemma`/`theorem` that carries weight, its statement, the context
it depends on, and whether anything downstream uses it.

Two rules:

- **Parsed, not invented.** The decomposition comes from the artifact's
  own structure. Nobody gets to choose it, because the claimed proof
  already committed to one by being written down. The planner's job is to
  read that structure faithfully — including the whole-file claim, which
  is always an obligation, because the defect is often in a *definition*
  rather than in any step. Mechanical extraction through Lean's real
  frontend (`safeverifyagent/lean/ExtractLemmas.lean`) does the reading;
  the agent resolves dependencies and drops dead steps. A step nothing
  depends on cannot make the theorem unsound — but its presence is an
  anomaly and gets counted.
- **Never trust prose.** The artifact's comments were written by whoever
  submitted it. They are evidence about the author, not about the proof,
  and they never influence which obligations exist or what they are worth
  (see §4.1).

### Stage 2 — the workers, in parallel

One subagent per obligation, each running a two-rung ladder on **its
lemma alone**:

1. **check** — the mechanical ensemble (§3), run on this lemma extracted
   as a standalone obligation. Per-lemma rather than per-file, because a
   disagreement is then *localised the moment it appears*: you know which
   lemma it is about, since that is all you ran. The minimised
   reproduction a checker-bug report needs falls out of the audit instead
   of being a separate job afterwards.
2. **coherence** — reconstruct why the lemma is true, as mathematics. Not
   a Lean check; the kernel already had its turn.

The ladder is ordered cheap→expensive and **gated within a lemma**: if
the mechanical rung already refutes it, the coherence rung never opens.
An LLM audit of a lemma the ensemble has already killed is exactly the
spend worth avoiding. The gate is *within* a lemma and never across
lemmas — every obligation gets its own ladder, which is what makes the
fan-out embarrassingly parallel.

Workers are isolated: a worker sees its obligation and the artifact, not
the other workers' findings. They cannot talk each other into a verdict.

### Stage 3 — the aggregator

The conjunction, plus the part that is easy to skip and shouldn't be:
the **residue**. An ACCEPT is not "this proof is correct". It is "no
attack in this configuration landed", and the residue is the list of what
that leaves uncovered — every obligation that closed on non-formal
evidence, every tier that was unavailable, and, on a bare claim, the
statement itself. Reported as structure, not prose, so it can be read by
whatever consumes the verdict.

---

## 3. The checker ensemble

Ported from the same implementation the tree-structured predecessor uses,
because this part is orthogonal to how the work is decomposed.

| tier | member | what it establishes | independent of Lean? |
|---|---|---|---|
| quick | `lean` elaboration + axiom scan | it elaborates; its axioms are in the whitelist | — |
| medium | [Lean4Lean][l4l] | a second kernel, in Lean, re-checks the declarations | **no** — a port of the C++ kernel, by its own README |
| high | [comparator][cmp] | proves the same statement as an independently authored challenge, within an axiom budget, accepted by the kernel | — |
| high | [nanoda][nan], via comparator's `external_kernels` | an independent kernel re-checks the export | **yes** — from scratch, in Rust |

[l4l]: https://github.com/digama0/lean4lean
[nan]: https://github.com/ammkrn/nanoda_lib

Three rules, and each cost somebody something:

**`leanchecker` is deliberately not a tier.** It ships with the toolchain
and replays an olean, but it is Lean's own kernel running a second time —
it shares every blind spot of the thing it is checking. Counting it as a
second opinion is the elaborator-common-mode failure this whole design is
trying to avoid.

**Members are not equally independent, so a verdict count is not a
diversity measure.** Weight them. Lean4Lean *agreeing* with Lean is weak
evidence; Lean4Lean *disagreeing* is strong. The asymmetry is real and
any likelihood-ratio computed over these verdicts has to carry it.

**Parse the tool's output, never its exit code.** comparator exits
non-zero when it merely fails to *build*; `lean4lean` exits **zero**
while printing "found a problem". Each of those bugs once inverted a
verdict in the predecessor — two adapters, two opposite errors, one
lesson.

And one type rule that follows: `error` and `timeout` are **not folded
into accept or reject**. A member that could not run has not voted.
Treating infrastructure failure as either is how an ensemble manufactures
agreement it did not earn — and a resource blow-out is its own signal
worth keeping, since honest proofs of a given size rarely cost that much.

---

## 4. The rules a search inside a verifier needs

### 4.1 Attention is computed, never read

Whoever wrote the artifact would like to choose where the audit budget
goes. If prose in the file could raise or lower an obligation's priority,
the author would own the auditor's search policy: make the bad lemma look
expensive and watch the budget drain into the clean ones.

So any ordering or weighting comes only from **measured facts over
comment-stripped source** — term size, tactic class, declared holes,
trust-surface hits (`native_decide`, `addDecl`, raw `Expr` manipulation,
`macro`/`elab`). Never from anything the author wrote in words.

The asymmetry is deliberate: **a claim may make itself cheaper to audit,
never more expensive.** Padding a file with scary-looking constructs must
not be able to buy the expensive rung on every claim.

### 4.2 The evidence ceiling

Verdicts carry an evidence level, and the top one is not available to the
cheap tiers:

| evidence | who may file it | why |
|---|---|---|
| `formal` accept | the high tier only (comparator + an external kernel, or a human) | permanent — it must not be reachable from anything that might later turn out to be a checker bug |
| `stated` accept | any clean mechanical rung | revocable |
| `informal` | any coherence judgment, in either direction | a reading, not a certificate |
| `formal` refutation | a re-executed counterexample | a fact about the statement, not a report from a checker that might be wrong |

The premise of the entire exercise is that the checker may be wrong. If
unanimity bought permanence, a checker bug disclosed next month could not
reopen the accept it produced. The gap between "what was established" and
"what was established *formally*" is then exactly this claim's dependence
on unaudited checker trust — which is a number worth having, and it goes
in the residue.

### 4.3 Disagreement is not a refutation

When the informative members split, the claim is not refuted — the lemma
may be perfectly sound and one checker merely wrong. It is the strongest
escalation signal in the pipeline, and it is also a **checker-bug
candidate**: the minimised artifact goes in the report whether or not the
proof turns out to be bad. Auditing live traffic is worth doing partly
because it audits the checkers.

### 4.4 The auditor does not repair the proof

Refuting is the job. Suggesting a fix is the author's work, and for an
agent that will be scored on what it found, it is a conflict of interest.

### 4.5 "I cannot reconstruct this" is not "this is wrong"

The single most expensive mistake available to a coherence auditor. The
first is a fact about the auditor and belongs in the report as *could not
reconstruct, not refuted*; the second is a fact about the proof and
refutes it.

An auditor that reports the first as the second flags every lemma it
finds hard, and is worth exactly nothing. Worse, it is **expensive to
detect**: a flag-everything auditor and a real one look identical on any
single claim.

### 4.6 Therefore: teeth

Which is why a run's verdicts only count if the run had controls. The
harness mixes obligations of known status into the queue and checks that
the auditor separated them. **A run that flags everything and a run that
flags nothing both fail**, and neither should be reported as a detection
rate.

This is not a nice-to-have that got promoted; it is the only thing
standing between this design and a very confident random number
generator.

---

## 5. Verdicts

| verdict | meaning |
|---|---|
| `REFUTE` | at least one obligation was refuted — with which one, and on what evidence |
| `REJECT` | malformed input: undeclared holes, manifest violation, does not elaborate. **Never a refutation** |
| `ACCEPT` | every obligation survived every rung that ran. Always carries the residue |
| `ESCALATE` | the ensemble split, or a cost anomaly, or the coherence rung could not reach a reading. Establishes nothing and asks for a bigger hammer |

`ACCEPT` is the one worth stating carefully, since it is the one people
will quote: it means *no attack in this configuration landed*, over this
ensemble, at this toolchain version, under this intake shape. It does not
mean the proof is correct, and the report is written so that a reader
cannot mistake one for the other.

---

## 6. Flat decomposition: what it costs, and why it is still the right default

The predecessor to this design decomposes into an AND/OR tree and uses
proof-number search to choose where to spend next. This repo deliberately
does not. The comparison, honestly:

**What flat gives up.**

- **Adaptive allocation.** The tree's central claim is that escalation
  stops being a threshold on a whole claim and becomes a *resource
  allocation over its parts* — "escalate this proof to comparator" is
  unaffordable, "spend comparator on this one lemma" is not. Flat
  fan-out spends uniformly, so that lever is gone. On a small file the
  lever was not worth much; on a 400-lemma development it is the whole
  ball game.
- **Cross-lemma learning.** A tree can let a clean attack on one lemma
  lower the priority of related ones. Flat workers are independent by
  construction, so nothing propagates. (Measured on the predecessor, that
  propagation bought nothing on a uniform ladder anyway — but it is a
  real capability that a flat design cannot have at all.)
- **Minimisation by descent.** Descending to the smallest node where a
  disagreement survives *is* minimisation. Flat gets per-lemma
  granularity for free and stops there; below the lemma it does not go.
- **Early exit.** A conjunction is settled the moment one lemma falls;
  flat has already paid for the rest.

**What flat buys.**

- **No substrate.** No event log, no leases, no tree state to be correct
  about. The failure modes above are all failure modes of *machinery*.
- **Parallelism.** Every obligation is independent, so the wall-clock is
  one lemma deep regardless of file size — where the tree's descent is
  sequential by design.
- **Coverage by construction.** This is the one that surprised me. A
  short-circuiting search stops at the first landing attack, so which of
  the remaining obligations got audited is decided by *scheduling* — and
  a per-rung detection rate computed that way is a rate over whatever ran
  first. The predecessor needed a dedicated measurement mode to fix that.
  Flat fan-out has the property for free: every obligation is audited
  because every obligation was dispatched. **The design that is worse at
  producing a verdict cheaply is better at producing a number you can
  trust.**

Since this repo exists to find out whether an LLM can tell sound
mathematics from one bad step, the second property is worth more than the
first. Allocation is an optimisation over a thing that works; coverage is
what decides whether you can tell that it works.

Early exit is therefore specified as **opt-in**, off by default, with the
report recording which mode ran — because the two modes produce different
denominators, and a report that hides that is lying with a true number.
`ClaimVerdict.stop_on_first_refutation` carries the flag; the drivers do
not implement the early-exit path yet (§10).

---

## 7. Model dispatch, and the confound this repo exists to fix

The reference worker calls Claude through the official Anthropic SDK
(`claude-opus-5` by default). But the model is behind a small `Model`
interface, and that is not incidental architecture-astronautics — it is
the fix for the sharpest known weakness in the predecessor's numbers:

> Four of the five items in the internal corpus were written by Claude
> and audited by Claude. An auditor reading an artifact from its own
> family is not an independent test.

Same-family authorship is a confound that no amount of *n* removes. The
only fix is staffing: items authored by one family, audited by another.
So the worker layer takes the model family as a parameter, and a run
records which family audited which artifact. A cross-family run is a
first-class configuration, not a fork.

The same applies to panels — several auditors on one obligation, ideally
from different families, with agreement reported rather than collapsed.

---

## 8. Harnesses

The stages are agents; the code around them is deterministic. Two ways to
run them:

- **Claude Code subagents** (`drivers/claude_code/`) — the planner and
  workers are subagent definitions; the fan-out is the harness's. Nothing
  to deploy; this is the path for auditing something today.
- **API driver** (`drivers/api_driver.py`) — a plain Python driver on the
  Messages API. Reproducible, scriptable, and what a benchmark run uses.

**Prompts live in `safeverifyagent/prompts/` as data, and both drivers
render the same files.** This is load-bearing rather than tidy: the
moment a driver paraphrases a prompt, the two harnesses are running
different agents and every cross-harness comparison is measuring the
paraphrase. A test asserts that both drivers resolve identical text.

---

## 9. The corpus lives somewhere else

Measuring this agent needs planted items — sound mathematics with one
exploit-bearing step, plus valid controls — and §4.6 makes controls
mandatory rather than optional.

That corpus is **not in this repo**, and may become a public benchmark in
its own right. What lives here instead is the *contract*: the item
schema, the answer-key format, the loader, and the teeth check
(`corpus/SPEC.md`). Keeping the harness and the benchmark separate has a
second benefit beyond release sequencing — a benchmark in the same repo
as the agent it scores is a benchmark the agent's authors are always one
commit from contaminating.

A corpus needs one property that is easy to miss: **its items must
actually compile, and their axioms must match the key.** An "exploit"
that does not elaborate is not an exploit, it is a broken file, and a
corpus without that gate measures a detector's ability to notice syntax
errors. It also needs a toolchain pin per item, because a kernel bug that
gets fixed makes its item uncatchable-by-checker and therefore uninformative
about anything except the fix.

---

## 10. Status

| component | state |
|---|---|
| checker ensemble + adapters | **ported, real.** The quick tier is verified against Lean v4.33.0; the medium and high tiers need their binaries and degrade to "unavailable" rather than to a verdict |
| output parsing, verdict types, aggregation, residue | **implemented and unit-tested** (fixtures, no toolchain needed) |
| lemma extraction through Lean's frontend | **implemented and tested** against Lean v4.33.0 (`tests/test_lean.py`, skipped without a toolchain) |
| prompts (planner, check, coherence, aggregator) | **written** |
| Claude Code driver | skeleton |
| API driver | skeleton |
| corpus loader + teeth check | contract specified (`corpus/SPEC.md`), loader stubbed |
| end-to-end run on a real claim | **not yet done** |

Nothing in this table is a promise about detection rates. No number in
this repo has been measured against a public corpus, and the internal
one (n=5, same-family) is an upper bound on a mechanism, not a
measurement of a detector.

---

## 11. Open questions

1. **Does the flat planner match the frontend extractor?** The planner is
   an agent and can miss an obligation the parser found. Disagreement
   between the two is a cheap, mechanical alarm and should probably be a
   hard gate rather than a warning.
2. **What is a lemma, on a real development?** `have`-granularity is
   right for a self-contained file and probably wrong for a multi-module
   project where the interesting defect is in an import.
3. **How correlated are the rungs?** A clean mechanical run should lower
   the prior that the coherence rung finds something — by how much is the
   number this entire architecture is gated on, and it needs a labelled
   corpus to answer.
4. **Can a panel beat a single auditor per obligation?** And is
   cross-family disagreement more informative than same-family
   disagreement, as §7 assumes?
5. **Does per-lemma checking find defects that per-file checking
   misses?** The predecessor has one case where aim decided the verdict —
   a checker pointed at the exported result said "checked 2 declarations"
   and was right, while the defect was an import away. That is an
   argument for per-lemma, not yet a measurement.
