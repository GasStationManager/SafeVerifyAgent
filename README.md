# SafeVerifyAgent

An agent that is handed a Lean 4 proof somebody claims is finished and
decides whether to believe it.

It never proves anything. A claimed proof is a conjunction — sound only
if every obligation is sound — so it is unsound if *some* obligation is
unsound, and the job is to find one or run out of ways to look.

> **Status (October 2026).** Two tracks. The *pipeline* (`drivers/`)
> runs end to end on the demonstration pair in `examples/`: a
> specification that drifts by one token and its honest twin, which no
> checker separates and the coherence rung does. That is n = 1 per arm
> and eleven lines long; no detection rate has been measured against a
> public corpus. The *audit* track has pointed the method at eleven
> real, published artifacts since September 2026 ([`audits/`](audits/)),
> from a 641k-line Navier–Stokes formalization to OpenAI's ω ≤ 9/4; every
> verdict so far is "no defect found", each with its escalations and its
> stated coverage. The method those audits converged on is written down
> in [`audits/PLAYBOOK.md`](audits/PLAYBOOK.md), and the external
> checkers it leans on have a measured decline/reject/accept corpus
> ([`audits/checkers/`](audits/checkers/DECLINE-CORPUS.md)). Component
> state: [DESIGN.md §10](DESIGN.md#10-status).

## Why this exists

Lean already answers "does this file compile", and
[SafeVerify](https://github.com/GasStationManager/SafeVerify) and
[comparator](https://github.com/leanprover/comparator) answer the harder
mechanical versions — sandboxing, axiom budgets, kernel replay, and
whether a solution proves the statement that was actually asked.

The gap is narrow, and it is the whole point:

> Every mechanical checker runs the artifact through an elaborator, so
> every mechanical checker shares the elaborator's blind spots. A proof
> that exploits a checker bug is **accepted** by the kernel and tells you
> nothing — being accepted is what makes it an exploit.

So the one signal that cannot be corrupted by the bug being exploited is
a reader who tries to reconstruct why a step is true and cannot. The
finding this agent hunts is therefore not "a checker said no". It is
**two kinds of evidence disagreeing about the same claim**: the ensemble
says true, and nobody can say why.

## Two intake shapes

| shape | input | what an ACCEPT can mean |
|---|---|---|
| **paired** | an independently authored statement (challenge) + a claimed solution | *this proves the thing that was asked*: comparator compares the declarations the statement mentions across both environments, so specification drift is a mechanical finding |
| **bare** | a claimed proof, alone | *something was proved, with these axioms*; the statement is the author's. With nothing to drift from, "proves the intended theorem" is not a checkable proposition, and on a bare claim no tier may certify the claim as a whole |

Most proofs arrive bare. For those the first job is the **statement
rung**: a reference written in words *before* reading the Lean, then a
clause-by-clause pairing against the headline's binders and conclusion
(`audits/statement.py`). The shape is recorded in every report because
the same verdict means different things in the two cases
([DESIGN.md §1.1](DESIGN.md#11-two-intake-shapes-and-they-are-not-worth-the-same)).

## How it works

```
claimed proof ──► INTAKE ──► PLANNER ──►  one WORKER per obligation  ──► AGGREGATE
                                          (check rung, then coherence)
```

Flat, not a search tree. One agent reads the artifact's own structure
into a list of obligations; one subagent audits each, in parallel; the
results are folded back as a conjunction. The decomposition is **read,
never invented** — the claimed proof already committed to one by being
written down.

Flat costs adaptive allocation and buys something worth more at this
stage: **every obligation is audited because every obligation was
dispatched.** A search that short-circuits on the first refutation makes
its own coverage a fact about scheduling. See
[DESIGN.md §6](DESIGN.md#6-flat-decomposition-what-it-costs-and-why-it-is-still-the-right-default)
for the honest version of that trade.

On an artifact of thousands of theorems the same idea runs at a
different grain: the planner becomes a **brief** that cuts the
headline's dependency cone into parts, each part goes to a reader whose
job is to reconstruct the argument and escalate any discrepancy with the
paper or with its own mathematics, and the instruments below supply the
denominators. That is the playbook, and it is how the audits in
`audits/` were made.

## The ensemble

| tier | member | independent of Lean? |
|---|---|---|
| quick | `lean` elaboration + axiom scan | — |
| medium | [Lean4Lean](https://github.com/digama0/lean4lean) | **no** — a port of the C++ kernel, by its own README |
| high | [comparator](https://github.com/leanprover/comparator) | — (statement comparison + axiom budget + kernel replay) |
| high | [nanoda](https://github.com/ammkrn/nanoda_lib), via comparator's `external_kernels` | **yes** — from scratch, in Rust |
| high | [con-leche](https://github.com/leanprover/con-leche) `--verified`, on a `lean4export` stream | **yes** — own term representation, in Lean, proven in Lean to accept no proof of `False` |
| high-trusted | con-leche `--trusted` | yes, but outside the proven theorem; cannot file a `formal` finding |

`leanchecker` is deliberately not a tier: it is Lean's own kernel running
twice, so counting it as a second opinion is the exact common-mode
failure this design exists to avoid. Members are not equally
independent, so a verdict count is **not** a diversity measure. And every
adapter parses what its tool *printed*, never how it *exited* —
comparator exits non-zero when it merely fails to build, `lean4lean`
exits **zero** while printing "found a problem", and con-leche's
out-of-memory panic shares exit code 1 with a reject. `error`, `timeout`
and `declined` are never folded into accept or reject: a member that
could not run has not voted.

What the four external checkers actually do with a non-standard axiom
was measured rather than assumed ([`audits/checkers/DECLINE-CORPUS.md`](audits/checkers/DECLINE-CORPUS.md),
sixteen fixtures): `leanchecker --from-export` **accepts** an export whose
theorem rests on `sorryAx`, a user axiom, or the per-proof axiom
`native_decide` now adds; nanoda panics on them rather than voting; only
con-leche and [con-ron](https://github.com/leanprover/con-ron) turn an
axiom into a verdict, and they *decline* rather than reject. So
"accepted by leanchecker" is read together with `#print axioms`, always.
con-ron has no adapter in the package yet; the audits run it by script,
beside the other three, from the toolchain bundle that ships all four.

## Install

```bash
git clone https://github.com/GasStationManager/SafeVerifyAgent
cd SafeVerifyAgent
python3 -m unittest discover -s tests     # 136 tests, 15 skipped without a toolchain
```

The core has no dependencies. For the Lean-gated half — frontend
extraction, the quick tier, the statement rung's `#check`/`#print`
dossier — install a toolchain (the tests are pinned to v4.33.0):

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.0
export PATH="$HOME/.elan/bin:$PATH"
```

`lean_available()` probes that Lean actually *runs* rather than that a
file called `lean` exists — elan installs a shim that resolves a
toolchain at call time, so the binary can be present and still fail.

Checkers are discovered by environment variable and every one of them
degrades to "unavailable" — never to a verdict — when its binary is
missing:

```bash
export SVA_LEAN4LEAN=~/lean4lean      # optional, medium tier
export SVA_COMPARATOR=~/comparator    # optional, high tier
export SVA_NANODA=~/nanoda_lib        # optional, the independent kernel
export CON_LECHE=~/con-leche          # optional; binary or repo, also PATH and ~/.local/bin
export LEAN4EXPORT=~/lean4export      # built at the audited project's toolchain
python3 -c "from safeverifyagent import checkers; print(checkers.available())"
```

## Use

A single claimed file, through the driver:

```bash
# Each worker is its own `claude -p` agent. No API key needed, and the
# check rung gets real tools — it actually runs Lean.
python3 drivers/audit.py Claimed.lean --model claude-cli --json

# Any other one-shot CLI, for a cross-family audit (DESIGN.md §7)
python3 drivers/audit.py Claimed.lean --model cli:codex:codex:exec:{prompt}

# The Messages API (needs `pip install anthropic`). Text-only, so the
# check rung is REFUSED rather than faked — see below.
python3 drivers/audit.py Claimed.lean --model api:claude-opus-5

# Or dispatch by hand from an interactive Claude Code session
python3 drivers/claude_code/render_tasks.py Claimed.lean --rung check
```

A whole repository, the way the audits were run (playbook §5 has the
full order; every instrument is stdlib-only and reads source):

```bash
R=/path/to/lean-project; SEED=Some.headline_theorem
python3 audits/scan_repo.py $R --md SCAN.md            # holes, trust surface, every metaprogramming site
python3 audits/scan_kernel_risk.py $R -o out            # what a kernel bug could fake: recursors, numerals, defeq
python3 audits/cone.py $R --seed $SEED -o CONE.csv      # the dependency cone: the honest denominator
python3 audits/cone.py route --cone CONE.csv -o ROUTE.md   # the route a reader walks, by depth
python3 audits/nosupplier.py $R --cone CONE.csv -o NOSUPPLIER.csv  # predicates nobody ever supplies
python3 audits/junkvalue.py $R                           # divisions by an unconstrained denominator
python3 audits/statement.py $R Module theorem --reference REF.md -o STATEMENT.md  # the bare-claim statement rung
python3 audits/ledger.py CONE.csv reports/ -o LEDGER.md  # coverage, in tiers, computed from what readers declared
```

Checker replay on a built project goes through `lean4export` and the
`ConLeche` adapter (`safeverifyagent.checkers.ConLeche`, documented in
[`audits/README.md`](audits/README.md)), with nanoda through comparator
and con-ron by script.

### Who may audit what

Tool capability decides which rungs an adapter may serve, and it is
enforced rather than documented. The check rung has to *run* the
ensemble; a text-only model asked to do that will not fail, it will
describe a checker run that never happened. So a tool-less adapter is
refused the check rung and that rung is reported as never-run, on the
same principle as an ensemble member that could not vote.

That is why `claude-cli` is the default and the SDK adapter is not.

## What a verdict means

| verdict | meaning |
|---|---|
| `REFUTE` | an obligation was refuted — which one, on what evidence |
| `REJECT` | malformed input: undeclared holes, does not elaborate. **Never a refutation** |
| `ACCEPT` | no attack in this configuration landed. Always carries a residue |
| `ESCALATE` | checkers split, or a cost anomaly, or no reading was reached |

`ACCEPT` is the one people will quote, so it is the one stated carefully:
it means *no attack in this configuration landed* — over this ensemble,
at this toolchain, under this intake shape. It does not mean the proof is
correct, and every ACCEPT ships the **residue**: the computed list of
what it does not cover.

Two rules are enforced in code rather than requested in a prompt, because
a rule an agent is merely asked to follow holds until the agent is having
a bad day:

- **The evidence ceiling.** A cheap tier may not certify permanently. The
  premise of the whole exercise is that a checker may be wrong, so a bug
  disclosed next month has to be able to reopen the accept it produced.
- **A bare claim's whole-claim obligation never closes formally.** With
  no independently authored statement, "proves the intended theorem" is
  not a checkable proposition; certifying it would launder a gap into a
  guarantee.

## Audits

[`audits/`](audits/) holds the reports from pointing this method at real,
published artifacts, kept in the repo because a verdict whose method is
not reproducible is an opinion. Each report states the commit it
audited, which rungs ran, what it did not cover, which model family read
it, and how to re-run the mechanical half; plain-language summaries sit
beside the long ones, and the index with every verdict and escalation is
[`audits/README.md`](audits/README.md).

| date | artifact | what the pass was |
|---|---|---|
| 2026-09-15 … 09-20 | [openai/NavierStokesAndEuler](audits/2026-09-18-openai-NavierStokesAndEuler-FINAL.md) (641k lines), four passes | statement, kernel-trust census, final coverage in tiers, paper alignment |
| 2026-09-28 | [qinz1yang/differential-geometry](audits/2026-09-28-qinz1yang-differential-geometry.md) | bare-claim statement rung; con-leche accepts 50 declarations |
| 2026-09-30 | [RBarish/FourColorTheorem-Lean4](audits/2026-09-30-RBarish-FourColorTheorem-Lean4-metaprogramming.md) | metaprogramming and kernel-computation audit; certificates through four checkers |
| 2026-10-04 | [anthropics/formal-math percolation](audits/2026-10-04-anthropics-formal-math-percolation.md), [nasqret/semibase-order6](audits/2026-10-04-nasqret-semibase-order6.md) | statement rungs at scope, trust surface |
| 2026-10-04 | [openai/ten-proofs GapCVP](audits/2026-10-04-openai-ten-proofs-GapCVP.md) | statement, route walk, no-supplier, four checkers, a mutated-challenge control on comparator |
| 2026-10-07 | [openai/math corpus look](audits/2026-10-07-openai-math-corpus-look.md) (405 challenges, 25.9M lines) | trust surface, four statements paired, 634-digit kernel literals replayed |
| 2026-10-08 | [openai/math ω ≤ 9/4](audits/2026-10-08-openai-math-MatrixMultiplication-9-4.md) | six-reader reconstruction of the paper, nine numeric reproductions, authors' comparator config, four checkers |

Every verdict so far is **no defect found**, which is the expected
outcome on artifacts that already passed a kernel; what the reports add
is the enumerated exposure (what a kernel bug could fake, what a
statement quietly weakens, what nobody read), the escalations for an
expert, and the controls that show the instruments can fail. The
playbook's lessons are numbered and each names the incident that paid
for it. The follow-up research that some audits start — on ω ≤ 9/4, an
LP-dual reading of the paper and its formalisation — lives in the lab's
ReadingGroup repository, not here.

## Corpus

Not in this repo — see [corpus/SPEC.md](corpus/SPEC.md) for the contract
a benchmark must satisfy, and why controls are mandatory rather than
nice-to-have. A run that flags everything and a run that flags nothing
both fail the teeth check, and neither may be reported as a detection
rate. `examples/` is a smoke test published with its answers, never a
benchmark item.

## License

[Apache-2.0](LICENSE).
