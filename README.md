# SafeVerifyAgent

An agent that is handed a Lean 4 proof somebody claims is finished and
decides whether to believe it.

It never proves anything. A claimed proof is a conjunction — sound only
if every obligation is sound — so it is unsound if *some* obligation is
unsound, and the job is to find one or run out of ways to look.

> **Status: early.** The checker ensemble, the verdict types and the
> aggregation are implemented and tested; the agent stages have prompts
> and skeleton drivers, and the pipeline has **not been run end to end
> against a real claim**. No number in this repo has been measured
> against a public corpus. See [DESIGN.md §10](DESIGN.md#10-status).

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

## The ensemble

| tier | member | independent of Lean? |
|---|---|---|
| quick | `lean` elaboration + axiom scan | — |
| medium | [Lean4Lean](https://github.com/digama0/lean4lean) | **no** — a port of the C++ kernel, by its own README |
| high | [comparator](https://github.com/leanprover/comparator) | — |
| high | [nanoda](https://github.com/ammkrn/nanoda_lib) | **yes** — from scratch, in Rust |

`leanchecker` is deliberately not a tier: it is Lean's own kernel running
twice, so counting it as a second opinion is the exact common-mode
failure this design exists to avoid.

Members are not equally independent, so a verdict count is **not** a
diversity measure. And every adapter parses what its tool *printed*,
never how it *exited* — comparator exits non-zero when it merely fails to
build, and `lean4lean` exits **zero** while printing "found a problem".
Both bugs once inverted a verdict; both are now pinned by tests.

## Install

```bash
git clone https://github.com/GasStationManager/SafeVerifyAgent
cd SafeVerifyAgent
python3 -m unittest discover -s tests     # 43 pass, 10 skip — no toolchain needed
```

For the Lean-gated half — frontend extraction and the quick tier — install
a toolchain:

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.0
export PATH="$HOME/.elan/bin:$PATH"
python3 -m unittest discover -s tests     # 53 tests
```

`lean_available()` probes that Lean actually *runs* rather than that a
file called `lean` exists — elan installs a shim that resolves a
toolchain at call time, so the binary can be present and still fail, and
the difference between a clean fall back to the regex path and a pile of
confusing errors is worth one subprocess.

The core has no dependencies. Checkers are discovered by environment
variable and every one of them degrades to "unavailable" — never to a
verdict — when its binary is missing:

```bash
export SVA_LEAN4LEAN=~/lean4lean      # optional, medium tier
export SVA_COMPARATOR=~/comparator    # optional, high tier
export SVA_NANODA=~/nanoda_lib        # optional, the independent kernel
python3 -c "from safeverifyagent import checkers; print(checkers.available())"
```

## Use

```bash
# Claude Code: render one task per obligation, dispatch them in parallel
python3 drivers/claude_code/render_tasks.py Claimed.lean --rung check

# API driver (needs `pip install anthropic`)
python3 drivers/api_driver.py Claimed.lean --intake bare --json
```

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

## Corpus

Not in this repo — see [corpus/SPEC.md](corpus/SPEC.md) for the contract
a benchmark must satisfy, and why controls are mandatory rather than
nice-to-have. A run that flags everything and a run that flags nothing
both fail the teeth check, and neither may be reported as a detection
rate.

## License

[Apache-2.0](LICENSE).
