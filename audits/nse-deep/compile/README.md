# Compile & evidence checks — NSE deep audit

Every previous cycle of this audit recorded the same blocker: **no build possible**. That is no longer true,
and this directory holds the evidence for the checks that became available.

## Why the blocker lifted
| fact | as recorded by every prior cycle | measured this cycle |
|---|---|---|
| disk | 99-100% full, 4.1G free | 88-90% used, ~54G free |
| toolchain | box had Mathlib v4.33.0 only; the pin `lean4:v4.34.0-rc2` was unavailable | **installed**, `lean --version` = 4.34.0-rc2, commit `6a10ac8c22be` |
| dependencies | `.lake` absent, 0 built `.olean` | Mathlib cache **8,747 / 8,747 (100%)** |
| network | not established | github reachable (HTTP 200) |

Artifact: `/home/gsm/.openclaw/workspace/repos/NSE` @ `f9e8bc5`, pinned `leanprover/lean4:v4.34.0-rc2`,
mathlib `85e3a25e006c`.

## Contents
* `PROVENANCE.json` — requested vs actual models (controller and subagents), the three GPT-5.6 Luna provider
  failures with their distinct causes, artifact pins, environment deltas.
* `01-deps.log` — toolchain install + `lake exe cache get`. Ends `Decompressed 8747 file(s)`.
* `02-lake-build.log` — `lake build` of the full 641,332-line artifact.
* `nse_axioms.lean` — the axiom provenance probe. **Deliberately outside the artifact tree**; run with
  `cd NSE && lake env lean /tmp/nse_axioms.lean` so the repository stays byte-identical. Targets the audit's
  own cone seeds, reduced to the three that carry proofs.
* `ea4_test.sh` — the E-A4 test. Re-elaborates NavierStokes files with `-DautoImplicit=false
  -DwarningAsError=true` supplied **on the command line**; `lakefile.toml` is never edited.

## Read-only discipline
The audit has been read-only on NSE throughout. The build writes only to `.lake/` (untracked build output);
`git status` inside the artifact is verified clean before and after. No probe file is placed in the tree.

## What these checks can and cannot settle
`#print axioms` settles **axiom provenance**: whether the headline theorems rest on anything beyond
`propext`, `Classical.choice`, `Quot.sound`, and in particular whether `sorryAx` appears anywhere in their
closure. It does **not** settle whether a constant in an estimate is the right constant.
The E-A4 test settles whether the missing `autoImplicit := false` on the 816-file NavierStokes library
actually admits silently auto-bound identifiers, which no amount of source reading could decide.
