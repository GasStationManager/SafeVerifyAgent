# NSE deep audit — running findings

Artifact: `github.com/openai/NavierStokesAndEuler` @ `f9e8bc5` (clone at
`/home/gsm/.openclaw/workspace/repos/NSE`, read-only).
Pass: **kernel-trust**, not specification. The 2026-09-15 audit read the two challenge
*statements*; this pass reads *proofs*, and asks which of them a bug in the Lean kernel
could turn into a fake. Threat vectors, in the order we were told they matter:
(1) recursive inductive types, (2) `Nat` arithmetic delegated to GMP, (3) custom
metaprogramming.

Verdict tags: **OK** (understood and benign), **NOTE** (true but only hygiene),
**ESCALATE** (an expert should answer a specific question), **REFUTED** (a defect).
Nothing is REFUTED so far.

---

## P0 — measurement corrections to our own instrument (not artifact findings)

- `safeverifyagent/extract.py:strip_comments` deletes block comments outright, so every
  `file:line` computed on stripped text drifts by the height of preceding comments —
  on `Euler/EulerProof.lean` an `inductive` reported at 3015 actually lives at **3064**.
  Fixed by adding `blank_comments` (comment content removed, newlines kept) and
  switching the new scanner to it. All site lists in this directory are 2nd generation
  and verified against the original files. Six in-flight workers were sent the
  correction. *Lesson: a citation that lands 49 lines away is worse than no citation,
  because it looks checkable.*

## A1 — vector (3) is empty at source level — OK

`python3 audits/scan_kernel_risk.py <repo> -o audits/nse-deep` over 2,659 files /
641,332 lines / **52,516 declarations** (38,503 `theorem`, 10,827 `def`, 1,578
`instance`, 899 `abbrev`, 667 `structure`, 28 `lemma`, 14 `inductive`):

`macro`/`macro_rules`/`syntax`/`elab`/`notation`-declaration = **0**;
`run_cmd`/`#eval`/`#reduce`/`MetaM`/`TacticM` = **0**; `set_option` (any, incl.
`maxHeartbeats`, `maxRecDepth`, `debug.skipKernelTC`) = **0**; `axiom` = **0**;
`opaque` = **0**; `native_decide` = **0**; `unsafe`/`@[extern]`/`implemented_by`/
`partial def` = **0**; `sorry` = 4, all of them the two challenge files' placeholders.
The only elaboration-affecting declarations are 25 `attribute` lines, **all `local`**
(11 `local instance`, 10 `local irreducible`, 2 `local gcongr`, 4 of the instances being
`Classical.propDecidable`). So there is no custom metaprogramming to audit: the artifact
is written in plain Lean + Mathlib tactics. The residue is Mathlib's own trust surface,
which this artifact does not control.

## A2 — the solution's private copies of the challenge structures are exact — OK
*(closes a residue item of the previous audit)*

Comparator requires the solution not to import the challenge, so the solution restates
the challenge's definitions. Both copies exist:

| challenge | solution-side copy |
|---|---|
| `ComparatorChallenges/Euler.lean` | `Euler/SolutionDefinitions.lean` |
| `ComparatorChallenges/NavierStokes.lean` | `NavierStokes/ComparatorDefinitions.lean` |

Normalized diff (comments blanked, attributes/imports/`namespace`/`open`/`section`/
`local notation`/`#print` lines dropped, whitespace collapsed) over each pair: the
**only** difference is the deletion of the placeholder theorems (`euler_breakdown_R3`,
`exists_compact_smooth_euler_singularity`; `navier_stokes_breakdown_R3`,
`navier_stokes_breakdown_periodic`) with their `sorry`s. **Every definition and every
structure field is character-identical.** Field lists, `extends` chains, and the junk-prone
`toL2` are identical, so nothing was silently added to or dropped from a solution
structure.

The elaboration *context* is identical too, which is the part that a text diff does not
by itself establish: both members of each pair are the only 4 files in the repo that do
`import Mathlib` wholesale (and nothing else), and their `open`/`local notation` lists
match line for line (`open ContDiff Set InnerProductSpace MeasureTheory`,
`open scoped Laplacian`/`ENNReal Topology`, `ℝ³`, `ℝ^n`, `∇⬝`).

## A3 — ESCALATE (refines the previous audit's E2, with a mechanism)

`Euler/Solution.lean:41`: `attribute [local instance] CompletePartialOrder.toSupSet`,
commented "Match the reference's elaboration of ENNReal suprema independently of import
order", placed between `euler_breakdown_R3` and `exists_compact_smooth_euler_singularity`.

What we can now say precisely:

- The `⨆ t ∈ Icc (0:ℝ) T, velocityC1Norm (v · t)` and `⨆`-in-`velocityC1Norm`/
  `vorticityNorm` occurrences are `ℝ≥0∞`-valued suprema, and the ones in the *theorem
  statement* are elaborated **in `Euler/Solution.lean`**, not in the definitions file.
- `Euler/SolutionDefinitions.lean` (the copy) elaborates its `⨆` with an import set of
  exactly `Mathlib`. `Euler/Solution.lean` elaborates its own `⨆` sitting on top of
  **1,829 modules** (measured on the import graph), exactly one of which pulls in
  Mathlib wholesale. Instance resolution among same-priority instances depends on
  declaration order, hence on module order — which is what the author's comment says.
- So the acceptance of the Euler headline rests on the kernel deciding that the
  challenge's `SupSet ℝ≥0∞` and `CompletePartialOrder.toSupSet` denote the same
  function. That is a defeq between two paths through Mathlib's `CompleteLattice`
  hierarchy, i.e. **structure-projection unfolding and structure eta** — the same
  machinery listed under threat vector (1).

**Question for an expert (checkable in ~10 lines of Lean):** in an environment with the
solution's import set, do
`(inferInstance : SupSet ℝ≥0∞)` and `CompletePartialOrder.toSupSet` elaborate to terms
that are equal by `rfl` *and* print identically under `set_option pp.all true`? And is
Comparator's declaration comparison sensitive to the difference if they are not? A
positive `rfl` answer that relies on a long projection-unfolding chain is exactly the
kind of judgement a kernel bug could get wrong, and it sits on the deliverable path.

## A4 — ESCALATE (build-option asymmetry: the NS half is elaborated with `autoImplicit`)

`lakefile.toml` gives the `Euler` library `leanOptions = { autoImplicit = false,
warningAsError = true }`. The `NavierStokes` library (816 files) and
`ComparatorChallenges` get **no `leanOptions` at all**, so they build with Lean's
defaults: `autoImplicit := true`, `relaxedAutoImplicit := true`, warnings not errors.
With `autoImplicit` on, a mistyped identifier in a *statement* is silently bound as a
fresh implicit argument instead of being an error, so the theorem that gets proved is
not the theorem that was written down.

This is a specification-drift vector, not a kernel one, and it cannot manufacture a
proof of a false statement (auto-binding generalizes, which makes a statement harder,
not easier). It does mean an intermediate NS lemma can quietly be about a fresh
variable while its name says otherwise.

Mitigating and interesting: the authors clearly know the check — 11 `…NoOptions.lean`
modules document `lake env lean -DautoImplicit=false -DwarningAsError=true <file>` as
their verification command. They applied it to selected files, not to the library.

**Suggested:** build the `NavierStokes` library once with `-DautoImplicit=false
-DwarningAsError=true` and report the diff. We cannot run it here (no Mathlib build:
7.4 GB free disk), so this is escalated rather than measured.

## A5 — NOTE: the 11 `NoOptions` siblings do not re-verify their namesakes

The `…NoOptions.lean` modules exist to reprove something without a resource-limit
override, but **`set_option` occurs 0 times in the repo**, so whatever override they
were built against is gone from the source. Nine of the eleven are near-copies
(e.g. `NavierStokes/CorrectionInitializationNoOptions.lean` vs
`CorrectionInitialization.lean`: 5,573 vs 5,562 lines, `difflib` ratio 0.999 — the only
substantive change is the namespace and a docstring paragraph). Two are **not** copies:

- `Euler/TransversePacketCorrectorNoOptions.lean` — 39 lines vs 160: it reproves exactly
  one theorem (`potentialCoefficientPath_time`) and says the original's `simpa only`
  "exceeds the default recursion depth in an isolated reproduction".
- `NavierStokes/ActualParticularDynamicsNoOptions.lean` — 143 lines vs 1,633.

Nothing wrong with that, but the name invites the reading "this module is also checked
under strict options", and for these two the strict-option check covers a fragment.

---

## Coverage ledger

`INVENTORY.csv` — 52,516 rows, one per declaration, with per-body counts of
`decide, norm_num, omega, simp, rfl, native, rec, induction, termination_by, wf, bignum,
pow, choose_fact, finset, nat_prim`. An audited theorem is a row signed off here.
Parent-read so far: the two challenge files, both definition copies, `Euler/Solution.lean`,
`Euler/EulerSingularity.lean` (head), `Euler/EulerProof.lean:3040-3130`, the 25
`attribute` sites, the 14 `inductive` headers, all 12 `termination_by` and 5 explicit
recursor sites (locations verified, bodies delegated).
**Six workers in flight** (see `workers/`): `jet-inductives`, `expr-inductives`,
`decide-bignum`, `wf-recursion`, `euler-spine`, `ns-spine`.
