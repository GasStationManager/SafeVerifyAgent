# Audit: openai/NavierStokesAndEuler

**Artifact:** `github.com/openai/NavierStokesAndEuler` @ `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`
**Auditor:** SafeVerifyAgent, coherence rung via `claude -p` (claude-opus-5); mechanical scans local
**Date:** 2026-09-15
**Intake shape:** PAIRED for Navier–Stokes, effectively BARE for Euler (see E1)

> **Verdict: no defect found. Three items escalated for expert review.**
> This is a *specification* audit. The 641k-line proof body was not audited and
> Comparator/nanoda were **not run** — see "What this does not cover".

---

## Summary

| | |
|---|---|
| Lean files / lines | 2,659 / 641,332 |
| Trust-surface markers | **0** |
| `sorry` outside intentional challenge placeholders | **0** |
| Solution modules importing a challenge module | **0** |
| NS challenge vs independent upstream | **semantically identical** |
| Coherence rung | 2/2 clean, 3 escalations |

This is a conspicuously well-constructed formalization. It ships its own
Comparator challenges, pins a toolchain, declares its axioms, and states
`review: self-assessed` rather than implying external review. The findings below
are places an expert should look, **not** defects.

---

## Verified mechanically

**1. Zero trust surface across 641,332 lines.** No `native_decide`, `addDecl`,
`mkProj`/`Expr.proj`, `macro_rules`/`elab`, `unsafe`, `implemented_by`,
`partial def`, or hash/depth comparisons standing in for equality. The usual
kernel-exploit vectors are simply absent.

**2. The four `sorry`s are the intentional Comparator placeholders**, all in the
two challenge files, which document them as such. A challenge module is supposed
to state the theorem and leave the proof to the solution; this is the correct
pattern, not a hole.

**3. Challenge/solution independence holds.** `ComparatorChallenges/NavierStokes.lean`
asserts "Neither the proof root nor the submission imports this reference." That is
checkable and true — no solution module imports a challenge module.

**4. The Navier–Stokes challenge is a faithful copy of an independently authored
statement.** It is taken from google-deepmind/formal-conjectures at **pinned commit
`8bf45ed`**. A normalized diff (ignoring comments, attributes, imports, namespace,
notation) finds the **only** semantic difference to be the deletion of alternatives
(A) and (B) — the two *existence* statements OpenAI does not claim. Every definition
and both breakdown theorems (C) and (D) are mathematically identical to upstream.

This is the strongest structural fact in the audit: for Navier–Stokes, a Comparator
ACCEPT means *the statement the community wrote for the Clay problem was proved*,
not a statement the claimant chose.

## Coherence rung — 2/2 clean

Two independent auditors, one per challenge file, auditing the **statements**.

**Navier–Stokes — clean.** Field-by-field correspondence to Fefferman: `navier_stokes`
is (1) with the convective term `fderiv (v·t) x (v x t)` = Σⱼ uⱼ∂uᵢ/∂xⱼ and correct
signs; `div_free` (2), `initial_condition` (3), the `ContDiffOn` fields (6)/(11),
`integrable`+`globally_bounded_energy` (7), decay conditions (4)/(5), periodic
conditions (8)/(9)/(10).

Two checks worth recording because they are the ones that catch a rigged
non-existence claim:

- **Polarity.** The claim is `∃ u₀ f, P ∧ Q ∧ ¬∃ v p, S`. Weakening `P`/`Q` or
  *strengthening* `S` makes it easier. No field of `S` goes beyond (1),(2),(3),(6),(7),
  and the data conditions carry all of (4)/(5). Junk values (`fderiv`, `derivWithin`,
  `Δ`, `gradient` collapsing to 0 off differentiability) run the **safe** direction
  here — they enlarge the solution class, making `¬∃` *harder*.
- **Non-degeneracy.** `¬∃ v p, S` would be free if `S` were unsatisfiable. It is not:
  `u₀ = f = 0`, `v = p = 0` satisfies every field in both structures. So neither
  breakdown theorem is trivially true, and the data conditions are satisfiable.

**Euler — clean.** The ν=0, f=0 specialization is field-for-field exact against the
pinned NS structure: the field lists are in bijection and substituting `nu := 0`,
`f := 0` into the NS equation yields the Euler one exactly. Nothing added, nothing
dropped. Further:

- `toL2`'s `else 0` junk branch is **unreachable** where it constrains anything:
  `SobolevSmoothOn` requires `MemLp … 2` at every `t ∈ I`, `ContinuousOn` only
  evaluates on `𝓝[I] t`, and `HasDerivAt` is a germ condition at `t ∈ interior I`,
  which is open and inside `I`.
- The blowup clauses cannot be satisfied by unconstrained junk `v` past `T*`: they
  use `𝓝[<] Tstar` and `∫⁻ t in Ico 0 Tstar`, both strictly below `T*`. Had either
  used `𝓝 Tstar` or `Icc 0 Tstar`, the theorem would be free.
- `vorticity` is the correct curl (cyclic `Fin 3` indices), and the `∫⁻` clause is
  the Beale–Kato–Majda criterion.
- The maximal-lifespan `iff` is self-guarding: `0 < Tstar` forces the bespoke class
  to be satisfiable, so it cannot be secretly contradictory.

---

## Escalations

### E1 — Provenance asymmetry between the two results *(the main one)*

**Navier–Stokes**: challenge is a verbatim copy of an independently authored
statement at a **pinned** commit. Genuine paired intake.

**Euler**: the challenge was **authored by the claimant**, adapted from the NS file
("specialized to zero viscosity and zero external force"), citing formal-conjectures
at **`main`** rather than a pinned commit.

So for Euler no independent party wrote the statement. Comparator still establishes
"the solution proves this statement" — it cannot establish "this is the right
statement", because with no independently authored statement there is nothing for a
specification to have drifted *from*. That question falls entirely to human reading.

**Mitigating:** the coherence auditor found the specialization field-for-field exact
against the pinned NS ancestor sitting in the same directory, so the drift risk is
small in practice. **But the two results are not equally underwritten**, and the
README presents them side by side without noting it.

*Suggested:* pin the Euler citation to a commit; better, land an independent Euler
blowup statement in formal-conjectures and challenge against that.

### E2 — Instance swap at the challenge/solution seam

`Euler/Solution.lean:41`:

```lean
-- Match the reference's elaboration of ENNReal suprema independently of import order.
attribute [local instance] CompletePartialOrder.toSupSet
```

It appears exactly once in the repository, positioned between `euler_breakdown_R3`
and `exists_compact_smooth_euler_singularity`, i.e. it governs how `⨆` elaborates in
the second theorem's statement — which is where `velocityC1Norm` and `vorticityNorm`
live, the quantities the blowup claim is *about*.

The stated intent is to make the solution match the reference, which is the right
direction, and a genuine mismatch is what Comparator's declaration comparison should
catch. The challenge file declares no such instance. Still: this is precisely the seam
where a challenge and a solution can silently mean different things by the same
notation, and it is an `ℝ≥0∞` instance diamond, not an obvious equality.

*Suggested:* an expert confirms the challenge's `⨆` and the solution's `⨆` elaborate
to the same function, and that Comparator's comparison is sensitive to the difference
if they do not.

### E3 — `isOnePeriodic_pressure` in alternative (D) — traced upstream, downgraded

`NavierStokesExistenceAndSmoothnessPeriodic` requires the **pressure** to be
1-periodic. Fefferman's (10)/(11) state periodicity of the velocity. An extra field
on the solution structure *strengthens* it and therefore *weakens* the non-existence
claim (D): a periodic `v` only forces `∇p` periodic, so `p` may carry an `a(t)·x`
term, and ruling out only periodic-`p` solutions is strictly less than ruling out all.

**Traced:** the field is **inherited verbatim from the independently authored
upstream**, which justifies it by the Clay errata, and the justifying docstring
travels with the field into the copy. Only the file-header paragraph about the errata
was trimmed. So this is *not* a weakening introduced by the claimant — it is a
question for the formal-conjectures authors and the Clay errata text.

**Unverified:** I could not read the Clay PDF (no PDF extraction in this container),
so the errata wording itself is unconfirmed. **(C) is unaffected and is by itself a
full Clay alternative**, so the headline does not rest on this.

---

## What this does not cover

Stated plainly, because an audit that hides its own gaps is worth less than one that
does not:

- **Comparator and nanoda were NOT run.** That is the high tier, and running it needs
  `lake exe cache get` plus a Mathlib build. Everything above is the cheap rung plus
  argument-level reading. The authors document how to run it.
- **The proof body was not audited.** 641k lines; only the two challenge
  specifications were read. Whether the solution actually proves them is exactly what
  Comparator answers.
- **`#print axioms` was not executed.** The declared axioms (`propext`,
  `Classical.choice`, `Quot.sound`) are on the whitelist but are the authors' claim,
  not a measurement, in this audit.
- **`Euler/SolutionDefinitions`' copies** of the solution structures were not checked
  kernel-identical to the challenge module's. Comparator's job, and see E2.
- **n = 1 per statement**, one auditor each, same model family as the artifact's
  authoring family is *not* an issue here (the artifact is GPT-authored, the auditor
  is Claude) — this is the rare cross-family case, which is the one confound this
  audit does *not* have.

## Reproduce

```bash
git clone --depth 1 https://github.com/openai/NavierStokesAndEuler /tmp/nse

# the mechanical rung — reproduces the three headline numbers exactly:
#   2659 Lean files / 641,332 lines; 4 sorry (both challenge files); 0 trust surface
python3 audits/scan_repo.py /tmp/nse

# the independence claim, which is checkable:
grep -rn "import ComparatorChallenges" --include="*.lean" /tmp/nse | grep -v /ComparatorChallenges/

# the statement diff against the pinned upstream (§ "Verified mechanically" item 4):
curl -fsSL https://raw.githubusercontent.com/google-deepmind/formal-conjectures/8bf45ed70d48b2b2a501de9c00b26bfa38c573ee/FormalConjectures/Millenium/NavierStokes.lean \
  -o /tmp/upstream_NavierStokes.lean
diff -u /tmp/upstream_NavierStokes.lean /tmp/nse/ComparatorChallenges/NavierStokes.lean
```

The coherence rung was two `claude -p` auditors, one per challenge file, through
`safeverifyagent.prompts.render("coherence", ...)`. What they found is quoted
above; an agent run does not repeat byte for byte.
