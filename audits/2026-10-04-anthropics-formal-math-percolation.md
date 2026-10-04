# anthropics/formal-math `percolation/` — statement rung and trust-surface scan

Status: **concluded 2026-10-04** at the scope below: statement rung and metaprogramming /
trust-surface scan; nothing built, no axiom listing, no independent checker, no route walk.

Artifact: `anthropics/formal-math` at `795efb86f191735c5481675763537cfb4ff37e55`, subdirectory
`percolation/`; Lean `v4.32.0`, Mathlib tag v4.32.0 (`81a5d257`); 251 Lean files, 97,574
lines. Headline: `BondPercolation.percolation_continuity : ∀ d, 2 ≤ d → PercolationContinuity d`
and `percolation_continuity_Z3` in `Challenge.lean`, proved in `Solution.lean` by `Iff.rfl`
transport from `Percolation.Continuity.CSH.percolationContinuity_allDimensions`. Informal
claim: θ(p_c) = 0 for nearest-neighbour Bernoulli bond percolation on ℤ^d for every d ≥ 2
(open for 3 ≤ d ≤ 10), via Kozma–Nitzan's Conjecture 3 proved through a new conditioned
slack hierarchy. Author per `formalization.yaml`: Justin Leder; "not yet refereed by anyone
independent of the author". PAIRED claim: `Challenge.lean` is the trusted statement file and
the artifact's `AUDIT.md` records a comparator run with nanoda. Intake: `perc-intake/`.

## 1. Verdict

**Statement: PAIRED, EXACT.** Every reference clause has a Lean counterpart saying the same
thing; the one difference of form is p_c as `sInf ({p ∈ [0,1] : θ(p) > 0} ∪ {1})` rather than
the textbook `sup {p : θ(p) = 0}`, equal for any non-decreasing θ with θ(0) = 0. **Trust
surface: empty.** Comment-stripped: no `run_cmd`, `macro`, `macro_rules`, `elab`, `syntax`,
`notation`, `simproc`, `initialize`, `attribute`, `unsafe`, `implemented_by`, `extern`,
`native_decide`, `decide +kernel`, `addDecl`, `axiom`, `opaque`, `partial`; two `set_option`s
(`pp.fullNames`, `format.width`, in the axiom-listing script); 268 plain `decide`s on small
`Fin` facts in the block-construction files; two `sorry`s, both the placeholders in
`Challenge.lean`. **No defect found** at this scope.

## 2. What was checked

| item | result |
|---|---|
| Reference statement (`REFERENCE-theta-pc.md`, written before the Lean) | model O1–O11, hypothesis H1, conclusion C1, eight weakening modes W1–W8 |
| Measure | pinned `setBernoulli` (`SetBernoulli.lean:44–46` at `81a5d257`, read by blobless fetch) is `comap (fun s i ↦ i ∈ s)` of `infinitePi` over `p•δ(i∈u) + (1−p)•δ False`: Bernoulli(p) per unordered pair, a.s. closed off the edge set, product σ-algebra; `infinitePi` and `Measure.comap` return the zero measure when their preconditions fail, ruled out by Mathlib's `IsProbabilityMeasure` instance (:50) |
| Graph | `zdGraph d := SimpleGraph.hasse (Fin d → ℤ)`; via `Pi.covBy_iff` and `covBy_iff_add_one_eq` on ℤ this is exactly L1-distance-1 nearest neighbour |
| "infinite cluster" event | nonempty; Mathlib applies the outer measure to any set, so θ = 0 is the strong reading; the library also proves it measurable (`measurableSet_percolatesAt_holds`) |
| p_c | `S ∪ {1}` nonempty and bounded below, so neither `sInf` fallback (`sInf ∅ = 0`; not-bounded-below) applies; θ ≡ 0 would give p_c = 1 and the false claim θ(1) = 0 (θ(1) = 1 via `setBernoulli_one`), so unprovable rather than vacuous; the only trivialising route is p_c = 0, not forced by the definition and refuted by the library's `criticalProb_zd_pos` (outside the compared statement) |
| `PercolationContinuity d` | literally `theta (zdGraph d) 0 (criticalProbI d) = 0`; no limit, inequality or extra hypothesis; `2 ≤ d` satisfiable and needed (false for d = 1) |
| Challenge vs library vs Solution | `Challenge.lean:51–138` byte-identical to `Solution.lean:22–109` (diff); library definitions have the same bodies up to the `setBer(·,·)` notation and a tactic-versus-term proof inside a subtype, so `Iff.rfl` is plausible by unfolding |
| Informal vs formal | continuity of θ on [0,1] is not formalised and every artifact document says so; the name `PercolationContinuity` promises more than its content (θ(p_c) = 0); `summary.tex:101` writes p_c without `∪ {1}` (harmless) |

## 3. What this audit does not say

No build, no elaboration (disk); the `Iff.rfl`, the comparator result and the seven
`#print axioms` lines are taken from `AUDIT.md`, not re-run. No route walk: the mathematical
novelty (the conditioned slack hierarchy and additive gluing proving Conjecture 3, then
Kozma–Nitzan's Theorem 6 re-proved) is unread. The library carries literature inputs as
named `Prop` definitions each with a separate `_holds` theorem (e.g. the
Duminil-Copin–Sidoravicius–Tassion slab theorem); the headline carries no such hypothesis
and `AUDIT.md` reports only the standard axioms, but by playbook rule 4 that pattern calls for
a no-supplier pass. The sibling `zeta23/` directory was not scanned.

## 4. Reproduce

```
git clone https://github.com/anthropics/formal-math && cd formal-math && git checkout 795efb86 && cd percolation
python3 <SafeVerifyAgent>/audits/scan_repo.py --sites .
lake exe cache get && lake build && lake env lean scripts/Axioms.lean   # the artifact's own AUDIT.md recipe
```
