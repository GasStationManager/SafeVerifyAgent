# Statement rung: `Challenge.lean` against the reference θ(p_c) = 0

Verdict: **PAIRED, EXACT.** Every reference clause has a Lean counterpart that says the same thing; the
one difference of FORM (p_c as `sInf ({p ∈ [0,1] : θ(p) > 0} ∪ {1})` instead of the textbook
`sup {p : θ(p) = 0}`) is the form the README states and is equal to the textbook one for every
non-decreasing θ with θ(0) = 0, which the honest θ is. No clause is weaker, none stronger, nothing vacuous.

Artifact: `anthropics/formal-math` @ `795efb86f191735c5481675763537cfb4ff37e55`, subdirectory `percolation/`
(read at `/home/user/formal-math/percolation`, unmodified). Lean `v4.32.0`, Mathlib `81a5d257c8e4…` (tag v4.32.0).
Reference: `REFERENCE-theta-pc.md` in this directory, written before `Challenge.lean` was opened.

## What did not run

- **No build, no elaboration.** The artifact is not built here (disk: 2.2 GB free). Everything below is
  reading of source text; nothing was `#print`ed, `#check`ed or unfolded by Lean. In particular the
  `Iff.rfl` in `Solution.lean` and the comparator verdict are taken from `AUDIT.md`, not re-run.
- **Mathlib was read at the pinned commit** for the definitions the statement anchors to: a blobless
  `git fetch --depth 1` of `81a5d257` (2.5 MB in the scratchpad), files pulled one by one with
  `git show FETCH_HEAD:<path>`. Citations below marked `ML@81a5d257` are at that commit. The v4.33.1
  checkout was used only to locate names; its `SetBernoulli.lean` differs from the pinned one only in
  proof scripts and the `MeasurableEquiv.setOf → setOfPred` rename, not in the `setBernoulli` body
  (diffed). The v4.35.0-rc2 body is `infinitePi fun i ↦ Ber(i ∈ u, False, p)` — a refactor, not used here.
- No independent checker, no `#print axioms` (AUDIT.md records them; not re-run).

## 1. Clause-by-clause pairing

Reference ids (O1–O11, H1, C1, W1–W8) are those of `REFERENCE-theta-pc.md`. Lean lines are
`Challenge.lean:<line>`.

| ref | Lean (verbatim) | match | why |
|---|---|---|---|
| O1 vertex set ℤ^d, origin | `abbrev Site (d : ℕ) : Type := Fin d → ℤ` (:59); origin `(0 : Site d)` (:131, :138) | exact | `Fin d → ℤ` is ℤ^d; `0` is the Pi `Zero`, the zero vector. `abbrev` so all `Fin d → ℤ` instances apply. |
| O2 nearest-neighbour edges, ‖x−y‖₁ = 1, unordered | `noncomputable abbrev zdGraph (d : ℕ) : SimpleGraph (Site d) := SimpleGraph.hasse (Site d)` (:67) | exact | see §2(a). `SimpleGraph` is simple and loopless; adjacency = `a ⋖ b ∨ b ⋖ a` = differ by ±1 in exactly one coordinate. |
| O3 configurations Ω = {0,1}^E, product σ-algebra | `abbrev BondConfig (V : Type*) : Type _ := Set (Sym2 V)` (:77) | exact (larger index set, harmless) | Ω is indexed by ALL unordered pairs `Sym2 V` (incl. diagonals and non-edges), not just E; non-edges carry `dirac False` (below), so they are a.s. closed. σ-algebra on `Set α` is `inferInstanceAs <| MeasurableSpace (α → Prop)` (ML@81a5d257 `MeasureTheory/MeasurableSpace/Constructions.lean:922`), the product σ-algebra with `Prop` carrying `⊤` (`MeasurableSpace/Instances.lean:28`) = the cylinder σ-algebra. |
| O4 P_p = ⊗_{e∈E} Bernoulli(p), one coin per UNORDERED edge | `ProbabilityTheory.setBernoulli G.edgeSet p` with `p : unitInterval` (:84–86) | exact | see §2(b). One factor per `e : Sym2 V`, so one coin per unordered pair — not per orientation. `p` is a `unitInterval` element, no clamping needed. |
| O5 open subgraph | `def openGraph (ω) : SimpleGraph V := SimpleGraph.fromEdgeSet ω` (:90) | exact | `fromEdgeSet` adj = `Sym2.ToRel s ⊓ Ne` (ML@81a5d257 `Combinatorics/SimpleGraph/Basic.lean:633–635`): `x ∼ y ↔ s(x,y) ∈ ω ∧ x ≠ y`. Diagonals dropped. |
| O6 open cluster of x, paths in the INFINITE graph | `def openCluster (ω) (x : V) : Set V := {y \| (openGraph ω).Reachable x y}` (:94) | exact | `Reachable u v := Nonempty (G.Walk u v)` (ML@81a5d257 `SimpleGraph/Connectivity/Connected.lean:52`): finite walks, no box. `x ∈ C(x)` (empty walk). |
| O7 "infinite" = vertex set infinite | `def percolatesAt (x : V) : Set (BondConfig V) := {ω \| (openCluster ω x).Infinite}` (:98) | exact | `protected def Infinite (s : Set α) : Prop := ¬s.Finite` (ML@81a5d257 `Data/Finite/Defs.lean:205–206`). Infinitely many VERTICES, as in the reference. |
| O8 θ(p) = P_p(\|C(0)\| = ∞) ∈ [0,1] | `noncomputable def theta (G) (x) (p : unitInterval) : ℝ := (bondPercolation G p).real (percolatesAt x)` (:102–103) | exact | `Measure.real μ s := (μ s).toReal` (ML@81a5d257 `MeasureTheory/Measure/MeasureSpaceDef.lean:101–102`); no `∞` junk since `setBer` is a probability measure (§2(b)). Measurability: §2(b). |
| O9 monotonicity | not in the statement | n/a (fact) | Used only to justify O10's form; proved in the library (`theta_mono_holds`, `Percolation/Literature/PercolationProofs.lean:271`), not compared. |
| O10 p_c, inf-form with ∪{1} | `sInf ({p : ℝ \| ∃ h : p ∈ unitInterval, 0 < theta G x ⟨p, h⟩} ∪ {1})` (:111–112) | exact (= README form; = textbook sup-form for monotone θ) | see §2(c). |
| — | `theorem criticalProb_mem_Icc … : criticalProb G x ∈ Set.Icc (0 : ℝ) 1` (:116–121), `criticalProbI d : unitInterval := ⟨criticalProb (zdGraph d) (0 : Site d), criticalProb_mem_Icc _ _⟩` (:130–131) | bookkeeping | see §2(e). Coercion of p_c into the parameter type; no content. |
| O11 0 < p_c < 1 for d ≥ 2 | not in the statement | n/a (fact) | Not needed for the statement to mean the right thing; it is what rules out triviality (§2(g)). Library has `criticalProb_zd_pos` / `criticalProb_zd_lt_one` (`Percolation/Literature/CriticalContinuityProofs.lean:222, 441`), not compared, not checked here. |
| H1 d ≥ 2 | `(d : ℕ) (hd : 2 ≤ d)` (:143) | exact | see §2(f). |
| C1 θ(p_c) = 0, an equality at the point | `def PercolationContinuity (d : ℕ) : Prop := theta (zdGraph d) (0 : Site d) (criticalProbI d) = 0` (:137–138); `theorem percolation_continuity (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d` (:143); `theorem percolation_continuity_Z3 : PercolationContinuity 3` (:149) | exact | see §2(d). The Z3 theorem is the d = 3 instance (no hypothesis left to discharge). |

Reference clauses with no Lean counterpart: none (O9, O11 are facts, not parts of the claim).
Lean clauses with no reference counterpart: `criticalProb_mem_Icc` and `criticalProbI` (bookkeeping, §2(e));
the generality over an arbitrary `G : SimpleGraph V` and vertex `x` in the `Bond` section, specialised to
`zdGraph d` and `0` in `PercolationContinuity`.

## 2. The specific checks

**(a) Adjacency is exactly L1-distance-1 on `Fin d → ℤ`.** `SimpleGraph.hasse α` has
`Adj a b := a ⋖ b ∨ b ⋖ a` (ML@81a5d257 `Combinatorics/SimpleGraph/Hasse.lean:41–42`), over the
`Preorder` on `Fin d → ℤ`, which is the pointwise Pi order (the only `LE` on a function type; lexicographic
orders live on the `Lex` synonym; the library declares no order instance on `Site`, grepped
`instance` × `Preorder|PartialOrder|LE|LT` over `Percolation/`). In the Pi order
`a ⋖ b ↔ ∃ i, a i ⋖ b i ∧ ∀ j ≠ i, a j = b j` (`Order/Cover.lean:723`, `namespace Pi` from :633;
also `covBy_iff_exists_right_eq` :735–736), and on ℤ `x ⋖ y ↔ x + 1 = y`
(`Algebra/Order/SuccPred.lean:142–143`, `covBy_iff_add_one_eq`, needs `SuccAddOrder ℤ`, `NoMaxOrder ℤ`).
So `x ∼ y` iff they agree off one coordinate i and `y i = x i ± 1`, i.e. ‖x − y‖₁ = 1. No king moves, no
loops (`⋖` is irreflexive), undirected (`∨` symmetrised). The library proves the same characterisation
(`zdGraph_adj_iff`, `Percolation/Literature/LatticeModels/LatticeGraph.lean:97–99`, via `Site.covBy_iff` :68);
not re-checked here, but my reading of the Mathlib lemmas agrees with it.

**(b) The measure and the event.** `setBernoulli` at the pinned commit
(ML@81a5d257 `Probability/Distributions/SetBernoulli.lean:44–46`):

```lean
noncomputable def setBernoulli : Measure (Set ι) :=
  .comap (fun s i ↦ i ∈ s) <| infinitePi fun i : ι ↦
    toNNReal p • dirac (i ∈ u) + toNNReal (σ p) • dirac False
```

with `p : I` (`unitInterval`, `Topology/UnitInterval.lean:32`, `Set.Icc 0 1`), `σ p = 1 - p` (:75),
`toNNReal` the identity coercion (:566). The factor at `i ∈ u` is `p·δ_True + (1−p)·δ_False` =
Bernoulli(p); at `i ∉ u` it is `p·δ_False + (1−p)·δ_False = δ_False`. `infinitePi` is the genuine
product (Kolmogorov extension) when every factor is a probability measure and `0` otherwise
(`Probability/ProductMeasure.lean:356–360`, `if h : ∀ i, IsProbabilityMeasure (μ i) then … else 0`);
`Measure.comap` likewise returns `0` unless the map is injective with null-measurable images
(`MeasureTheory/Measure/Comap.lean:62–67`). Both junk branches are excluded by Mathlib's own
`instance : IsProbabilityMeasure setBer(u, p)` (`SetBernoulli.lean:50–52`), and the library restates it
for `bondPercolation` (`Percolation/Literature/Basic.lean:81–83`). Sanity anchors:
`setBernoulli_zero : setBer(u, 0) = dirac ∅` (:69), `setBernoulli_one : setBer(u, 1) = dirac u` (:72).
So `bondPercolation (zdGraph d) p` is P_p on `{0,1}^{Sym2 (ℤ^d)}`, edges of ℤ^d Bernoulli(p)
independently, every other pair a.s. closed. The measure is on SETS (`Set (Sym2 V)`), transported from
functions `Sym2 V → Prop` by `comap` of the `setOf` equivalence — the same object.

Event. `percolatesAt 0` is nonempty (it contains `(zdGraph d).edgeSet`, whose open graph is
`zdGraph d` by `fromEdgeSet_edgeSet`, `SimpleGraph/Basic.lean:652`, and whose cluster is all of ℤ^d for
d ≥ 1) and its complement is nonempty (`∅`). Measurability: a Mathlib `Measure` applied to an arbitrary
set gives the outer measure (inf over measurable supersets), so `θ = 0` would in any case mean the event is
contained in a measurable null set — the STRONG reading, not a loophole. The event is in fact measurable
(`measurableSet_percolatesAt_holds`, `Percolation/Literature/PercolationProofs.lean:128`, `Countable V`;
library, not compared). Either way the statement is not weakened by the encoding.

**(c) p_c.** `criticalProb G x := sInf (S ∪ {1})`, `S = {p : ℝ | ∃ h : p ∈ unitInterval, 0 < θ⟨p,h⟩}`.
On ℝ, `sInf ∅ = 0` (ML@81a5d257 `Algebra/Order/Archimedean/Real/Basic.lean:195`) and `sInf` of a set not
bounded below is `0` (:206). Here `S ∪ {1}` is nonempty (contains 1) and bounded below by 0 (every element
is in [0,1]), so `sInf` is the genuine infimum — neither junk branch can fire. If θ ≡ 0 on [0,1] then
`S = ∅` and p_c = 1 (the README's stated convention); otherwise p_c = inf S, since S ⊆ [0,1]. As the
reference (O10) argues, for any non-decreasing θ with θ(0) = 0 this equals `sup {p : θ(p) = 0}`; the honest θ
is non-decreasing (coupling; library `theta_mono_holds`) and θ(0) = 0 (library `theta_bot`,
`Basic.lean:162`; also immediate from `setBernoulli_zero`). So the inf-form is the textbook p_c — this
is the README's own formulation, and the equivalence is correctly flagged in `Challenge.lean:28–30` as
outside the compared statement. Note the `{1}` cannot make p_c trivially 1: if p_c were 1 the claim
would read θ(1) = 0, which is FALSE (θ(1) = `dirac edgeSet`-measure of an event containing `edgeSet`
= 1, using `Set.instMeasurableSingletonClass`, `Constructions.lean:925`, as `Sym2 (Fin d → ℤ)` is
countable). So that path makes the theorem unprovable, not vacuous.

**(d) `PercolationContinuity d` is literally θ(p_c) = 0.** `theta (zdGraph d) (0 : Site d) (criticalProbI d) = 0`
(:138): an equality in ℝ at the single parameter `criticalProbI d`. Not an inequality, not a limit, not
"for all p < p_c", no extra hypothesis.

**(e) `criticalProb_mem_Icc` and `criticalProbI`.** The lemma (:116–121) is a complete term proof
(`le_csInf ⟨1, Or.inr rfl⟩ h0`, `csInf_le ⟨0, h0⟩ (Or.inr rfl)`) — no `sorry`, no tactic hiding a gap; its
only role is to inhabit the `unitInterval` subtype in `criticalProbI` (:131). Its proof term is irrelevant
to the statement's meaning (proof irrelevance: any proof gives the same subtype element). It is the only
auxiliary lemma in the file; the only `sorry`s are the two theorem bodies (:144, :150), as declared.

**(f) Hypothesis inhabitability.** `hd : 2 ≤ d` on `d : ℕ` is inhabited by every d ≥ 2 (e.g. `d = 3`,
witnessed in `Solution.lean:128` by `by norm_num`). It is not vacuous, and it is necessary: for d = 1 the
claim is false (O11). `percolation_continuity_Z3` has no hypothesis.

**(g) Could the statement be vacuous or trivially true?** Checked routes, none open:
- θ ≡ 0 for a definitional reason: no — θ(1) = 1 (above); the measure is a probability measure;
  the cluster is taken over open edges, not over no edges.
- p_c trivially 0 (which WOULD make the claim trivial, since θ(0) = 0): only if θ(p) > 0 for arbitrarily
  small p, which is mathematically false for d ≥ 1 (Peierls; library `criticalProb_zd_pos`). The
  definition does not force it: the `sInf` is over a set bounded below with no junk branch, and S
  contains no p with θ(p) = 0.
- p_c trivially 1: leads to a false, not a trivial, statement (above).
- Junk in `toReal`: excluded, probability measure.
- No `variable` is used by the statements beyond `{V : Type*}` in the `Bond` section; no `autoParam`,
  `optParam`, `class` or `instance` is declared in the file; `autoImplicit = false` in `lakefile.toml`.
- The file imports `Mathlib` only (:1), so no artifact code can shape the statement's elaboration.
So the formal statement is true iff θ(p_c(ℤ^d)) = 0 at the honest p_c ∈ (0,1), which is the open-problem
content for 3 ≤ d ≤ 10.

## 3. Challenge vs library vs `Solution.lean`

- `Challenge.lean:51–138` and `Solution.lean:22–109` are **byte-identical** (`diff`, empty output). The
  two theorem statements are identical; only the bodies differ (`sorry` vs proof), and `Solution.lean`
  adds `bridge` (:113–115).
- Library definitions, pairwise against `Challenge.lean`:
  `Site`, `zdGraph` (`LatticeModels/LatticeGraph.lean:48, 93`, namespace `Percolation.Literature.LatticeModels`) —
  same bodies. `BondConfig`, `openGraph`, `openCluster`, `percolatesAt`, `theta`, `criticalProb`
  (`Literature/Basic.lean:70, 87, 96, 112, 123–124, 130–131`, namespace `Percolation.Literature`) — same
  bodies. `bondPercolation` (`Basic.lean:75–77`) is written `setBer(G.edgeSet, p)`, the scoped notation
  for `setBernoulli G.edgeSet p` (`SetBernoulli.lean:48`) — same term after notation expansion.
  `criticalProbI`, `PercolationContinuity` (`Literature/CriticalContinuity.lean:64–65, 82–83`, inside
  `noncomputable section`) — same bodies. `criticalProb_mem_Icc` (`Basic.lean:134–140`) is proved by a
  tactic script where `Challenge.lean` has a term; the conclusion is the same, and inside `criticalProbI`
  the proofs differ only as proofs of a `Prop`, which are definitionally equal (proof irrelevance).
- So the `Iff.rfl` in `Solution.lean:113–115` is plausible as pure δ-unfolding: both sides unfold,
  constant by constant, to the same Mathlib term (`theta`→`Measure.real`/`setBernoulli`/`hasse`/
  `fromEdgeSet`/`Reachable`/`Set.Infinite`/`sInf`), modulo the irrelevant proof inside `criticalProbI`.
  The library declares no instance that could change elaboration of these terms in `Solution.lean`
  (grepped `instance` over `Percolation/`: only `DecidableRel (zdGraph d).Adj`, `LocallyFinite`, a
  `DecidablePred` on `Site 2`, `Countable (BrickPos d)` and a product-Bernoulli probability instance,
  none of which occurs in these terms).
- `percolationContinuity_allDimensions` (`Continuity/MainTheorem.lean:176–177`) has type
  `PercolationContinuity d` with `open … Percolation.Literature` (:66); no other declaration named
  `PercolationContinuity` exists in `Percolation/` (grepped `def|abbrev PercolationContinuity`), and
  `Solution.lean:114` names `Percolation.Literature.PercolationContinuity` explicitly.
- The comparator (`comparator.json`: theorems `BondPercolation.percolation_continuity`,
  `…_Z3`; `definition_names: []`; axioms `propext, Quot.sound, Classical.choice`; nanoda on) is the
  mechanical check of this; per `../.github/scripts/comparator-check.sh` header it requires "each Solution
  theorem has exactly the statement of its trusted Challenge namesake". `AUDIT.md` records
  "post-check `comparator`: OK in 256 s … Your solution is okay!". Not re-run here.

## 4. Informal claim vs formal statement

- **Continuity of θ on [0,1] is NOT formalised**, and the artifact says so plainly: README:4–5 ("continuity of
  p ↦ θ(p) on [0,1] follows classically and is not part of the formal statement"), the Abstract, the
  "Not claimed" paragraph, `Challenge.lean:43–45`, `summary.tex:195–196`, `formalization.yaml:15–17`. The
  name `PercolationContinuity` is therefore slightly louder than its content (θ(p_c) = 0); the docstring
  at `Challenge.lean:133–136` states the content correctly.
- `summary.tex:101` defines p_c informally as `inf{p : θ(p) > 0}` (no `[0,1]`, no `∪ {1}`); the theorem at
  `summary.tex:186–188` and the README use the ∪{1} form, which is what Lean states. Harmless (θ(1) = 1).
- README:"at the critical parameter the open cluster of the origin is almost surely finite" and
  MainTheorem's "almost surely no infinite open cluster" — the formal statement is about the ORIGIN's
  cluster only. "No infinite cluster anywhere" follows by translation invariance and a countable union
  but is not part of the compared statement. Equivalent classically; recorded, not a defect.
- "0 < p_c < 1, so the statement concerns a non-degenerate parameter" (`Challenge.lean:45–47`) is context,
  not in the statement; the library proves both bounds (§1, O11), outside the comparator's scope.
- The formal statement is not stronger than the informal one anywhere. It is about BOND percolation on the
  nearest-neighbour ℤ^d only, as claimed; nothing about site percolation, slabs or other lattices is stated.

## 5. Leads for later rungs (not statement defects)

- The library carries literature results as named `Prop` `def`s with separate `_holds` theorems
  (e.g. `theta_mono : Prop` with `theta_mono_holds`; `measurableSet_percolatesAt : Prop`). Per PLAYBOOK §1.4
  that convention needs a no-supplier pass on the route; the headline theorem has no such hypothesis and
  AUDIT.md's `#print axioms` is standard-only, so on the route every such `Prop` must be discharged — the
  route rung should confirm, e.g. for "the Duminil-Copin–Sidoravicius–Tassion slab theorem is formalised as
  a literature input" (README; `DuminilCopinSidoraviciusTassion2016_holds` is a theorem, `Percolation/Literature/SlabGluingFact2.lean:569`; `formalization.yaml:99`).
- The mathematical claim is a proof of Kozma–Nitzan's Conjecture 3 (open in their paper), which settles an
  open problem for 3 ≤ d ≤ 10. The statement rung says the statement is the right one; it says nothing
  about the proof, and the evidence ceiling for that is the kernel/comparator/axiom rungs.
