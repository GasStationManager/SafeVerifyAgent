# Audit: qinz1yang/differential-geometry — the Poincaré conjecture

**Status: DRAFT** — the build-backed rungs (§2) are pending: the headline's
import closure (about 14,200 modules) is compiling; `#print axioms`, the
Lean rung of the statement dossier and a con-leche run follow when it
finishes. Everything else below is complete and its evidence is committed under
`dg-intake/`.

**Artifact:** `github.com/qinz1yang/differential-geometry` @ `7a48598d`
(release v0.1.3, 2026-09-27). Lean and Mathlib `v4.33.1`. 17,555 Lean files,
4.7 million lines, about 107,000 theorems and lemmas. Read-only throughout;
the only writes were the build's own under `.lake/`, and `git status` stays
clean.
**Headline:** `DifferentialGeometry.Topology.poincare_conjecture`
(`DifferentialGeometry/Topology/ThreeManifold/Poincare.lean:12`).
**Claim shape:** BARE. No independently authored challenge, no Comparator.
The README claims `#print axioms` gives exactly `propext, Classical.choice,
Quot.sound`.
**Auditor:** SafeVerifyAgent, method per `audits/PLAYBOOK.md`; nine reading
passes by one model family plus the mechanical tools in `audits/`. Intake in
`dg-intake/INTAKE.md`.

---

## 1. Verdict so far

**No defect found. No gap found on the proof route. The statement is the
Poincaré conjecture.** Every reading pass reconstructed the standard
mathematics at the step it read, and every named open result met on the
route is discharged by a hypothesis-free theorem whose definition matches the
literature statement. What this audit cannot yet say is what only a build
can: that the kernel accepts the whole closure with the three standard axioms
and that an independent checker agrees. Those are §2.

The structural fact that frames everything else: the headline takes no
Prop hypotheses, only Mathlib classes on `M`, and its proof chain passes none.
So the artifact's convention of *naming* a missing result as a Prop
hypothesis instead of writing `sorry` cannot hide a gap in the headline: an
undischarged predicate on the route would appear in the headline's type or
fail elaboration. It can hide one only in a theorem someone reuses, which is
§5.

## 2. Build-backed rungs (pending)

| rung | status |
|---|---|
| `lake build` of the headline module's closure with the three standard axioms | running |
| `#print axioms DifferentialGeometry.Topology.poincare_conjecture` | pending |
| Lean rung of `statement.py` (`#check`, `#print`, resolved constants) | pending |
| `lean4export` of the headline's dependencies + con-leche `--verified` | pending |
| the closing-`rfl`/`decide` defeq workload | not attempted; same instrument gap as NSE |

## 3. The statement (`dg-intake/STATEMENT.md`, `REFERENCE-poincare.md`)

The reference was written before reading the Lean: compact, Hausdorff,
connected, simply connected topological 3-manifold without boundary is
homeomorphic to S³. The Lean:

```lean
theorem poincare_conjecture (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
```

Pairing: Hausdorff, compact and simply connected match by name; the
conclusion is the unit sphere in ℝ⁴, which is S³. Two reference clauses have
no named counterpart and are carried implicitly, with the Mathlib definitions
quoted in the dossier: **without boundary** by `ChartedSpace` on ℝ³ itself
(every chart is an open partial homeomorphism onto an open subset of ℝ³, so no
half-space model and no boundary), and **connected** by
`SimplyConnectedSpace → PathConnectedSpace → ConnectedSpace`, which also gives
non-emptiness. No hypothesis is stronger than the reference. The smooth case
underneath (`smoothPoincareConjecture_holds`) adds `IsManifold (𝓡 3) ∞ M` and
`ConnectedSpace M`, and the headline discharges both: the first from Moise's
theorem, the second from the instance chain. **EXACT.**

## 4. Trust surface (`dg-intake/TRUST.md`)

Nothing in the artifact can change what the kernel accepts or hide an axiom.

- `run_cmd`: 28 sites, every one an axiom-allowlist tripwire that reads the
  environment and raises an error on a violation; none names the headline, so
  they do not replace `#print axioms`.
- `set_option`: 7,584 sites and only six option/value pairs; 927 relax
  definitional-equality transparency for the elaborator, an elaboration-
  strength setting the pinned Mathlib itself uses 6,909 times; no
  `debug.skipKernelTC`, `maxHeartbeats`, `maxRecDepth`. Two upstream vendored
  files set `autoImplicit true`, both outside the headline's imports.
- Attributes: no `implemented_by`, `extern`, `csimp`, `unsafe`,
  `native_decide`, `addDecl`. 36 global `instance` attributes, all fields of
  project structures, none applicable to the headline's types.
- **Escalation, provenance:** five of the six vendored projects had statements
  changed, always by dropping hypotheses; four `ClassificationOfSurfaces`
  adapter modules restate upstream arguments over the project's own objects
  and have no upstream counterpart. So "vendored" gives those in-cone
  declarations no backing; they were read as native code (§5.4).
  `External/README.md` lists three of the seven vendored projects.

## 5. The route, read as mathematics (`dg-intake/ROUTE-WALK*.md`, five passes)

The argument the Lean expresses, with the theorem beside each step:

1. **Moise** (`exists_isManifold_three`): a compact topological 3-manifold
   carries a smooth structure. A recognisable formalisation of Moise's 1977
   book proof: finitely many charts glued one at a time with PL
   approximations of the transition maps; the approximation theorem from the
   §34 cell-diagram construction on top of the loop theorem tower (25.2, 26.4,
   32.3/32.4, 33.1, 30.7); PL to smooth through a derived-neighbourhood
   handle filtration, smoothing handle by handle. Invariance of domain enters
   through vendored code and was read natively (§5.4).
2. **Reduction** (`Surgery/Poincare.lean`): pick a metric; simple
   connectivity gives an orientation; if Ricci flow with surgery goes extinct
   with every discarded piece Poincaré-standard, undoing the surgeries
   presents M as a connected sum of spherical space forms and S²×S¹; Van
   Kampen makes π₁ the free product; a trivial free product has trivial
   factors; S²×S¹ has π₁ = ℤ and a space form with trivial group is S³; a
   connected sum of S³s is S³.
3. **Perelman** (`exists_poincare_controlled_extinction`): canonical
   neighbourhoods through surgery by induction over surgery intervals from
   Hamilton–Ivey pinching, κ-noncollapsing (reduced volume for large scales,
   a small-scale lemma below), and continuation of canonical neighbourhoods;
   one surgery along strong δ-necks with standard caps, records, standard
   discards and a volume debit; finitely many surgeries by a volume count;
   extinction by Perelman III's width over S²-families of loops with the
   −2π − ½R_min·W rate under curve shortening with a ramp and no upward jump
   across a surgery, against an explicit threshold from the initial scalar
   barrier and width.

**Escalations, none a gap:**

- **Simple connectivity is used where Perelman does not use it.** The
  small-scale noncollapsing lemma takes `[SimplyConnectedSpace]`, and simple
  connectivity of every later stage is *proved* to propagate through surgery
  (Van Kampen over two-sided S² collars, then a star cover after capping).
  Enough for Poincaré; the surgery theory as formalised does not transfer to
  geometrization.
- **Constants are quantified in the right order.** The canonical
  neighbourhood theorem reads `∃ ε_can, ∀ ε ≤ ε_can, ∃ C₁ C₂, ∀ M …, ∃ Q_can`,
  uniform over manifolds with only the threshold per flow, proved by the
  standard sequence-rescale-limit contradiction against compactness of
  κ-solutions and the universal κ for non-round solutions. The surgery-era
  continuation theorems choose C before κ before q before δ, as Perelman II
  does. The one per-manifold constant (a positive-curvature producer) is
  applied only to the compact limit model inside a contradiction.
- **Pinching survives surgery** by the Hamilton–Perelman argument; the
  route-level parameter of 1 is harmless because a surgery record cannot be
  built without δ below an explicit threshold, min(τ, 1/200000000).
- **No docstrings anywhere on the route.** The link to the literature rests
  on identifier names and on the readers' reconstruction.
- **Surgery-era statements are per initial data**, weaker than the
  textbook's ε-only constants; reusable only as such.

### 5.4 Vendored invariance of domain (`dg-intake/VENDORED-CHAIN.md`)

The class `BrouwerFixedPoint E` states the standard fixed-point theorem;
`invariance_of_domain_open_map` is the standard theorem, proved by the
Tietze-plus-perturbation route; the `HasInvarianceOfDomain` instance is
conditional on the class; the class is discharged by a native instance built
on Mathlib singular homology through a Mayer–Vietoris computation of the
sphere's top homology and the no-retraction theorem. The CanonicalTopology
homology code has no public upstream, so its vendored status is no evidence
and the native read is what carries it; 70 of its 80 files are byte-identical
to the tarball the artifact ships, and the three statement changes are sound
generalisations.

## 6. Can an intermediate theorem be reused?

- **Named hypotheses** (`dg-intake/NOSUPPLIER.md`, verification in
  `workers/nosupplier-verify-1.md`): the mechanical pass listed 445
  candidates; reading the top 48 found 44 were instrument false positives (in-
  proof constructions, dot-notation types, supply through statement
  definitions, a signature splitter that cut at the wrong colon). The four
  genuinely unsupplied predicates are all off route: a legacy Cheeger–Gromov
  interface with no base case, and one abandoned reduction. A theorem stated
  over those is unreachable. Of the 151 `*Frontier*` modules, "Frontier"
  usually means topological frontier, not an open result.
- **Junk values** (`dg-intake/JUNKVALUE-TRIAGE.md`): 617 scanner hits, 290
  triaged, none a reachable degenerate value a consumer relies on. One
  route-shaped effect is neutralised: at δ = 0 a "δ-neck" is the shortest
  neck, not the longest, but every neck object on the route carries a
  positivity field.
- **Definitions match their names.** Every literature-named predicate on the
  route (`Moise352`, `PLApproximation`, `Section34CellDiagram`,
  `PinchingThroughSurgery`, `NoncollapsingThroughSurgery`,
  `CanonicalNeighborhoodContinuation`, `isPoincareStandard`, …) was compared
  with the standard statement and none is weaker.

## 7. What was not done

Build-backed rungs (§2). The `rfl`/`decide` defeq workload. Proof bodies
below the readers' frontiers (each report lists its own; the deepest unread
items are the universal-κ theorem for non-round κ-solutions, the strong-neck
selection body, the minimizer-existence lemmas through surgery, and the
Section34 leaf bodies). A `Nat`-subtraction pass. Coverage in tiers
(`ledger.py`) once the reports declare their read ranges. One model family
throughout.

## 8. Instrument findings from this audit

Seven `cone.py` and `nosupplier.py` defects were fixed before the smoke test;
the verification pass then found six more in `nosupplier.py` and one in
`cone.py` (short-name resolution pulls `.trans`, `refine` into the cone), and
the junk-value triage twelve false-positive patterns in `junkvalue.py`. All
are being fixed against the readers' verdicts as the oracle. The name-level
cone is a weak denominator on this artifact (54% of the repository); the
import closure (81%) is the sound upper bound, and the build's module list
is the exact one.
