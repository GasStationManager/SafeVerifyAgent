# Intake: qinz1yang/differential-geometry

Playbook §5 step 1, recorded before any tool ran. Facts only.

| | |
|---|---|
| artifact | `github.com/qinz1yang/differential-geometry` @ `7a48598d` (2026-09-27, release v0.1.3) |
| toolchain | Lean `v4.33.1`, Mathlib `v4.33.1`; `autoImplicit = false` for the whole library, `maxSynthPendingDepth = 3` |
| size | 17,555 Lean files, 4,704,458 lines, 85,124 `theorem` + 4,623 `lemma`, 11,974 `def`, 892 `structure`, 41 `inductive`, 17 `class` — about seven times NavierStokesAndEuler |
| headline | `DifferentialGeometry.Topology.poincare_conjecture` (`Topology/ThreeManifold/Poincare.lean:12`): compact T2 simply-connected charted space on E³ is homeomorphic to S³; proved from Moise (`PiecewiseLinear.exists_isManifold_three`) plus the smooth case `Surgery.Topology.smoothPoincareConjecture_holds` (`Surgery/Skeleton/PoincareEndgame.lean:103`), which adds `IsManifold (𝓡 3) ∞ M` and `ConnectedSpace M` |
| claim shape | **BARE**: no independently authored challenge, no Comparator run. The README claims `#print axioms` gives exactly `propext, Classical.choice, Quot.sound` for every listed theorem |
| authorship | 2,325 files `DifferentialGeometry contributors`; 141 Yuan Liao; 132 Álvaro Begué (vendored Schoenflies); **91 `Bennett Chow, OpenAI`**; 85 Bennett Chow; 30 Jack McCarthy; 15 Yury Kudryashov. Git history is one author (Ziyang Qin) at this depth |
| vendored code | `External/`: DeGiorgi (Armstrong–Kempe, arXiv:2604.05984), Schoenflies (Begué), ClassificationOfSurfaces (McCorvie), RiemannMapping, CanonicalTopology(+Provenance), TauCeti; each with `MODIFICATIONS.md` |
| trust markers (word grep) | `axiom`: 6 hits, all in comments; `run_cmd`: 28 sites, unclassified; `native_decide`/`unsafe`/`implemented_by`/`@[extern]`/`partial def`/`macro_rules`/`elab`: 0; `sorry`: 3 hits, all in comments |
| open-result convention | stated in `External/Schoenflies/JordanClosed.lean`: "a missing result is named rather than `sorry`-ed" — carried as a Prop hypothesis or structure, discharged later. 151 modules named `*Frontier*` define `… : Prop` predicates of that kind; the surgery `Skeleton/PoincareEndgame.lean` is a chain of `…_holds` theorems discharging them |
| paper | none named in the README; the Perelman/Hamilton programme with Morgan–Tian / Kleiner–Lott as the natural references. Establish the map by content |

What this means for the plan: the statement rung and the no-supplier pass over
the headline route are the audit. A `Frontier` predicate that is never proved
unconditionally, or is proved only from another undischarged one, is a `sorry`
by another name, and the README's axiom claim cannot see it. Scale means the
route extractor, not the cone CSV, is what a reader walks.
