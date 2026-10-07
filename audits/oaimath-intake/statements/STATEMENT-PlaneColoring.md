# Statement check: PlaneColoring

- Challenge: `ComparatorChallenges/PlaneColoring.lean` (21 lines), config `ComparatorChallenges/PlaneColoring.json`
- Theorem: `OAI.Problem160.properColoring_seven`; solution module `OAI.Geometry.PlaneColoring.Main`;
  `definition_names: []`; permitted axioms `propext`, `Quot.sound`, `Classical.choice`.
- Scope note: `docs/158.md`
- Paper: `preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf`
  (fetched at commit adc7f124, 62 pages, text extracted with pypdf).

## 1. Reference statement (from the paper, written before reading the Lean)

Paper definition (Introduction, p. 1): a proper k-coloring of the Euclidean plane is a function
c : R^2 -> {1,...,k} with c(x) != c(y) whenever ||x - y|| = 1. No regularity on colour classes.

Headline, Theorem 1.1 (p. 2): the Euclidean plane has no proper five-coloring, even with arbitrary
colour classes; consequently 6 <= chi(R^2) <= 7.

The upper half (chi(R^2) <= 7) is NOT a new theorem of the paper. It is the classical
Isbell/Hadwiger hexagonal colouring, re-proved in one paragraph right after the deduction of
Theorem 1.1 (pp. 2-3): Voronoi hexagons of a triangular lattice with circumradius r = 2/5; colour
the centres by the seven cosets of the index-7 sublattice (2 - omega)(Z + Z omega); give each
point the colour of a hexagon containing it, boundary points to any incident hexagon. Within one
hexagon distances are <= 2r < 1; same-colour hexagons have centres >= sqrt(21) r apart, so points
in them are >= (sqrt(21) - 2) r > 1 apart. "This is a proper seven-coloring, including all
boundaries."

So the paper statement this challenge should match is:

  (U) There exists c : R^2 -> {1,...,7} such that for all x, y in R^2 with ||x - y|| = 1
      (Euclidean norm), c(x) != c(y).

Other main claims of the paper (for denominator (a)): Theorem 1.1 lower bound (no proper
5-colouring); Theorem 1.3 (transfer: proper k-colouring exists iff weak measurable k-colouring
exists, every k >= 1); Theorem 1.4 (no weak measurable 5-colouring).

## Scope note's own statement (docs/158.md)

"The formalized results prove that five colors do not suffice and that seven colors do suffice.
The lower bound applies to arbitrary colorings, with no measurability or continuity assumption;
the upper bound includes every boundary point of the coloring regions." It links two
comparator statements: "No proper five-coloring" -> `EuclideanFiveColor.lean`, and
"Proper seven-coloring" -> `PlaneColoring.lean`. The note states no gap: it presents the
seven-colouring as the companion upper bound, not as the paper's main result. It does not list
Theorems 1.3/1.4 as separate comparator statements (they are presumably internal to the
solution of the five-colour challenge; not checked here).

## 2. The Lean statement (read in full)

```lean
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k, ∀ x y : Plane, dist x y = 1 → c x ≠ c y
theorem properColoring_seven : ProperColoring 7 := by sorry
```

Answers to the caller's specific questions:
- Which graph: the full unit-distance graph on the plane (all of `EuclideanSpace ℝ (Fin 2)`),
  NOT a finite certificate graph. No finite vertex set, point list or edge list appears.
- Which points: every point of R^2 (domain of `c` is the whole `Plane`).
- Which distance: `dist` on `EuclideanSpace ℝ (Fin 2)` = `PiLp 2`, i.e. the Euclidean (L2)
  distance, exactly 1 (`= 1`, not `<=`, not a range).
- Colour count: 7 (`Fin 7`); `c` need not be surjective, so this is "at most 7 colours",
  which is the correct reading of chi <= 7.
- Non-5-colourability: NOT stated in this file. This challenge is only the existence of a
  7-colouring (the classical upper bound). The paper's headline lower bound is a separate
  challenge, `ComparatorChallenges/EuclideanFiveColor.lean`:
  `¬ ∃ coloring : ℂ → Fin 5, ProperColoring 5 coloring` with `‖p - q‖ = 1` on ℂ
  (also the whole plane, no finite graph). Read only for context; not audited here.

## 3. Clause table (reference (U) vs Lean)

| Reference clause | Lean clause | Class |
| --- | --- | --- |
| domain R^2, all points, no regularity | `c : Plane → Fin k`, `Plane = EuclideanSpace ℝ (Fin 2)`, arbitrary function | EXACT |
| colours {1,...,7} | `Fin 7` (labels 0..6; relabelling) | EXACT |
| ||x - y|| = 1, Euclidean norm | `dist x y = 1` on `PiLp 2` | EXACT |
| c(x) != c(y) | `c x ≠ c y` | EXACT |
| "exists a proper 7-coloring" | `∃ c, ...` with k := 7 | EXACT |
| "including all boundaries" (every point coloured) | total function on `Plane` | EXACT |
| hexagonal construction, r = 2/5, index-7 sublattice | none in statement (proof detail; the solution's `Seven.lean` uses a `triangular_lattice_cover`) | proof, not statement |

## 4. Denominators

(a) Paper main claims formalised: Theorem 1.1 lower bound -> EuclideanFiveColor (separate
challenge); Theorem 1.1 upper bound chi <= 7 (classical, re-proved in the paper) -> THIS
challenge. Theorems 1.3 and 1.4 have no comparator statement of their own (not located in
`ComparatorChallenges/`; searched by grep for `Problem160`/`PlaneColoring`, which hit only
docs/158.md and the two configs). For this challenge alone: 1 of 1 targeted claims (the
upper bound) is formalised; of the paper's headline results, it covers the minor, known half.
The scope note's description ("seven colors do suffice ... includes every boundary point")
matches.

(b) Lean clauses matching the paper: 5 of 5 statement clauses EXACT; no STRONGER, WEAKER,
DIFFERENT or NOT LOCATED clauses.

## 5. Traps checked

- Vacuity: `ProperColoring 7` requires an actual function on all of R^2; not trivially true
  (with k = 1 it would be false, since unit pairs exist). `Fin 7` is nonempty. No `0 < k`
  guard issues.
- Metric: `EuclideanSpace` (not `Fin 2 → ℝ`, which would be the sup metric and change the
  problem). Correct L2 distance.
- `=` vs `≤`: distance exactly 1, as in the paper.
- Definition fixity: `definition_names` is empty, so `ProperColoring`/`Plane` are checked by
  the comparator as part of the challenge statement against the solution's (the solution's
  `Basic.lean` defines the same names at lines 11 and 26; not compared token-by-token here).
- `opaque`, `axiom`, `implemented_by`, `native_decide`, `unsafe`: none in the challenge file
  (grep). Axiom whitelist standard.
- Measurability: neither required nor excluded; the paper's statement has none either.
- Name: "Problem160" vs docs 158 is a numbering label only.

## 6. Verdict

PAIRED (compared against the paper's own seven-colouring paragraph, pp. 2-3). EXACT.

Deviation to flag: none at the statement level. The important scope fact is that this
challenge is the classical upper bound chi(R^2) <= 7 on the whole plane, not the paper's
headline result; it does not state non-5-colourability, and it involves no finite
certificate graph. The headline lower bound lives in `EuclideanFiveColor.lean`.
