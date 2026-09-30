# Statement rung: `Challenge.lean` against Gonthier's `realplane.v` / `fourcolor.v`

Reference: `math-comp/fourcolor` at `c1d6b1cd5288bea4b067aac13cdde3c18dffe018` (the commit the
port's README names), files `theories/proof/realplane.v` (177 lines), `theories/proof/fourcolor.v`
(37 lines), `theories/reals/real.v` (242 lines). Candidate: `Challenge.lean` (220 lines) at
`20fa345`; the block between `BEGIN SYNCED DEFINITIONS` and `END SYNCED DEFINITIONS` is
byte-identical to the one in `FourColor/RealPlane.lean` (153 lines; my own diff, not the port's
`check_challenge_sync.py`), which is what `Solution.lean` proves the theorem about.

Verdict: **PAIRED, EXACT up to the one declared specialisation** (an arbitrary model of Coq's
axiomatised reals becomes Mathlib's `ℝ`), definition by definition, in the same order.

## Definition by definition

| Coq (`realplane.v`, section `Variable R : Real.structure`) | Lean (`FourColor.RealPlane`) | match |
|---|---|---|
| `Inductive point := Point (x y : Real.val R)` | `structure Point where x y : ℝ` | exact |
| `region := point -> Prop`; `map := point -> region` | `abbrev Region := Point → Prop`; `abbrev Map := Point → Region` | exact |
| `interval := Interval (x y)`; `rectangle := Rectangle (hspan vspan)` | `structure Interval (lo hi : ℝ)`; `structure Rectangle (hspan vspan)` | exact |
| `in_interval s t := Real.lt x t /\ Real.lt t y` | `s.lo < t ∧ t < s.hi` | exact given `lt` (below) |
| `in_rectangle rr z := in_interval hspan x /\ in_interval vspan y` | same | exact |
| `union`, `intersect`, `nonempty`, `subregion`, `meet` | `union`, `intersect`, `NonemptyRegion`, `Subregion`, `Meet` | exact |
| `plain_map m`: `map_sym : m z1 z2 -> m z2 z1`; `map_trans : m z1 z2 -> subregion (m z2) (m z1)` | `structure PlainMap (m) : Prop` with the same two fields (`{z1 z2}` implicit) | exact |
| `cover m z := m z z`; `submap m1 m2 := forall z, subregion (m1 z) (m2 z)` | same | exact |
| `at_most_regions n m := exists f, forall z, cover m z -> exists2 i : nat, Peano.lt i n & m (f i) z` | `∃ f : ℕ → Point, ∀ z, cover m z → ∃ i : ℕ, i < n ∧ m (f i) z` | exact (`exists2 … & …` is `∃ …, … ∧ …`) |
| `open r := forall z, r z -> exists2 u, in_rectangle u z & subregion (in_rectangle u) r` | `Open` | exact |
| `closure r z := forall u, open u -> u z -> meet r u` | `closure` | exact |
| `connected r := forall u v, open u -> open v -> subregion r (union u v) -> meet u r -> meet v r -> meet u v` | `Connected` | exact |
| `simple_map m` = plain + `open (m z)` + `connected (m z)` | `structure SimpleMap (m) extends PlainMap m` + the two fields | exact |
| `finite_simple_map` | `FiniteSimpleMap` | exact (not used by the headline) |
| `border m z1 z2 := intersect (closure (m z1)) (closure (m z2))` | `border` | exact |
| `corner_map m z z1 z2 := m z1 z2 /\ closure (m z1) z` | `cornerMap` | exact |
| `not_corner m z := at_most_regions 2 (corner_map m z)` | `notCorner` | exact |
| `adjacent m z1 z2 := ~ m z1 z2 /\ meet (not_corner m) (border m z1 z2)` | `Adjacent` | exact |
| `coloring m k`: `plain_map k`; `subregion (cover k) (cover m)`; `submap m k`; `adjacent m z1 z2 -> ~ k z1 z2` | `structure Coloring (m k) extends PlainMap k` + the three fields | exact |
| `colorable_with n m := exists2 k, coloring m k & at_most_regions n k` | `∃ k, Coloring m k ∧ AtMostRegions n k` | exact |
| `Theorem four_color m : simple_map m -> colorable_with 4 m` (section `Variable Rmodel : Real.model`, `R := model_structure Rmodel`) | `theorem four_color (m : Map) (h : SimpleMap m) : ColorableWith 4 m` | exact, at `R := ℝ` |

## The one deviation, and why it is not a weakening

Coq's theorem is universally quantified over `Rmodel : Real.model`, a `Real.structure`
(`val`, `le`, `sup`, `add`, `zero`, `opp`, `mul`, `one`, `inv`) with `Real.axioms` (order
reflexive and transitive, sup axioms, ordered-field axioms). The only field the statement
uses is `le`, through `Notation lt x y := (~ le y x)` — `real.v` says outright "The 'lt'
notation presupposes 'le' is total". The Lean statement fixes the model to Mathlib's `ℝ` and
writes `<`. On a linear order `x < y ↔ ¬ y ≤ x` (`not_le`), so `inInterval` is the Coq
definition at that model. Fixing the model is a SPECIALISATION of Coq's `∀ Rmodel`; the
port's README argues equivalence via `realcategorical.v` (every model is isomorphic to every
other, and the definitions use only the order). For the informal claim "every simple map of
the real plane is 4-colourable", the specialised statement IS the claim; what is lost is only
Coq's extra generality over models, which no reader of the theorem wants.

`Challenge.lean` imports one Mathlib file (`Mathlib.Basic.Real.Basic`) and uses from it only
`ℝ` and `<` (`Real.lt` is an `irreducible_def`, the `LT ℝ` instance at line 266 of that file).
No Mathlib topology is used; `Open`, `closure`, `Connected` are the Coq rectangle definitions.

## Things checked that a statement diff can miss

- The theorem `Solution.lean` proves has the same name (`FourColor.RealPlane.four_color`) and
  binder shape as the `sorry`-ed one in `Challenge.lean`, and `comparator.json` names it.
- No definition in the synced block is a `class`, `instance`, `axiom`, `opaque` or carries an
  `autoParam`/`optParam`; `Region`/`Map` are `abbrev`s, the rest `def`/`structure`.
- The Lean `PlainMap`/`Coloring` fields bind `z1 z2` implicitly where Coq binds them
  explicitly; the propositions are the same.
- Not checked here: `#print axioms` of the unconditional `four_color` (needs the full
  build; Palomar's comparator did it at registration, trust `high`).
