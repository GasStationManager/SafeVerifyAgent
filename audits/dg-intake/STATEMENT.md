# Statement dossier: `DifferentialGeometry.Topology.poincare_conjecture`

- module: `DifferentialGeometry.Topology.ThreeManifold.Poincare` — `DifferentialGeometry/Topology/ThreeManifold/Poincare.lean:12`
- kind: `theorem`
- source roots searched: project (`/home/user/differential-geometry` @ 7a48598d3510), mathlib (`/home/user/mathlib-src` @ 0df444a360ea), lean (`/root/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`)
- Lean rung: not run: the project is not built (no `.lake/build/lib/lean/DifferentialGeometry/Topology/ThreeManifold/Poincare.olean`); run `lake build DifferentialGeometry.Topology.ThreeManifold.Poincare` (and `lake exe cache get` for Mathlib) first

Resolution below is by SOURCE TEXT (grep plus namespace tracking), not elaboration: every resolved name carries a `root:path:line` to check with `sed -n`, and more than one hit is printed as ambiguity rather than resolved.

## 1. Source text

```lean
theorem poincare_conjecture
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨C, hC⟩ := PiecewiseLinear.exists_isManifold_three (M := M)
  let := C
  let : IsManifold (𝓡 3) ∞ M := hC
  obtain ⟨f⟩ := PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds M
  exact ⟨f.toHomeomorph⟩
```

## 2. Hypotheses and instance arguments

| # | binder | names | type |
|---|---|---|---|
| 1 | () explicit | M | `Type u` |
| 2 | [] instance | — | `TopologicalSpace M` |
| 3 | [] instance | — | `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` |
| 4 | [] instance | — | `T2Space M` |
| 5 | [] instance | — | `CompactSpace M` |
| 6 | [] instance | — | `SimplyConnectedSpace M` |

**Conclusion:** `Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)`

## 3. Scope at the declaration

- namespace: `DifferentialGeometry.Topology`
- open: `Manifold`, `ContDiff`
- `variable`s in scope (they become binders if used): none
- universe parameters: declared `u`; used in the signature `u`
- `set_option`s in force: 
  - file line 4: `set_option autoImplicit false`
  - project-wide, lakefile.toml [leanOptions]: pp.unicode.fun = true
  - project-wide, lakefile.toml [leanOptions]: autoImplicit = false
  - project-wide, lakefile.toml [leanOptions]: maxSynthPendingDepth = 3
  - project-wide, lakefile.toml [leanOptions]: weak.linter.mathlibStandardSet = true
  - project-wide, lakefile.toml [leanOptions]: linter.style.header = false
  - project-wide, lakefile.toml [leanOptions]: linter.style.longLine = false

## 4. What the signature's names resolve to

One level down: each declaration's own binders, `extends`, fields or body. Follow a field's type by hand, or run the Lean rung.

### `TopologicalSpace`

- `class TopologicalSpace` — mathlib:Mathlib/Topology/Defs/Basic.lean:73
  - doc: A topology on `X`.
  - binders: `(X : Type u)`
  - field `IsOpen` : `Set X → Prop`
  - field `isOpen_univ` : `IsOpen univ`
  - field `isOpen_inter` : `∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)`
  - field `isOpen_sUnion` : `∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)`

### `ChartedSpace`

- `class ChartedSpace` — mathlib:Mathlib/Geometry/Manifold/ChartedSpace.lean:139
  - doc: A charted space is a topological space endowed with an atlas, i.e., a set of local homeomorphisms taking values in a model space `H`, called charts, such that the domains of the charts cover the whole space. We express the covering property by choosing for each `x` a member `chartAt x` of the atlas containing `x` in its source: in the smooth case, this is convenient to construct the tangent bundle in an efficient way. The model space is written as an explicit parameter as there can be several model spaces for a given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen sometimes as a real manifold over `ℝ^(2n)`.
  - binders: `(H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M]`
  - field `atlas` : `Set (OpenPartialHomeomorph M H)`
  - field `chartAt` : `M → OpenPartialHomeomorph M H`
  - field `mem_chart_source` : `∀ x, x ∈ (chartAt x).source`
  - field `chart_mem_atlas` : `∀ x, chartAt x ∈ atlas`

### `EuclideanSpace`

- `abbrev EuclideanSpace` — mathlib:Mathlib/Analysis/InnerProductSpace/PiL2.lean:113
  - doc: The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building elements of this type, analogous to `![x, y, ...]` notation.
  - binders: `(𝕜 : Type*) (n : Type*)`
  - type: `Type _`
  - body: `PiLp 2 fun _ : n => 𝕜`

### `ℝ`

- notation: `notation "ℝ" => Real` — mathlib:Mathlib/Data/Real/Basic.lean:41 → `Real`
- `structure Real` — mathlib:Mathlib/Data/Real/Basic.lean:36
  - doc: The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational numbers.
  - field `cauchy` : `CauSeq.Completion.Cauchy (abs : ℚ → ℚ)`

### `Fin`

- `structure Fin` — lean:Init/Prelude.lean:2324
  - doc: Natural numbers less than some upper bound. In particular, a `Fin n` is a natural number `i` with the constraint that `i < n`. It is the canonical type with `n` elements.
  - binders: `(n : Nat)`
  - field `val` : `Nat`
  - field `isLt` : `LT.lt val n`

### `T2Space`

- `class T2Space` — mathlib:Mathlib/Topology/Separation/Hausdorff.lean:84
  - doc: A T₂ space, also known as a Hausdorff space, is one in which for every `x ≠ y` there exists disjoint open sets around `x` and `y`. This is the most widely used of the separation axioms.
  - binders: `(X : Type u) [TopologicalSpace X]`
  - type: `Prop`
  - field `t2` : `Pairwise fun x y => ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v`

### `CompactSpace`

- `class CompactSpace` — mathlib:Mathlib/Topology/Defs/Filter.lean:283
  - doc: Type class for compact spaces. Separation is sometimes included in the definition, especially in the French literature, but we do not include it here.
  - type: `Prop`
  - prefixed by: `variable (X) in`
  - binders come from `variable`s in scope: `variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]`; `variable (X)`; `variable {X}`
  - field `isCompact_univ` : `IsCompact (Set.univ : Set X)`

### `SimplyConnectedSpace`

- `class SimplyConnectedSpace` — mathlib:Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:40
  - doc: A simply connected space is one whose fundamental groupoid is equivalent to `Discrete Unit`
  - binders: `(X : Type*) [TopologicalSpace X]`
  - type: `Prop`
  - field `equiv_unit` : `Nonempty (FundamentalGroupoid X ≌ Discrete Unit)`

### `Nonempty`

- `class inductive Nonempty` — lean:Init/Prelude.lean:792
  - doc: `Nonempty α` is a typeclass that says that `α` is not an empty type, that is, there exists an element in the type. It differs from `Inhabited α` in that `Nonempty α` is a `Prop`, which means that it does not actually carry an element of `α`, only a proof that *there exists* such an element. Given `Nonempty α`, you can construct an element of `α` *nonconstructively* using `Classical.choice`.
  - binders: `(α : Sort u)`
  - type: `Prop`

### `≃ₜ`

- notation: `infixl:25 " ≃ₜ " => Homeomorph` — mathlib:Mathlib/Topology/Homeomorph/Defs.lean:53 → `Homeomorph`
- `structure Homeomorph` — mathlib:Mathlib/Topology/Homeomorph/Defs.lean:43
  - doc: Homeomorphism between `X` and `Y`, also called topological isomorphism
  - binders: `(X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]`
  - extends: `X ≃ Y`
  - field `continuous_toFun` : `Continuous toFun := by first | fun_prop | eta_expand; dsimp; fun_prop | skip`
  - field `continuous_invFun` : `Continuous invFun := by first | fun_prop | eta_expand; dsimp; fun_prop | skip`

### `Metric.sphere`

- `def Metric.sphere` — mathlib:Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:432
  - doc: `sphere x ε` is the set of all points `y` with `dist y x = ε`
  - binders: `(x : α) (ε : ℝ)`
  - body: `{ y | dist y x = ε }`

## 5. Instances derived from the signature's classes

Instances that turn one class into another on the same carrier and need nothing beyond the class's own parameters, found by SOURCE GREP (followed 2 step(s)). Absence here is not absence in Lean.

| from | step | where | instance |
|---|---|---|---|
| `T2Space` | T2Space ⟹ T1Space (depth 1) | mathlib:Mathlib/Topology/Separation/Hausdorff.lean:115 | `instance (priority := 100) T2Space.t1Space [T2Space X] : T1Space X := …` |
| `T2Space` | T2Space ⟹ R1Space (depth 1) | mathlib:Mathlib/Topology/Separation/Hausdorff.lean:120 | `instance (priority := 100) T2Space.r1Space [T2Space X] : R1Space X := …` |
| `T2Space` | T2Space ⟹ QuasiSeparatedSpace (depth 1) | mathlib:Mathlib/Topology/QuasiSeparated.lean:110 | `instance (priority := 100) T2Space.to_quasiSeparatedSpace [T2Space α] : QuasiSeparatedSpace α := …` |
| `T2Space` | T1Space ⟹ R0Space (depth 2) | mathlib:Mathlib/Topology/Separation/Basic.lean:500 | `instance (priority := 100) [T1Space X] : R0Space X := …` |
| `T2Space` | T1Space ⟹ T0Space (depth 2) | mathlib:Mathlib/Topology/Separation/Basic.lean:562 | `instance (priority := 100) T1Space.t0Space [T1Space X] : T0Space X := …` |
| `T2Space` | T1Space ⟹ JacobsonSpace (depth 2) | mathlib:Mathlib/Topology/JacobsonSpace.lean:168 | `instance (priority := 100) [T1Space X] : JacobsonSpace X := …` |
| `T2Space` | R1Space ⟹ QuasiSober (depth 2) | mathlib:Mathlib/Topology/Sober.lean:247 | `instance (priority := 100) R1Space.quasiSober [R1Space α] : QuasiSober α where …` |
| `T2Space` | R1Space ⟹ R0Space (depth 2) | mathlib:Mathlib/Topology/Separation/Basic.lean:916 | `instance (priority := 100) : R0Space X where …` |
| `SimplyConnectedSpace` | SimplyConnectedSpace ⟹ PathConnectedSpace (depth 1) | mathlib:Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:73 | `instance (priority := 100) : PathConnectedSpace X := …` |
| `SimplyConnectedSpace` | PathConnectedSpace ⟹ ConnectedSpace (depth 2) | mathlib:Mathlib/Topology/Connected/PathConnected.lean:687 | `instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] : …` |

## 6. Lean rung

not run: the project is not built (no `.lake/build/lib/lean/DifferentialGeometry/Topology/ThreeManifold/Poincare.olean`); run `lake build DifferentialGeometry.Topology.ThreeManifold.Poincare` (and `lake exe cache get` for Mathlib) first

## 7. Reference pairing

Reference: `audits/dg-intake/REFERENCE-poincare.md` — written before reading the Lean. Pairing is by word overlap after camel-case splitting, notation expansion and a small synonym table; a pair is a pointer for a human, not a verdict. **The unmatched lists are the output.**

| ref | reference clause | Lean clause(s) | shared words | note |
|---|---|---|---|---|
| H1 | M is a topological 3-manifold: every point has a neighbourhood homeomorphic to an open subset of ℝ³. | L2 `[TopologicalSpace M]` | topological |  |
| H1 | M is a topological 3-manifold: every point has a neighbourhood homeomorphic to an open subset of ℝ³. | L3 `[ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]` | 3, charted |  |
| H2 | M is Hausdorff. | L4 `[T2Space M]` | t2 |  |
| H3 | M is compact. | L5 `[CompactSpace M]` | compact |  |
| H4 | M is without boundary (a closed manifold is compact and boundaryless). | **none** | | |
| H5 | M is connected. | **none** | | |
| H6 | M is simply connected: its fundamental group is trivial. | L6 `[SimplyConnectedSpace M]` | connected, simply |  |
| C1 | M is homeomorphic to the 3-sphere S³. | L-concl `Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)` | homeomorph, sphere | numerals differ: reference ['3'], Lean ['0', '1', '4'] — check the dimension convention |

### Reference clauses with no Lean counterpart

- **H4** M is without boundary (a closed manifold is compact and boundaryless).
  - shares charted with L3 `[ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]`, which paired elsewhere
  - shares compact with L5 `[CompactSpace M]`, which paired elsewhere
- **H5** M is connected.
  - shares connected with L6 `[SimplyConnectedSpace M]`, which paired elsewhere
  - possibly implied: SimplyConnectedSpace ⟹ PathConnectedSpace (mathlib:Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:73, depth 1; source grep, unverified)
  - possibly implied: PathConnectedSpace ⟹ ConnectedSpace (mathlib:Mathlib/Topology/Connected/PathConnected.lean:687, depth 2; source grep, unverified)

### Lean clauses with no reference counterpart

- **L1** `(M : Type u)` — an assumption the reference did not state, or bookkeeping (a carrier type, a structure the reference takes for granted)
