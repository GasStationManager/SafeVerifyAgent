# Trust surface and metaprogramming: `GapCVP.lean`

Artifact `openai/ten-proofs` @ `94bc0feb`, `/home/user/ten-proofs/GapCVP.lean` (130,430
lines, one file, `import Mathlib` only). Read-only; not built; `#print axioms` not run; no
independent kernel checker ran. The question this file answers is whether anything in the
source lets a value into the proof that the kernel does not check, or makes a statement mean
something other than what it says. Counts are from greps over the whole file. The file has
**no comments at all** (0 `--`, 0 `/-`), so the comment-stripped scan and the raw scan are
the same scan.

## Verdict

**No trust-relevant metaprogramming.** The only user metaprogramming is 23 tactic
`macro`s. Each expands to ordinary tactics (`simp`, `congr`, `funext`, `fin_cases`, `rfl`,
and in one case Mathlib's `rw!`), so everything they produce is a proof term the kernel
checks. No declaration is added outside elaboration, no option is set, and there is no
native evaluation. The classical `Decidable` instances only fix how `Prop`s are packaged as
`Bool`s and are unpacked by `decide_eq_true_eq`, which holds for every instance. Every
`decide` used as a tactic closes a small finite goal. No large numeral appears anywhere: the
biggest literal in the file is `2000`, an instance priority.

## 1. Inventory

| construct | count | note |
|---|---|---|
| `axiom`, `sorry`, `opaque`, `native_decide`, `ofReduceBool`, `unsafe`, `implemented_by`, `@[extern`, `elab`, `syntax`, `macro_rules`, `run_cmd`, `initialize`, `set_option`, `Lean.` (meta API), `debug.` | **0 each** | |
| `macro "<name>" … : tactic` | 23 | §2 |
| `attribute [local instance] Classical.propDecidable` | **11** (the brief said 12; recount: lines 63522, 65770, 72237, 80660, 103025, 106530, 107109, 107558, 109352, 109807, 115758) | §3 |
| `attribute [-instance] Classical.propDecidable in` | 2 (109374, 109387) | §3 |
| `@decide … (Classical.propDecidable _)` Bool definitions | 112 occurrences in 101 declarations | §4 |
| word `decide` | 655 occurrences on 653 lines: 112 `@decide`, 543 bare. Of the bare ones, 34 are the **tactic** (25 `by decide`, 3 `<;> decide`, 6 stand-alone); the rest are term-level `decide (p)` inside definitions and specifications | §5 |
| `rfl` | 794 lines (819 occurrences) | §5 |
| `omega` | 914 lines (915 occurrences) | decision procedure; produces checked terms |
| `@[irreducible]` | 208 | elaborator-only unfolding control; the kernel ignores it |
| `@[simp]` | 685 | |
| `rw!` (Mathlib `DepRewrite`) | 11, all inside `original_source_preservation_step_tac` | produces ordinary `Eq.mpr`/cast terms |
| simprocs named explicitly | `Nat.reduceAdd` ×2 (80203, 128994) | core simproc; proof by kernel `Nat` literal arithmetic |
| `variable` lines | 42 (56277–73612) | implicit types and instance arguments only; see `ROUTE-MAP.md` §1 |

## 2. The 23 tactic macros: what they prove

All 23 have the same skeleton. Line 7 is the parametrised template; the other 22 inline it
with a fixed list of definitions:

```
simp [<machine>, <configuration>, <peek/pop/push/goto helpers>, <statement defs>,
      Turing.haltList, Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux]
  <;> try { congr 2; funext stack; fin_cases stack <;> simp [Function.update] }
  <;> try rfl
```

The one variant is `original_source_preservation_step_tac` (37877). It uses
`simp +instances [...]` and then `first | rfl | (congr 2; first | exact
originalSourcePreserving_embedded_haltStacks _ _ | rw! (castMode := .all) [← sourceStacks_update_*, …] | …)`,
a fixed menu of stack-update lemmas proved in the file.

**What they prove.** Each proves one-step transition equations of a specific, concrete TM2
program, `M.step cfg = some cfg'` (or `= none` at halt), with the configuration's stacks
given as symbolic lists. The `simp` unfolds Mathlib's `FinTM2.step`/`TM2.step`/`stepAux` on
the program's statement. The `funext stack; fin_cases stack` branch proves equality of the
stack-assignment functions, which are `Function.update` chains over a finite stack index
type, pointwise. Uses read:

- `payload_prefix_delimiter` (17961): `payloadDecoderMachine.step (payloadConfiguration 0
  (false :: input) …) = some (payloadConfiguration 1 input …)` by
  `compact_machine_step_tac [payloadDecoderMachine, payloadConfiguration]`, plus its two
  neighbours `payload_prefix_missing_delimiter` and the theorem above it.
- `delimitedCompare_firstPrefix_true` (23313): one step of `delimitedPairComparisonMachine`
  moving a `true` from the input to the counter and source stacks, by
  `delimited_compare_step_tac`.
- `pivot_scan_false` / `pivot_scan_true` (79503 / 79510): one step of
  `binaryGaussianPivotMachine` on a `false`/`true` input bit, by
  `binary_gaussian_pivot_step_tac`.

These per-step lemmas are chained by `TraceGolf.oneStep`/`rebound` (17–33) and
`EvalsToInTime.trans` into the runs that inhabit `BitTM f`. A wrong step lemma cannot be
proved by these tactics, because they only rewrite with definitions and close by `rfl`. A
macro that failed on some goal would make the build fail rather than produce a false lemma.

| macro | line | uses |
|---|---|---|
| `compact_machine_step_tac [defs]` | 7 | 88 |
| `prefix_writer_step_tac` | 17320 | 6 |
| `natural_binary_writer_step_tac` | 22478 | 11 |
| `delimited_compare_step_tac` | 23285 | 36 |
| `natural_compare_step_tac` | 25478 | 11 |
| `polynomial_row_marker_step_tac` | 27493 | 19 |
| `flat_literal_record_step_tac` | 30755 | 22 |
| `unary_pair_step_tac` | 32235 | 37 |
| `source_pair_prefix_step_tac` | 33541 | 17 |
| `formula_preservation_step_tac` | 34124 | 6 |
| `source_marker_step_tac` | 34579 | 7 |
| `radius_marker_tail_step_tac` | 34897 | 6 |
| `rational_radius_step_tac` | 35143 | 20 |
| `source_flat_atomic_step_tac` | 36081 | 18 |
| `source_grid_index_step_tac` | 36858 | 15 |
| `original_source_preservation_step_tac` (`simp +instances`, `rw!`) | 37877 | 10 |
| `flat_adjacent_record_step_tac` | 38533 | 21 |
| `capped_unary_minimum_step_tac` | 39666 | 14 |
| `source_integer_multiplication_step_tac` | 42752 | 24 |
| `source_unary_division_step_tac` | 43760 | 30 |
| `preserving_xor_step_tac` | 71211 | 8 |
| `binary_gaussian_xor_step_tac` | 71772 | 6 |
| `binary_gaussian_pivot_step_tac` | 79492 | 7 |

Total uses: 439 (grep count of each name, minus its definition).

## 3. `Classical.propDecidable` as a local instance, and its two removals

The 11 `attribute [local instance] Classical.propDecidable` lines open sections that
manipulate field elements of `GaloisField 2 e`, finsets and matrix entries. Examples: a
`Fintype (GaloisField 2 degree)` instance at 63522; the physical-word field at 103025; the
refinement-row bookkeeping at 109352. With the local instance, any `if`/`decide` on an
arbitrary `Prop` elaborates.

It matters only in two ways, and neither is soundness:

1. **Meaning of statements.** A `Bool` defined as `decide p` with a classical instance is
   `true` exactly when `p` holds. Every unpacking in the file goes through
   `decide_eq_true_eq` / `decide_eq_false`, which are instance-generic. So a statement of the
   form `f x = [decide p]` means the same thing whichever instance was elaborated.
2. **Agreement with what a machine computes.** A `BitTM f` fixes `f` as a function, and the
   machine must output `f x` on every input. If `f` were defined through a classical
   `decide`, the machine-correctness proof would have to establish the equation
   propositionally, which is no weaker. Classical instances make proofs harder here, not
   easier.

The two `attribute [-instance] Classical.propDecidable in` (109374, 109387) **remove** the
classical instance for two `Bool` definitions inside a classical section:
`physicalRefinementSourceLocalTagInRange` and `physicalRefinementSourceFieldMatch`. Both
`decide` `Nat` inequalities and `Nat` equalities. Removing the instance makes them use the
structural `Nat.decLe`/`Nat.decEq` instances, so the cell-check machines can be proved
correct by unfolding. This is a convenience for proofs and has no trust effect.

## 4. The `@decide … (Classical.propDecidable _)` pattern: roles

There are 112 occurrences in 101 declarations (enumerated by script; list reproducible with
the cone script's declaration table). Every one defines a `Bool` from a `Prop` that is
generally undecidable (it quantifies over ℝ, over all functions `ℕ → Bool`, or over all
languages). They fall into these roles:

| role | declarations (line) |
|---|---|
| complexity classes and hardness, **the headline's own predicates** | `IsNP` 638, `PolynomialTimeClosedUnderComposition` 653, `NPHard` 660, `NPHardPromise` 682, `Comparator.IsNPHardPromise` 130210 |
| languages and promise problems (yes/no sides) | `threeSATLanguage` 664, `paperOriginalThreeSATLanguage` 88578, `gapCVP400Promise` 62138, `integerTargetGapCVP400Promise` 126046, `binaryNearestCodewordPromise` 126186, `binarySyndromeDecodingPromise` 126231, `finitePGapCVPPromise` 87345, Comparator copies 129869–130166 |
| instance predicates | `gapCVPWellFormed` 302, `gapYES` 690, `gapYES400`/`gapNO400` 62100/62106, `HasIntegerTarget` 126042, `Core.GapCVPInstance.IsYes`/`IsNo` 78/82, `Core.SquaredYes`/`SquaredNoAt` 101/106, Comparator `wellFormed`/`hasIntegerTarget`/`gapYES400`/`gapNO400` 129810–129838 |
| SAT semantics | `literalSatisfied`/`clauseSatisfied`/`threeCNFSatisfiable`/`clauseHasDistinctVariables` 259–271, `CL.satisfiesClause`/`satisfiesFormula` 1800/1805, `ThreeCNFReduction.satisfies`/`allDistinct` 2277/2296, `Core.Clause.Satisfied`, `Formula.Satisfied`/`Satisfiable` 62243–62255, `Clause.LocalSatisfied` 64408 |
| linear-algebra predicates | `BinaryAffineSystem.Solves`/`InLattice` 63739/63744, `concreteSATFieldChecks` 64768, `EffectiveBinaryGaussian.System.Satisfies`/`InKernel`/`PrefixNormal` 62349/75957/70977 |
| Cook–Levin invariants (≈ 60 declarations in `CL*`, 1878–16100) | `ValidTrace` 1878, `GuessInvariant` 3407, `TimedGuessInvariant` 3469, the `…Allowed`/`…Coherent`/`…Windows` window predicates, `PaddedAcceptancePhaseAllowed` 16100 |
| two machine-layer invariants | `PolynomiallyBoundedFoldStates` 29312, `CorrectFlatAnnotatedBundledSourceComparison` 42492 |

**Consequence for the headline.** `IsNPHardPromise gapCVP400Promise` is the `Bool` equation
`… = true`. It is equivalent to the `Prop` `∀ L, IsNP L → Nonempty (PromiseReduction L
gapCVP400Promise)` by `decide_eq_true_eq`, and `IsNP L` in turn unfolds to the existential.
So the `Bool` packaging does not change what is claimed. Whether the `Bool` packaging in the
challenge file is the same object is for `STATEMENT.md`.

## 5. `decide`, `rfl`, `norm_num` as computation

- **Tactic `decide` (34 sites).** All 34 were inspected. They decide `(2 : ZMod 2) = 0`
  (62386, 76533, 89271), `0 < (2:ℕ)` (106581, 107694), Bool/`ZMod 2` truth tables after
  `cases` (62852, 62857, 62863, 116096, 117066), `Fin 2` cases of the canonical syndrome NO
  instance (126318–126348), `if`-conditions on literal `Nat`s in record decoders
  (100126–100183, 129368–129421), the canonical YES instance's `0 < 1` (17555), the
  comparison outcomes `.less/.equal/.greater` (25663–25677), a padding-variable disequality
  `2 ≠ 3` (2363), coefficient zero tests (81592), and short `Nat` length identities after a
  `simp` (61078). **None is a large computation.**
- **Term-level `decide (p)`** (≈ 510): this is data, not proof. It writes the `Bool` a
  specification or a machine output is compared with, e.g. the cell checks
  `[decide (row < boundary) && decide (H.check row col = 1)]` (125900–126010). It is
  evaluated only when a proof unfolds it.
- **`rfl` (794 lines).** Sampled: definitional identities between encoders
  (`encodeInstance_eq_original`, 130255; `structuralWholeCNFWord_eq_encodedTableau`, 22899),
  structure re-packing (`toOriginal_ofOriginal`, 130222), dimension unfoldings
  (`paperVariableArityPhysicalFormulaSystem_dimension`, 92379), and `_output` lemmas of
  computer packs (88563). All are symbolic. No `rfl` closes a goal over concrete large data;
  the file contains no large numerals to compute with.
- **`norm_num` with a large intermediate.** `80^100 < 100^99` (74112) is the only
  big-number fact on the route. I recomputed it independently: 191 digits against 199 digits.
  It is true.

## 6. What this does not cover

- The kernel itself. No independent checker (nanoda, con-leche, lean4export replay) ran, for
  the same reason nothing was built (disk).
- `Mathlib` version drift: TM2 definitions were read in v4.33.1, and the artifact pins
  v4.32.0.
- Recall control: no seeded-finding positive control was run for the greps. The greps are
  literal-token scans of a comment-free file, and each zero was cross-checked by a second
  spelling (`axiom` with and without a leading anchor, `native` as a prefix, `Lean.` for
  meta-API use).
