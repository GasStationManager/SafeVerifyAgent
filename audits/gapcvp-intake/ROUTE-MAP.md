# Route map: `GapCVP.Comparator.gapCVP400IsNPHard`

Artifact `openai/ten-proofs` @ `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`, file
`/home/user/ten-proofs/GapCVP.lean` (130,430 lines), Lean/Mathlib v4.32.0. Read-only;
**nothing was compiled**, `#print axioms` was **not** run, no external checker ran. Every
`file:line` below is a line of `GapCVP.lean` and was read with `sed -n` in this pass unless
marked *(name only)*. Paper = Chapter 7 of the ten-proofs PDF (local text
`paper-ch7-cvp.txt`). The statement rung (`ComparatorChallenges/H_GapCVP.lean` vs the
`Comparator` namespace) is a separate deliverable (`STATEMENT.md`) and is not repeated here.

## 0. What did not run

- No build: the no-supplier conclusion below is "supplied by a constructing `def`/`theorem`
  in the source" — it becomes a kernel fact only when the file compiles. The repository's
  own `formalization.yaml` claims `sorry_count: 0` and axioms
  `[propext, Classical.choice, Quot.sound]`; not re-checked.
- The algebraic-reconstruction core (paper §4–§5, Lean lines ~66,000–74,400) and the
  tableau compiler (Lean ~3,900–17,200) were located and their interface statements read;
  their bodies were not read line by line (§4 below gives the denominators).

## 1. No-supplier verdict (the headline question)

**Every assumption-shaped object on the route is supplied by a construction in the file.**

- `polynomialTimeClosedUnderComposition` is a **theorem**, `GapCVP.lean:1736`, proved
  from the explicit two-phase TM2 construction `TMComposition.machine` (`:1065`) /
  `computableInPolyTimeOfSeam` (`:1692`) / `computableInPolyTime` (`:1727`). The
  `PolynomialTimeClosedUnderComposition` it inhabits is a `Bool` `def` (`:653`) of the
  form `@decide (∀ f g, Nonempty (BitTM f) → Nonempty (BitTM g) → Nonempty (BitTM (g ∘ f)))
  (Classical.propDecidable _)`. It is consumed as an explicit argument (`closed`) by
  `PromiseReduction.comp` (`:1760`) and `nphardPromise_of_nphard_of_promiseReduction`
  (`:1772`), and every one of the four call sites (`:126156`, `:127327`, `:128278`,
  `:129733`) passes the theorem itself.
- Comment-stripped greps over the whole file (it has **zero** comments: 0 `--`, 0 `/-`):
  0 `axiom`, 0 `sorry`, 0 `opaque`, 0 `native_decide`, 0 `unsafe`, 0 `implemented_by`,
  0 `@[extern`, 0 `set_option`, 0 `elab`, 0 `syntax`, 0 `macro_rules`, 0 `run_cmd`, 0
  `ofReduceBool`, 0 `Lean.` (no metaprogramming API use at all). The headline
  `gapCVP400IsNPHard : IsNPHardPromise gapCVP400Promise` (`:130398`) has no hypotheses.
  So an unsupplied object could only enter as an axiom, and there is no axiom declaration
  in the source.
- 42 `variable` lines (`:56277–56282`, `:63657–73612`): all are implicit types/indices or
  instance arguments (`[Field K] [Algebra (RatFunc K) E] [FiniteDimensional …]
  [Algebra.IsSeparable …]`) for the algebraic-reconstruction sections. They become
  ordinary theorem arguments, discharged at use by the explicit splitting field
  `SourceFormulaCommonSeparableSplittingField` (paper Lemma 3). None is a proposition
  standing in for a result.
- Structures that look like hypotheses ("computer", "initializer", "compiler", "shape"),
  each with its constructing declaration (all read):

| structure (line) | fields of note | constructed at |
|---|---|---|
| `CLNondeterminism.LocalTableauCompiler` (3774) | `specification`, `encode` (run ⇒ trace), `decode` (trace ⇒ run) | `paddedAcceptanceLocalTableauCompiler` (17155), a `def … where` with all four fields |
| `CLVerifier.TableauSimulation` (3285) | `correct : (∃ trace, ValidTrace …) ↔ Nonempty AcceptedExecution` | `tableauSimulationOfLocalCompiler` (3806); route instance `paddedStructuralTableauSimulation` (22855) |
| `PaperVariableArityCanonicalBinaryMatrixShape` (93650) | `system = physicalWordBinarySystem`, row/column-count machines + correctness | `paperCanonicalPhysicalMatrixShape` (102664) |
| `PaperVariableArityCanonicalBinaryMatrixCellComputer shape` (93672) | `check`/`rhs` : `BitTM` + per-cell correctness | `paperVariableArityCanonicalPhysicalMatrixCellComputer` (`@[irreducible]`, def head 126017, name line 126018) from four concrete check-bit machines and their `_valid` theorems |
| `BinaryGaussianExactSourceInitializer` (85565) | `computer : BitTM output`, `output_eq` | `gaussianPaperVariableArityExactSourceInitializer` (101168) |
| `PaperVariableArityPhysicalPackedMatrixSourceComputer` (98979) | `computer`, `output_valid` | `paperVariableArityCanonicalPhysicalPackedMatrixSourceComputer` (99501) |
| `PaperVariableArityShiftedTupleRankComputers` (116274) | three `SourcePhysicalLagrangeWordComputer`s | `physicalShiftedRowTupleRankComputers` (121838) |
| `SourceQaryMaskDynamicGridWidth` (75046), `ConstructiveStructuralAtomComputer` (75521), `SourcePhysicalLagrangeWordComputer` (81753) | `output` + `computer : BitTM output`, **no correctness field** | many `… where` constructors (8+, 3, 8+ sites by grep). Packs without a correctness field cannot carry a false claim: any consumer that needs `pack.output x = f x` must get it from a separate `_output`/`_valid` theorem, e.g. `compactPhysicalGaussianStructuralAtomComputerPack_output` (88563, `rfl`). |

Instrument note: a first pass of the cone script missed every declaration whose name sits
on the line after the keyword (`@[simp] theorem` ⏎ `name`, `noncomputable def` ⏎ `name`;
40 theorems and ~300 defs). Fixed; the counts in §4 are from the fixed script.

## 2. The route, as a tree

Depth is call depth through proof terms. `⟵` = "is proved/built from".

```
gapCVP400IsNPHard : IsNPHardPromise gapCVP400Promise                       130398
 ⟵ isNPHardPromise_of_original yesLanguage_iff_original noLanguage_iff_original  130374 (private)
 │     Bridge: given ∀bits, yes↔yes' and no↔no', copy map / polynomial_time /
 │     completeness / soundness field by field. `IsNP` and `BitTM` in `Comparator`
 │     are the body's own (`export GapCVP (… IsNP)` at 129765; `BitTM` resolves by
 │     namespace nesting since `Comparator` is `GapCVP.Comparator`), so
 │     `have original_hnp : GapCVP.IsNP language := hnp` is definitional.
 ├─ yesLanguage_iff_original / noLanguage_iff_original                       130272 / 130285
 │     Comparator yes/no languages ↔ body `integerTargetGapCVP400Promise`;
 │     proof: toOriginal is surjective (`toOriginal_ofOriginal` rfl), encoders agree by rfl.
 └─ paperVariableArityPhysicalIntegerTargetNPHardPromise                     126152
     ⟵ nphardPromise_of_nphard_of_promiseReduction                           1772
     │     NPHard A + PromiseReduction A P + closure ⇒ NPHardPromise P
     │     (compose L ≤ A with A ⇒ P via PromiseReduction.comp, 1760).
     ├─ (i) paperOriginalThreeSATIsNPHard : NPHard paperOriginalThreeSATLanguage   88642
     │     Cook–Levin. For L ∈ NP with (bound, verifier, machine): map
     │     x ↦ structuralWholeCNFWord bound machine x, machine
     │     actualWholeStructuralCNFOutputComputable (62083), correctness
     │     structuralWholeCNFWord_mem_paperOriginalThreeSAT_iff (88626).
     │     ├─ paperOriginalThreeSATLanguage                                      88578
     │     │     bits = encodeThreeCNF φ ∧ ∃ assignment, ∀ clause ∈ φ, clauseSatisfied.
     │     ├─ structuralWholeCNFWord / structuralWholeThreeCNF                    22882 / 22874
     │     │     encodeThreeCNF (encodeFormulaFrom 0 (sortedElements (tableauFormula
     │     │       (paddedAcceptancePhaseSpecification bound machine x))))
     │     ├─ structuralWholeCNFWord_mem_threeSAT_iff                            22909
     │     │   ⟵ compiledTableau_iff_verifier                                    3824
     │     │      ⟵ encodedTableau_mem_threeSAT_iff                              3320
     │     │         ⟵ ThreeCNFReduction.encodeTableau_satisfiable_iff_validTrace 2879
     │     │            ⟵ encodeFormula_satisfiable_iff (Tseitin, 2861)
     │     │            ⟵ CL.tableau_satisfiable_iff_validTrace (2236:
     │     │                 tableau_completeness 1970, tableau_soundness 2226)
     │     │      ⟵ tableauSimulationOfLocalCompiler (3806) with
     │     │         paddedAcceptanceLocalTableauCompiler (17155):
     │     │           encode = acceptedExecution_paddedAcceptance_validTrace (17136)
     │     │           decode = paddedAcceptanceValidTrace_guessingExecution (16512)
     │     │      ⟵ acceptedExecution_iff (3239), guessingExecutionOfAccepted (3711),
     │     │         verifying_stack_length_le (3639; tableau width bound)
     │     ├─ paperOriginalThreeSATLanguage_encode_iff_threeSAT                   88610
     │     │     with structuralWholeThreeCNF_allDistinct (22922): on the CNFs Cook–Levin
     │     │     emits, "paper" 3SAT = the stricter distinct-variable `threeSATLanguage` (664).
     │     └─ actualWholeStructuralCNFOutputComputable                            62083
     │           ⟵ …_of_flatPreparation (31857), actualSortedFiveFamilyFlatPreparationComputable
     │             (62065): the TM2 machine that writes the CNF. (Polytime-machine layer;
     │             statements read, bodies not.)
     ├─ (ii) paperVariableArityPhysicalIntegerTargetSourceReduction              126117
     │     : PromiseReduction paperOriginalThreeSATLanguage integerTargetGapCVP400Promise
     │     Strengthens paperVariableArityPhysicalSourceReduction (126112) by
     │     paperVariableArityPhysicalSourceInstance_hasIntegerTarget (126086).
     │     ├─ integerTargetGapCVP400Promise                                       126046
     │     │     yes: ∃ I, encode I = bits ∧ HasIntegerTarget I ∧ gapYES400 I;
     │     │     no : … ∧ gapNO400 I. gapYES400/gapNO400 at 62100/62106, factor
     │     │     gapFactor400 I = dim^(1/400) (62097).
     │     ├─ paperVariableArityPhysicalSourceMapMachine : BitTM …SourceMap       126105
     │     │     ⟵ paperVariableArityPhysicalSourceMapMachine_of_cell (101396, name only)
     │     │        applied to paperVariableArityCanonicalPhysicalMatrixCellComputer
     │     │        paperCanonicalPhysicalMatrixShape (126018 / 102664).
     │     └─ paperVariableArityPhysicalSourceReductionOfMachine                  92773
     │         map = paperVariableArityPhysicalSourceMap = encode ∘ physicalSourceInstance
     │         (92581 / 92554): decode φ; non-canonical ⇒ canonical NO; normalized-empty ⇒
     │         canonical YES; affine system inconsistent ⇒ canonical NO; else
     │         physicalFormulaInstance s φ (92415).
     │         ├─ completeness: paperVariableArityPhysicalSourceMap_completeness   92679
     │         │   ⟵ paperVariableArityPhysicalFormulaInstance_gapYES400_of_satisfiable 92454
     │         │      ⟵ physicalFormulaSystem_consistent_of_satisfiable           92440
     │         │      ⟵ paperVariableArityPhysicalWordBinarySystem_signedSolution_of_satisfiable 92247
     │         │         ⟵ sourceFormula_signedSolution_of_satisfiable (74564):
     │         │            one-hot table solves the system (sourceOneHot_solves_… 65385),
     │         │            ‖z‖² = (ℓ+1)|P| (sourceOneHotSignedTable_squaredNorm 65477)
     │         │            ≤ r² (sourceOneHotCompletenessRadius_squared_bound 65557)   [Lemma 8]
     │         │      ⟵ effectiveConstructionAInstance_yes_iff_signedSolution     76820 [Lemma 7]
     │         │      ⟵ adaptGapCVPInstance_gapYES400_iff_metricYes               74740
     │         └─ soundness: paperVariableArityPhysicalSourceMap_soundness         92715
     │             ├─ canonical NO: adaptedCanonicalNoWord_mem_no                  62219
     │             │     B=(2), t=(1), r=1/2 (Core.canonicalNoInstance 238)
     │             └─ paperVariableArityPhysicalFormulaInstance_gapNO400_of_unsatisfiable 92493
     │                 ⟵ effectiveConstructionAInstance_no_iff_signedSolutionNorm (76888) [Lemma 7]
     │                 ⟵ paperVariableArityPhysicalWordBinarySystem_strict_factor400_of_unsatisfiable (92323)
     │                    ⟵ physicalColumnPermutation_norm (92188), physicalWordBinarySystem_solves_iff_explicit
     │                    ⟵ paperVariableArityExplicitBinarySystem_strict_factor400_of_unsatisfiable (89563)
     │                       ⟵ sourceFormulaExplicitBinarySystem_squaredNorm_gt_factor400_of_unsatisfiable (74659)
     │                          ⟵ sourceFormula_satisfiable_of_factor400_short_signed_solution (74512)
     │                             ⟵ sourceFormula_ten_mul_integerSquaredNorm_lt_field_mul_fourth_power_of_short (74221)
     │                             │    (n^{1/400} r)² bound ⇒ 10‖z‖² < q·N⁴
     │                             └─ sourceFormula_satisfiable_of_short_signed_solution (74442)  [Prop 14]
     │                                 ⟵ sourceFormulaGlobalGenericRoot_mem_satisfyingSubtype (73571) [Lemma 13]
     │                                 ⟵ sourceFormulaCommonRoot_close_to_localBit (74394)          [Lemma 12]
     │                                 ⟵ satisfiable_of_common_valuation_root (70572)               [§5.5]
     │                                 ⟵ scaledSupport_maximalGenericGoodFiberPoints_card (72934)    [§5.1 Markov]
     └─ (iii) polynomialTimeClosedUnderComposition                              1736  (theorem)
```

Sibling headlines, same skeleton (§3 of `ROUTE-WALK.md`):

```
binaryNearestCodewordIsNPHard (130402) ⟵ binaryNearestCodeword_nphard_unconditional (129728)
   ⟵ nphardPromise_of_nphard_of_promiseReduction paperOriginalThreeSATIsNPHard
       paperVariableArityNearestUnconditionalSourceReduction (129716) polynomialTimeClosedUnderComposition
   reduction: paperNearestRoutedSourceMap (129588); instance nearestInstanceOfAffine (128645):
   generator = square basis mod 2, target = particular solution, radius R = (ℓ+1)|P|;
   nearestInstanceOfAffine_completeness/soundness (128751/128815)
binarySyndromeDecodingIsNPHard (130409) ⟵ binarySyndromeDecoding_nphard_unconditional (127320)
   ⟵ … paperVariableAritySyndromeSourceReduction (127310, name only) …
finitePNormGapCVPIsNPHard p hp (130416) ⟵ paperVariableArityFinitePNPHardPromise (128630)
   ⟵ paperVariableArityFiniteP_nphard_of_sourceMachine (128271)
   ⟵ nphardPromise_of_nphard_of_promiseReduction paperOriginalThreeSATIsNPHard
       (paperVariableArityFinitePSourceReductionOfMachine 128261) polynomialTimeClosedUnderComposition
   radius finitePRadius p R (87310), A = ⌈4p⌉ (finitePRadiusScale 87293);
   close/far: paperVariableArityFinitePPhysicalFormulaInstance_close_of_satisfiable (127909),
   …_far_of_unsatisfiable (127990)
```

## 3. Foundations the route stands on (all read)

| name | line | meaning |
|---|---|---|
| `BitLanguage`, `bitEncoding` | 621, 623 | `List Bool → Bool`; identity encoding |
| `BitTM f` | 631 | `Turing.TM2ComputableInPolyTime bitEncoding bitEncoding f` (Mathlib) |
| `VerifierTM v` | 634 | `TM2ComputableInPolyTime pairBitEncoding encodeBool v`, pair encoding = Mathlib `encodingProd (encodingList Bool) (encodingList Bool)` (625) |
| `IsNP L` | 638 | ∃ poly `bound`, verifier with a `VerifierTM`, `L x ↔ ∃ c, |c| ≤ bound(|x|) ∧ v(x,c)` |
| `PolynomialReduction`, `NPHard` | 647, 660 | many-one, `∀ x, A x ↔ B (map x)`, `BitTM map` |
| `PromiseProblem`, `PromiseReduction`, `NPHardPromise` | 670, 675, 682 | yes/no disjoint; `A x → yes(map x)`, `¬A x → no(map x)` |
| `ThreeClause`/`ThreeCNF` | 253–257 | `Fin 3 → ℕ × Bool` / list of clauses |
| `GapCVPInstance` (body) | 276 | dimension, ℤ basis, ℚ target, ℚ radius (no side conditions; `gapCVPWellFormed` 302 adds dim>0, det≠0, r>0) |
| `distanceSquared` | 306 | `∑ᵢ (∑ⱼ Bᵢⱼ zⱼ − tᵢ)²` over ℝ |

Mathlib side (read in `/home/user/differential-geometry/.lake/packages/mathlib/…/Computable.lean`,
v4.33.1 checkout; pinned is v4.32.0, not diffed): `FinTM2` requires `Fintype` of `K`, `Λ`,
`σ` and of the **input** alphabet `Γ k₀` only; `TM2ComputableInPolyTime` asks for a run from
`initList` to exactly `haltList` (all non-output stacks empty) within `time.eval (ea a).length`
`FinTM2.step`s.

## 4. Denominators

| measure | count |
|---|---|
| lines of `GapCVP.lean` read with `sed -n` (union of ranges) | ≈ 6,550 / 130,430 (5.0 %); whole-file grep/awk scans for every mechanical count |
| theorem declarations (`theorem`, incl. `@[simp]`/`private`; there are 0 `lemma`) | 3,683 |
| theorem statements read | ≈ 120 / 3,683 (3.3 %); proof bodies read ≈ 45 |
| declarations (theorem/def/abbrev/structure/instance/inductive/class) | 8,029 |
| in the name-reference cone of `gapCVP400IsNPHard` (upper bound: closure over body tokens resolved by name suffix; 47 short names are ambiguous) | 7,019 (87 %), 111,849 lines |
| cones of the three sibling headlines | 7,350 / 7,153 / 7,530 |

The cone is an over-approximation (a local variable named like a declaration creates an
edge). It says the file is single-purpose: ~1,000 declarations are outside it, 411 of them in
`GapCVP.Core` (the older formulation `GapCVP.Core.GapCVPInstance` with built-in side
conditions, used on the route only through `effectiveConstructionAInstance` and the
canonical instances).
