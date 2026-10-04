# Route walk: three places where the argument is reconstructed

Companion to `ROUTE-MAP.md` (same artifact, same conventions: `GapCVP.lean` line numbers,
every cited line read with `sed -n`, nothing compiled). Each section states the argument
the Lean expresses in two or three sentences, sets it beside the paper (Chapter 7,
`paper-ch7-cvp.txt`), and gives a verdict: EXACT (same argument, same parameters),
DIFFERENT (stated difference, with whether it matters), or NOT LOCATED (with where I
looked). Escalations are listed at the end. An escalation is a question, not an accusation.

## 1. Cook–Levin: a polynomial-time TM2 verifier run as a 3-CNF

**What the Lean proves.** `paperOriginalThreeSATIsNPHard` (88642) takes an arbitrary
`L ∈ IsNP` (638), i.e. a polynomial `bound` and a Mathlib `TM2ComputableInPolyTime` verifier
on the pair encoding, and maps `x` to the 3-CNF `structuralWholeThreeCNF bound machine x`
(22874). That formula is the Tseitin translation (`ThreeCNFReduction.encodeFormula`, 2565–2585:
an OR-gate chain on fresh accumulator variables, short clauses padded with
`paddingVariable₀/₁`) of the classical tableau formula `CL.tableauFormula` (1874) for a
**nondeterministic** machine that first appends at most `bound(|x|)` guessed certificate bits
(`GuessStep.guess`, 3378) and then runs the verifier on `(x, c)` (`GuessStep.begin`/`execute`).
The tableau has `T+1` rows and `T+1` columns over a finite cell alphabet; its clauses are
one-hot per cell (`atLeastOneClause`/`atMostOneClause`), the fixed first row
(`initialClause`), "the accept symbol occurs in the last row" (`acceptanceClause`), and one
forbidden-window clause for every 2×3 window `(left, centre, right at t; centre at t+1)` that
the local relation `allowed` rejects (`transitionClause`, 1846). `tableau_completeness` (1970)
and `tableau_soundness` (2226) give satisfiable ⇔ valid trace; `LocalTableauCompiler.encode`/
`decode`, supplied by `paddedAcceptanceLocalTableauCompiler` (17155), give valid trace ⇔
accepted guessing run; `acceptedExecution_iff` (3239) gives that ⇔ `∃ c, |c| ≤ bound(|x|) ∧
verifier (x, c) = true`.

**Time bound.** The verifier on `(x, c)` takes at most `machine.time(|x| + |c|) ≤
machine.time(|x| + bound(|x|))` steps (`witnessTimePolynomial`, 2963, and its bound lemma,
using `pairBitEncoding_length = |x|+|c|`). The guessing run adds `bound + 1` steps
(`guessTimePolynomial`, 3624). The tableau side is
`T = |x| + bound + g·maxPushPerStep + g + 1` with `g = guessTimePolynomial`
(`nondeterministicTableauDimensionPolynomial`, 3630), chosen so that every stack stays
within the row width: `verifying_stack_length_le` (3639) bounds each stack by
`|x| + bound + steps·maxPushPerStep`. So `T` is a polynomial in `|x|`, and the formula has
`poly(T)` clauses. Polynomial **computability** of the map is the separate object
`actualWholeStructuralCNFOutputComputable` (62083), a concrete TM2 machine; its body is a
long machine-construction layer (≈ 3,900–62,000) that I located and did not read.

**A point where a naive formalization would fail, handled.** Mathlib's `FinTM2` requires a
`Fintype` instance for the input alphabet `Γ k₀` only; the work stacks may have infinite
alphabets. A tableau needs a finite cell alphabet. The Lean tags every symbol on a work stack
by the push site that wrote it (`CLBoundedStates.PushSlot`/`PushTag`, 3842–3870: label ×
statement slot × internal state, all finite), so `completePhaseSymbolCount` (7750) is
`Fintype.card` of a finite cell type. This is correct because a TM2 `push` writes `f σ` for a
finite `σ`, so only finitely many symbols are ever written.

**Is the target the paper's 3SAT?** `paperOriginalThreeSATLanguage` (88578): bit strings that
are `encodeThreeCNF φ` for a list of clauses `Fin 3 → ℕ × Bool` with a satisfying assignment.
A clause has exactly three literal slots and repeats are allowed, so it expresses every
non-empty clause of at most three literals; the empty clause is not expressible, which the
paper's preprocessing treats separately anyway. The paper's Theorem 1 starts from "3SAT"
with no stricter convention, and its §3 preprocessing ("delete tautological clauses and
repeated occurrences of a literal… delete unused variables") is mirrored in Lean by
`noTautClauses`, `paperSourceNormalizedClauses` and the variable renumbering
`paperVariableArityVariableCount`/`…VariableRank` (88906–88910). The Cook–Levin output is
also in the stricter language `threeSATLanguage` (664: `threeCNFSatisfiable` additionally
demands three distinct variables per clause), via `structuralWholeThreeCNF_allDistinct`
(22922) and `paperOriginalThreeSATLanguage_encode_iff_threeSAT` (88610). The route uses the
lenient language on both sides, so the two agree.

**Verdict: EXACT** (textbook Cook–Levin tableau with nondeterministic certificate guessing
plus a Tseitin 3-CNF translation). The paper does not prove Cook–Levin; it cites "3SAT is
NP-hard". The formalization proves it from Mathlib's TM2 model, with no hypothesis left over.
Read depth: tableau semantics (1783–2248) and the reduction interfaces (3226–3840) read; the
compiler that shows the specific `allowed` relation simulates TM2 steps (`CLExactVerifierTransition`,
`CLPaddedAcceptanceCompiler`, ≈ 5,800–17,200) located, statements of `encode`/`decode` read,
bodies not read.

## 2. The gap-producing core: where n^{1/400} comes from

**Lean statement of the gap.** For a decoded canonical formula `φ` with non-empty normalized
clause list and a consistent affine system, the instance is `physicalFormulaInstance s φ`
(92415): the parity-lift lattice of `H = physicalWordBinarySystem s φ`, with target the
particular 0/1 solution and radius `r = ⌈√((ℓ+1)|P|)⌉` (`sourceOneHotCompletenessRadius`,
65534). Then

- YES (`paperVariableArityPhysicalFormulaInstance_gapYES400_of_satisfiable`, 92454):
  `∃ z, distanceSquared I z ≤ r²`;
- NO (`…_gapNO400_of_unsatisfiable`, 92493): `∀ z, (n^{1/400}·r)² < distanceSquared I z`,
  where `n = I.dimension = H.dimension = M` (`effectiveConstructionAInstance` sets
  `dimension := H.dimension`, 70940; `gapFactor400 I = I.dimension^(1/400)`, 62097).

The paper's Theorem 1 states distance (not squared) `≤ r` and `> n^{1/400} r`. Lean states
squares and a strict inequality for every lattice vector; these agree because the lattice
distance is attained (`exists_latticePoint_eq_latticeDistance`, 164, used in
`adaptGapCVPInstance_gapYES400_iff_metricYes`, 74740, and `squaredNoAt_iff_metricNo`).

**Construction and parameters (paper §3.5 vs Lean).**

| quantity | paper | Lean | verdict |
|---|---|---|---|
| size parameter | `N = 100 + s + m + ℓ` | `sourceSizeParameter = 100 + encodingLength + variableCount + clauses.length` (64371); `encodingLength = input.length` (92554) | EXACT |
| field | `q = 2^e`, least `e` with `2^e ≥ N^200` | `GaloisField 2 (Nat.clog 2 (N^200))` (64057–64062); `N^200 ≤ q < 2N^200` (64082, `…_upper`) | EXACT |
| evaluation set | `P = K \ {anchors}` | `sourceSATPuncturedGrid` (64912), `card = q − m` (`sourceFormulaGrid_card`) | EXACT |
| moment budget, degree | `T = N^30`, `d = m` | `concreteSATBinaryAffineSystem … (N ^ 30)` (89508 call); RS degrees `variableCount·j` and `(variableCount − 1)·j` (`sourceSATFamilyRowCount`, 64668) | EXACT |
| constraint families C1–C4 | odd global fibre; clause copies reproduce global mod 2; RS on ordinary moments; RS on shifted moments | `sourceSATConstraintFamily` (64659): `Unit ⊕ clause ⊕ (type × j) ⊕ (clause, tuple, localVar, j)`, row counts as above | EXACT (shape; bodies of the linear maps not read) |
| table types | `|Θ| ≤ 1 + 8ℓ` | `sourceSATTableType = Unit ⊕ Σ clause, SatisfyingLocalTuple` (64459), `card ≤ 1 + 8ℓ` (64464) | EXACT |
| dimension | `M = |Θ||P|q ≤ 40N^401` (4) | `sourceSATTableDimension_eq` (64489), `…_le` (64497), `sourceFormulaDimension_le` (65724) | EXACT |
| YES radius | `r = ⌈√R⌉`, `R = (ℓ+1)|P|` | same (65534); `r² ≥ R` (65557), `r² ≤ 4R` (69499) | EXACT |

**The NO-side arithmetic.** Paper §6: if `dist(u, L) ≤ M^{1/400} r` then
`W(H,b) = dist² ≤ M^{1/200} r² ≤ 4 M^{1/200} R`, and Proposition 14 (hypothesis
`wt(x) ≤ 4M^{1/200}R`) gives satisfiable. Its §5.1 Markov step turns that into
`|P \ P_τ| ≤ 4M^{1/200}R / N⁴ < q/20`. Lean runs the same chain with a different
intermediate normal form:

1. `‖z‖² ≤ (M^{1/400} r)²` ⇒ `10·‖z‖² < q·N⁴`
   (`sourceFormula_ten_mul_integerSquaredNorm_lt_field_mul_fourth_power_of_short`, 74221).
   Ingredients: `r² ≤ 8qN` (74200, i.e. `r² ≤ 4R` with `R ≤ 2N·q`, which is looser than the
   paper's `R ≤ Nq`); `(M^{1/400})² = M^{1/200}` (`gapFactor400_sq`, 74072);
   `M ≤ 40N^401 ≤ N^402` ⇒ `M^{1/200} ≤ N^{201/100}` (74090); and `80·N^{301/100} < N⁴`
   for `N ≥ 100` (`source_power_margin`, 74134, from `80^100 < 100^99` by `norm_num`,
   74112). I checked that last numeral independently: `80^100 = 2^{300}·10^{100} ≈ 2.04·10^{190}`
   and `100^99 = 10^{198}`.
2. Proposition 14 in Lean, `sourceFormula_satisfiable_of_short_signed_solution` (74442), has
   hypothesis `10·‖z‖² ≤ q·N⁴` on an **integer** vector solving the system mod 2. Since every
   odd coordinate contributes at least 1 to `‖z‖²`, this is at least as strong as the
   Hamming-weight hypothesis.
3. Markov with support threshold `N⁴`: discarded points `≤ budget/(N⁴+1) ≤ q/10`
   (`scaledSupport_div_ten_mul_le_field`, 72915); anchors plus Hankel exceptions
   `m + N⁹ ≤ q/10` (`source_variable_and_hankel_exceptions_ten_mul_le_field_size`, 69427); so
   more than `2N^{39}` good points remain (`scaledSupport_maximalGenericGoodFiberPoints_card`,
   72934). This parallels the paper's (13)–(14) (`|P| − q/20 − N⁹ > q/2 > 2N^{39}`).
4. Lemma 13 → `sourceFormulaGlobalGenericRoot_mem_satisfyingSubtype` (73571); Lemma 12 →
   `sourceFormulaCommonRoot_close_to_localBit` (74394), which is a valuation `< 1` statement;
   §5.5's agreement on shared variables → `satisfiable_of_common_valuation_root` (70572).

**Verdict: EXACT in exponent, `n`, radius and parameters; DIFFERENT in constants of the
intermediate inequalities.** The Lean form is `10‖z‖² ≤ qN⁴` with Markov slack `q/10`; the
paper's is `wt ≤ 4M^{1/200}R` with `q/20`. Both are proved in Lean with margin, so the
difference does not matter. The exponent 1/400 is `(1/200)/2`: the binary-weight factor
`M^{1/200}` (Corollary 15) is square-rooted by the Euclidean transfer. Read depth: the
algebraic reconstruction (paper Lemma 10 and §4, Lean ≈ 66,000–73,600, with the
"maximal generic Hankel rank" machinery `maximalGenericGoodFiberPoints_card_lower_bound`,
67481) was **located but not read**. It is the deepest mathematics in the artifact and the
largest unread block on the route.

## 3. Binary decoding and ℓ_p transfers (paper Lemma 7, Corollaries 15–16)

**Lemma 7 (parity-lift lattice).** Lean `effectiveConstructionAInstance` (70940): the basis is
`effectiveSquareBasisMatrix` (70860) read off the reduced echelon form. A free column has
identity entries; a pivot column has `2` on the diagonal; the pivot row and free column
entry is the 0/1 lift of the reduced check-matrix entry. This is the paper's
`B_H = [[I, 0], [P̃_sys, 2I]]` in original coordinate order. `det ≠ 0` is
`effectiveSquareBasisMatrix_det_ne_zero` (70912). The target is the 0/1 particular solution
`effectiveAffineRepresentative`. The coset identity is
`effectiveConstructionAInstance_solution_coset` (76711) plus
`…_squaredDistance_eq_integerSquaredNorm` (76722): `‖t − Bc‖²` equals `‖v‖²` where `v` ranges
over integer solutions of `H(v mod 2) = b`. YES/NO then become statements about short
integer solutions (76820 / 76888, with the factor exponent as a parameter). The rank is
exactly `M`. **EXACT.** Lean phrases the identity with integer solutions and `‖v‖²` rather
than binary words and `wt`. This is the same as the paper's own proof step ("each nonzero
coordinate of x comes from an odd integer coordinate").

**Corollary 15 (nearest codeword / syndrome decoding, factor n^{1/200}).**
`nearestInstanceOfAffine` (128645) has block length = generator rank = `M`, generator = the
square basis mod 2 (pivot columns vanish mod 2, so the image is `C = ker H`), target = the
particular solution, radius `R = (ℓ+1)|P|` (`sourceBinaryDecodingRadius`, 87487; the paper's
integer radius). Completeness comes from the one-hot solution of weight exactly `R`
(89475). Soundness (`nearestInstanceOfAffine_soundness`, 128815): a codeword within
`n^{1/200}·R` gives a binary solution of weight `≤ 2·n^{1/200}·R`, and
`sourceBinaryDecoding_scaledNorm_support` (87526) turns that into the same `10‖z‖² ≤ qN⁴`
core (margin `20·n^{1/200}·N < N⁴`). The inconsistent-system output is
`canonicalBinaryNearestCodewordNo` (126293): length 2, rank 0 (code {00}), target 11,
radius 1, distance 2 > 2^{1/200} (`binaryCodeGapFactor_two_lt_two`, 126307). This is the
paper's fixed NO instance. The syndrome variant uses `canonicalBinarySyndromeNo` (126300,
`H = I₂`, `b = 11`, radius 1). Its NO language additionally requires that the system is
solvable (130126). **EXACT.** The headline nearest-codeword factor is
`blockLength^{1/200}` (`binaryCodeGapFactor`, 130063), with `blockLength = M = n`.

**Corollary 16 (ℓ_p, factor n^{1/(200p)}).** `finitePRadiusScale p = ⌈4p⌉` (87293) is the
paper's `A`. `finitePRadius p R = ceilRoot_a(A^a·R^b) / A` with `p = a/b` (87302–87311) is
the paper's `j_p/A`. The Lean bounds are `R^{1/p} ≤ r_p` (`finitePRadius_lower`, 127463)
and `r_p^p < 2R` (`finitePRadius_rpow_lt_two_mul`, 127628, via `(1+1/A)^p ≤ e^{1/4} < 2`,
127553–127570). The ℓ_p identity's "≥" direction is `|z_i|^p ≥ 1` on every odd coordinate
(`finitePSignedBinarySupport_card_le_power_sum`, 87316). The NO side
(`finiteP_power_sum_le_scaled_binary_radius`, 127678): `(n^{1/(200p)} r_p)^p =
n^{1/200} r_p^p < 2n^{1/200}R` (`finitePGapFactor_rpow`, 127338), which is again the
`2·n^{1/200}·R` hypothesis of the shared core. The paper writes
`< 2n^{1/200}R ≤ 4n^{1/200}R`. **EXACT.** `p` is a fixed rational `≥ 1`, as in the paper.

## Escalations and observations

- **O1 (no escalation): no unsupplied hypothesis.** `polynomialTimeClosedUnderComposition` is
  proved (1736) by an explicit composed TM2 machine. The machine runs `first`, which by
  Mathlib's `haltList` ends with every non-output stack empty and the state reset. It then
  runs `second` with its input stack identified with `first`'s output stack
  (`TMComposition.Stack`, 701; `secondStack`, 980; `machine`, 1065). Time is
  `first.time + second.time ∘ (X + maxPush·first.time)` (960), using the output-length bound
  `|f x| ≤ |x| + maxPush·time` (945). This is the standard argument.
- **O2 (observation): the lattice-to-promise bridge and the Comparator bridge are thin and
  read in full.** `isNPHardPromise_of_original` (130374) copies fields. The four
  `*_iff_original` lemmas (130272–130370) close by surjectivity of a structure re-packing and
  `rfl` on encoders. Within this file the Comparator namespace reuses the body's `IsNP`,
  `BitTM`, `bitEncoding` and encoders (`export` at 129765). Whether `H_GapCVP.lean`'s copies
  are the same objects is the statement rung's question (`STATEMENT.md`).
- **E1 (question, low): Mathlib version.** The TM2 definitions were read in a v4.33.1
  Mathlib checkout; the artifact pins v4.32.0. Nothing on the route depends on a lemma I
  cited from Mathlib; the definitions `FinTM2`, `initList`, `haltList` and
  `TM2ComputableInPolyTime` should be diffed against v4.32.0 before the statement rung
  relies on them.
- **E2 (coverage, not a defect): two unread blocks carry most of the proof's mass.** These are
  the algebraic reconstruction (§2.4) and the TM2 machine layer (the `BitTM` constructions
  for the map, ≈ 17,000–62,000 and 93,000–126,000). Only the kernel can certify the second
  block. The first is mathematics and is the place to spend the next reading budget.
