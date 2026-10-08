# READ-A — computational model, ω, ν, and the rank→program bridge

Reader A. Scope: paper §1 (definition of ω), §2 eq. (2.2) (ν), end of §5 ("To obtain an
arithmetic algorithm" through Remark 5.2), plus the coordinator's REFERENCE-mm94.md and
STATEMENT.md. All paths below are relative to
`/home/user/openai-math/repo/lean/OAI/LinearAlgebra/MatrixMultiplication/` unless they start
with `ComparatorChallenges/`. Every file:line was read with `cat -n`/`sed -n`.

## 1. Files read

Read WHOLE, leaves first:

| file | lines | on route? |
|---|---|---|
| `ComparatorChallenges/MatrixMultiplication.lean` | 132 | challenge |
| `Model.lean` | 114 | yes (`diff` vs challenge lines 11–112: identical apart from the file header/footer) |
| `Tensor/ComplexTensor.lean` | 315 | yes |
| `ComplexArithmetic/Complexity.lean` | 151 | yes |
| `ComplexArithmetic/Programs.lean` | 184 | yes |
| `ComplexArithmetic/ProgramComposition.lean` | 192 | yes |
| `ComplexArithmetic/MatrixPadding.lean` | 101 | yes |
| `ComplexArithmetic/NaiveAlgorithm.lean` | 101 | yes |
| `ComplexArithmetic/LowerBound.lean` | 104 | yes |
| `ComplexArithmetic/Exponent.lean` | 56 | yes |
| `Tensor/ComplexMatrixTensor.lean` | 109 | yes |
| `ComplexArithmetic/RecursiveBlockPrograms.lean` | 368 | yes |
| `ComplexArithmetic/Growth.lean` | 226 | yes |
| `Tensor/ComplexTensorFlattening.lean` | 70 | yes |
| `Arithmetic/Complexity.lean` | 109 | yes |
| `Arithmetic/Programs.lean` | 188 | yes |
| `Arithmetic/ProgramComposition.lean` | 198 | yes |
| `Arithmetic/Padding.lean` | 120 | yes |
| `Arithmetic/NaiveAlgorithm.lean` | 106 | yes |
| `Arithmetic/LowerBound.lean` | 222 | yes |
| `Arithmetic/Exponent.lean` | 159 | yes |
| `Arithmetic/Compatibility.lean` | 180 | yes |
| `AuxiliarySeparation/Arithmetic/RankExponent.lean` | 225 | yes |
| `AuxiliarySeparation/Arithmetic/ExponentComparison.lean` | 89 | yes |
| `AuxiliarySeparation/Arithmetic/Exponent.lean` | 131 | yes |
| `AuxiliarySeparation/Arithmetic/CharacterRounding.lean` | 122 | yes |
| `AuxiliarySeparation/Arithmetic/RankBound.lean` | 29 | yes |
| `AuxiliarySeparation/Main.lean` | 33 | yes |
| `Main.lean` | 31 | yes |

Grepped only: `Polynomial/ExpressionFamily.lean` (71) and `Polynomial/ComplexExpressionFamily.lean`
(69) — only the `CompiledFamily` contract (`correct`, `cost_eq` fields, lines 23–24 / 21–22);
`AuxiliarySeparation/Character/Basic.lean:35–55` (the `Character` structure) and
`Character/Existence.lean:25–27` (statement of `exists_detecting_character`) — signatures only.
Paper: `paper.txt` lines 20–110 and 420–450.

Note: `Arithmetic/RecursiveBlockPrograms.lean` (400 lines, generic-field copy) exists but is NOT in
`route-closure.txt`; the route uses the ℂ-only `ComplexArithmetic/RecursiveBlockPrograms.lean`.
Not read.

## 2. Argument reconstruction

There are TWO copies of the program model: the challenge/`Model.lean` one
(`MatrixMultiplication.Arithmetic`, field-generic, square-or-rectangular) and an internal ℂ-only
"legacy" one (`MatrixMultiplication.Foundation.Arithmetic`, square only). The bridge is proved
in the legacy model and transported by `Compatibility.lean`.

1. **Model** (`Model.lean:11–95`, = challenge 13–95). Straight-line programs; `omega F = sInf
   {τ | AdmissibleExponent F τ}`. Paper §1 / Reference clause 1–3.
2. **Legacy model** `ComplexArithmetic/Complexity.lean:17–131`: constructor-for-constructor
   the same `Gate`/`Program`/`eval`/`cost`/`MatrixAlgorithm`/`Correct`/`AdmissibleExponent`,
   specialised to ℂ and square n.
3. **Model ↔ legacy** `Arithmetic/Compatibility.lean:16–109` (`toLegacy`/`ofLegacy`, structural
   maps preserving eval (`:61`, `:79`) and cost (`:73`, `:92`)); `complex_admissibleExponent_iff`
   (`:153`): `AdmissibleExponent ℂ τ ↔ Foundation.Arithmetic.AdmissibleExponent τ`.
4. **Nonempty**: `Arithmetic/NaiveAlgorithm.lean:200` `admissibleExponent_three` (naive program,
   cost exactly `2abc` `:187`, C = 2); `:219` nonempty.
5. **Bounded below by 2**: `Arithmetic/LowerBound.lean:124` `output_size_le_cost` (a·c ≤ cost:
   output map injective `:76` via elementary matrices, each output register has register-cost ≥ 1
   `:96` since a cost-0 register is a constant or a raw input, refuted by test matrices);
   `:144` ⇒ any admissible τ ≥ 2; `:203` `admissibleExponent_bddBelow`.
6. **sInf meaning**: `Arithmetic/Exponent.lean:27` `omega_two_le`, `:35`
   `omega_admissibleExponent` (ω itself is admissible: for ε pick τ < ω+ε/2 in the set, use its
   ε/2-constant), `:49` `admissibleExponent_iff_omega_le` (← = `omega_admissibleExponent.mono`,
   `:15` upward closure). Paper's "infimum" definition read correctly.
7. **Block step** `ComplexArithmetic/RecursiveBlockPrograms.lean:355` `rank_block_step`: from
   `RankAtMost T_n r` and a correct m×m program p, a correct (nm)×(nm) program with cost EXACTLY
   `r·cost p + 6 r n² m²` (`:348–353`). Correctness `:333` from `block_identity` `:226`
   (bilinear identity `:186` applied blockwise; recursive products are genuine matrix products
   of blocks, left before right, computed by p which is correct for all inputs). Paper §5
   "bilinear identities remain valid on matrix blocks".
8. **Recursion → powers** `Growth.lean:153` `power_programs_of_block_step` (S(0)=1 scalar
   program, S(k+1) ≤ R·S(k) + K(b^k)²), `:24` `geometric_cost_recurrence_bound` (x_{k+1} ≤ a x_k
   + b d^k with a < q, d ≤ q ⇒ x_k ≤ C q^k).
9. **Padding** `ComplexArithmetic/MatrixPadding.lean:263–285` (zero-pad, input gates for padded
   entries become free `constant 0`, cost unchanged), `Growth.lean:18` (n ≤ b^k ≤ b·n), `:57`.
10. **Bridge** `Growth.lean:213` `admissibleExponent_of_rankAtMost`: n ≥ 2, `RankAtMost T_n R`,
    2 ≤ τ, R ≤ n^τ ⇒ legacy `AdmissibleExponent τ`. Lifted at
    `AuxiliarySeparation/Arithmetic/Exponent.lean:144` and `:151` `omega_le_of_rankAtMost`.
11. `:159` `omega_le_logb_rank`: τ := log_n R, with τ ≥ 2 from the flattening bound R ≥ n²
    (`RankExponent.lean:114`). Paper "Flattening gives r ≥ u²".
12. **ν**: `RankExponent.lean:84` `exactMatrixRank`, `:142–146` set and `exactRankExponent`;
    `AuxiliarySeparation/Arithmetic/Exponent.lean:194` `omega_le_exactRankExponent` by
    `le_csInf` over the set. Paper (2.2) + §5 final paragraph.
13. **ν ≤ 9/4** `CharacterRounding.lean:111` from `detect` (Lemma 2.2) and `bound`
    (λ(T_d) ≤ d^{9/4}); discharged in `RankBound.lean:11–20` by `exists_detecting_character`
    and `χ.value_matrixMultiplication` + `exponent_sum_le_nine_quarters` (other readers).
14. **Headline** `AuxiliarySeparation/Main.lean:21` `matrix_multiplication_cost_le` (explicit
    ε–C–n–P form, from `Exponent.lean:209`), `:28` `omega_le_nine_quarters`; `Main.lean:14`
    `complex_omega_le_nine_quarters := AuxiliarySeparation.omega_le_nine_quarters`.

What the formalization added vs the paper: the paper chooses u with r < u^{9/4+δ} and solves
the recursion with an O(N² log N)/O(N^{log_u r}) case split. Lean instead proves ω ≤ log_n R(T_n)
for EVERY n ≥ 2 (with ε slack absorbing the boundary case) and then takes the infimum, so it
never needs to pick δ or attain ν. Remark 5.2 (Nullstellensatz, number-field coefficients) is
not formalized and not needed: the model is over ℂ.

## 3. Definitions checked

| Lean name | file:line | what it is | matches? | note |
|---|---|---|---|---|
| `Gate` | `Model.lean:11` | constant z∈F / input i / add,sub,mul of two registers | yes | binary fan-in; no division, no branching |
| `Gate.eval` | `Model.lean:22–28` (challenge 24–30) | one field op per gate | yes | uses the ambient `[Field F]` |
| `Gate.cost` | challenge 32–37 | constant 0, input 0, add/sub/mul 1 | yes | constants & loads free (standard) |
| `Program` | challenge 41–43 | snoc-list; the gate added at length r has type `Gate F Input (Fin r)` | yes | a gate can only name the r EARLIER registers — self-reference / forward reference are ill-typed |
| `Program.eval` | challenge 49–52 | `Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)` | yes | newest register = index 0, older = `succ`; gate evaluated on `p.eval` (prefix) only |
| `Program.cost` | challenge 54–56 | sum of gate costs | yes | |
| `MatrixInput`, `matrixInputs` | challenge 60–66 | inl (i,j) ↦ A i j, inr (j,k) ↦ B j k | yes | inputs are exactly the a·b + b·c entries |
| `MatrixAlgorithm` | challenge 68–71 | registers count, program, `output : Fin a → Fin c → Fin registers` | yes | output may point at any register (incl. an input/constant register — cost-0; the lower bound handles it) |
| `Correct` | challenge 82–83 | ∀ A B, eval = `A * B` | yes | Mathlib `Matrix` `*` on `Fin` indices over F |
| `AdmissibleExponent` | challenge 90–93 | ∀ε>0 ∃C>0 ∀n≥1 ∃P correct, cost ≤ C n^{τ+ε} | yes | C independent of n; P depends on n, ε |
| `omega` | challenge 95 | `sInf` of admissible set | yes | non-vacuous: set ⊆ [2,∞), ∋ 3, upward closed, contains its inf |
| legacy `Gate/Program/MatrixAlgorithm/AdmissibleExponent` | `ComplexArithmetic/Complexity.lean:17–131` | ℂ-specialised copy | yes | equivalence proved `Compatibility.lean:153` |
| `Tensor` | `Tensor/ComplexTensor.lean:16` | `X → Y → Z → K` coefficient array | yes | |
| `rankOne` | `:24` | a x · b y · c z | yes | |
| `RankAtMost T r` | `:27` | ∃ a b c : Fin r → _ → K, T = Σ_i rankOne | yes | arbitrary vectors over K (= ℂ here) |
| `restrict` | `:31` | T'(x',y',z') = Σ A x' x B y' y C z' z T x y z | yes | independent linear maps on each leg |
| `matrixMultiplication a b c` | `ComplexArithmetic/Complexity.lean:137` | 1 iff x=(i,j), y=(j,k), z=(k,i) | yes | T = Σ x_ij y_jk z_ki, paper (2.2) |
| `exactRank` | `RankExponent.lean:36` | `Nat.find` of ∃r RankAtMost | yes | least r; `exactRank_le` `:48` minimality, `exactRank_spec` `:42` |
| `exactMatrixRank n` | `:84` | exactRank T_n | yes | = R(T_n) |
| `exactRankExponentSet`, `exactRankExponent` | `:142`, `:146` | {log_n R(T_n) : n ≥ 2}, its sInf | yes | bdd below by 2 `:169`, nonempty `:148`; ν ∈ [2,3] `:174`, `:183` |
| `Character` | `Character/Basic.lean:35–55` | value ≥ 0, 0↦0, unit↦1, additive on directSum, multiplicative on product, monotone under restrict | yes (Def 2.1) | signature only read; X Y Z : Type 0 |
| `AuxiliarySeparation.omega` | `AuxiliarySeparation/Arithmetic/Exponent.lean:120` | `abbrev` = `Arithmetic.omega ℂ` | yes | the challenge's ω, not the legacy one |

## 4. Answers to the eight questions

**Q1 (register indexing).** `Program.step : Program F Input r → Gate F Input (Fin r) → Program
F Input (r+1)` (challenge:43): the new gate's register operands live in `Fin r`, the registers
that already exist. `eval` (challenge:49–52) evaluates the new gate on `p.eval inputs` — the
prefix's evaluation — and stores it at index 0, shifting the prefix by `Fin.succ`. So a gate
can read only earlier registers; it cannot read itself or anything later (ill-typed). The
indexing is relative ("de Bruijn"), confirmed by `scalarAlgorithm` (`Arithmetic/Complexity.lean:
55–59`: `.mul 1 0` on [B00, A00] computes A00·B00, proved `:61`). Inputs are reachable only
through `.input i` gates, and `i : MatrixInput a b c` names an entry of A or B; there is no other
input. `output` may point at any register; that is harmless (all registers are polynomials in
the inputs).

**Q2 (cost).** `Gate.cost` (challenge:32–37) is 1 for add/sub/mul and 0 for constant/input;
`Program.cost` sums it. `Gate.eval` (challenge:24–30) is one binary field operation per gate;
there is no n-ary or composite gate, no division, no comparison. Constants are arbitrary z ∈ ℂ
and free — standard in the algebraic model (Bürgisser–Clausen–Shokrollahi), and since programs
have no branching a constant cannot smuggle in computation; constant loads and input loads are
free copies. No gate does more than one scalar operation.

**Q3 (correctness).** `Correct P := ∀ A B, P.eval A B = A * B` (challenge:82–83): universally
quantified over all A, B over F. `A * B` is Mathlib's `Matrix` multiplication on `Fin a`/`Fin b`/
`Fin c` (no local instances anywhere in my files; proofs unfold it with `Matrix.mul_apply`,
e.g. `Arithmetic/Complexity.lean:69`, `Arithmetic/Padding.lean:42`).

**Q4 (sInf trap).** Nonempty: `Arithmetic/NaiveAlgorithm.lean:219` (τ = 3, C = 2, cost = 2n³
`:187`). Bounded below by 2: `Arithmetic/LowerBound.lean:199–205` via `output_size_le_cost`
(`:124`, n² ≤ cost). Hence ω ∈ [2,3] (`Arithmetic/Exponent.lean:27`, `:32`). The ← direction
of `admissibleExponent_iff_omega_le` (`Arithmetic/Exponent.lean:49–51`) is honest: given ε,
`exists_lt_of_csInf_lt` (`:38`) gives an admissible τ < ω + ε/2; its constant for slack ε/2
bounds cost by C n^{τ+ε/2} ≤ C n^{ω+ε} (n ≥ 1); then `mono` (`:15`) for any τ' ≥ ω. Real.sInf
of ∅ or of an unbounded-below set is 0 — neither applies. Independently, the headline also has
the explicit form `matrix_multiplication_cost_le` (`AuxiliarySeparation/Main.lean:21`), which
does not mention sInf at all. `omega ℂ ≤ 9/4` is therefore not vacuous. (The legacy model's lower
bound is only 0 — `ComplexArithmetic/LowerBound.lean:174–199` — but that is used only for its own
csInf lemmas; the challenge ω uses the Model-side bound 2.)

**Q5 (the bridge).** `admissibleExponent_of_rankAtMost` is at `ComplexArithmetic/Growth.lean:213`
(called from `AuxiliarySeparation/Arithmetic/Exponent.lean:149`). Construction:
- Decomposition T_n = Σ_{q<R} a_q⊗b_q⊗c_q. For A, B of size nm, view them as n×n arrays of m×m
  blocks (`join` = `finProdFinEquiv`, `RecursiveBlockPrograms.lean:184`). Form L_q = Σ_x a_q(x)
  A_x, R_q = Σ_y b_q(y) B_y (`leftBlock`/`rightBlock` `:216–224`), multiply each pair with the
  recursive program (R copies, `Family.copies` `:145`), output block (i,k) = Σ_q c_q(k,i) L_qR_q
  (`outputExpressions` `:304`). Correct for all A, B (`algorithm_correct` `:333`).
- Linear-combination overhead: each block-entry linear form is compiled as Σ (const·input) =
  2·n² gates (`LinearExpression.cost_linear` `:52`), input side 4Rn²m² (`:274`), output side
  2Rn²m² (`:321`); total `cost = R·cost(p) + 6Rn²·m²` exactly (`:348`). Every scalar op of the
  linear combinations is counted (no free scalings).
- Recursion: `power_programs_of_block_step` (`Growth.lean:153`) gives programs for sizes n^k with
  cost ≤ S(k), S(0)=1, S(k+1)=R S(k)+K n^{2k}, K = 6Rn² (`:142`, `:217`).
- Growth: for each ε, `geometric_cost_recurrence_bound` (`:24`) with a = R, d = n², q = n^{τ+ε}:
  needs R < q (from R ≤ n^τ < n^{τ+ε}, `:184`) and n² ≤ q (from τ ≥ 2, `:186`). Gives S(k) ≤ C q^k.
- Padding: any N ≥ 1 sits in [n^k, n·N] for some k (`:18`); restrict the n^k program by zero
  padding (`MatrixPadding.lean:263`, cost unchanged) ⇒ cost ≤ C n^{τ+ε} N^{τ+ε} (`:57–82`).
- **Boundary R = n²**: handled — R ≤ n^τ with τ = 2 still gives R < n^{2+ε}, so the geometric
  bound applies with q = n^{2+ε}. Lean never proves the paper's O(N² log N); it proves
  O_ε(N^{2+ε}) for every ε, which is exactly what `AdmissibleExponent 2` requires. Correct.
- **`hτ : 2 ≤ τ`** is used for exactly two things: n² ≤ n^{τ+ε} so the quadratic per-level
  overhead is dominated (`Growth.lean:186–189`), and τ ≥ 0 for the padding monotonicity (`:181`).
  It is discharged at the call site by flattening: τ = log_n R ≥ 2 because R ≥ n²
  (`AuxiliarySeparation/Arithmetic/Exponent.lean:162–171`, `RankExponent.lean:114`) — the paper's
  "Flattening gives r ≥ u²".

**Q6 (ν).** `exactRank` = `Nat.find (exists_rankAtMost T)` (`RankExponent.lean:36–39`);
`exists_rankAtMost` (`:22`) is the trivial |X||Y||Z| decomposition, so `Nat.find` is well-defined
and returns the least r with `RankAtMost T r` (`exactRank_le` `:48` gives minimality) = true tensor
rank over ℂ with arbitrary complex vectors (`ComplexTensor.lean:27–29`). `exactRankExponentSet`
(`:142`) = {log_n R(T_n) : n ≥ 2} = paper (2.2). `omega_le_exactRankExponent`
(`AuxiliarySeparation/Arithmetic/Exponent.lean:194–197`) is `le_csInf exactRankExponentSet_nonempty`
plus the per-n bound `omega_le_exactMatrixRank_logb` (`:188`); no attainment of the infimum is used.

**Q7 (rounding).** `CharacterRounding.lean:111–118`: `detect : ∀ d ≥ 2, ∀ k : ℕ, k < d^ν → ∃ χ,
k ≤ χ.value(T_d)` is Lemma 2.2 verbatim (paper lines 104–105), χ chosen after d and k.
`bound : ∀ χ, ∀ d ≥ 2, χ.value(T_d) ≤ d^{9/4}` is the paper's "λ(T_d) ≤ d^{9/4} for every
character" (line 430). The argument (`:79–91`): k_d = ⌈d^ν⌉ − 1 (`exists_nat_sub_one_le_lt`
`:22`, checked for integer d^ν: ⌈x⌉−1 = x−1 < x), so d^ν − 1 ≤ k_d ≤ d^{9/4}; then
`rpow_exponent_le_of_nat_sub_one_bound` (`:33`) with C = 2 and `rpow_exponent_le_of_nat_bound`
(`ExponentComparison.lean:19`, evaluated along n = 2^k) gives ν ≤ 9/4. Matches paper lines 431–434.

**Q8 (instances).** No `attribute`, `instance`, `set_option` or `open Classical` line in any of my
29 files (grep returned nothing). Across the whole 129-module route, the global instances are
all on new types (`TensorClass`, `FiniteTensor`, `Decidable (MiddleY …)`, `Fintype` of label
records, `NeZero`) — none on ℂ, ℝ, `Field`, `Matrix`, or `Mul`/`Add` of an existing type. Also,
since the comparator elaborates the challenge statement with only `import Mathlib`, a different
`Field ℂ` instance in the solution would change the elaborated term and fail the comparison.

## 5. Coordinator's tables — agreement

STATEMENT.md rows: model EXACT — agree; cost EXACT — agree; correctness EXACT — agree; exponent
set and ω EXACT in form — agree; conclusion EXACT — agree; explicit form "not in the challenge;
in the solution" — agree. Two citation nits: `admissibleExponent_iff_omega_le` is at
`Arithmetic/Exponent.lean:49`; `AuxiliarySeparation/Arithmetic/Exponent.lean:38–39` is the alias
`arithmeticBound_iff_omega_le` (and `:134` the expanded ε–C–n–P form). The "bounded below by 2
(`Arithmetic/LowerBound.lean`)" observation is confirmed at `:199–205`.
REFERENCE-mm94.md: every clause 1–4 is met; none of the "weakening" items occurs (cost counts all
of +,−,×; correctness over all A, B over ℂ; programs are input-independent straight-line; fan-in 2;
ω's set non-empty and bounded below, and the explicit form is proved).

## 6. Escalations (all resolved; none blocking)

E1. **Two program models.** The bridge is proved in the ℂ-only legacy model and transported.
Resolved: `Compatibility.lean:16–174` maps constructors one-to-one with eval/cost preservation,
and the transported statement is the Model's `AdmissibleExponent ℂ`. Risk would only be in the
Model definitions, which are identical to the challenge.

E2. **Cost of helper compilers trusted by contract.** `compileFamily`, `substitute`, `append`
carry `correct`/`cost_eq` fields proved by the kernel, so final programs' cost is the Model's
`Program.cost` by proof; I did not need to trust helper implementations. `substitute`'s `.input`
case (`Arithmetic/ProgramComposition.lean:167–179`) reuses an existing register instead of
emitting a gate — legitimate, input gates cost 0 anyway.

E3. **Free arbitrary constants.** Allowed by the model and used (rank-decomposition coefficients,
`RecursiveBlockPrograms.lean:43`). Standard; does not change ω (paper Remark 5.2). Worth stating
in any public summary: the algorithm's existence is non-constructive (coefficients come from a
`Nat.find`/`Classical` rank decomposition whose size bound rests on Lemma 2.2's fixed-point
argument), so no explicit algorithm is extracted — same as in the paper.

E4. **Boundary R = n² proved differently from the paper** (O(N^{2+ε}) via ε slack rather than
O(N² log N)). Sufficient for the definition. Resolved.

E5. **Paper says padding increases size "by less than the fixed factor u"**; Lean uses ≤ u·n
(`Growth.lean:18–22`). Immaterial.

## 7. Sanity computation

`scratchpad/readA/rec.py` (run with `python3 -I`): iterates the Lean recurrence S(0)=1,
S(k+1)=R S(k)+6Ru²·u^{2k}. For R = u² (u=2,3): S/(N² log_u N) → 24.03, 54.03 (constant: 6R),
i.e. Θ(N² log N). For R > u² ((2,7), (3,23), (4,49)): S/N^{log_u R} → 57.0, 89.71, 143.55,
i.e. Θ(N^{log_u R}). Also checked the Lean constant C = x₀ + K/(q−R) + 1 of
`geometric_cost_recurrence_bound` against 200 levels for (u,R,ε) = (2,4,0.01), (2,7,0.001): bound holds.

## 8. Verdict and what I did NOT read

Verdict: the model, the definition of ω, the definition of ν, and the rank→program bridge mean
what the paper and the reference say — ω here is the standard division-free ℂ-arithmetic exponent
(all +,−,× counted, constants free, exact correctness for all inputs, non-vacuous sInf), and
`omega_le_exactRankExponent` honestly converts any finite exact rank decomposition of T_n into
programs of cost O_ε(N^{log_n R + ε}) for all N ≥ 1; the 9/4 therefore rests entirely on
`exactRankExponent_le_nine_quarters` (Lemma 2.2 + the character bound), which is outside my part.

Not read: `Arithmetic/RecursiveBlockPrograms.lean` (off-route); `Arithmetic/CommonDimensions.lean`,
`Arithmetic/MatrixMapDecidable.lean` (off-route); bodies of `Polynomial/*ExpressionFamily.lean`;
everything under `AuxiliarySeparation/Character/` beyond the two signatures cited (including the
proof of `exists_detecting_character`, `value_matrixMultiplication`,
`exponent_sum_le_nine_quarters`); `Tensor/ComplexTensorBatching.lean` (imported by
`ComplexMatrixTensor.lean`, used only by `matrixCoefficients_batch_rank`, not on my chain); the
secondary theorems (α, rectangular ω) in `Main.lean`'s other imports.
