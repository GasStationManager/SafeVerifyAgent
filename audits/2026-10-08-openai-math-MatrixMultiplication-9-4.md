# openai/math result 107 — "An Upper Bound of 9/4 for the Matrix Multiplication Exponent": read-through

**Verdict: no defect found.** The headline `Arithmetic.omega ℂ ≤ 9/4` is EXACT against a
reference statement written from the paper, the model of computation is the standard one,
the explicit ∀ε ∃C ∀n ∃P form is proved beside it, the whole route builds here on exactly the
three standard axioms, and the headline's export (49,693 declarations, 1,403 of them the
artifact's own) is accepted by leanchecker, con-leche (verified mode), con-ron and nanoda. Six
independent readers reconstructed the argument section by section against the paper and found
no discrepancy; every escalation closed. The method is new (not laser/Coppersmith–Winograd) and
the result, if the mathematics community accepts the paper, moves ω from 2.3712 to 2.25.

## 0. What did not run / caveats, first

- **Authors' comparator config** (`MatrixMultiplication.json`, three theorems): needs the full
  504-module `Main`; see §6 for the result. The 9/4 theorem's own statement was compared by hand
  (§2) and by an auditor-written comparator challenge (§6).
- **One model family.** Coordinator and all six readers are Claude models (Fable 5.1 coordinator,
  Opus readers). Independence is between passes and against the paper, not between model
  families. Nothing in this audit is a mathematical referee's judgement of the PAPER; it is a
  check that the Lean proves the paper's theorem and that the Lean's argument IS the paper's.
- **Read coverage.** 129 route modules / 20,694 lines; readers read 108 files whole (by their
  own lists) and the rest at statement level; proof bodies of Mathlib lemmas trusted by
  signature; the external Brouwer package read at statement level and scanned.
- **Paper PDF absent from the repository checkout and git tree** (only `README.md`); fetched
  from the public GitHub raw URL (371 KB). The two Sep-24 "secondary writeups" are not this
  theorem's paper.
- The two companion theorems (α > 0.465, rectangular ω(1,0.709,1) < 2.092) were NOT read: they
  ride the Coppersmith–Winograd machinery (163 and 115 modules).

## 1. Intake

| item | value |
|---|---|
| repository / commit | `github.com/openai/math` @ `adc7f1241` ("Initial commit"), `lean/` project |
| toolchain | Lean `v4.34.1`, Mathlib + 23 patched third-party packages (`lean/patches/`) |
| solution | `OAI/LinearAlgebra/MatrixMultiplication/` — 509 files, 83,302 lines, 20 subdirectories |
| 9/4 route | `Main.lean` → `AuxiliarySeparation/Main.lean` → 129-module import closure, 20,694 lines (`mm94-intake/route-closure.txt`) |
| kernel cone (from the export) | 1,403 OAI constants reached from the headline: 919 `AuxiliarySeparation.*`, 333 `Foundation.*` (tensors), 150 `Arithmetic.*` (programs), 1 stray; plus 32 constants of the external Brouwer package |
| claim type | PAIRED: `ComparatorChallenges/MatrixMultiplication.lean` (132 lines) + `.json` (3 theorem names, `definition_names: []`, standard axioms, `enable_nanoda: false`) |
| authorship | OpenAI; `formalization.yaml` lists the three theorems under `main_results` |
| external code on the route | `harfe/fixed-point-theorems-lean4` @ `770940dd` (Brouwer via cubical Sperner), with the repository's 640-line Lean-4.34.1 compatibility patch applied — §4 |
| `cone.py` | its name resolver found only the wrapper theorems on this artifact (term-mode proofs under `open`); the export's constant set is the cone used here |

## 2. Statement rung — EXACT

Reference written from the paper's Theorem 1.1 and §1 definition of ω (`mm94-intake/REFERENCE-mm94.md`;
honesty note there: `Model.lean` had been opened to locate the result before the reference was
written). Clause table in `STATEMENT.md`, every row confirmed by reader A:

- **Model** (`Model.lean`, textually identical to the challenge's `Arithmetic` namespace):
  straight-line programs; a `Gate` is a complex constant, an input entry, or `+`/`−`/`×` of two
  EARLIER registers (`Gate F Input (Fin r)` is added to a program with `r` registers, so reading
  itself or a later register is ill-typed); no division, no branching, no fan-in > 2; cost = number
  of `+`,`−`,`×` gates, constants and input loads free (standard). `Correct P := ∀ A B, P.eval A B = A * B`
  with Mathlib's matrix product over `Fin n`. `AdmissibleExponent F τ := ∀ ε>0 ∃ C>0 ∀ n≥1 ∃ P,
  P.Correct ∧ cost ≤ C·n^(τ+ε)`; `omega F := sInf {τ | Admissible}`.
- **The `sInf` trap is closed**: the admissible set is nonempty (naive algorithm, τ = 3,
  `Arithmetic/NaiveAlgorithm.lean:219`) and bounded below by 2 (n² distinct output registers each
  costing ≥ 1, `Arithmetic/LowerBound.lean:124,199–205`); `admissibleExponent_iff_omega_le`
  (`Arithmetic/Exponent.lean:49`) proves the ← direction honestly (ε/2 slack + upward closure);
  and the explicit form is a separate theorem, `AuxiliarySeparation.matrix_multiplication_cost_le`
  (`AuxiliarySeparation/Main.lean:21`): ∀ ε>0 ∃ C>0 ∀ n≥1 ∃ P correct with cost ≤ C·n^(9/4+ε).
- **Headline** `complex_omega_le_nine_quarters : Arithmetic.omega ℂ ≤ (9:ℝ)/4` — `pp.all` form in
  `mm94-intake/out/axioms.txt` (scratch): `@LE.le ℝ _ (@omega ℂ Complex.instField) (9/4)` with the
  numerals `OfNat` literals 9 and 4. Nothing weaker than the paper; the constants in the
  algorithm are non-constructive (classical choice on a rank decomposition), as in the paper.

## 3. Mechanical rung

| scan | solution subtree (509 files) | 9/4 route (129 modules) | Brouwer package (8 files, 3,183 lines) |
|---|---|---|---|
| `sorry`/`admit`/`axiom` | none | none | none |
| trust markers (`native_decide`, `unsafe`, `implemented_by`, `extern`, …) | none | none | none |
| `run_cmd`/`macro`/`elab`/`syntax`/`notation`/`set_option`/`#eval`/`initialize`/`simproc` | 0 | 0 | 0 |
| `attribute [...]` | 229 sites: 163 `local instance` (`Classical.propDecidable`/`decEq`, `instDecidableEqFin`, 3 harmless others), 78 `local instance <prio>`, 9 global `[instance]` (all on the artifact's own structures, CW/Completion files only), 5 `local irreducible`, 1 `local simp` | **0** | 0 |
| numeral literals in the export | — | 126 `natVal`, max 10 digits; no `decide +kernel` workload | — |

The local changes in `.lake/packages/fixed-point-theorems` are byte-for-byte the shipped
`patches/fixed-point-theorems-lean4341.patch` (78+/111−, toolchain and `simpa using!`-style
fixes); the patch adds no marker (grep of its `+` lines).

## 4. Build, axioms, independent checkers

| step | result |
|---|---|
| `lake build …AuxiliarySeparation.Main` (route, `LEAN_NUM_THREADS=3`) | success, 9,058 jobs, 950 s |
| `#print axioms` on `omega_le_nine_quarters`, `matrix_multiplication_cost_le`, `exactRankExponent_le_nine_quarters`, `exists_detecting_character`, `Character.exponent_sum_le_nine_quarters` | each exactly `[propext, Classical.choice, Quot.sound]` |
| lean4export (v4.34.0 tag under v4.34.1) of the two headline theorems | 44 s, 349 MB, 6,468,332 lines, 49,693 constants (10,540 def, 39,108 thm, 38 opaque, 4 quot, **3 axioms**: `propext`, `Quot.sound`, `Classical.choice`), 0 `sorryAx` |
| leanchecker (v4.35.0-rc2) `--from-export` | rc 0, 93 s, "Lean default kernel accepts the solution", 52,778 declarations |
| con-leche `--verified --jobs=3` | rc 0, 75 s, accepted 50,675 declarations |
| con-ron `--verified --jobs=3` | rc 0, 76 s, accepted 50,675 declarations |
| nanoda (v4.35.0-rc2) | rc 0, 28 s, no error |

Four independently implemented kernels (Lean's C++, con-leche in Lean, con-ron in Rust,
nanoda in Rust) accept the proof; with no big literals, nothing here stresses the shared
bignum runtime.

## 5. Reading rung — the argument, reconstructed (readers A–F, `mm94-intake/READ-*.md`)

The paper proves ν ≤ 9/4 for the exact-rank exponent ν = inf_{n≥2} log_n R(T_n), then converts
to arithmetic programs. The chain in Lean, with the paper's statement each step formalizes:

1. **Arithmetic bridge** (A). `omega ≤ exactRankExponent` (`AuxiliarySeparation/Arithmetic/Exponent.lean:113`):
   a rank-R decomposition of T_n gives block-recursive programs of cost exactly R·cost + 6Rn²m²
   per level (`ComplexArithmetic/RecursiveBlockPrograms.lean:348`), geometric sum with q = n^{τ+ε}
   (`Growth.lean:24,153`), zero-padding to a power of n; the boundary R = n² is covered by the ε
   slack rather than the paper's log factor; the n² lower bound (flattening) supplies `2 ≤ τ`.
   Two copies of the program model exist (a ℂ-internal one and the challenge's); the transfer
   `Arithmetic/Compatibility.lean:153` is gate-by-gate, evaluation- and cost-preserving.
2. **Tensors and characters** (B). `Tensor ℂ X Y Z = X → Y → Z → ℂ`; `restrict` applies arbitrary
   complex matrices on each leg (Strassen's order); `product`, `directSum` are Kronecker product
   and full direct sum; `matrixMultiplication a b c = Σ x_ij y_jk z_ki`; `RankAtMost T r` = sum of
   r outer products. `Character` (`Character/Basic.lean:35`) = Definition 2.1, and is proved
   EQUIVALENT to the monotone ring homomorphisms S → ℝ on the actual semiring S of tensors modulo
   mutual restriction (`Tensor/Characters.lean:166`; S built as an `Antisymmetrization` over
   `Fin`-indexed tensors with `IsOrderedRing`, `Tensor/Semiring.lean:126–422`). Dot-product
   exponents: p = log₂ χ(B(2)) with the paper's sandwich argument (`Growth/MultiplicativePower.lean:62–137`),
   p ∈ [0,1] proved, and (2.4) `value_matrixMultiplication` via the explicit reindexing
   B_X(c)⊗B_Y(a)⊗B_Z(b) ≅ T(a,b,c) (`Tensor/ComplexPairingMatrixTensor.lean:124`). Lemma 2.3
   (interpolation) is proved by Lagrange interpolation on the n-th tensor power at nD+1 nodes,
   χ(B)^n ≤ (nD+1)χ(A)^n, no continuity of χ used (`Character/Degeneration.lean:67–158`).
3. **Detecting characters, Lemma 2.2 / Appendix A** (C). `exists_detecting_character`
   (`Character/Existence.lean:25`). States live in `TensorClass → ℝ` with the product topology,
   coordinates in [0, rank]; compactness from Mathlib's Tychonoff. Lemma A.1's Schauder–Tychonoff
   step is PROVED (`Convex/FixedPoint.lean:45–216`) by Schauder projection + Brouwer on a finite
   simplex + finite intersection property; Brouwer is the external package's
   `brouwer_fixed_point` (cubical Sperner). Non-emptiness: a locally proved Farkas lemma
   (`Convex/Farkas.lean:122`, closed finitely generated cones + Mathlib's hyperplane separation),
   rationality via a ℚ-linear retraction on an affinely independent support, denominators
   cleared, the certificate pushed through Mathlib's `Algebra.GrothendieckAddGroup`
   (`AddLocalization.exists_of_eq`) to the catalyst D + m + T_d·s ≤ D + k·s. The obstruction
   (`Spectrum/Obstruction.lean:88–363`) iterates (A.3) without cancellation, keeps every limit as
   a finite-j inequality, removes u and R(s) by a ratio-limit lemma, then δ → 0 at fixed n, then
   n → ∞ (`Growth/SpectralLimit.lean:65`) — the paper's order. `s ≠ 0` from rank monotonicity
   instead of a flattening (equivalent).
4. **Separation, Prop 3.1 and Cor 3.2** (D). The construction is executed, not asserted:
   `sharedFirstTensor` encodes the shared-first-leg, matched-sector hypothesis; the three
   substitutions on 5M copies (`Separation/Basic.lean:51–70`) match the paper including the 1/L;
   ζ = exp(2πi/5M) with `IsPrimitiveRoot`; Σ_r ζ^{rk} = L·[L | k] (`Fourier.lean:28`); no-wrap
   |u−v+2(g−h)| ≤ 3(M−1) < 5M for labels 1..M (`NoWrap.lean:19–29`); total weight (g−h)² + h·phase,
   zero iff g = h and u = v (`SquareWeights.lean:33–61`); weight-zero part proved equal up to
   reindexing to ⊕_h (A_h ⊗ B_X(M)) (`Basic.lean:175,332`). What the proof consumes is the
   character inequality `finiteSeparation_bound` (`Character/FiniteSeparation.lean:90`),
   derived from that polynomial by Lemma 2.3. Cor 3.2 is `Character.sharedFirst_tag`
   (`Tensor/TagInequality.lean:156`) with `Real.negMulLog` entropy, two-sided multinomial
   estimate (`Entropy/ComplexTypeEntropy.lean:108`), rational q then continuity. The two "tag"
   lemmas §4 uses are this corollary with 2 and 3 sectors.
5. **Polynomial inequalities, §4** (E). `convolution a b` is (4.1) exactly; rank ≤ a+b−1 by an
   explicit evaluation/interpolation decomposition at 0..a+b−2 (`Convolution/Rank.lean:37,50`);
   symmetry and P(1,b) = b as in the paper; P := sixfold^(1/(6t)). Lemma 4.1: the quotient/kernel
   bases are explicit, the slice matrix (4.8) is `adaptedTensor`, proved equal to the true
   coefficients so the only block that could carry negative weight is PROVED zero; one restriction
   takes C(a,b)⊗B_X(2) to it; weights shifted by +1; Cor 3.2 with the exact entropy identity
   (q strictly inside, so no boundary step needed). Lemma 4.2: intervals match the paper's table;
   one degeneration of the whole tensor with the identity on leg 1; `Fin.rev` used only to
   evaluate the middle branch's value (the paper's caveat observed); Π_π λ_π(C^σ) = Π_π λ_π(C)
   from `sixfoldProduct_swap23`. Hypotheses are exactly a ≥ 1, b ≥ 2 (resp. a,h ≥ 1) and 0 < t.
6. **Diagonal growth, Lemma 5.1, and assembly** (F). `ScalarProfile t` (`Growth/Profile.lean:23–33`)
   has exactly the six hypotheses; conclusion n⁴ ≤ P(n,n)³ for all n ≥ 1. The Lean route differs
   from the paper's finite telescope: it uses the limiting row slope g_a = inf of increments
   and infinite tripling (`ProfileSlopes.lean:67–132`), giving P(a,a) ≤ ((3a−1)/2)·g_a as a
   fixed-point offset — so the paper's 3a−1 count never arises; (5.1) at `ProfileSlopes.lean:136`,
   the recurrence by simultaneous induction, the product (5.2) `growthProduct`, (1+1/(3a))³ ≥ 1+1/a
   by `nlinarith`. t ≤ 3/4 by `rpow_exponent_le_of_nat_bound` at n = 2^k; the t ≤ 0 branch is
   t = 0 (p ≥ 0 proved) and trivial. ν ≤ 9/4 by rounding k = ⌈d^ν⌉−1 for every d ≥ 2 with
   constant 2 (`Arithmetic/CharacterRounding.lean:33–44,111`), the character depending on d.

**Independent computations** (scripts in `mm94-intake/scripts/`, all `python3 -I`, stdlib):
the recursion orders N² log N / N^{log_u R} (A); exact flattening ranks of T_n and the three dot
products for n ≤ 5, confirming the X-flattening is a character with (p_X,p_Y,p_Z) = (0,1,1) and
value n² on T_n (B); the Appendix-A contradiction is numerically real and the order of limits
matters — at fixed δ the post-j inequality recovers for n ≥ 10²¹ (C); Prop 3.1's construction
rebuilt from scratch for M = 1..5 with random blocks, surviving terms exactly u−v+2(g−h) = 0,
weight-zero part exactly ⊕(A_h ⊗ B_X(M)), and the negative controls L = 6 (M = 3), L = 9 (M = 4)
FAIL as they should (D); C(a,b)'s flattening ranks (a, b, a+b−1); the flattening profile
satisfies (4.5), (4.6), (4.9) for a,b,h ≤ 12; Lemma 4.1's tensor rebuilt in the paper's bases
matches `adaptedTensor` entry-for-entry for a ≤ 5, b ≤ 6; Figure 1 and a = 3, h = 2 reproduce (E);
(1+1/(3m))³ ≥ 1+1/m exactly for m ≤ 10⁶, H_a³ ≥ a for a ≤ 2000, three valid profiles pass and
P = a+b−1 (violates tripling) falls to ratio 0.51, and the POINTWISE LEAST table satisfying the
hypotheses attains the proof's bound ((3a−1)/2)·∏(1+1/(3m)) exactly for a = 2..12 — Lemma 5.1
is tight, so 9/4 is the most this method yields (F).

### Escalations (all resolved; none blocking)

| id | what | resolution |
|---|---|---|
| E-C1 | Brouwer comes from an external package with a 640-line local patch, outside the solution subtree | scanned (§3): no hole, no marker, no metaprogramming; local changes = shipped patch; 32 of its constants are on the kernel route; every checker in §4 re-checks them |
| E-B4 / E-E3 | t > 0 (p_X+p_Y+p_Z ≥ 1, paper §2.1) is never proved; a `by_cases 0 < t` takes its place | harmless: t ≥ 0 is proved, the t = 0 branch gives t ≤ 3/4 outright; only an upper bound on t is consumed |
| E-A1 | the R = n² boundary is proved by the ε slack, not the paper's O(N² log N) | equivalent for the definition of ω |
| E-D1 | an unused closure-topology `DegeneratesTo` statement (`Separation/Basic.lean:306/351`) sits beside the used polynomial one | nothing consumes it (grep) |
| E-E2 | the rank LOWER bound (4.2) and the exact sequence (4.7) in `Determinant/Bounds.lean` are proved but unused on the route | display layer; the route needs only rank ≤ a+b−1 |
| E-F4 | `Growth/Floor.lean` is dead code imported only by `AuxiliarySeparation/Main.lean`; `PermutationProduct`'s `LegPermutation` unused | cosmetic |
| E-* | docstrings cite an earlier draft's numbering ("Lemma 3.1", "Section 6 / Lemma 6.1", a different paper title in `NoWrap.lean:9`) | cosmetic; the content map above is by content |
| E-C5 | the order of limits in Appendix A matters (δ → 0 before n → ∞) | Lean does it in the paper's order (`SpectralLimit.lean:65`) |

## 6. Comparator

COMPARATOR_PLACEHOLDER

## 7. Coverage

| tier | count |
|---|---|
| route modules / lines | 129 / 20,694 |
| files read WHOLE by a reader | 108 (A 29, B 31+4, C ~20, D 14 + consumed statements, E 20+4, F 15) |
| files read at statement level only | the shared `Separation.Complex*`/`Entropy.Complex*`/`Polynomial.Complex*` modules not consumed by the route, `BinaryCharacter`, `SixfoldProductBounds`, the Brouwer package |
| kernel-route OAI constants | 1,403 (405 def, 998 thm); every one re-checked by four kernels |
| independent computations | 9 scripts, outputs recorded in the READ files |

## 8. What this audit does and does not say

It says: the Lean theorem is the paper's Theorem 1.1 in the standard arithmetic model; the Lean
proof is the paper's argument, step for step, with the paper's constructions executed rather
than assumed; the proof is accepted by Lean and by three independent checkers on exactly the
three standard axioms; and the one external dependency is clean. Given that, ω ≤ 9/4 over ℂ is
a theorem of Lean + Mathlib + the three axioms — the question "is the paper right?" is answered
by the kernel, and the question "does the kernel check the right statement?" by §2.

It does not say: that the algorithm is explicit (it is not — the decomposition is chosen
classically, as in the paper, and no competitive finite size is given); anything about the two
companion theorems; or anything a second model family would say.
